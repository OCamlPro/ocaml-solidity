(**************************************************************************)
(*                                                                        *)
(*  Copyright (c) 2021 OCamlPro & Origin Labs                             *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*  This file is distributed under the terms of the GNU Lesser General    *)
(*  Public License version 2.1, with the special exception on linking     *)
(*  described in the LICENSE.md file in the root directory.               *)
(*                                                                        *)
(*                                                                        *)
(**************************************************************************)

open Solidity_common
open Solidity_ast
open Solidity_checker_TYPES
open Solidity_exceptions

let error = type_error

type lookup_kind =
  | LAny
  | LInternal
  | LExternal
  | LStatic of contract_kind * bool (* true = contract is a parent *)
  | LSuper
  | LUsingFor

let is_internally_visible = function
  | VPublic | VInternal | VPrivate -> true
  | VExternal -> false

let is_externally_visible = function
  | VExternal | VPublic -> true
  | VInternal | VPrivate -> false

let is_statically_visible ~library = function
  | VPublic | VInternal -> true
  | VExternal -> library
  | VPrivate -> false

let is_defined = function
  | Defined -> true
  | Imported | Inherited -> false

let is_imported = function
  | Imported -> true
  | Defined | Inherited -> false

let is_inherited = function
  | Inherited -> true
  | Defined | Imported -> false

(* variables and functions only *)
let is_visible lookup visibility ~origin ~variable =
  match lookup with
  | LAny ->
      true
  | LInternal -> (* Note: privates are only those defined by the contract *)
      is_internally_visible visibility
  | LExternal ->
      is_externally_visible visibility
  | LStatic (Interface, _) ->
      !for_freeton
  | LStatic (Contract, false) ->
      is_statically_visible visibility ~library:false
  | LStatic (Contract, true) ->
      (* Fabrice: I set ~library:true for a freeton contract in
         tvm.functionId(D4Auct) *)
      let a = is_statically_visible visibility ~library:true in
      let b = not (is_inherited origin) in
      a && b
  | LStatic (Library, false) ->
      is_statically_visible visibility ~library:true
  | LStatic (Library, true) -> (* i.e. call from the library itself *)
      is_internal visibility ||
      variable && is_public visibility
  | LSuper ->
      is_statically_visible visibility ~library:false && not variable
  | LUsingFor ->
      is_statically_visible visibility ~library:true && not variable

let filter_by_visibility lookup idl =
  List.filter (fun id ->
      match id, lookup with
      | ((Field _ | Constr _ | Alias _), _), _ ->
          false
      | _, LAny ->
          true
      | (Module _, _), LInternal ->
          true
      | (Module _, _), (LExternal | LStatic (_) | LSuper | LUsingFor) ->
          false
      | (Contract _, _), LInternal ->
          true
      | (Contract _, _), (LExternal | LStatic (_) | LSuper | LUsingFor) ->
          false
      | (Modifier _, _), LInternal -> (* Maybe allow Lib.Mod ? *)
          true                        (* and Cnt.Mod when Cnt is parent ? *)
      | (Modifier _, _), (LExternal | LStatic (_) | LSuper | LUsingFor) ->
          false
      | (Type _, _), (LInternal | LStatic ((Library | Interface), _)) ->
          true
      | (Type _, _), (LExternal | LSuper | LUsingFor) ->
          false
      | (Type _, origin), LStatic (Contract, _) ->
          not (is_inherited origin)
      | (Event _, _), (LInternal | LStatic (Library, _)) ->
          true
      | (Event _, _), (LExternal | LSuper | LUsingFor) ->
          false
      | (Event _, origin), LStatic ((Contract | Interface), is_parent) ->
          is_parent && not (is_inherited origin)
      | (Variable { variable_visibility; _ }, origin), _ ->
          (* TODO: return as function when external ? *)
          is_visible lookup variable_visibility ~origin ~variable:true
      | (Function ({ function_visibility; _ }), origin), _ ->
          is_visible lookup function_visibility ~origin ~variable:false
    ) idl


let rec lookup_ident
    (env : env) ~(upper : bool) ~(lookup : lookup_kind)
    (ident : Ident.t) : ident_desc list =
  let idl =
    filter_by_visibility lookup (
        Option.value ~default:[] (IdentMap.find_opt ident env.ident_map))
  in
  match idl with
  | [] ->
      begin
        match upper, env.upper_env with
        | true, Some (env) -> lookup_ident env ~upper ~lookup ident
        | _ -> []
      end
  | _ -> List.map fst idl

let rec lookup_lident
    (env : env) ~(upper : bool) ~(lookup : lookup_kind)
    (lident : relative LongIdent.t) : ident_desc list =
  match LongIdent.to_ident_list lident with
  | [] -> assert false
  | [ident] ->
      lookup_ident env ~upper ~lookup ident
  | ident :: lident ->
      match lookup_ident env ~upper ~lookup:LAny ident with
      | [] -> []
      | [Contract c] ->
          lookup_lident c.contract_env ~upper:false ~lookup
            (LongIdent.of_ident_list_rel lident)
      | [Module m] ->
          lookup_lident m.module_env ~upper:false ~lookup
            (LongIdent.of_ident_list_rel lident)
      | _ ->
          []

let find_ident env ~lookup ident =
  lookup_ident env ~upper:true ~lookup ident

let find_lident env ~lookup lident =
  lookup_lident env ~upper:true ~lookup lident

let find_type env lident =
  match lookup_lident env ~upper:true ~lookup:LAny lident with
  | [Type (TDEnum (ed))] ->
      Some (TEnum (ed.enum_abs_name, ed))
  | [Type (TDStruct (sd))] ->
      Some (TStruct (sd.struct_abs_name, sd, LStorage (true)))
  | [Contract (cd)] ->
      Some (TContract (cd.contract_abs_name, cd, false (* super *)))
  | [Module (md)] ->
      Some (TModule (md.module_abs_name, md))
  | _ -> None

let find_contract env lident =
  match lookup_lident env ~upper:true ~lookup:LAny lident with
  | [Contract (cd)] -> Some (cd)
  | _ -> None

let find_constructor pos { contract_abs_name; contract_env; _ } =
  match lookup_ident contract_env ~upper:false
          ~lookup:LAny Ident.constructor with
  | [Function (fd)] ->
      fd
  | [_] ->
      error pos "Constructor is not a function !"
  | _ :: _ :: _ ->
      error pos "Multiple definitions found for constructor !"
  | [] ->
      { function_abs_name =
          LongIdent.append contract_abs_name Ident.constructor;
        function_params = [];
        function_returns = [];
        function_returns_lvalue = false;
        function_visibility = VPublic; (* unless abstract ct*)
        function_mutability = MNonPayable;
        function_override = None;
        function_selector = None;
        function_is_method = true;
        function_is_primitive = false;
        function_def = None;
        function_ops = [];
        function_purity = PurityUnknown;
      }

let has_abstract_function cd =
  let exception Found of Ident.t in
  try
    IdentMap.iter (fun id idl ->
        List.iter (fun (id_desc, _inh) ->
            match id_desc with
            | Function { function_def = Some { fun_body = None; _ }; _ }
            | Modifier { modifier_def = { mod_body = None; _ }; _ } ->
                raise (Found (id))
            | _ ->
                ()
          ) idl
      ) cd.contract_env.ident_map;
    None
  with Found (id) ->
    Some (id)

let prim_desc =
  Array.make (Solidity_common.max_primitives + 1) (fun _ -> assert false)

let add_primitive_desc id
    (f : Solidity_common.pos ->
         options ->
         Solidity_checker_TYPES.type_ option ->
         Solidity_checker_TYPES.ident_desc option)
  =
  if (id < 0) then
    error dummy_pos "Negative primitive id";
  if (id > Solidity_common.max_primitives) then
    error dummy_pos "Primitive id above limit";
  prim_desc.(id) <- f
