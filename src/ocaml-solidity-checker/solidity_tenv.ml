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

let error pos fmt =
  Format.kasprintf (fun s -> raise (TypecheckError (s, pos))) fmt




(* ---------- Environment lookup functions (internal/external) ---------- *)

type lookup_kind =
  | LAny
  | LInternal
  | LExternal
  | LStatic of contract_kind * bool (* true = contract is a parent *)
  | LSuper

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

(* variables and functions only *)
let is_visible lookup visibility ~inherited ~variable =
  match lookup with
  | LAny ->
      true
  | LInternal -> (* Note: privates are only those defined by the contract *)
      is_internally_visible visibility
  | LExternal ->
      is_externally_visible visibility
  | LStatic (Interface, _) ->
      false
  | LStatic (Contract, false) ->
      false
  | LStatic (Contract, true) ->
      is_statically_visible visibility ~library:false && not inherited
  | LStatic (Library, false) ->
      is_statically_visible visibility ~library:true
  | LStatic (Library, true) -> (* i.e. call from the library itself *)
      is_internal visibility ||
      variable && is_public visibility
  | LSuper ->
      is_statically_visible visibility ~library:false && not variable

let filter_by_visibility lookup idl =
  List.filter (fun id ->
      match id, lookup with
      | _, LAny ->
          true
      | (Contract _, _), LInternal ->
          true
      | (Contract _, _), (LExternal | LStatic (_) | LSuper) ->
          false
      | (Type _, _), (LInternal | LStatic ((Library | Interface), _)) ->
          true
      | (Type _, _), (LExternal | LSuper) ->
          false
      | (Type _, inherited), LStatic (Contract, _) ->
          not inherited
      | (Modifier _, _), LInternal ->
          true
      | (Modifier _, _), (LExternal | LStatic (_) | LSuper) ->
          false
      | (Variable { variable_visibility; _ }, inherited), _ ->
          (* TODO: return as function when external ? *)
          is_visible lookup variable_visibility ~inherited ~variable:true
      | (Function ({ function_visibility; _ }), inherited), _ ->
          is_visible lookup function_visibility ~inherited ~variable:false
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
        | true, Some env -> lookup_ident env ~upper ~lookup ident
        | _ -> []
      end
  | _ -> List.map fst idl

let rec lookup_lident
    (pos : pos) (env : env) ~(upper : bool) ~(lookup : lookup_kind)
    (lident : relative LongIdent.t) : ident_desc list =
  match LongIdent.to_ident_list lident with
  | [] -> assert false
  | [ident] -> lookup_ident env ~upper ~lookup ident
  | ident :: lident ->
      match lookup_ident env ~upper ~lookup:LAny ident with
      | [] -> []
      | [Contract c] ->
          lookup_lident pos c.contract_env ~upper:false ~lookup
            (LongIdent.of_ident_list_rel lident)
      | _ ->
(* TODO: just None ? *)
          error pos "Member %s not found or not visible after \
                     argument-dependent lookup in %s"
            (Ident.to_string (List.hd lident)) (Ident.to_string ident)
(* TODO: find_lident no longer needed in typecheck // error irrelevant *)

let find_ident env ~lookup ident =
  lookup_ident env ~upper:true ~lookup ident

let find_lident pos env ~lookup lident =
  lookup_lident pos env ~upper:true ~lookup lident

let find_type pos env lident =
  match lookup_lident pos env ~upper:true ~lookup:LAny lident with
  | [Type (TDEnum (ed))] ->
      Some (TEnum (ed.enum_abs_name, ed))
  | [Type (TDStruct (sd))] ->
      Some (TStruct (sd.struct_abs_name, sd, LStorage (true)))
  | [Contract (cd)] ->
      Some (TContract (cd.contract_abs_name, cd, false (* super *)))
  | _ -> None

let find_contract pos env lident =
  match lookup_lident pos env ~upper:true ~lookup:LAny lident with
  | [Contract (cd)] -> Some (cd)
  | _ -> None
(*
let find_constructor cd =
  match lookup_ident cd.contract_env ~upper:false
          ~lookup:LAny Ident.constructor with
  | [Function fd] -> Some (fd)
  | _ -> None
*)
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
        function_def = None;
        function_override = None;
        function_selector = None; }





(* ---------- Environment construction (internal/external) ---------- *)

let ensure_undefined pos env ident =
  if IdentMap.mem ident env.ident_map then
    error pos "Identifier %s already declared" (Ident.to_string ident);
  if String.equal (Ident.to_string ident) "default" then
    error pos "Identifier \"default\" is reserved"

let replace_idents pos env ident descl =
  if String.equal (Ident.to_string ident) "default" then
    error pos "Identifier \"default\" is reserved";
  env.ident_map <- IdentMap.add ident descl env.ident_map

let add_unique_ident pos env ident desc =
  ensure_undefined pos env ident;
  env.ident_map <- IdentMap.add ident [desc] env.ident_map



let add_type pos env ~inherited type_name type_desc =
  add_unique_ident pos env type_name (Type (type_desc), inherited)

let add_contract pos env contract_name contract_desc =
  add_unique_ident pos env contract_name (Contract (contract_desc), false)

let add_enum pos env ~inherited enum_abs_name enum_name values =
  let values, _ =
    List.fold_left (fun (enum_values, i) enum_value ->
        IdentAList.add_uniq enum_value i enum_values, (i+1)
      ) ([], 0) values
  in
  let enum_desc = { enum_abs_name; enum_values = List.rev values } in
  add_type pos env ~inherited enum_name (TDEnum enum_desc)

let add_struct pos env ~inherited struct_abs_name struct_name struct_def =
  let struct_desc = {
    struct_abs_name; struct_fields = []; has_mapping = false;
    struct_def; struct_env = env }
  in
  add_type pos env ~inherited struct_name (TDStruct struct_desc)

let add_struct_fields struct_desc fields =
  let fields =
    List.fold_left (fun fields (field_name, field_type) ->
        struct_desc.has_mapping <-
          struct_desc.has_mapping || Solidity_type.has_mapping field_type;
        IdentAList.add_uniq field_name field_type fields
      ) [] fields
  in
  struct_desc.struct_fields <- IdentAList.rev fields

let add_nonpublic_variable pos env ~inherited variable_name variable_desc =
(*  add_unique_ident pos env variable_name (Variable (variable_desc), inherited)
*)
  let iddl =
    Option.value ~default:[] (IdentMap.find_opt variable_name env.ident_map) in
  let iddl_rev =
    List.fold_left (fun iddl (id, inh) ->
        if inherited && not inh then
          error pos "Can not add an inherited variable \
                     over a non-inherited symbol !";
        match id with
        | Modifier _ | Variable _ | Type _ | Contract _ ->
            error pos "Identifier %s already declared"
              (Ident.to_string variable_name)
        | Function (fd)
          when not inh || not (is_external fd.function_visibility) ->
            (* Note: multiple definition in the same contract *)
            error pos "Identifier %s already declared"
              (Ident.to_string variable_name)
        | Function (fd) ->
            (Function (fd), inh) :: iddl
      ) [] iddl
  in
  replace_idents pos env variable_name
    (List.rev ((Variable (variable_desc), inherited) :: iddl_rev))

let add_public_variable pos env ~inherited variable_name variable_desc =
  let function_desc =
    match variable_desc.variable_getter with
    | None -> error pos "Public state variable without getter !"
    | Some (fd) -> fd
  in
  let iddl =
    Option.value ~default:[] (IdentMap.find_opt variable_name env.ident_map) in
  let iddl_rev =
    List.fold_left (fun iddl (id, inh) ->
        if inherited && not inh then
          error pos "Can not add an inherited variable \
                     over a non-inherited symbol !";
        match id with
        | Modifier _ | Variable _ | Type _ | Contract _ ->
            error pos "Identifier %s already declared"
              (Ident.to_string variable_name)
        | Function (_fd) when not inh ->
            (* Note: multiple definition in the same contract *)
            error pos "Identifier %s already declared"
              (Ident.to_string variable_name)
        | Function (fd)
          when not (Solidity_type.same_signature fd function_desc) ->
            (* Note: overload (hierachy-wise), because signature is different *)
            (Function (fd), inh) :: iddl
        | Function (fd) (* when inh *) ->
            (* Note: override because previous function is inherited *)
            begin
              match fd.function_def with
              | None -> () (* error ? *)
              | Some (fd) ->
                  if not fd.fun_virtual then
                    error pos "Trying to override non-virtual function"
            end;
            if is_none variable_desc.variable_override then
              error pos "Overriding public state variable \
                         is missing \"override\" specifier";
            if not (is_external fd.function_visibility) then
              error pos "Public state variables can only override \
                         functions with external visibility";
            if not (convertible_mutability
                      ~from:fd.function_mutability
                      ~to_:function_desc.function_mutability) then
              error pos "Overriding public state variable changes \
                         state mutability from \"%s\" to \"%s\""
                (Solidity_printer.string_of_fun_mutability
                   fd.function_mutability)
                (Solidity_printer.string_of_fun_mutability
                   function_desc.function_mutability);
            iddl
      ) [] iddl
  in
  replace_idents pos env variable_name
    (List.rev ((Variable (variable_desc), inherited) :: iddl_rev))

let add_variable pos env ~inherited variable_name variable_desc =
  match variable_desc.variable_visibility with
  | VPublic ->
      add_public_variable pos env ~inherited variable_name variable_desc
  | _ ->
      add_nonpublic_variable pos env ~inherited variable_name variable_desc

let add_function pos env ~inherited function_name function_desc =
  let iddl =
    Option.value ~default:[] (IdentMap.find_opt function_name env.ident_map) in
  let iddl_rev =
    List.fold_left (fun iddl (id, inh) ->
        if inherited && not inh then
          error pos "Can not add an inherited function \
                     over a non-inherited symbol !";
        match id with
        | Modifier _ | Variable _ | Type _ | Contract _ ->
            error pos "Identifier %s already declared"
              (Ident.to_string function_name)
        | Function (fd)
          when not (Solidity_type.same_signature fd function_desc) ->
            (* Note: overload (hierachy-wise), because signature is different *)
            (Function (fd), inh) :: iddl
        | Function (_fd) when not inh ->
            (* Note: multiple definition in the same contract *)
            error pos "Function with same name and arguments defined twice"
        | Function (fd) (* when inh *) ->
            (* Note: override because previous function is inherited *)
            begin
              match fd.function_def with
              | None -> () (* error ? *)
              | Some (fd) ->
                  if not fd.fun_virtual then
                    error pos "Trying to override non-virtual function"
            end;
            begin
              match function_desc.function_def with
              | None -> () (* error ? *)
              | Some (fd) ->
                  if is_none fd.fun_override && not inh then
                    error pos "Overriding function is missing \
                               \"override\" specifier"
            end;
            if not (convertible_visibility
                      ~from:fd.function_visibility
                      ~to_:function_desc.function_visibility) then
              error pos "Overriding function visibility differs";
            if not (convertible_mutability
                      ~from:fd.function_mutability
                      ~to_:function_desc.function_mutability) then
              error pos "Overriding function changes state \
                         mutability from \"%s\" to \"%s\""
                (Solidity_printer.string_of_fun_mutability
                   fd.function_mutability)
                (Solidity_printer.string_of_fun_mutability
                   function_desc.function_mutability);
            iddl
      ) [] iddl
  in
  replace_idents pos env function_name
    (List.rev ((Function (function_desc), inherited) :: iddl_rev))

let add_modifier pos env ~inherited modifier_name modifier_desc =
  begin
    match IdentMap.find_opt modifier_name env.ident_map with
    | None ->
        ()
    | Some (idl) ->
        if List.exists (fun (id, inh) ->
            match id with
            | Modifier (_md) -> not inh
            | Function _ | Variable _ | Type _ | Contract _ -> true) idl
        then
          error pos "Identifier %s already declared"
            (Ident.to_string modifier_name)
  end;
  (* add_unique_ident pos env modifier_name
   *   (Modifier (modifier_desc), inherited) *)
  replace_idents pos env modifier_name
    [(Modifier (modifier_desc), inherited)]

let add_parent_definitions pos ~preprocess c =
  List.iter (fun (_lid, cd) ->
      IdentMap.iter (fun id idl ->
          List.iter (fun (id_desc, inh) ->
              if not inh then
                match id_desc, preprocess with
                | Type (td), true ->
                    add_type pos c.contract_env ~inherited:true id td
                | Variable (vd), false ->
                    if is_inheritable vd.variable_visibility then
                      add_variable pos c.contract_env ~inherited:true id vd
                    else
                      ensure_undefined pos c.contract_env id
                | Modifier (md), false ->
                    add_modifier pos c.contract_env ~inherited:true id md
                | Function (_fd), false when Ident.equal id Ident.constructor ->
                    ()
                | Function (fd), false ->
                    (* TODO: overriding function should have same visibility *)
                    if is_inheritable fd.function_visibility then
                      add_function pos c.contract_env
                        ~inherited:true id fd
                | _ ->
                    ()
            ) idl
        ) cd.contract_env.ident_map
    ) (List.rev (List.tl (c.contract_hierarchy)))









let new_env ?upper_env () =
  { ident_map = IdentMap.empty; upper_env }

let new_fun_options = {
  kind = KOther;
  value = false;
  gas = false;
  salt = false
}


(* SHOULD move to type builder ? *)
(* have primitive + anonymous ?*)
let primitive_type ?(kind=KOther) ?(returns_lvalue=false)
    arg_types ret_types function_mutability =
  let fd = {
    function_abs_name = LongIdent.empty;
    function_params = List.map (fun t -> (t, None)) arg_types;
    function_returns = List.map (fun t -> (t, None)) ret_types;
    function_returns_lvalue = returns_lvalue;
    function_visibility = VPublic; (* or private for builtins *)
    function_mutability;
    function_def = None;
    function_override = None;
    function_selector = None; }
  in
  TFunction (fd, { new_fun_options with kind })




let prim_type =
  Array.make (Solidity_common.max_primitives + 1) (fun _ -> assert false)

let add_primitive_type id
    (f : Solidity_common.pos ->
         options ->
         Solidity_checker_TYPES.type_ option ->
         Solidity_checker_TYPES.type_ option)
  =
  if (id < 0) then
    error dummy_pos "Negative primitive id";
  if (id > Solidity_common.max_primitives) then
    error dummy_pos "Primitive id above limit";
  prim_type.(id) <- f







(* ----- Check if contract has abstract functions (external use) ----- *)

let has_abstract_function c =
  let exception Found of Ident.t in
  try
    IdentMap.iter (fun id idl ->
        List.iter (fun (id_desc, _inh) ->
            match id_desc with
            | Function { function_def = Some { fun_body = None; _ }; _ } ->
                raise (Found (id))
            | _ ->
                ()
          ) idl
      ) c.contract_env.ident_map;
    None
  with Found (id) ->
    Some (id)



let node_list_pos body =
  match body with
    | [] -> dummy_pos
    | {pos; _} :: _ -> pos


