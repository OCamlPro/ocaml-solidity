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
  | LUsingFor
(*
let is_external_lookup = function
  | LExternal -> true
  | LAny | LInternal | LStatic (_) | LSuper -> false
*)
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
  | LUsingFor ->
      is_statically_visible visibility ~library:true && not variable

let filter_by_visibility lookup idl =
  List.filter (fun id ->
      match id, lookup with
      | ((Field _ | Constr _), _), _ ->
          false
      | _, LAny ->
          true
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
      | (Type _, inherited), LStatic (Contract, _) ->
          not inherited
      | (Event _, _), (LInternal | LStatic (Library, _)) ->
          true
      | (Event _, _), (LExternal | LSuper | LUsingFor) ->
          false
      | (Event _, inherited), LStatic ((Contract | Interface), is_parent) ->
          is_parent && not inherited
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
        function_selector = None;
        function_is_method = true;
        function_is_primitive = false; }





(* ---------- Environment construction (internal/external) ---------- *)

let error_already_declared pos ident =
  error pos "Identifier %s already declared" (Ident.to_string ident)

let error_defined_twice pos kind =
  error pos "%s with same name and arguments defined twice" kind

let error_inherited_over_non_inherited pos =
  error pos "Can not add an inherited variable over a non-inherited symbol !"

let ensure_undefined pos env ident =
  if IdentMap.mem ident env.ident_map then
    error_already_declared pos ident

let add_unique_ident pos env ident desc =
  ensure_undefined pos env ident;
  env.ident_map <- IdentMap.add ident [desc] env.ident_map

let replace_idents _pos env ident descl =
  env.ident_map <- IdentMap.add ident descl env.ident_map

let add_contract pos env contract_name contract_desc =
  add_unique_ident pos env contract_name (Contract (contract_desc), false)

let add_type pos env ~inherited type_name type_desc =
  add_unique_ident pos env type_name (Type (type_desc), inherited)

(* Enums are inheritable, but not overloadable nor overridable *)
let add_enum pos env ~inherited enum_name enum_abs_name values =
  let values_rev, _ =
    List.fold_left (fun (enum_values, i) enum_value ->
        IdentAList.add_uniq enum_value i enum_values, (i+1)
      ) ([], 0) values
  in
  let enum_desc = { enum_abs_name; enum_values = List.rev values_rev } in
  add_type pos env ~inherited enum_name (TDEnum enum_desc)

(* Structs are inheritable, but not overloadable nor overridable *)
let add_struct pos env ~inherited struct_name struct_abs_name struct_def =
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

(* Non-public variables are inheritable, but not overloadable nor overridable *)
let add_nonpublic_variable pos env ~inherited variable_name variable_desc =
(*  add_unique_ident pos env variable_name (Variable (variable_desc), inherited)
*)
  let iddl =
    Option.value ~default:[] (IdentMap.find_opt variable_name env.ident_map) in
  let iddl_rev =
    List.fold_left (fun iddl (id, inh) ->
        if inherited && not inh then
          error_inherited_over_non_inherited pos;
        match id with
        | Field _ | Constr _ ->
            failwith "Invariant broken"
        | Modifier _ | Variable _ | Type _ | Event _ | Contract _ ->
            error_already_declared pos variable_name
        | Function (fd)
(* TODO: What if public, since it also has external ? *)
          when not inh || not (is_external fd.function_visibility) ->
            (* Note: multiple definition in the same contract *)
            error_already_declared pos variable_name
        | Function (fd) ->
            (Function (fd), inh) :: iddl
      ) [] iddl
  in
  replace_idents pos env variable_name
    (List.rev ((Variable (variable_desc), inherited) :: iddl_rev))

(* Public variables are inheritable, overloadable and overridable *)
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
          error_inherited_over_non_inherited pos;
        match id with
        | Field _ | Constr _ ->
            failwith "Invariant broken"
        | Modifier _ | Variable _ | Type _ | Event _ | Contract _ ->
            error_already_declared pos variable_name
        | Function (_fd) when not inh ->
            (* Note: multiple definition in the same contract *)
            error_already_declared pos variable_name
        | Function (fd)
          when not (Solidity_type.same_signature
                      fd.function_params function_desc.function_params) ->
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

(* Functions are inheritable, overloadable and overridable *)
let add_function pos env ~inherited function_name function_desc =
  let iddl =
    Option.value ~default:[] (IdentMap.find_opt function_name env.ident_map) in
  let iddl_rev =
    List.fold_left (fun iddl (id, inh) ->
        if inherited && not inh then
          error_inherited_over_non_inherited pos;
        match id with
        | Field _ | Constr _ ->
            failwith "Invariant broken"
        | Modifier _ | Variable _ | Type _ | Event _ | Contract _ ->
            error_already_declared pos function_name
        | Function (fd)
          when not (Solidity_type.same_signature
                      fd.function_params function_desc.function_params) ->
            (* Note: overload (hierachy-wise), because signature is different *)
            (Function (fd), inh) :: iddl
        | Function (_fd) when not inh ->
            (* Note: multiple definition in the same contract *)
            error_defined_twice pos "Function"
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

(* Modifiers are inheritable and overridable, but not overloadable *)
let add_modifier pos env ~inherited modifier_name modifier_desc =
  begin
    match IdentMap.find_opt modifier_name env.ident_map with
    | None ->
        ()
    | Some (idl) ->
        if List.exists (fun (id, inh) ->
            match id with
            | Field _ | Constr _ ->
                failwith "Invariant broken"
            | Modifier (_md) -> not inh
(* TODO: if trying to change signature, error:
   Override changes modifier signature *)
(*
when adding inherited over inherited, keep both ?
and replace by a single one when non-inherited
this allows to give more expressive message when overriding with non-inherited
*)
            | Function _ | Variable _ | Type _
            | Event _ | Contract _ -> true) idl
        then
          error_already_declared pos modifier_name
  end;
  replace_idents pos env modifier_name
    [(Modifier (modifier_desc), inherited)]

(* Events are inheritable and overloadable, but not overridable *)
let add_event pos env ~inherited event_name event_desc =
  let iddl =
    Option.value ~default:[] (IdentMap.find_opt event_name env.ident_map) in
  let iddl_rev =
    List.fold_left (fun iddl (id, inh) ->
        if inherited && not inh then
          error_inherited_over_non_inherited pos;
        match id with
        | Field _ | Constr _ ->
            failwith "Invariant broken"
        | Modifier _ | Variable _ | Function _ | Type _ | Contract _ ->
            error_already_declared pos event_name
        | Event (ed)
          when not (Solidity_type.same_signature
                      ed.event_params event_desc.event_params) ->
            (* Note: overload (hierachy-wise), because signature is different *)
            (Event (ed), inh) :: iddl
        | Event (_ed) ->
            (* Note: multiple definition in the same contract *)
            error_defined_twice pos "Event"
      ) [] iddl
  in
  replace_idents pos env event_name
    (List.rev ((Event (event_desc), inherited) :: iddl_rev))

(* type_opt = None => all_types = * *)
let add_using_for env lib type_opt =
  let uf_opt = AbsLongIdentMap.find_opt lib.contract_abs_name env.using_for in
  let lib_env, tl =
    match uf_opt, type_opt with
    | None, None -> lib.contract_env, []
    | None, Some (t) -> lib.contract_env, [t]
    | Some (env, []), _ -> env, []
    | Some (env, _), None -> env, []
    | Some (env, tl), Some (t) ->
        if List.exists (fun t' ->
               Solidity_type.same_type ~ignore_loc:true t t') tl then
          env, tl
        else
          env, t :: tl
  in
  env.using_for <-
    AbsLongIdentMap.add lib.contract_abs_name (lib_env, tl) env.using_for



(* Add everything from the contract's hierarchy in the contract's environment *)
let add_parent_definitions pos ~preprocess c =
  List.iter (fun (_lid, cd) ->
      IdentMap.iter (fun id idl ->
          List.iter (fun (id_desc, inh) ->
              if not inh then
                match id_desc, preprocess with
                | Type (td), true ->
                    add_type pos c.contract_env ~inherited:true id td
                | Event (ed), false ->
                    add_event pos c.contract_env ~inherited:true id ed
                | Variable (vd), false ->
                    if is_inheritable vd.variable_visibility then
                      add_variable pos c.contract_env ~inherited:true id vd
                    else
                      ensure_undefined pos c.contract_env id
                | Modifier (md), false ->
                    add_modifier pos c.contract_env ~inherited:true id md
                | Function (_fd), false when Ident.equal id Ident.constructor ->
                    () (* are fallback/receive inherited ? *)
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
  { upper_env;  ident_map = IdentMap.empty; using_for = AbsLongIdentMap.empty }



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
    function_selector = None;
    function_is_method = false; (* can be true *)
    function_is_primitive = true; }
  in
  TFunction (fd, { new_fun_options with kind })


let primitive_fun_desc ?(returns_lvalue=false)
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
    function_selector = None;
    function_is_method = false; (* can be true *)
    function_is_primitive = true; }
  in
  Function (fd)

let primitive_var_desc (*?(is_lvalue=false)*) variable_type =
  let vd = {
    variable_abs_name = LongIdent.empty;
    variable_type;
    variable_visibility = VPublic; (* or private for builtins *)
    variable_mutability = MImmutable; (* depends ? *)
    variable_local = false;
    variable_init = None;
    variable_override = None;
    variable_getter = None;
    variable_is_primitive = true; }
  in
  Variable (vd)


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


