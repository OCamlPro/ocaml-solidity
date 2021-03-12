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

let sha3kec msg =
  Bytes.unsafe_of_string (EzHash.SHA3KEC.digest (Bytes.unsafe_to_string msg))

let compute_selector pos ~library id args =
  let arg_types =
    List.map (fun (t, _id_opt) ->
        Solidity_type_printer.string_of_type_canonical pos ~library t
      ) args
  in
  let fun_sig =
    Format.asprintf "%a(%s)" Ident.printf id (String.concat "," arg_types) in
  Bytes.to_string (Bytes.sub (sha3kec (Bytes.of_string fun_sig)) 0 4)

let eval_array_length_exp env e =
  let error_invalid () =
    error e.pos "Invalid array length, expected integer \
                 literal or constant expression"
  in
  let rec aux e =
    match strip e with
    | NumberLiteral (q, unit, _hex_size_opt) ->
        apply_unit q unit
    | PrefixExpression (op, e) ->
        begin
          match apply_unop op (aux e) with
          | Some (v) -> v
          | None -> error_invalid ()
        end
    | BinaryExpression (e1, op, e2) ->
        begin
          match apply_binop (aux e1) op (aux e2) with
          | Some (v) -> v
          | None -> error_invalid ()
        end
    | IdentifierExpression (id) ->
        process_ident id
          (Solidity_tenv.find_ident env ~lookup:LInternal (strip id))
    | FieldExpression (e, id) ->
        let cd =
          match strip e with
          | IdentifierExpression (id) ->
              begin
                match Solidity_tenv.find_ident env
                        ~lookup:LInternal (strip id) with
                | [Contract (cd)] ->
                    cd
                | _ ->
                    error id.pos "Undeclared identifier: %a"
                      Ident.printf (strip id)
              end
          | _ ->
              error_invalid ()
        in
        process_ident id
          (Solidity_tenv.find_ident cd.contract_env
             ~lookup:(LStatic (cd.contract_def.contract_kind, false)) (strip id))
    | _ ->
        error_invalid ()

  and process_ident id iddl =
    match iddl with
    | [Variable { variable_mutability = MConstant;
                  variable_init = Some (e); _ }] ->
        aux e
    | _ ->
        error id.pos "Undeclared identifier: %a" Ident.printf (strip id)
  in

  let v = aux e in
  if not (ExtQ.is_int v) then
    error e.pos "Array with fractional length specified"
  else if ExtQ.is_neg v then
    error e.pos "Array with negative length specified"
  else if Z.numbits (Q.num v) > 31 then
    error e.pos "Array too big"
  else
    Q.num v

(* only used to get the type of an ident *)
let type_desc_to_base_type ~loc : type_desc -> type_ =
  function
  | TDEnum (ed) ->
      TEnum (ed.enum_abs_name, ed)
  | TDStruct (sd) ->
      Solidity_type.change_type_location loc
        (TStruct (sd.struct_abs_name, sd, loc))

let type_lid_to_base_type pos ~loc env lid =
  match Solidity_tenv.find_type env lid with
  | Some (t) ->
      Solidity_type.change_type_location loc t
  | None ->
      error pos "type %s is undefined" (LongIdent.to_string lid)

let storage_location_to_location : Solidity_ast.storage_location -> location =
  function
  | Memory ->
      LMemory
  | Storage ->
      LStorage (true)
  | Calldata ->
      LCalldata

let elementary_type_to_type ~loc : Solidity_ast.elementary_type -> type_ =
  function
  | TypeBool ->
      TBool
  | TypeInt (sz) ->
      TInt (sz)
  | TypeUint (sz) ->
      TUint (sz)
  | TypeFixed (sz, dec) ->
      TFixed (sz, dec)
  | TypeUfixed (sz, dec) ->
      TUfixed (sz, dec)
  | TypeAddress (payable) ->
      TAddress (payable)
  | TypeBytes (Some sz) ->
      TFixBytes (sz)
  | TypeBytes (None)->
      TBytes (loc)
  | TypeString ->
      TString (loc)

let rec ast_type_to_type pos ~loc env = function
  | ElementaryType (et) ->
      elementary_type_to_type ~loc et
  | UserDefinedType (lid) ->
      let t = type_lid_to_base_type ~loc pos env (strip lid) in
      set_annot lid (AType t);
      t
  | Mapping (tk, tv) ->
      begin
        match loc with
        | LMemory | LCalldata ->
            error pos "Mapping types can only have a data location of \
                       \"storage\" and thus only be parameters or return \
                       variables for internal or library functions"
        | LStorage (_ptr) ->
            (* Mapping keys are always in memory
               Mapping values are always in storage *)
            TMapping (ast_type_to_type pos ~loc:LMemory env tk,
                      ast_type_to_type pos ~loc:(LStorage (false)) env tv,
                      loc)
      end
  | Array (t, None) ->
      let iloc = Solidity_type.promote_loc loc in
      TArray (ast_type_to_type ~loc:iloc pos env t, None, loc)
  | Array (t, Some (e_sz)) ->
      let sz = eval_array_length_exp env e_sz in
      set_annot e_sz (AType (TUint 256));
      let iloc = Solidity_type.promote_loc loc in
      TArray (ast_type_to_type ~loc:iloc pos env t, Some (sz), loc)
  | FunctionType (ft) ->
      TFunction (function_type_to_desc pos env ft,
                 Solidity_tenv.new_fun_options)

and var_type_to_type pos env ~arg ~ext loc_opt t =
  let loc =
    storage_location_to_location (Option.value ~default:Memory loc_opt) in
  let t = ast_type_to_type pos ~loc env t in
  begin
    if Solidity_type.is_reference_type t then
      begin
        let valid =
          match loc_opt with
          | None -> false
          | Some (Storage) -> not ext
          | Some (Memory | Calldata) -> true
        in
        if not valid then
          let expected =
            if ext then "\"memory\" or \"calldata\""
            else "\"storage\", \"memory\" or \"calldata\""
          in
          let context =
            if not arg then "variable"
            else if ext then "parameter in external function"
            else "parameter in function"
          in
          let given = match loc_opt with
            | None -> "none"
            | Some loc -> Solidity_printer.string_of_storage_location loc
          in
          error pos "Data location must be %s for %s, \
                     but %s was given" expected context given
        else if Solidity_type.has_mapping t &&
                  not (Solidity_type.is_storage_type t) then
          error pos "Type %s is only valid in storage because \
                     it contains a (nested) mapping"
            (Solidity_type_printer.string_of_type t)
      end
    else
      begin
        match loc_opt with
        | Some (loc) ->
            error pos "Data location can only be specified for array, \
                       struct or mapping types, but \"%s\" was given"
              (Solidity_printer.string_of_storage_location loc)
        | None ->
            ()
      end
  end;
  t

and make_function_desc pos env ~funtype ~library ~is_method
    fid function_abs_name params returns function_returns_lvalue
    function_visibility function_mutability function_def : function_desc =
  let ext =
    match function_visibility with
    | VExternal | VPublic -> true
    | _ -> false
  in
  let function_params =
    List.map (fun (t, loc_opt, name_opt) ->
        var_type_to_type pos env ~arg:true ~ext loc_opt t,
        Option.map strip name_opt
      ) params
  in
  let function_returns =
    List.map (fun (t, loc_opt, name_opt) ->
        var_type_to_type pos env ~arg:true ~ext loc_opt t,
        Option.map strip name_opt
      ) returns
  in
  let function_selector =
    if funtype then
      None
    else
      if ext then Some (compute_selector pos ~library fid function_params)
      else None
  in
  let function_override =
    match function_def with
    | None -> None
    | Some (fd) ->
        Option.map (List.map (fun lid_node ->
            let lid = strip lid_node in
            match Solidity_tenv.find_contract env lid with
            | None ->
                error lid_node.pos
                  "Invalid contract specified in override list: %a"
                  LongIdent.printf lid
            | Some (cd) ->
                cd.contract_abs_name
          )) fd.fun_override
  in
  { function_abs_name; function_params; function_returns;
    function_visibility; function_mutability;
    function_returns_lvalue; function_def;
    function_override; function_selector;
    function_is_method = is_method;
    function_is_primitive = false; }

and function_type_to_desc pos env ft =
  (* Note: library and fid parameters not used when funtype=true *)
  let function_abs_name = LongIdent.empty in
  make_function_desc pos env ~funtype:true ~library:true ~is_method:false
    (Ident.of_string "") function_abs_name ft.fun_type_params
    (List.map (fun (t, loc_opt) -> (t, loc_opt, None)) ft.fun_type_returns)
    false ft.fun_type_visibility ft.fun_type_mutability None

let function_def_to_desc pos (c : contract_desc) fd : function_desc =
  let function_abs_name =
    LongIdent.append c.contract_abs_name (strip fd.fun_name) in
  let library = is_library c.contract_def.contract_kind in
  let is_method =
    is_contract c.contract_def.contract_kind ||
      is_interface c.contract_def.contract_kind
  in
  let fd = {
    fd with fun_virtual =
              fd.fun_virtual ||
              is_interface c.contract_def.contract_kind } in
  make_function_desc pos c.contract_env ~funtype:false ~library ~is_method
    (strip fd.fun_name) function_abs_name fd.fun_params fd.fun_returns false
    fd.fun_visibility fd.fun_mutability (Some fd)

let modifier_def_to_desc pos (c : contract_desc) md : modifier_desc =
  let modifier_abs_name =
    LongIdent.append c.contract_abs_name (strip md.mod_name) in
  let modifier_params =
    List.map (fun (t, loc_opt, name_opt) ->
        var_type_to_type pos c.contract_env ~arg:true ~ext:false loc_opt t,
        Option.map strip name_opt
      ) md.mod_params
  in
  { modifier_abs_name; modifier_params; modifier_def = md }

let variable_type_to_function_type loc t =
  let allowed_in_struct = function
    | TArray (_) | TMapping (_) | TStruct (_) -> false
    | _ -> true
  in
  let rec aux atl = function
    | TArray (t, _sz_opt, _loc) ->
        aux ((TUint 256, None) :: atl) t
    | TMapping (kt, vt, _loc) ->
        aux ((kt, None) :: atl) vt
    | TStruct (_lid, sd, _loc) ->
        let rtl =
          List.map (fun (_id, t) ->
              if allowed_in_struct t then (t, None)
              else error loc "Can not make getter for such type"
            ) sd.struct_fields
        in
        List.rev atl, rtl
    | t ->
        List.rev atl, [(t, None)]
  in
  aux [] t

let variable_desc_to_function_desc pos vid variable_abs_name vt :
    function_desc =
  let function_params, function_returns =
    variable_type_to_function_type pos vt in
  let function_selector =
    Some (compute_selector pos ~library:false vid function_params) in
  { function_abs_name = variable_abs_name;
    function_params; function_returns;
    function_visibility = VExternal;
    function_mutability = MView;
    function_returns_lvalue = false;
    function_def = None;
    function_override = None;
    function_selector;
    function_is_method = true;
    function_is_primitive = false; }

let state_variable_def_to_desc pos (c : contract_desc) vd : variable_desc =
  let vid = strip (vd.var_name) in
  let variable_abs_name = LongIdent.append c.contract_abs_name vid in
  let variable_type =
    ast_type_to_type pos ~loc:(LStorage (false)) c.contract_env vd.var_type in
  let is_contract =
    is_contract c.contract_def.contract_kind ||
      is_interface c.contract_def.contract_kind
  in
  let variable_getter =
    match vd.var_visibility with
    | VPublic when is_contract ->
        Some (variable_desc_to_function_desc pos
                vid variable_abs_name variable_type)
    | _ -> None
  in
  let variable_override =
    Option.map (List.map (fun lid_node ->
        let lid = strip lid_node in
        match Solidity_tenv.find_contract c.contract_env lid with
        | None ->
            error lid_node.pos
              "Invalid contract specified in override list: %a"
              LongIdent.printf lid
        | Some (cd) ->
            cd.contract_abs_name
      )) vd.var_override
  in
  { variable_abs_name; variable_type;
    variable_visibility = vd.var_visibility;
    variable_mutability = vd.var_mutability;
    variable_local = false;
    variable_init = vd.var_init;
    variable_override;
    variable_getter;
    variable_is_primitive = false; }

let local_variable_desc variable_type : variable_desc =
  { variable_abs_name = LongIdent.empty;
    variable_type;
    variable_visibility = VPrivate;
    variable_mutability = MMutable;
    variable_local = true;
    variable_init = None;
    variable_override = None;
    variable_getter = None;
    variable_is_primitive = false; }

let event_def_to_desc pos (c : contract_desc) event_def : event_desc =
  let eid = strip (event_def.event_name) in
  let event_abs_name = LongIdent.append c.contract_abs_name eid in
  let event_params =
    List.map (fun (t, _indexed, name_opt) ->
        ast_type_to_type pos ~loc:LMemory c.contract_env t,
        Option.map strip name_opt
      ) event_def.event_params
  in
  { event_abs_name; event_params; event_def }

let event_desc_to_function_desc (ed : event_desc) : function_desc =
  { function_abs_name = ed.event_abs_name;
    function_params = ed.event_params;
    function_returns = [];
    function_visibility = VInternal;
    function_mutability = MNonPayable;
    function_returns_lvalue = false;
    function_def = None;
    function_override = None;
    function_selector = None;
    function_is_method = false;
    function_is_primitive = false; }


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
  TFunction (fd, { Solidity_tenv.new_fun_options with kind })

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
