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

let new_fun_options = {
  kind = KOther; value = false; gas = false; salt = false;
  stateInit = false; code = false; pubkey = false; varInit = false;
  flag = false; callback = false; bounce = false;
  fields = StringSet.empty ;
}

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
             ~lookup:(LStatic (cd.contract_def.contract_kind, false))
             (strip id))
    | _ ->
        error_invalid ()

  and process_ident id iddl =
    match iddl with
    | [Variable { variable_mutability = MConstant;
                  variable_def = Some ({ var_init = Some (e); _ }); _ }] ->
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

(* Used to give a proper type to type idents in expressions *)
let type_desc_to_base_type ~loc : type_desc -> type_ =
  function
  | TDEnum (ed) ->
      TEnum (ed.enum_abs_name, ed)
  | TDStruct (sd) ->
      Solidity_type.change_type_location loc
        (TStruct (sd.struct_abs_name, sd, loc))

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
  | TypeAbstract "TvmCell" -> TAbstract TvmCell
  | TypeAbstract "TvmSlice" -> TAbstract TvmSlice
  | TypeAbstract "TvmBuilder" -> TAbstract TvmBuilder
  | TypeAbstract s ->
      Printf.kprintf failwith "Unknown abstract type %S in Solidity_type_builder.elementary_type_to_type" s

let rec ast_type_to_type pos ~loc env = function
  | ElementaryType (et) ->
      elementary_type_to_type ~loc et
  | UserDefinedType (lid) ->
      let t =
        match Solidity_tenv.find_type env (strip lid) with
        | Some (t) ->
            Solidity_type.change_type_location loc t
        | None ->
            error pos "type %s is undefined" (LongIdent.to_string (strip lid))
      in
      set_annot lid (AType t);
      t
  | Optional tk ->
      TOptional (
        match tk with
          [ t ] -> ast_type_to_type pos ~loc env t
        | _ ->
            TTuple ( List.map (fun t ->
                Some (ast_type_to_type pos ~loc env t )) tk )
      )
  | Mapping (tk, tv) ->
      begin
        match loc with
        | ( LMemory | LCalldata ) when not !for_freeton ->
            error pos "Mapping types can only have a data location of \
                       \"storage\" and thus only be parameters or return \
                       variables for internal or library functions"
        | _ ->
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
      TFunction (function_type_to_desc pos env ft, new_fun_options)

and var_type_to_type pos env ~arg ~ext loc_opt t =
  let loc =
    storage_location_to_location (Option.value ~default:Memory loc_opt) in
  let t = ast_type_to_type pos ~loc env t in
  if not !for_freeton then begin
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

and function_type_to_desc pos env ft =
  let ext =
    match ft.fun_type_visibility with
    | VExternal | VPublic -> true
    | _ -> false
  in
  let function_params = process_fun_params pos env ~ext ft.fun_type_params in
  let function_returns =
    process_fun_type_returns pos env ~ext ft.fun_type_returns in
  { function_abs_name = LongIdent.empty;
    function_params; function_returns;
    function_visibility = ft.fun_type_visibility;
    function_mutability = ft.fun_type_mutability;
    function_returns_lvalue = false;
    function_override = None;
    function_selector = None;
    function_is_method = false;
    function_is_primitive = false;
    function_def = None;
    function_ops = [];
    function_purity = PurityUnknown;
  }

and process_fun_params pos env ~ext params =
  List.map (fun (t, loc_opt, name_opt) ->
      var_type_to_type pos env ~arg:true ~ext loc_opt t,
      Option.map strip name_opt
    ) params

and process_fun_type_returns pos env ~ext returns =
  List.map (fun (t, loc_opt) ->
      var_type_to_type pos env ~arg:true ~ext loc_opt t,
      None
    ) returns

let process_event_params pos env params =
  List.map (fun (t, _indexed, name_opt) ->
      ast_type_to_type pos ~loc:LMemory env t,
      Option.map strip name_opt
    ) params





(* Get a function type equivalent to a variable *)
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

(* Make a getter function from a variable *)
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
    function_override = None;
    function_selector;
    function_is_method = true;
    function_is_primitive = false;
    function_def = None;
    function_ops = [];
    function_purity = PurityUnknown;
  }

(* Build the function corresponding to an event *)
let event_desc_to_function_desc (ed : event_desc) : function_desc =
  { function_abs_name = ed.event_abs_name;
    function_params = ed.event_params;
    function_returns = [];
    function_visibility = VInternal;
    function_mutability = MNonPayable;
    function_returns_lvalue = false;
    function_override = None;
    function_selector = None;
    function_is_method = false;
    function_is_primitive = false;
    function_def = None;
    function_ops = [];
    function_purity = PurityUnknown;
  }

(* Make a ident description for a local variable *)
let local_variable_desc variable_type : variable_desc =
  { variable_abs_name = LongIdent.empty;
    variable_type;
    variable_visibility = VPrivate;
    variable_mutability = MMutable;
    variable_local = true;
    variable_override = None;
    variable_getter = None;
    variable_is_primitive = false;
    variable_def = None;
    variable_ops = [] ;
  }



(* Functions to build ident descriptions for environment construction *)

let process_overrides env overrides_opt =
  Option.map (
      List.map (fun lid_node ->
          let lid = strip lid_node in
          match Solidity_tenv.find_contract env lid with
          | None ->
              error lid_node.pos
                "Invalid contract specified in override list: %a"
                LongIdent.printf lid
          | Some (cd) ->
              cd.contract_abs_name
    )) overrides_opt

let make_modifier_desc mlid md =
  { modifier_abs_name = mlid;
    modifier_params = [];
    modifier_def = md; }

let update_modifier_desc pos env md =
  let md' = md.modifier_def in
  let modifier_params = process_fun_params pos env ~ext:false md'.mod_params in
  md.modifier_params <- modifier_params

let make_event_desc elid ed =
  { event_abs_name = elid;
    event_params = [];
    event_def = ed; }

let update_event_desc pos env ed =
  let ed' = ed.event_def in
  let event_params = process_event_params pos env ed'.event_params in
  ed.event_params <- event_params

let make_variable_desc vlid vd =
  { variable_abs_name = vlid;
    variable_type = TTuple [];
    variable_visibility = vd.var_visibility;
    variable_mutability = vd.var_mutability;
    variable_local = false;
    variable_override = None;
    variable_getter = None;
    variable_is_primitive = false;
    variable_def = Some (vd);
    variable_ops = [] ;
  }

let update_variable_desc pos env vd kind_opt =
  let vd' =
    match vd.variable_def with
    | Some (vd') -> vd'
    | None -> invariant_broken __LOC__
  in
  let variable_type =
    ast_type_to_type pos ~loc:(LStorage (false)) env vd'.var_type in
  let variable_getter =
    match vd'.var_visibility, kind_opt with
    | VPublic, Some (Solidity_ast.Contract | Interface) ->
        Some (variable_desc_to_function_desc pos (strip vd'.var_name)
                vd.variable_abs_name variable_type)
    | _ -> None
  in
  let variable_override = process_overrides env vd'.var_override in
  vd.variable_type <- variable_type;
  vd.variable_override <- variable_override;
  vd.variable_getter <- variable_getter

let make_function_desc flid fd method_ =
  { function_abs_name = flid;
    function_params = [];
    function_returns = [];
    function_visibility = fd.fun_visibility;
    function_mutability = fd.fun_mutability;
    function_returns_lvalue = false;
    function_override = None;
    function_selector = None;
    function_is_method = method_;
    function_is_primitive = false;
    function_def = Some (fd);
    function_ops = [];
    function_purity = PurityUnknown;
  }

let update_function_desc pos env fd kind_opt =
  let fd' =
    match fd.function_def with
    | Some (fd') -> fd'
    | None -> invariant_broken __LOC__
  in
  let ext =
    match fd'.fun_visibility with
    | VExternal | VPublic -> true
    | _ -> false
  in
  let fid = strip fd'.fun_name in
  let function_params = process_fun_params pos ~ext env fd'.fun_params in
  let function_returns = process_fun_params pos ~ext env fd'.fun_returns in
  let library = Option.fold ~none:false ~some:is_library kind_opt in
  let function_selector =
    if not ext then None
    else Some (compute_selector pos ~library fid function_params)
  in
  let function_override = process_overrides env fd'.fun_override in
  fd.function_params <- function_params;
  fd.function_returns <- function_returns;
  fd.function_override <- function_override;
  fd.function_selector <- function_selector

let update_struct_fields sd fields =
  let fields =
    List.fold_left (fun fields (field_name, field_type) ->
        IdentAList.add_uniq field_name field_type fields
      ) [] fields
  in
  sd.struct_fields <- IdentAList.rev fields



(* Functions to build primitive types/desc *)

let primitive_fun_desc ?(returns_lvalue=false)
    ?(purity=PurityPure)
    arg_types ret_types function_mutability =
  { function_abs_name = LongIdent.empty;
    function_params = List.map (fun t -> (t, None)) arg_types;
    function_returns = List.map (fun t -> (t, None)) ret_types;
    function_returns_lvalue = returns_lvalue;
    function_visibility = VPublic;
    function_mutability;
    function_override = None;
    function_selector = None;
    function_is_method = false; (* can be true *)
    function_is_primitive = true;
    function_def = None;
    function_ops = [];
    function_purity = purity;
  }


let primitive_fun_named_args_desc ?(returns_lvalue=false)
    ?(purity=PurityPure)
    arg_names_types ret_types function_mutability =
  { function_abs_name = LongIdent.empty;
    function_params = arg_names_types;
    function_returns = List.map (fun t -> (t, None)) ret_types;
    function_returns_lvalue = returns_lvalue;
    function_visibility = VPublic;
    function_mutability;
    function_override = None;
    function_selector = None;
    function_is_method = false; (* can be true *)
    function_is_primitive = true;
    function_def = None;
    function_ops = [];
    function_purity = purity;
  }

let primitive_fun_type ?(kind=KOther) ?(returns_lvalue=false)
    arg_types ret_types function_mutability =
  let fd = primitive_fun_desc ~returns_lvalue
             arg_types ret_types function_mutability in
  TFunction (fd, { new_fun_options with kind })

let primitive_fun ?(returns_lvalue=false) ?purity
    arg_types ret_types function_mutability =
  let fd = primitive_fun_desc ~returns_lvalue ?purity
             arg_types ret_types function_mutability in
  Function (fd)

let primitive_fun_named_args ?(returns_lvalue=false) ?purity
    arg_names_types ret_types function_mutability =
  let fd = primitive_fun_named_args_desc ~returns_lvalue ?purity
             arg_names_types ret_types function_mutability in
  Function (fd)

let primitive_var_desc (*?(is_lvalue=false)*) variable_type =
  { variable_abs_name = LongIdent.empty;
    variable_type;
    variable_visibility = VPublic;
    variable_mutability = MImmutable;
    variable_local = false;
    variable_override = None;
    variable_getter = None;
    variable_is_primitive = true;
    variable_def = None;
    variable_ops = [] ;
  }

let primitive_var (*?(is_lvalue=false)*) variable_type =
  let vd = primitive_var_desc variable_type in
  Variable (vd)
