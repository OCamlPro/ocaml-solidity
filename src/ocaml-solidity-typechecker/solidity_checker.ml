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

let sha3kec msg =
  Bytes.unsafe_of_string
    (EzHash.SHA3KEC.digest (Bytes.unsafe_to_string msg))

let error loc fmt =
  Format.kasprintf (fun s -> raise (TypecheckError (s, loc))) fmt

type args =
  | AList of Solidity_tenv.type_ list
  | ANamed of (Ident.t * Solidity_tenv.type_) list

type options = {
  allow_empty: bool; (* whether to allow empty elements in tuple *)
  call_args: args option;    (* could just have an in_lvalue flag *)
  fun_returns : Solidity_tenv.type_ list;
  in_loop: bool;
  in_function: bool;
  in_modifier: bool;
  current_hierarchy: absolute LongIdent.t list;
  current_contract: Solidity_tenv.contract_desc option;
}

let default_options = {
  allow_empty = false;
  call_args = None;
  fun_returns = [];
  in_loop = false;
  in_function = false;
  in_modifier = false;
  current_hierarchy = [];
  current_contract = None;
}



let prim_type =
  Array.make (Solidity_common.max_primitives + 1)
    (fun _ -> assert false)

let add_primitive_type id
    (f : Solidity_common.loc ->
         options ->
         Solidity_tenv.type_ option ->
         Solidity_tenv.type_ option)
  =
  if (id < 0) then
    error dummy_loc "Negative primitive id";
  if (id > Solidity_common.max_primitives) then
    error dummy_loc "Primitive id above limit";
  prim_type.(id) <- f




(* (this and following) move to solidity_tenv ? *)
let storage_location_opt_to_location :
  Solidity_ast.storage_location option -> Solidity_tenv.location =
  function
  | None ->
      LMemory
  | Some (Memory) ->
      LMemory
  | Some (Storage) ->
      LStorage (true)
  | Some (Calldata) ->
      LCalldata

let promote_loc :
  Solidity_tenv.location -> Solidity_tenv.location =
  function
  | LMemory ->
      LMemory
  | LCalldata ->
      LCalldata
  | LStorage (_) ->
      LStorage (false)

let unpromote_loc :
  Solidity_tenv.location -> Solidity_tenv.location =
  function
  | LMemory ->
      LMemory
  | LCalldata ->
      LCalldata
  | LStorage (_) ->
      LStorage (true)

let get_type_location astloc :
  Solidity_tenv.type_ -> Solidity_tenv.location = function
  | TString (loc) -> loc
  | TBytes (loc) -> loc
  | TStruct (_lid, _sd, loc) -> loc
  | TArray (_t, _sz_opt, loc) -> loc
  | TArraySlice (_t, loc) -> loc
  | TMapping (_tk, _tv, loc) -> loc
  | TTuple (_tl) -> error astloc "Unexpected tuple type"
  | _t -> LMemory

(* only needed to determine the type of immediate array elements *)
(* and to change location of structure fields *)
(* whenever the root becomes storage *, child become storage ref *)
let rec change_type_location loc :
  Solidity_tenv.type_ -> Solidity_tenv.type_ = function
  | TString (_loc) ->
      TString (loc)
  | TBytes (_loc) ->
      TBytes (loc)
  | TStruct (lid, sd, _loc) ->
      TStruct (lid, {
          sd with struct_fields =
                    List.map (fun (id, t) ->
                        (id, change_type_location (promote_loc loc) t)
                      ) sd.struct_fields }, loc)
  | TArray (t, sz_opt, _loc) ->
      TArray (change_type_location (promote_loc loc) t, sz_opt, loc)
  | TArraySlice (t, _loc) ->
      TArraySlice (change_type_location (promote_loc loc) t, loc)
  | TMapping (tk, tv, _loc) ->
      TMapping (tk, change_type_location (promote_loc loc) tv, loc)
  | TTuple (tl) ->
      TTuple (List.map (Option.map (change_type_location loc)) tl)
  | t ->
      t

(* only needed to determine inferred types for variable *)
(* this basically turns storage ref to storage pointer on the root type *)
(* child types with storage location are assumed to be storage ref *)
let rec unpromote_type :
  Solidity_tenv.type_ -> Solidity_tenv.type_ = function
  | TString (loc) ->
      TString (unpromote_loc loc)
  | TBytes (loc) ->
      TBytes (unpromote_loc loc)
  | TStruct (lid, sd, loc) ->
      TStruct (lid, sd, unpromote_loc loc)
  | TArray (t, sz_opt, loc) ->
      TArray (t, sz_opt, unpromote_loc loc)
  | TArraySlice (t, loc) ->
      TArraySlice (t, unpromote_loc loc)
  | TMapping (tk, tv, loc) ->
      TMapping (tk, tv, unpromote_loc loc)
  | TTuple (tl) ->
      TTuple (List.map (Option.map unpromote_type) tl)
  | t ->
      t


let elementary_type_to_type ~loc :
  Solidity_ast.elementary_type -> Solidity_tenv.type_ =
  function
  | TypeBool ->
      TBool
  | TypeInt (sz_opt) ->
      TInt (sz_opt)
  | TypeUint (sz_opt) ->
      TUint (sz_opt)
  | TypeFixed (sz_opt, dec) ->
      TFixed (sz_opt, dec)
  | TypeUfixed (sz_opt, dec) ->
      TUfixed (sz_opt, dec)
  | TypeAddress (payable) ->
      TAddress (payable)
  | TypeBytes (Some sz) ->
      TFixBytes (sz)
  | TypeBytes (None)->
      TBytes (loc)
  | TypeString ->
      TString (loc)
  (* TON-specific *)
  | TvmCell ->
      TTvmCell
  | TvmSlice ->
      TTvmSlice
  | TvmBuilder ->
      TTvmBuilder
  | ExtraCurrencyCollection ->
      TExtraCurrencyCollection



(* only used to get the type of an ident *)
let type_desc_to_base_type ~loc :
  Solidity_tenv.type_desc -> Solidity_tenv.type_ =
  function
  | TDEnum (ed) ->
      TEnum (ed.enum_abs_name, ed)
  | TDStruct (sd) ->
      change_type_location loc (TStruct (sd.struct_abs_name, sd, loc))

let type_lid_to_base_type astloc ~loc env lid =
  match Solidity_tenv.find_type astloc env lid with
  | Some (t) ->
      change_type_location loc t
  | None ->
      error astloc "type %s is undefined" (LongIdent.to_string lid)



let eval_array_length_exp env e =
  let error_invalid () =
    error e.loc "Invalid array length, expected integer \
                 literal or constant expression"
  in
  let rec aux e =
    match strip e with
    | NumberLiteral (q, unit, _hex_size_opt) ->
        apply_unit q unit
    | PrefixExpression (op, e) ->
        begin
          match apply_unop op (aux e) with
          | Some v -> v
          | None -> error_invalid ()
        end
    | BinaryExpression (e1, op, e2) ->
        begin
          match apply_binop (aux e1) op (aux e2) with
          | Some v -> v
          | None -> error_invalid ()
        end
(* TODO: consts in libs ? *)
    | IdentifierExpression (id) ->
        begin
          match Solidity_tenv.find_ident env ~lookup:LInternal (strip id) with
          | [Variable { variable_mutability = MConstant;
                        variable_init = Some e; _ }] ->
              aux e
          | _ ->
              error id.loc "Undeclared identifier: %a" Ident.printf id.contents
        end
(* TODO: set annot ? *)
    | _ ->
        error_invalid ()
  in
  let v = aux e in
  if not (ExtQ.is_int v) then
    error e.loc "Array with fractional length specified"
  else if ExtQ.is_neg v then
    error e.loc "Array with negative length specified"
  else if (Z.numbits (Q.num v) > 31) then
    error e.loc "Array too big"
  else
    Q.num v




(* (this and following) move to solidity_tenv ? *)

let rec ast_type_to_type astloc ~loc env = function
  | ElementaryType (et) ->
      elementary_type_to_type ~loc et
  | UserDefinedType (lid) ->
      let t = type_lid_to_base_type ~loc astloc env (strip lid) in
      set_annot lid (Solidity_tenv.AType t);
      t
  | Mapping (tk, tv) ->
      begin
        match loc with
        | LMemory | LCalldata ->
            error astloc "Mapping types can only have a data location of \
                          \"storage\" and thus only be parameters or return \
                          variables for internal or library functions"
        | LStorage (_ptr) ->
            (* Mapping keys are always in memory
               Mapping values are always in storage *)
            TMapping (ast_type_to_type astloc ~loc:LMemory env tk,
                      ast_type_to_type astloc ~loc:(LStorage (false)) env tv,
                      loc)
      end
  | Array (t, None) ->
      TArray (ast_type_to_type ~loc:(promote_loc loc) astloc env t, None, loc)
  | Array (t, Some e_sz) ->
      let sz = eval_array_length_exp env e_sz in
      set_annot e_sz (Solidity_tenv.AType (TUint None));
      TArray (ast_type_to_type ~loc:(promote_loc loc) astloc env t,
              Some (sz), loc)
  | FunctionType (ft) ->
      TFunction (function_type_to_desc astloc env ft,
                 Solidity_tenv.new_fun_options)
  (* TON-specific *)
  | Optional (t) ->
      TOptional (ast_type_to_type astloc ~loc env t)

and var_type_to_type astloc env ~arg ~ext loc_opt t =
  let loc = storage_location_opt_to_location loc_opt in
  let t = ast_type_to_type astloc ~loc env t in
  begin
    match t with
    (* Reference type -> is_reference_type ? *)
    | TBytes _ | TString _ | TStruct _ | TArray _ | TMapping _ ->
        let valid =
          match loc_opt with
          | None -> false
          | Some Storage -> not ext
          | Some Memory -> true
          | Some Calldata -> true
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
          error astloc "Data location must be %s for %s, \
                        but %s was given" expected context given
        else if Solidity_tenv.has_mapping t &&
           not (Solidity_tenv.is_storage_type t) then
          error astloc "Type %s is only valid in storage because \
                     it contains a (nested) mapping"
            (Solidity_tenv.string_of_type t);

    | _ ->
        begin
          match loc_opt with
          | Some loc ->
              error astloc "Data location can only be specified for array, \
                            struct or mapping types, but \"%s\" was given"
                (Solidity_printer.string_of_storage_location loc)
          | None ->
              ()
        end
  end;
  t

and compute_selector astloc ~library id args =
  let arg_types =
    List.map (fun (t, _id_opt) ->
        Solidity_tenv.canonical_type astloc ~library t) args in
  let fun_sig =
    Format.asprintf "%a(%s)" Ident.printf id (String.concat "," arg_types) in
  Bytes.to_string (Bytes.sub (sha3kec (Bytes.of_string fun_sig)) 0 4)

and variable_type_to_function_type loc t =
  let open Solidity_tenv in
  let allowed_in_struct = function
    | TArray (_) | TMapping (_) | TStruct (_) -> false
    | _ -> true
  in
  let rec aux atl = function
    | TArray (t, _sz_opt, _loc) ->
        aux ((TUint (None), None) :: atl) t
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

and variable_desc_to_function_desc astloc vid variable_abs_name vt :
    Solidity_tenv.function_desc =
  let function_params, function_returns =
    variable_type_to_function_type astloc vt in
  let function_selector =
    Some (compute_selector astloc ~library:false vid function_params) in
  { function_abs_name = variable_abs_name;
    function_params; function_returns;
    function_visibility = VExternal; function_mutability = MView;
    function_returns_lvalue = false;
    function_def = None; function_override = None;
    function_selector; }

and make_function_desc astloc env ~funtype ~library
    fid function_abs_name params returns function_returns_lvalue
    function_visibility function_mutability function_def :
      Solidity_tenv.function_desc =
  let ext =
    match function_visibility with
    | VExternal | VPublic -> true
    | _ -> false
  in
  let function_params =
    List.map (fun (t, loc_opt, name_opt) ->
        var_type_to_type astloc env ~arg:true ~ext loc_opt t,
        Option.map strip name_opt
      ) params
  in
  let function_returns =
    List.map (fun (t, loc_opt, name_opt) ->
        var_type_to_type astloc env ~arg:true ~ext loc_opt t,
        Option.map strip name_opt
      ) returns
  in
(* TODO: don't compute for receive/fallback/constr *)
  let function_selector =
    if funtype then
      None
    else
      if ext then Some (compute_selector astloc ~library fid function_params)
      else None
  in
  let function_override =
    match function_def with
    | None -> None
    | Some (fd) ->
        Option.map (List.map (fun lid_node ->
            let lid = strip lid_node in
            match Solidity_tenv.find_contract astloc env lid with
            | None ->
                error lid_node.loc
                  "Invalid contract specified in override list: %a"
                  LongIdent.printf lid
            | Some (cd) ->
                cd.contract_abs_name
          )) fd.fun_override
  in
  { function_abs_name; function_params; function_returns;
    function_visibility; function_mutability;
    function_returns_lvalue; function_def;
    function_override; function_selector; }

and function_type_to_desc astloc env ft =
  (* Note: library and fid parameters not used when funtype=true *)
  let function_abs_name = LongIdent.empty in
  make_function_desc astloc env ~funtype:true ~library:true
    (Ident.of_string "") function_abs_name ft.fun_type_params
    (List.map (fun (t, loc_opt) -> (t, loc_opt, None)) ft.fun_type_returns)
    false ft.fun_type_visibility ft.fun_type_mutability None

let function_def_to_desc astloc (c : Solidity_tenv.contract_desc) fd =
  let function_abs_name =
    LongIdent.append c.contract_abs_name (strip fd.fun_name) in
  let library = is_library c.contract_def.contract_kind in
  let fd = {
    fd with fun_virtual =
              fd.fun_virtual ||
              is_interface c.contract_def.contract_kind } in
  make_function_desc astloc c.contract_env ~funtype:false ~library
    (strip fd.fun_name) function_abs_name fd.fun_params fd.fun_returns false
    fd.fun_visibility fd.fun_mutability (Some fd)

let modifier_def_to_desc astloc (c : Solidity_tenv.contract_desc) md :
  Solidity_tenv.modifier_desc =
  let modifier_abs_name =
    LongIdent.append c.contract_abs_name (strip md.mod_name) in
  let modifier_params =
    List.map (fun (t, loc_opt, name_opt) ->
        var_type_to_type astloc c.contract_env ~arg:true ~ext:false loc_opt t,
        Option.map strip name_opt
      ) md.mod_params
  in
  { modifier_abs_name; modifier_params; modifier_def = md }

let state_variable_def_to_desc astloc (c : Solidity_tenv.contract_desc) vd :
  Solidity_tenv.variable_desc =
  let vid = strip (vd.var_name) in
  let variable_abs_name = LongIdent.append c.contract_abs_name vid in
  let variable_type =
    ast_type_to_type astloc ~loc:(LStorage (false))
      c.contract_env vd.var_type in
  let variable_getter =
    match vd.var_visibility with
    | VPublic ->
        Some (variable_desc_to_function_desc astloc
                vid variable_abs_name variable_type)
    | _ -> None
  in
  let variable_override =
    Option.map (List.map (fun lid_node ->
        let lid = strip lid_node in
        match Solidity_tenv.find_contract astloc c.contract_env lid with
        | None ->
            error lid_node.loc
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
    variable_getter; }

let local_variable_desc variable_type : Solidity_tenv.variable_desc =
  { variable_abs_name = LongIdent.empty;
    variable_type;
    variable_visibility = VPrivate;
    variable_mutability = MMutable;
    variable_local = true;
    variable_init = None;
    variable_override = None;
    variable_getter = None; }











(* TODO: this could be improved *)
let immediate_array_element_type astloc tl =
  let rec aux t = function
    | [] -> t
    | t' :: tl ->
        let t =
          if Solidity_tenv.implicitly_convertible
              ~ignore_loc:true ~from:t' ~to_:t () then
            t
          else
            let t' = Solidity_tenv.mobile_type t' in
            if Solidity_tenv.implicitly_convertible
                ~ignore_loc:true ~from:t ~to_:t' () then
              t'
            else
              error astloc "Unable to deduce common type for array elements"
        in
        aux t tl
  in
  match tl with
  | [] -> error astloc "Unable to deduce common type for array elements"
  | t :: tl ->
      match aux (Solidity_tenv.mobile_type t) tl with
      | TRationalConst _ | TLiteralString _ ->
          error astloc "immediate_array_element_type: invariant broken"
      | (TTuple _ | TArraySlice _ | TFunction _ |
         TModifier _ | TType _ | TMagic _) as t ->
          error astloc "Type %s is only valid in storage"
            (Solidity_tenv.string_of_type t)
      | t ->
          (* Note: always LMemory, even when initializing state variables *)
          change_type_location LMemory t



let binop_type astloc op t1 t2 : Solidity_tenv.type_ =
  let error_incompat () =
    error astloc "Operator %s not compatible with types %s and %s"
      (Solidity_printer.string_of_binop op)
      (Solidity_tenv.string_of_type t1) (Solidity_tenv.string_of_type t2)
  in
  match op, t1, t2 with
  | _, TRationalConst (q1, _), TRationalConst (q2, _) ->
      begin
        match apply_binop q1 op q2 with
        | Some (q) -> TRationalConst (q, None)
        | None -> error_incompat ()
      end
  | (BExp | BLShift | BRShift), _, TRationalConst (q2, _) ->
      if not (ExtQ.is_int q2) then
        error_incompat ();
      Solidity_tenv.mobile_type t1
  | (BExp | BLShift | BRShift), _, _ ->
      let mt1 = Solidity_tenv.mobile_type t1 in
      let mt2 = Solidity_tenv.mobile_type t2 in
      begin
        match mt1, mt2 with
        | (TInt _ | TUint _), TUint _ -> mt1
        | _ -> error_incompat ()
      end
  | (BPlus | BMinus | BTimes | BDiv | BMod | BAnd | BOr | BXor), _, _ ->
      let mt1 = Solidity_tenv.mobile_type t1 in
      let mt2 = Solidity_tenv.mobile_type t2 in
      let t = Solidity_tenv.common_type mt1 mt2 in
      begin
        match t with
        | Some (TInt _ | TUint _ | TFixed _ | TUfixed _ as t) -> t
        | _ -> error_incompat ()
      end
  | (BLAnd | BLOr), TBool, TBool ->
      TBool
  | (BLAnd | BLOr), _, _ ->
      error_incompat ()

let unop_type astloc op t : Solidity_tenv.type_ =
  let error_incompat () =
    error astloc "Unary operator %s cannot be applied to type %s"
      (Solidity_printer.string_of_unop op) (Solidity_tenv.string_of_type t)
  in
  match t, op with
  | _, UPlus ->
      error astloc "Usage of unary + is disallowed";
  | TRationalConst (q, _), _ ->
      begin
        match apply_unop op q with
        | Some (q) -> TRationalConst (q, None)
        | None -> error_incompat ()
      end
  | (TBool | TInt _ | TUint _ | TFixed _ | TUfixed _ |
     TAddress _ | TFixBytes _ | TBytes _ | TString _ |
     TEnum _ | TStruct _ | TContract _ |
     TArray _ | TFunction _), UDelete ->
      TTuple []
  | _, UDelete ->
      error_incompat ()
  | _, (UMinus | UNot | UInc | UDec) ->
      let mt = Solidity_tenv.mobile_type t in
      begin
        match mt with
        | TInt _ | TUint _ | TFixed _ | TUfixed _ -> mt
        | _ -> error_incompat ()
      end
  | TBool, ULNot ->
      TBool
  | _, ULNot ->
      error_incompat ()








let check_argument_type astloc kind ~expected ~provided =
  if not (Solidity_tenv.implicitly_convertible
            ~from:provided ~to_:expected ()) then
    error astloc "Invalid type for argument in %s. \
                  Invalid implicit conversion from %s to %s requested"
      kind
      (Solidity_tenv.string_of_type provided)
      (Solidity_tenv.string_of_type expected)

let check_function_application astloc kind fp args =
  let nb_args_expected = List.length fp in
  let nb_args_provided =
    match args with
    | AList (tl) -> List.length tl
    | ANamed (ntl) -> List.length ntl
  in
  (* Note: named arguments in ANamed ntl are unique (checked previously) *)
  if (nb_args_provided <> nb_args_expected) then
    error astloc "Wrong argument count for %s: \
                  %d arguments given but expected %d"
      kind nb_args_provided nb_args_expected
  else
  (* TODO: warning, for structs, the location is the one that was determined
     when the struct was invoked, but it may depend on the usage context
     (storage init ?) *)
    begin
      match args with
      | AList (tl) ->
          List.iter2 (fun (ft, _id_opt) at ->
              check_argument_type astloc kind ~expected:ft ~provided:at
            ) fp tl
      | ANamed (ntl) ->
          List.iter (fun (fid, at) ->
              match List.find_opt (fun (_ft, id_opt) ->
                  match id_opt with
                  | Some id -> Ident.equal id fid
                  | None -> false) fp with
              | Some (ft, _id_opt) ->
                  check_argument_type astloc kind ~expected:ft ~provided:at
              | None ->
                  error astloc "Named argument \"%s\" does not \
                                match function declaration"
                    (Ident.to_string fid)
            ) ntl
    end

let compatible_function_type (fd : Solidity_tenv.function_desc) args  =
  let nb_args_expected = List.length fd.function_params in
  let nb_args_provided =
    match args with
    | AList (tl) -> List.length tl
    | ANamed (ntl) -> List.length ntl
  in
  (* Note: named arguments in ANamed ntl are unique (checked previously) *)
  if (nb_args_provided <> nb_args_expected) then
    false
  else
    begin
      match args with
      | AList (tl) ->
          List.for_all2 (fun (ft, _id_opt) at ->
              Solidity_tenv.explicitly_convertible_bool ~from:at ~to_:ft
            ) fd.function_params tl
      | ANamed (ntl) ->
          List.for_all (fun (fid, at) ->
              match List.find_opt (fun (_ft, id_opt) ->
                  match id_opt with
                  | Some (id) -> Ident.equal id fid
                  | None -> false) fd.function_params with
              | Some (ft, _id_opt) ->
                  Solidity_tenv.explicitly_convertible_bool ~from:at ~to_:ft
              | None ->
                  false
            ) ntl
    end

let fun_opt (lookup : Solidity_tenv.lookup_kind)
    (fd : Solidity_tenv.function_desc) =
  let kind =
    match lookup, fd.function_visibility with
    | LExternal, (VExternal | VPublic) -> Solidity_tenv.KExtContractFun
    | _ -> KOther
  in
  { Solidity_tenv.new_fun_options with kind }

let type_ident opt base_t_opt env lookup id_node
    ~err_notfound ~err_notunique ~err_nomatch ~err_manymatch =
  let external_lookup =
    match lookup with
    | Solidity_tenv.LExternal -> true
    | _ -> false
  in
  match Solidity_tenv.find_ident env ~lookup (strip id_node) with
  | [] ->
      let pid =
        match prim_of_ident (strip id_node) with
        | None ->
            err_notfound ()
        | Some (pid, _prim) ->
            pid
      in
      begin
        match prim_type.(pid) id_node.loc opt base_t_opt with
        | Some (t) ->
            set_annot id_node (Solidity_tenv.APrimitive);
            (t, false)
        | None ->
            begin
              match opt.call_args with
              | None ->
                  err_notunique ()
              | Some (_) ->
                  err_nomatch ()
            end
      end
  | [Contract (cd)] ->
      let t = Solidity_tenv.TContract (
          cd.contract_abs_name, cd, false (* super *)) in
      set_annot id_node (Solidity_tenv.AType t);
      TType (t), false
  | [Type (td)] ->
      (* Note: user types have their storage location
         set to storage pointer by default *)
      let t = type_desc_to_base_type ~loc:(LStorage true) td in
      set_annot id_node (Solidity_tenv.AType t);
      TType (t), false
  (* TODO: in contract, fail *)
  (* error "cannot extract field %S from contract def" field *)
  | [Modifier (md)] ->
      set_annot id_node (Solidity_tenv.AModifier md);
      TModifier (md), false
  | [Variable (vd)] when external_lookup ->
      if vd.variable_local then
        error id_node.loc "External lookup returning a local variable !";
      let fd =
        match vd.variable_getter with
        | Some (fd) -> fd
        | None -> error id_node.loc "Variable is missing a getter !"
      in
      set_annot id_node (Solidity_tenv.AFunction fd);
      TFunction (fd, fun_opt lookup fd), false
  | [Variable (vd)] ->
      set_annot id_node (Solidity_tenv.AVariable vd);
      vd.variable_type, true
  | [Function (fd)] ->
      set_annot id_node (Solidity_tenv.AFunction fd);
      TFunction (fd, fun_opt lookup fd), false
  | iddl ->
      begin
        match opt.call_args with
        | None ->
            err_notunique ()
        | Some (args) ->
            let iddl =
              List.fold_left (fun iddl idd ->
                  match idd with
                  | Solidity_tenv.Function (fd) ->
                      if compatible_function_type fd args then
                        idd :: iddl
                      else
                        iddl
                  | Solidity_tenv.Variable (vd) when external_lookup ->
                      if vd.variable_local then
                        error id_node.loc
                          "External lookup returning a local variable !";
                      let fd =
                        match vd.variable_getter with
                        | Some (fd) -> fd
                        | None ->
                            error id_node.loc "Variable is missing a getter !"
                      in
                      if compatible_function_type fd args then
                        Function (fd) :: iddl
                      else
                        iddl
                  | _ ->
                      iddl
                ) [] iddl
            in
            begin
       (* TODO: annot should tell whether to make the fct internal/external *)
              match iddl with
              | [Function (fd)] ->
                  set_annot id_node (Solidity_tenv.AFunction fd);
                  TFunction (fd, fun_opt lookup fd), false
              | [] ->
                  err_nomatch ()
              | _ ->
                  err_manymatch ()
            end
      end

let type_plain_ident opt env lookup id_node =
  let loc = id_node.loc in
  type_ident opt None env lookup id_node
    ~err_notfound:(fun () ->
        error loc "Undeclared identifier: %a" Ident.printf id_node.contents)
(* TODO: Did you mean "xxx"? *)
(*      error "Undeclared identifier. \"%s\" is not (or not yet) \
               visible at this point" (Ident.to_string id)) *)
    ~err_notunique:(fun () ->
        error loc
          "No matching declaration found after variable lookup")
    ~err_nomatch:(fun () ->
        error loc
          "No matching declaration found after argument-dependent lookup")
    ~err_manymatch:(fun () ->
        error loc
          "No unique declaration found after argument-dependent lookup")

let type_member_ident opt env lookup t id_node =
  let id = strip id_node in
  let loc = id_node.loc in
  let err_notfound () =
    error loc "Member %s not found or not visible after argument-dependent \
           lookup in %s" (Ident.to_string id) (Solidity_tenv.string_of_type t)
  in
  let err_notunique () =
    error loc "Member %s not unique after argument-dependent \
           lookup in %s" (Ident.to_string id) (Solidity_tenv.string_of_type t)
  in
  type_ident opt (Some t) env lookup id_node ~err_notfound ~err_notunique
    ~err_nomatch:err_notfound ~err_manymatch:err_notunique




let rec type_expression opt (env : Solidity_tenv.env) exp :
  Solidity_tenv.type_ =
  let t, _lv = type_expression_lv opt env exp in
  t


and type_expression_lv opt (env : Solidity_tenv.env) exp :
  Solidity_tenv.type_ * bool =
  let loc = exp.loc in
  let t, lv = match strip exp with

  (* Literals *)

  | BooleanLiteral (_b) ->
      Solidity_tenv.TBool, false

  | NumberLiteral (q, unit, sz_opt) ->
      (* Note: size set only if hex *)
      let q = apply_unit q unit in
      let sz_opt =
        match sz_opt with
        | Some (i) ->
            if (i mod 2 = 0) then
              Some (i / 2)
            else
              None (* TODO: error *)
        | None ->
            None
      in
      TRationalConst (q, sz_opt), false

  | StringLiteral (s) ->
      TLiteralString (s), false

  | AddressLiteral (_a) ->
      (* Note: the lexer handles both binary and identifiers with dn*/KT1 *)
      (* Note: Valid address literals are of type address payable *)
      TAddress (true), false

  (* Array expressions *)

  | ImmediateArray (el) ->
      let tl = List.map (type_expression opt env) el in
      let t = immediate_array_element_type loc tl in
      let sz = Z.of_int (List.length tl) in
      (* Note: not an lvalue, but index access to such array is an lvalue *)
      TArray (t, Some (sz), LMemory), false

  | ArrayAccess (e, None) ->
      begin
        match type_expression opt env e with
        | TType (t) ->
            let t = change_type_location LMemory t in
            replace_annot e (Solidity_tenv.AType (TType t));
            TType (TArray (t, None, LMemory)),
            false
        | _ ->
            error loc "Index expression cannot be omitted"
      end

  | ArrayAccess (e1, Some e2) ->
      begin
        match type_expression opt env e1 with
        | TArray (t, sz_opt, _loc) ->
            ignore (expect_array_index_type opt env sz_opt e2);
            t, true
        | TArraySlice (t, _loc) ->
            ignore (expect_array_index_type opt env None e2);
            (* Note: array access into a slice is NOT an lvalue *)
            t, false
        | TMapping (tk, tv, _loc) ->
            expect_expression_type opt env e2 tk;
            tv, true
        | TType (t) ->
            begin
              match expect_array_index_type opt env None e2 with
              | Some (sz) ->
                  let t = change_type_location LMemory t in
                  replace_annot e1 (Solidity_tenv.AType (TType t));
                  TType (TArray (t, Some (sz), LMemory)), false
              | None ->
                  error loc "Integer constant expected"
            end
        | TString _ ->
            error loc "Index access for string is not possible"
        | t ->
            error loc "Indexed expression has to be a type, mapping \
                       or array (is %s)" (Solidity_tenv.string_of_type t)
      end

  | ArraySlice (e1, e1_opt, e2_opt) ->
      begin
        match type_expression opt env e1 with
        | TArray (t, None, (LCalldata as loc))
        | TArraySlice (t, loc) ->
            begin
              match e1_opt with
              | None -> ()
              | Some (e) -> ignore (expect_array_index_type opt env None e)
            end;
            begin
              match e2_opt with
              | None -> ()
              | Some (e) -> ignore (expect_array_index_type opt env None e)
            end;
            TArraySlice (t, loc), false
        | TArray (_t, _sz_opt, _loc) ->
            error loc "Index range access is only supported \
                       for dynamic calldata arrays"
        | _ ->
            error loc "Index range access is only possible \
                       for arrays and array slices"
      end

  (* Simple expressions *)

  | PrefixExpression ((UInc | UDec | UDelete as op), e)
  | SuffixExpression (e, (UInc | UDec as op)) ->
      let t, lv = type_expression_lv { opt with allow_empty = true } env e in
      if not lv then error loc "Expression has to be an lvalue";
      unop_type loc op t, false

  | PrefixExpression (op, e)
  | SuffixExpression (e, op) ->
      unop_type loc op (type_expression opt env e), false

  | BinaryExpression (e1, op, e2) ->
      let t1 = type_expression opt env e1 in
      let t2 = type_expression opt env e2 in
      binop_type loc op t1 t2, false

  | CompareExpression (e1, op, e2) ->
      let t1 = type_expression opt env e1 in
      let t2 = type_expression opt env e2 in
      let valid =
        match Solidity_tenv.common_type
                (Solidity_tenv.mobile_type t1)
                (Solidity_tenv.mobile_type t2) with
        | Some (t) -> Solidity_tenv.valid_compare_type op t
        | None -> false
      in
      if not valid then
        error loc "Operator %s not compatible with types %s and %s"
          (Solidity_printer.string_of_cmpop op)
          (Solidity_tenv.string_of_type t1)
          (Solidity_tenv.string_of_type t2);
      TBool, false

  | AssignExpression (e1, e2) ->
      let t1, lv = type_expression_lv { opt with allow_empty = true } env e1 in
      let t2 = type_expression opt env e2 in
      if not lv then
        error loc "Assignment operator requires lvalue as left-hand side";
      (* Note: (true ? tuple : tuple) = tuple
         may become allowed in the future *)
      expect_type loc ~expected:t1 ~provided:t2;
      t1, false

  | AssignBinaryExpression (e1, op, e2) ->
      let t1, lv = type_expression_lv { opt with allow_empty = true } env e1 in
      let t2 = type_expression opt env e2 in
      if not lv then
        error loc "Assignment operator requires lvalue as left-hand side";
      if Solidity_tenv.is_tuple t1 then
        error loc "Compound assignment is not allowed for tuple types"
      else
        let t = binop_type loc op t1 t2 in
        expect_type loc ~expected:t1 ~provided:t;
        t1, false (* or t ? *)

  | TupleExpression (list) ->
      let tl, lv =
        List.fold_left (fun (tl, lv) e_opt ->
            match e_opt with
            | Some (e) ->
                let t, elv = type_expression_lv opt env e in
                Some (t) :: tl, lv && elv
            | None when opt.allow_empty ->
                None :: tl, lv
            | None ->
                error loc "Tuple component cannot be empty"
          ) ([], true) list
      in
      TTuple (List.rev tl), lv

  | IfExpression (e_if, e_then, e_else) ->
      (* Note: may become an lvalue in the future *)
      expect_expression_type opt env e_if TBool;
      let t1 = type_expression opt env e_then in
      let t2 = type_expression opt env e_else in
      begin
        match Solidity_tenv.common_type
                (Solidity_tenv.mobile_type t1)
                (Solidity_tenv.mobile_type t2) with
        | Some (t) ->
            t, false
        | None ->
            error loc "True expression's type %s does not \
                       match false expression's type %s"
              (Solidity_tenv.string_of_type t1)
              (Solidity_tenv.string_of_type t2)
      end

  | NewExpression (t) ->
      (* Note: this produces a function that takes the
         constructor argument or array size as parameter *)
      (* Note: for arrays, only one parameter, even if multidimensional *)
      let t = ast_type_to_type loc ~loc:LMemory env t in
      begin
        match t with
        | TArray (_, None, _) | TBytes (_) | TString (_) ->
            let t = Solidity_tenv.primitive_type
                [TUint (Some 256)] [t] MPure in
            (t, false)
        | TContract (_lid, cd, false (* super *)) ->
(* TODO: find correct constructor type (may be overloaded...) *)
(* TODO: may be absent (default const) *)
(* TODO: if explicit const, is default const present ? *)
            if cd.contract_def.contract_abstract then
              error loc "Cannot instantiate an abstract contract";
            if is_interface cd.contract_def.contract_kind then
              error loc "Cannot instantiate an interface";
            if is_library cd.contract_def.contract_kind then
              error loc "Instantiating libraries is not supported yet";
            let t = Solidity_tenv.primitive_type ~kind:KNewContract
(* TODO *)
                [(*TODO*)] [t] MPayable in
            (t, false)
        | TArray (_, Some (_), _) ->
            error loc "Length has to be placed in parentheses \
                       after the array type for new expression"
        | TStruct (_) | TEnum _ ->
            error loc "Identifier is not a contract"
        | _ ->
            error loc "Contract or array type expected"
      end

  | TypeExpression (t) ->
      TType (ast_type_to_type loc ~loc:LMemory env t), false

  | IdentifierExpression (id_node) ->
      type_plain_ident opt env LInternal id_node

  | FieldExpression (e, field_node) ->
      let field = strip field_node in
      let t = type_expression opt env e in
      begin
        match t with
        | TStruct (_lid, sd, _loc) ->
            begin
              match IdentAList.find_opt field sd.struct_fields with
              | Some (field_type) ->
                  field_type, true (* lvalue : depends - see array *)
(* TODO: warning, location depends on where the struct variable was declared
   so ensure it is recorded in environment with the right location *)
              | None ->
                  error loc "no field %S in struct" (Ident.to_string field)
            end

        | TType (TEnum (lid, ed) as t) ->
            begin
              match IdentAList.find_opt field ed.enum_values with
              | Some (_i) ->
                  t, false
              | None ->
                  error loc "enum type %s does not define a value %s"
                    (LongIdent.to_string lid) (Ident.to_string field)
            end

        | TType (TContract (lid, cd, _super)) ->
            let is_parent = List.mem lid opt.current_hierarchy in
            type_member_ident opt cd.contract_env
              (LStatic (cd.contract_def.contract_kind, is_parent)) t field_node
(* TODO: Cannot call function via contract type name
         when calling an external function like C.f()
         or through interface *)

        | TContract (_lid, cd, true (* super *)) ->
            let env =
              match cd.contract_hierarchy with
              | _ :: (_lid, cd) :: _ -> cd.contract_env
              | _ -> Solidity_tenv.new_env ()
            in
            type_member_ident opt env LSuper t field_node

        | TContract (_lid, cd, false (* super *)) ->
            type_member_ident opt cd.contract_env LExternal t field_node

        | TMagic (_) | TArray (_) | TBytes (_) | TFixBytes (_)
        | TAddress (_) | TFunction (_) ->
            let pid =
              match prim_of_ident field with
              | None ->
                  error field_node.loc "Unknown primitive: %s"
                    (Ident.to_string field)
              | Some (pid, _prim) ->
                  pid
            in
            begin
              match prim_type.(pid) loc opt (Some t) with
              | Some (t) ->
                  set_annot field_node (Solidity_tenv.APrimitive);
                  (t, false)
              | None ->
                  error loc "cannot extract field %S from type %s"
                    (Ident.to_string field) (Solidity_tenv.string_of_type t)
            end
        | _ ->
            error loc "cannot extract field %S from type %s"
              (Ident.to_string field) (Solidity_tenv.string_of_type t)
      end

  | FunctionCallExpression (e, args) ->
      let args =
        match args with
        | ExpressionList (el) ->
            AList (List.map (type_expression opt env) el)
        | NameValueList (nel) ->
            let ntl = List.fold_left (fun ntl (id, e) ->
                IdentAList.add_uniq (strip id) (type_expression opt env e) ntl
              ) [] nel in
            ANamed (List.rev ntl)
      in
      let t = type_expression { opt with call_args = Some args } env e in
      begin
        match t, args with

        (* Function call *)
        | TFunction (fd, _fo), args ->
(* TODO: check function options can be applied (value, gas, salt) *)
            check_function_application loc "function call"
              fd.function_params args;
            begin
              match fd.function_returns with
              | [t, _id_opt] -> t, fd.function_returns_lvalue
              | tl -> TTuple (List.map (fun (t, _id_opt) -> Some t) tl),
                      fd.function_returns_lvalue
            end

        (* Struct constructor *)
        | TType (TStruct (_lid, sd, _loc) as t), args ->
            let t = change_type_location LMemory t in
            replace_annot e (Solidity_tenv.AType (TType t));
            let fp =
              List.map (fun (fid, ft) ->
                  (change_type_location LMemory ft, Some fid)
                ) sd.struct_fields
            in
            check_function_application loc "struct constructor" fp args;
            t, false

        (* Type conversion *)
        | TType (t), AList ([at]) ->
            begin
              let sloc = get_type_location e.loc at in
              let t = change_type_location sloc t in
              replace_annot e (Solidity_tenv.AType (TType t));
              match Solidity_tenv.explicitly_convertible ~from:at ~to_:t with
              | Some (t) -> t, false
              | None ->
                  error loc
                    "Explicit type conversion not allowed \
                     from \"%s\" to \"%s\""
                    (Solidity_tenv.string_of_type t)
                    (Solidity_tenv.string_of_type at)
            end
        | TType (_), AList (_) ->
            error loc "Exactly one argument expected \
                       for explicit type conversion"

        | TType (_), ANamed (_) ->
            error loc "Type conversion cannot allow named arguments"

        | (TRationalConst _ | TLiteralString _ |
           TBool | TInt _ | TUint _ | TFixed _ | TUfixed _ |
           TAddress _ | TFixBytes _ | TBytes _ | TString _ |
           TEnum _ | TStruct _ | TContract _ | TArray _ | TMapping _ |
           TTuple _ | TModifier _ | TArraySlice _ | TMagic _ |
           (* TON-specific *)
           TTvmCell | TTvmSlice | TTvmBuilder |
           TExtraCurrencyCollection | TOptional _
          ), _ ->
            error loc "Type is not callable"
      end

  | CallOptions (e, opts) ->
      begin
        match type_expression opt env e with
        | TFunction (fd, fo) ->
(* TODO: also available on call/delegatecall/staticcall*)
            let is_payable = is_payable fd.function_mutability in
            let fo = List.fold_left (fun fo (id, e) ->
                let id = strip id in
                let fo, already_set =
                  match Ident.to_string id, fo.Solidity_tenv.kind with
                  | "value", KExtContractFun when not is_payable ->
                      error loc "Cannot set option \"value\" \
                                 on a non-payable function type"
                  | "value", KNewContract when not is_payable ->
                      error loc "Cannot set option \"value\", since the \
                                 constructor of contract is non-payable"
                  | "value", (KExtContractFun | KNewContract) ->
                      expect_expression_type opt env e (TUint None);
                      { fo with value = true }, fo.value
                  | "gas", KExtContractFun ->
                      expect_expression_type opt env e (TUint None);
                      { fo with gas = true }, fo.gas
                  | "salt", KNewContract ->
                      expect_expression_type opt env e (TFixBytes 32);
                      { fo with salt = true }, fo.salt
                  | "gas", KNewContract ->
                      error loc "Function call option \"%s\" cannot \
                                 be used with \"new\""
                        (Ident.to_string id);
                  | "salt", KExtContractFun ->
                      error loc "Function call option \"%s\" can \
                                 only be used with \"new\""
                        (Ident.to_string id);
                  | _, KOther ->
                      error loc "Function call options can only be set on \
                                 external function calls or contract creations"
                        (Ident.to_string id);
                  | _ ->
                      error loc "Unknown option \"%s\". Valid options are \
                                 \"salt\", \"value\" and \"gas\""
                        (Ident.to_string id);
                in
                if already_set then
                  error loc "Option \"%s\" has already been set"
                    (Ident.to_string id);
                fo
              ) fo opts
            in
            TFunction (fd, fo), false
        | _ ->
            error loc "Expected callable expression before call options"
      end

  in
  set_annot exp (Solidity_tenv.AType t);
  t, lv

and expect_array_index_type opt env sz_opt exp =
  let loc = exp.loc in
  let t = type_expression opt env exp in
  expect_type loc ~expected:(TUint None) ~provided:t;
  match t, sz_opt with
  | TRationalConst (q, _), _ when not (ExtQ.is_int q) ->
      error loc "Non-integer array index"
  | TRationalConst (q, _), _ when ExtQ.is_neg q ->
      error loc "Negative array index"
  | TRationalConst (q, _), Some sz ->
      let n = Q.num q in
      if Z.equal (Z.min n sz) sz then
        error loc "Out of bounds array access";
      Some (n)
  | TRationalConst (q, _), None ->
      Some (Q.num q)
  | _ ->
      None

and expect_expression_type opt env exp expected =
  expect_type exp.loc ~expected ~provided:(type_expression opt env exp)

and expect_type loc ~expected ~provided =
  if not (Solidity_tenv.implicitly_convertible
            ~from:provided ~to_:expected ()) then
    error loc "Type %s is not implicitly convertible to expected type %s"
      (Solidity_tenv.string_of_type provided)
      (Solidity_tenv.string_of_type expected)





(* Check statements *)

let rec type_statement opt env s =
  let loc = s.loc in
  match strip s with
  | Block (sl) ->
      let env = Solidity_tenv.new_env ~upper_env:env () in
      List.iter (type_statement opt env) sl

  | Continue ->
      if not opt.in_loop then
        error loc "\"continue\" has to be in a \"for\" or \"while\" loop"

  | Break ->
      if not opt.in_loop then
        error loc "\"break\" has to be in a \"for\" or \"while\" loop"

  | PlaceholderStatement ->
      if not opt.in_modifier then
        error loc "\"_\" has to be in a modifier"

  | ExpressionStatement (e) ->
      ignore (type_expression opt env e)

  | IfStatement (e, s1, s2_opt) ->
      expect_expression_type opt env e TBool;
      type_statement opt env s1;
      Option.iter (type_statement opt env) s2_opt

  | WhileStatement (e, s) ->
      expect_expression_type opt env e TBool;
      type_statement { opt with in_loop = true } env s

  | DoWhileStatement (s, e) ->
      type_statement { opt with in_loop = true } env s;
      expect_expression_type opt env e TBool

  | ForStatement (s1_opt, e1_opt, e2_opt, s2) ->
      Option.iter (type_statement opt env) s1_opt;
      Option.iter (fun e -> expect_expression_type opt env e TBool) e1_opt;
      Option.iter (fun e -> ignore (type_expression opt env e)) e2_opt;
      type_statement { opt with in_loop = true } env s2;

  | TryStatement (e, _returns, body, catch_clauses) ->
      ignore (type_expression opt env e);
      List.iter (type_statement opt env) body;
      List.iter (fun (_id_opt, _params, body) ->
          List.iter (type_statement opt env) body
        ) catch_clauses

  | Return (e) ->
      let annot =
        match opt.fun_returns with
        | [t] -> t
        | tl -> Solidity_tenv.TTuple (List.map Option.some tl)
      in
      set_annot s (Solidity_tenv.AType annot);
      begin
        match (e, opt.fun_returns, opt.in_modifier) with
        | (None, [], _) ->
            ()
        | (None, _ :: _, _) ->
            error loc "Return arguments required"
        | (Some (_), _, true) ->
            error loc "Return arguments not allowed"
        | (Some (e), [rt], _) ->
            begin
              try expect_expression_type opt env e rt
              with Failure (s) -> error loc "%s in return" s
            end
        | (Some e, rtl, _) ->
            begin
              try expect_expression_type opt env e
                    (TTuple (List.map Option.some rtl))
              with Failure (s) -> error loc "%s in return" s
            end
      end

  | VariableDefinition (def) ->
      let var_decl_list =
        match def with
        | VarInfer (var_name_list, e) ->
            let tl =
              match unpromote_type (type_expression opt env e) with
              | TTuple (tl) ->
                  (* Note: unless opt.allow_empty is true,
                     tuple components will never be None *)
                  List.map (function
                      | Some (t) -> t
                      | None -> error loc "type_statement: invariant broken"
                    ) tl
              | t -> [t]
            in
            if not (ExtList.same_lengths tl var_name_list) then
              error loc "Left hand side and right hand side \
                         must have the same number of elements"
            else
              List.map2 (fun var_name_opt t ->
                  Option.map (fun var_name ->
                      (Solidity_tenv.mobile_type t, var_name)) var_name_opt
                ) var_name_list tl

        | VarType (var_decl_list, exp_opt) ->
            let var_decl_list =
              List.map (fun var_decl_opt ->
                  Option.map (fun (t, loc_opt, var_name) ->
                      var_type_to_type loc env ~arg:false ~ext:false loc_opt t,
                      var_name
                    ) var_decl_opt
                ) var_decl_list
            in
            Option.iter (fun e ->
                let tl =
                  match type_expression opt env e with
                  | TTuple (tl) ->
                      (* Note: unless opt.allow_empty is true,
                         tuple components will never be None *)
                      List.map (function
                          | Some (t) -> t
                          | None -> error loc "type_statement: invariant broken"
                        ) tl
                  | t -> [t]
                in
                if not (ExtList.same_lengths tl var_decl_list) then
                  error loc "Left hand side and right hand side \
                             must have the same number of elements"
                else
                  List.iter2 (fun var_decl_opt t ->
                      Option.iter (fun (t', _var_name) ->
                          if not (Solidity_tenv.implicitly_convertible
                                    ~from:t ~to_:t' ()) then
                            error loc "Incompatible types in assignment"
                        ) var_decl_opt
                    ) var_decl_list tl
              ) exp_opt;
            var_decl_list
      in
      let annot =
        match var_decl_list with
        | [Some (t, _id)] -> t
        | tidol -> TTuple (List.map (Option.map fst) tidol)
      in
      set_annot s (Solidity_tenv.AType annot);
      List.iter (function
          | None -> ()
          | Some (t, var_name) ->
              Solidity_tenv.add_variable loc env ~inherited:false
                (strip var_name) (local_variable_desc t)
        ) var_decl_list

  | Emit (_e, _args) ->
      failwith "Emitting events is not supported yet"
(*    ignore (type_expression opt env e); *)



let find_constructor loc Solidity_tenv.{ contract_abs_name; contract_env; _ } =
  match Solidity_tenv.lookup_ident contract_env ~upper:false
          ~lookup:LAny (Ident.constructor) with
  | [Function (fd)] ->
      fd
  | [_] ->
      error loc "Constructor is not a function !"
  | _ :: _ :: _ ->
      error loc "Multiple definitions found for constructor !"
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

let constructor_params env lid =
  match Solidity_tenv.find_lident lid.loc env ~lookup:LInternal (strip lid) with
  | [Contract (cd)] ->
      let fd = find_constructor lid.loc cd in
      (* set_annot lid (Solidity_tenv.AFunction fd); *)
      (* already set *)
      fd.function_params
  | [_] ->
      error lid.loc "Contract expected"
  | _ :: _ :: _ ->
      error lid.loc "Multiple definitions found for contract !"
  | [] ->
      error lid.loc "Identifier not found"

let modifier_or_constructor_params ~constructor env lid =
  match Solidity_tenv.find_lident lid.loc env ~lookup:LInternal (strip lid) with
  | [Contract (cd)] when constructor ->
      let fd = find_constructor lid.loc cd in
      set_annot lid (Solidity_tenv.AFunction fd);
      fd.function_params, true
  | [Modifier (md)] ->
      set_annot lid (Solidity_tenv.AModifier md);
      md.modifier_params, false
  | [_] when not constructor ->
      error lid.loc "Referenced declaration is not a modifier"
  | [_] ->
      error lid.loc "Referenced declaration is neither \
                     a modifier nor a base contract"
  | _ :: _ :: _ ->
      error lid.loc "Multiple definitions found for contract/modifier !"
  | [] ->
      error lid.loc "Undeclared identifier: %a" LongIdent.printf lid.contents

let type_function_body loc opt contract_env id params returns modifiers block =
  let env = Solidity_tenv.new_env ~upper_env:contract_env () in

  (* Add parameters to env *)
  List.iter (fun (t, var_opt) ->
      Option.iter (fun var_name ->
          Solidity_tenv.add_variable loc env ~inherited:false
            var_name (local_variable_desc t)
        ) var_opt
    ) params;

  (* Add return values to env *)
  List.iter (fun (t, var_opt) ->
      Option.iter (fun var_name ->
          Solidity_tenv.add_variable loc env ~inherited:false
            var_name (local_variable_desc t)
        ) var_opt
    ) returns;

  (* Typecheck modifier arguments *)
  let constructor = Ident.equal (Ident.constructor) id in
(* TODO: long id instead of id *)
  List.iter (fun (lid, el_opt) ->
      let params, is_constr =
        modifier_or_constructor_params ~constructor env lid in
      let args =
        match el_opt with
        | None -> []
        | Some (el) -> List.map (type_expression opt env) el
      in
      let kind =
        if is_constr then "constructor call"
        else "modifier invocation"
      in
      check_function_application lid.loc kind params (AList args)
    ) modifiers;

  (* Typecheck actual body *)
  List.iter (type_statement opt env) block



(* Check contracts *)


(* Type state variable initializers and function bodies *)
let type_contract_code (c : Solidity_tenv.contract_desc) =
  let opt = { default_options with
              current_hierarchy = List.map fst c.contract_hierarchy;
              current_contract = Some (c) } in

(*
TODO: check not both defined
*)

  (* Check base constructor arguments *)
  List.iter (fun (lid, el) ->
      match el with
      | [] -> () (* No args provided: don't check *)
      | _ ->
          let params = constructor_params c.contract_env lid in
          let args = List.map (type_expression opt c.contract_env) el in
          check_function_application lid.loc "constructor call"
            params (AList args)
    ) c.contract_def.contract_inheritance;

(* TODO: could iterate over the contract definition instead of env *)
  IdentMap.iter (fun id iddl ->
      List.iter (fun (id_desc, inh) ->
          if not inh then
            let open Solidity_tenv in
            match id_desc with
            | Variable ({ variable_init = Some (e); _ } as v) ->
                expect_expression_type opt c.contract_env e v.variable_type
            | Variable (_) ->
                () (* Note: variable without initializer or inherited variable*)
            | Function ({ function_def =
                            Some { fun_body = Some (body);
                                   fun_modifiers; _ }; _ } as f) ->
                let loc = Solidity_tenv.node_list_loc body in
                let opt = { opt with
                            in_function = true;
                            fun_returns = List.map fst f.function_returns } in
                type_function_body loc opt c.contract_env id
                  f.function_params f.function_returns
                  fun_modifiers body
            | Function (_) ->
                () (* Note: either no body or a builtin function *)
            | Modifier ({ modifier_def =
                            { mod_body = Some (body); _ }; _ } as m) ->
                let opt = { opt with in_modifier = true } in
                let loc = Solidity_tenv.node_list_loc body in
                type_function_body loc opt c.contract_env id
                  m.modifier_params [] [] body
            | Modifier (_) ->
                () (* Note: no body *)
            | Type (_)
            | Contract (_) ->
                ()
        ) iddl
    ) c.contract_env.ident_map





(* Type state variables and functions definition (not initializers/bodies) *)
let type_contract_definitions loc c =
  Solidity_tenv.add_parent_definitions loc ~preprocess:false c;
  List.iter (fun part_node ->
      match strip part_node with
      | StateVariableDeclaration (variable_def) ->
          let vd = state_variable_def_to_desc loc c variable_def in
          begin
            match c.contract_def.contract_kind with
            | Library ->
                if not (is_constant vd.variable_mutability) then
                error loc "Library cannot have non-constant state variables"
            | Interface ->
                error loc "Variables can not be declared in interfaces"
            | _ ->
                ()
          end;
          if is_external vd.variable_visibility then
            error loc "Variable visibility set to external";
          if is_constant vd.variable_mutability && is_none vd.variable_init then
            error loc "Uninitialized \"constant\" variable";
          if not (is_public vd.variable_visibility) &&
             is_some variable_def.var_override then
            error loc "Override can only be used with public state variables";
          Solidity_tenv.add_variable loc c.contract_env
            ~inherited:false (strip variable_def.var_name) vd;
          set_annot part_node (Solidity_tenv.AVariable vd)

      | FunctionDefinition (function_def) ->
          let function_name =
            if Ident.equal (strip function_def.fun_name)
                (strip c.contract_def.contract_name) then
              match function_def.fun_returns with
              | [] -> Ident.constructor
              | _ -> error loc "Non-empty \"returns\" directive for constructor"
            else
              strip function_def.fun_name
          in
          let function_def =
            { function_def with
              fun_name = { function_def.fun_name with
                           contents = function_name } }
          in
          let is_construct = Ident.equal Ident.constructor function_name in
          let is_fallback = Ident.equal Ident.fallback function_name in
          let is_receive = Ident.equal Ident.receive function_name in
          let has_body = is_some function_def.fun_body in
          let has_override = is_some function_def.fun_override in
          let is_external, is_internal, is_private =
            let v = function_def.fun_visibility in
            is_external v, is_internal v, is_private v
          in
          begin
            match c.contract_def.contract_kind with
            | Library ->
                if is_construct then
                  error loc "Constructor can not be defined in libraries";
                if is_fallback then
                  error loc "Libraries cannot have fallback functions";
                if is_receive then
                  error loc "Libraries cannot have receive ether functions";
                if function_def.fun_virtual then
                  error loc "Library functions can not be virtual";
                if has_override then
                  error loc "Library functions can not override";
                if not has_body then
                  error loc "Library functions must be implemented if declared"
            | Interface ->
                if is_construct then
                  error loc "Constructor can not be defined in interfaces";
                if function_def.fun_virtual then
                  error loc "Interface functions are implicitly virtual";
                if has_body then
                  error loc "Functions in interfaces cannot \
                             have an implementation";
                if not is_external then
                  error loc "Functions in interfaces must be declared external"
            | Contract ->
                (* Note: may be abstract even if all functions implemented *)
                if not has_body && not function_def.fun_virtual then
                  error loc "Functions without implementation \
                             must be marked virtual";
                if not has_body && not c.contract_def.contract_abstract then
                  error loc "Contract %s should be marked as \
                             abstract because %s is virtual"
                    (LongIdent.to_string c.contract_abs_name)
                    (Ident.to_string function_name);
          end;
          if is_private && function_def.fun_virtual then
            error loc "\"virtual\" and \"private\" can not be used together";
          if is_construct then
            begin
              if not has_body then
                error loc "Constructor must be implemented if declared";
              if function_def.fun_virtual then
                error loc "Constructors cannot be virtual";
              if is_private || is_external then
                error loc "Constructor cannot have visibility";
              if is_internal && not c.contract_def.contract_abstract then
                error loc "Non-abstract contracts cannot have internal \
                           constructors. Remove the \"internal\" keyword \
                           and make the contract abstract to fix this";
              if not (is_payable function_def.fun_mutability ||
                      is_nonpayable function_def.fun_mutability) then
                error loc "Constructor must be payable or \
                           non-payable, but is \"%s\""
                  (Solidity_printer.string_of_fun_mutability
                     function_def.fun_mutability)
            end;
          if is_fallback then
            begin
              if not is_external then
                error loc "Fallback function must be defined as \"external\"";
              if not (is_payable function_def.fun_mutability ||
                      is_nonpayable function_def.fun_mutability) then
                error loc "Fallback function must be payable or \
                           non-payable, but is \"%s\""
                  (Solidity_printer.string_of_fun_mutability
                     function_def.fun_mutability)
            end;
          if is_receive then
            begin
              if not is_external then
                error loc "Receive ether function must be \
                           defined as \"external\"";
              if is_receive && not (is_payable function_def.fun_mutability) then
                error loc "Receive ether function must be \
                           payable, but is \"%s\""
                  (Solidity_printer.string_of_fun_mutability
                     function_def.fun_mutability)
            end;
          let fd = function_def_to_desc loc c function_def in
          Solidity_tenv.add_function loc c.contract_env
            ~inherited:false function_name fd;
          set_annot part_node (Solidity_tenv.AFunction fd)

      | ModifierDefinition (modifier_def) ->
          let modifier_name = strip modifier_def.mod_name in
          let has_body = is_some modifier_def.mod_body in
          let has_override = is_some modifier_def.mod_override in
          if not has_body && not modifier_def.mod_virtual then
            error loc "Modifiers without implementation \
                       must be marked virtual";
          begin
            match c.contract_def.contract_kind with
            | Library ->
                if modifier_def.mod_virtual then
                  error loc "Modifiers in a library can not be virtual";
                if has_override then
                  error loc "Modifiers in a library can not override";
                if not has_body then
                  error loc
                    "Modifiers in a library must be implemented if declared"
            | Interface ->
                ()
            | Contract ->
                (* Note: may be abstract even if all functions implemented *)
                if not has_body && not c.contract_def.contract_abstract then
                  error loc "Contract %s should be marked as \
                             abstract because %s is virtual"
                    (LongIdent.to_string c.contract_abs_name)
                    (Ident.to_string modifier_name);
          end;
          let md = modifier_def_to_desc loc c modifier_def in
          Solidity_tenv.add_modifier loc c.contract_env
            ~inherited:false modifier_name md;
          set_annot part_node (Solidity_tenv.AModifier md)

      | EventDefinition (_event_def) ->
          failwith "Events are not supported yet"

      | UsingForDeclaration (_) ->
          failwith "Using for is not supported yet"

      | TypeDefinition (_td) ->
          () (* already handled during preprocessing *)
    ) c.contract_def.contract_parts;
  if not c.contract_def.contract_abstract &&
       not (is_interface c.contract_def.contract_kind) then
      match Solidity_tenv.has_abstract_function c with
      | None -> ()
      | Some (function_name) ->
          error loc "Contract %s should be marked as \
                     abstract because %s is virtual"
            (LongIdent.to_string c.contract_abs_name)
            (Ident.to_string function_name)






(* Perform linearization of inheritance diagram *)
let c3_linearization loc ~module_env:_
    (Solidity_tenv.{ contract_abs_name; contract_def; _ } as c) =
  let get_next lident_contract_ll =
    let res = List.find_opt (function
        | [] -> false (* should not happen *)
        | (lident, _) :: _ ->
            List.for_all (function
                | [] -> true (* should not happen *)
                | _ :: lident_contract_l ->
                    not (List.mem_assoc lident lident_contract_l)
              ) lident_contract_ll
      ) lident_contract_ll
    in
    match res with
    | None
    | Some ([]) -> None (* should not happen *)
    | Some (lident_contract :: _) -> Some lident_contract
  in
  let filter_out_empty lident_contract_ll =
    List.filter (function
        | [] -> false
        | _ -> true
      ) lident_contract_ll
  in
  let filter_out (lident, _) lident_contract_ll =
    List.map (fun lident_contract_l ->
        match lident_contract_l with
        | [] -> lident_contract_l (* should not happen *)
        | (lident', _) :: lident_contract_l' ->
            if LongIdent.equal lident lident' then
              lident_contract_l'
            else
              lident_contract_l
      ) lident_contract_ll
    |> filter_out_empty
  in
  let rec merge res lident_contract_ll =
    match lident_contract_ll with
    | [] -> List.rev res
    | _ ->
        match get_next lident_contract_ll with
        | None ->
            error loc "Linearization failed for %s"
               (LongIdent.to_string contract_abs_name)
        | Some (lident_contract) ->
            merge (lident_contract :: res)
              (filter_out lident_contract lident_contract_ll)
  in
  let parents_linearization, contract_parents =
    List.split (List.rev (List.map (fun (p, _) ->
        match get_annot p with
        | Solidity_tenv.AContract (c) ->
            c.contract_hierarchy, (c.contract_abs_name, c)
        | _ ->
            error loc "Contract %s parent contract %s is undefined"
              (LongIdent.to_string contract_abs_name)
              (LongIdent.to_string (strip p))
      ) contract_def.contract_inheritance))
  in
  c.contract_hierarchy <-
    merge [contract_abs_name, c]
      (filter_out_empty (parents_linearization @ [contract_parents]))





let preprocess_type_definition loc env
    (path_prefix : absolute LongIdent.t) type_def _parents =
  match type_def with
  | StructDefinition (name, fields) ->
      let struct_abs_name = LongIdent.append path_prefix (strip name) in
      Solidity_tenv.add_struct loc env ~inherited:false struct_abs_name
        (strip name) (strip name, fields)
  | EnumDefinition (name, values) ->
      let enum_abs_name = LongIdent.append path_prefix (strip name) in
      Solidity_tenv.add_enum loc env ~inherited:false enum_abs_name
        (strip name) (List.map strip values)


let preprocess_contract_definition
    loc ~module_env (mlid : absolute LongIdent.t) contract_def =
  let contract_name = strip contract_def.contract_name in

  begin
    match contract_def.contract_kind with
    | Library ->
        if contract_def.contract_abstract then
          error loc "Libraries can not be abstract";
        begin
          match contract_def.contract_inheritance with
          | _ :: _ -> error loc "Library is not allowed to inherit"
          | _ -> ()
        end;
    | Interface ->
        if contract_def.contract_abstract then
          error loc "Interfaces do not need the \"abstract\" keyword, \
                 they are abstract implicitly";
        List.iter (fun (lid, _el) ->
            match Solidity_tenv.find_contract
                    lid.loc module_env (strip lid) with
            | None ->
                error lid.loc "Interface %s parent interface %s is undefined"
                  (Ident.to_string contract_name)
                  (LongIdent.to_string (strip lid))
            | Some (c) ->
                set_annot lid (Solidity_tenv.AContract c);
                if not (is_interface c.contract_def.contract_kind) then
                  error lid.loc
                    "Interfaces can only inherit from other interfaces"
          ) contract_def.contract_inheritance
    | Contract ->
        List.iter (fun (lid, _el) ->
            match Solidity_tenv.find_contract
                    lid.loc module_env (strip lid) with
            | None ->
                error lid.loc "Contract %s parent contract %s is undefined"
                  (Ident.to_string contract_name)
                  (LongIdent.to_string (strip lid))
            | Some (c) ->
                set_annot lid (Solidity_tenv.AContract c);
                if is_library c.contract_def.contract_kind then
                  error lid.loc "Libraries can not be inherited from"
          ) contract_def.contract_inheritance
  end;

  let c = Solidity_tenv.{
    contract_abs_name = LongIdent.append mlid contract_name;
    contract_env = new_env ~upper_env:module_env ();
    contract_def; contract_hierarchy = [];
  }
  in

  (* Perform the linearization of the contract hierarchy *)
  c3_linearization loc ~module_env c;

  (* Add parent contracts contents to derived contract env *)
  Solidity_tenv.add_parent_definitions loc ~preprocess:true c;
(* TODO: check derivability virtual/override on fun/mod/var *)

  Solidity_tenv.add_contract loc module_env contract_name c;

(* TODO : how does it behave in a diamond-shaped inheritance diagram ? *)

  List.iter (fun part_node ->
      match strip part_node with
      | UsingForDeclaration (_) ->
          failwith "TODO : Using For"
      | TypeDefinition (td) ->
          preprocess_type_definition part_node.loc c.contract_env
            (c.contract_abs_name) td c.contract_hierarchy
      | StateVariableDeclaration (_)
      | FunctionDefinition (_)
      | ModifierDefinition (_)
      | EventDefinition (_) ->
          (* Nothing to do here, we just care about contract and types *)
          ()
    ) contract_def.contract_parts;
  c




let rec update_struct_fields ~env =
  IdentMap.iter (fun _id iddl ->
      List.iter (fun (id_desc, _inh) ->
          let open Solidity_tenv in
          match id_desc with
          | Contract (c) ->
              update_struct_fields ~env:c.contract_env
          | Type (TDStruct (s)) ->
              let fields =
                List.map (fun (t, id_node) ->
                    strip id_node,
                    (ast_type_to_type id_node.loc
                       ~loc:(LStorage (false)) s.struct_env t)
                  ) (snd s.struct_def)
              in
              Solidity_tenv.add_struct_fields s fields
          | Type (TDEnum _)
          | Variable (_)
          | Function (_)
          | Modifier (_) -> ()
        ) iddl
    ) env.ident_map





let check_types_acyclicity ~env =
  (* We only consider direct dependencies
     (recursive types are allowed under indirection *)
  let rec add_field_type_deps struct_ field_name field_type ty_deps =
    match field_type with
    | UserDefinedType (lid_node) ->
        let _rel_lid = strip lid_node in
        let abs_lid = assert false in (* TODO *)
        AbsLongIdentSet.add abs_lid ty_deps
    | Array (type_, Some (_)) ->
        add_field_type_deps struct_ field_name type_ ty_deps
    | Array (_, None) -> ty_deps
    | Mapping (_) -> ty_deps
    | FunctionType (_) -> ty_deps
    | ElementaryType (_) -> ty_deps
    (* TON-specific *)
    | Optional (_) -> ty_deps
  in
  let rec compute_types_deps deps ~env =
    IdentMap.fold (fun _name idl deps ->
        List.fold_left (fun deps (id_desc, _inh) ->
            let open Solidity_tenv in
            match id_desc with
            | Contract (c) ->
                compute_types_deps deps ~env:c.contract_env
            | Type (TDStruct (s)) ->
                let ty_deps =
                  List.fold_left (fun ty_deps (field_type, field_name) ->
                      add_field_type_deps s field_name field_type ty_deps
                    ) AbsLongIdentSet.empty (snd s.struct_def)
                in
                AbsLongIdentMap.add s.struct_abs_name ty_deps deps
            | Type (TDEnum (_))
            | Variable (_)
            | Function (_)
            | Modifier (_) -> deps
          ) deps idl
      ) env.ident_map deps
  in
  let rec compute_type_deps_closure deps ty_deps ty_deps_closure =
    if AbsLongIdentSet.is_empty ty_deps then ty_deps_closure
    else
      let new_ty_deps = AbsLongIdentSet.diff ty_deps ty_deps_closure in
      let ty_deps_closure = AbsLongIdentSet.union new_ty_deps ty_deps_closure in
      let next_ty_deps = AbsLongIdentSet.fold (fun ty next_ty_deps ->
          match AbsLongIdentMap.find_opt ty deps with
          | None -> next_ty_deps
          | Some (ty_deps) -> AbsLongIdentSet.union ty_deps next_ty_deps
        ) new_ty_deps AbsLongIdentSet.empty
      in
      compute_type_deps_closure deps next_ty_deps ty_deps_closure
  in
  let deps = compute_types_deps AbsLongIdentMap.empty ~env in
  let _ = AbsLongIdentMap.iter (fun ty ty_deps ->
      let ty_deps_closure =
        compute_type_deps_closure deps ty_deps AbsLongIdentSet.empty in
      if AbsLongIdentSet.mem ty ty_deps_closure then
        error dummy_loc "Type definition %s is cyclic" (LongIdent.to_string ty)
        (* todo: provide correct location *)
    ) deps
  in
  ()




(* Add contracts and types to environments *)
let preprocess_module loc mlid module_ =
  let module_env = Solidity_tenv.new_env () in
  let contents = List.rev (List.fold_left (fun contents unit_node ->
      match strip unit_node with
      | Pragma (_) ->
          contents
      | Import (_) ->
          failwith "Imports are not supported yet"
          (* set_annot unit_node (AImport (Ident.root 0)); *)
      | GlobalTypeDefinition (td) ->
          preprocess_type_definition loc module_env mlid td [];
          contents
      | GlobalFunctionDefinition (fd) ->
          (`Function (fd) :: contents)
      | ContractDefinition (cd) ->
          let cd = preprocess_contract_definition loc ~module_env mlid cd in
          set_annot unit_node (Solidity_tenv.AContract (cd));
          (`Contract (cd) :: contents)
    ) [] module_)
  in
  update_struct_fields ~env:module_env; (* This also ensures user types exist *)
  check_types_acyclicity ~env:module_env;
(* TODO: make an extra pass to check for module/contract type shadowing *)
(* TODO: this could be done when adding things in env *)
  contents, module_env

let type_module loc mlid module_ =
  (* Types and contract linearization *)
  let contents, module_env = preprocess_module loc mlid module_ in
  (* State variables, functions, modifiers, events *)
  List.iter (function
      | `Contract (cd) -> type_contract_definitions loc cd
      | `Function (_fd) -> failwith "Free functions TODO"
    ) contents;
  (* Code *)
  List.iter (function
      | `Contract (cd) -> type_contract_code cd
      | `Function (_fd) -> failwith "Free functions TODO"
    ) contents;
  module_env

let type_module m =
  let mlid = LongIdent.of_ident_abs (Ident.root 1) in
  let loc = Solidity_tenv.node_list_loc m in
  ignore (type_module loc mlid m)
