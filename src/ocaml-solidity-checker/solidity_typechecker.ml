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

let binop_type pos op t1 t2 : type_ =
  let error_incompat () =
    error pos "Operator %s not compatible with types %s and %s"
      (Solidity_printer.string_of_binop op)
      (Solidity_type_printer.string_of_type t1)
      (Solidity_type_printer.string_of_type t2)
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
      Solidity_type_conv.mobile_type pos t1
  | (BExp | BLShift | BRShift), _, _ ->
      let mt1 = Solidity_type_conv.mobile_type pos t1 in
      let mt2 = Solidity_type_conv.mobile_type pos t2 in
      begin
        match mt1, mt2 with
        | (TInt _ | TUint _), TUint _ -> mt1
        | _ -> error_incompat ()
      end
  | (BPlus | BMinus | BTimes | BDiv | BMod | BAnd | BOr | BXor), _, _ ->
      let mt1 = Solidity_type_conv.mobile_type pos t1 in
      let mt2 = Solidity_type_conv.mobile_type pos t2 in
      let t = Solidity_type_conv.common_type mt1 mt2 in
      begin
        match t with
        | Some (TInt _ | TUint _ | TFixed _ | TUfixed _ as t) -> t
        | _ -> error_incompat ()
      end
  | (BLAnd | BLOr), TBool, TBool ->
      TBool
  | (BLAnd | BLOr), _, _ ->
      error_incompat ()

let unop_type pos op t : type_ =
  let error_incompat () =
    error pos "Unary operator %s cannot be applied to type %s"
      (Solidity_printer.string_of_unop op)
      (Solidity_type_printer.string_of_type t)
  in
  match t, op with
  | _, UPlus ->
      error pos "Usage of unary + is disallowed";
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
      let mt = Solidity_type_conv.mobile_type pos t in
      begin
        match mt with
        | TInt _ | TUint _ | TFixed _ | TUfixed _ -> mt
        | _ -> error_incompat ()
      end
  | TBool, ULNot ->
      TBool
  | _, ULNot ->
      error_incompat ()

let immediate_array_element_type pos tl : type_ =
  let error_no_common_type () =
    error pos "Unable to deduce common type for array elements"
  in
  let rec aux t = function
    | [] -> t
    | t' :: tl ->
        let t =
          if Solidity_type_conv.implicitly_convertible
              ~ignore_loc:true ~from:t' ~to_:t () then
            t
          else
            let t' = Solidity_type_conv.mobile_type pos t' in
            if Solidity_type_conv.implicitly_convertible
                ~ignore_loc:true ~from:t ~to_:t' () then
              t'
            else
              error_no_common_type ()
        in
        aux t tl
  in
  match tl with
  | [] -> error_no_common_type ()
  | t :: tl ->
      begin
        match aux (Solidity_type_conv.mobile_type pos t) tl with
        | TRationalConst _ | TLiteralString _ ->
            error pos "immediate_array_element_type: invariant broken"
        | (TTuple _ | TArraySlice _ | TFunction _ |
           TModifier _ | TEvent _ | TType _ | TMagic _) as t ->
            error pos "Type %s is only valid in storage"
              (Solidity_type_printer.string_of_type t)
        | t ->
            (* Note: always LMemory, even when initializing state variables *)
            Solidity_type.change_type_location LMemory t
      end

let nb_args = function
  | AList (tl) -> List.length tl
  | ANamed (ntl) -> List.length ntl

let check_argument_type pos kind ~expected ~provided =
  if not (Solidity_type_conv.implicitly_convertible
            ~from:provided ~to_:expected ()) then
    error pos "Invalid type for argument in %s. \
               Invalid implicit conversion from %s to %s requested" kind
      (Solidity_type_printer.string_of_type provided)
      (Solidity_type_printer.string_of_type expected)

let check_function_application pos kind fp args =
  let nb_args_expected = List.length fp in
  let nb_args_provided = nb_args args in
  (* Note: named arguments in ANamed ntl are unique (checked previously) *)
  if nb_args_provided <> nb_args_expected then
    error pos "Wrong argument count for %s: \
               %d arguments given but expected %d"
      kind nb_args_provided nb_args_expected
  else
    begin
      match args with
      | AList (tl) ->
          List.iter2 (fun (ft, _id_opt) at ->
              check_argument_type pos kind ~expected:ft ~provided:at
            ) fp tl
      | ANamed (ntl) ->
          List.iter (fun (fid, at) ->
              match List.find_opt (fun (_ft, id_opt) ->
                  match id_opt with
                  | Some id -> Ident.equal id fid
                  | None -> false) fp with
              | Some (ft, _id_opt) ->
                  check_argument_type pos kind ~expected:ft ~provided:at
              | None ->
                  error pos "Named argument \"%s\" does not \
                             match function declaration"
                    (Ident.to_string fid)
            ) ntl
    end

let compatible_function_type (fd : function_desc) args  =
  let nb_args_expected = List.length fd.function_params in
  let nb_args_provided = nb_args args in
  (* Note: named arguments in ANamed ntl are unique (checked previously) *)
  if nb_args_provided <> nb_args_expected then
    false
  else
    begin
      match args with
      | AList (tl) ->
          List.for_all2 (fun (ft, _id_opt) at ->
              Solidity_type_conv.explicitly_convertible_bool ~from:at ~to_:ft
            ) fd.function_params tl
      | ANamed (ntl) ->
          List.for_all (fun (fid, at) ->
              match List.find_opt (fun (_ft, id_opt) ->
                  match id_opt with
                  | Some (id) -> Ident.equal id fid
                  | None -> false) fd.function_params with
              | Some (ft, _id_opt) ->
                  Solidity_type_conv.explicitly_convertible_bool
                    ~from:at ~to_:ft
              | None ->
                  false
            ) ntl
    end

(* Base types on which "using for" is allowed.
   These are the types the user can express, as well as the types coercible
   to these types. In particular, this excludes internal types. *)
let using_for_allowed base_t_opt =
  match base_t_opt with
  | None
  | Some (TModifier (_) | TEvent (_) | TTuple (_) |
          TArraySlice (_) | TType (_) | TMagic (_) |
          TContract (_, _, true (* super *))) ->
      false
  | Some (_) ->
      true

let is_contract_instance base_t_opt =
  match base_t_opt with
  | Some (TContract (_lid, _cd, false (* super *))) ->
      true
  | Some (_) | None ->
      false

let fun_opt base_t_opt is_uf (fd : function_desc) =
  (* Note: external functions attached to contracts with using for
     do not allow options and are considered as regular functions *)
  let kind =
    match fd.function_visibility with
    | (VExternal | VPublic) when is_contract_instance base_t_opt && not is_uf ->
        KExtContractFun
    | _ ->
        KOther
  in
  { Solidity_tenv.new_fun_options with kind }

let get_variable_getter pos vd =
  if vd.variable_local then
    error pos "Requesting getter on a local variable !";
  match vd.variable_getter with
  | Some (fd) -> fd
  | None -> error pos "Variable is missing a getter !"

let type_and_annot_of_id_desc pos base_t_opt idd is_uf =
  match idd with
  | Type (td) ->
      (* Note: user types have their storage location
         set to storage pointer by default *)
      let t =
        Solidity_type_builder.type_desc_to_base_type ~loc:(LStorage true) td in
      TType (t), false, AType (t)
  | Contract (cd) ->
      let t = TContract (cd.contract_abs_name, cd, false (* super *)) in
      TType (t), false, AContract (cd)
  | Modifier (md) ->
      TModifier (md), false, AModifier (md)
  | Event (ed) ->
      TEvent (ed), false, AEvent (ed)
  | Variable (vd) when is_contract_instance base_t_opt ->
      let fd = get_variable_getter pos vd in
      TFunction (fd, fun_opt base_t_opt false fd), false, AVariable (vd, true)
  | Variable (vd) when vd.variable_is_primitive ->
      vd.variable_type, is_mutable vd.variable_mutability, APrimitive
  | Variable (vd) ->
      let lv = not (is_constant vd.variable_mutability) in
      vd.variable_type, lv, AVariable (vd, false)
  | Function (fd) when is_uf ->
      assert (using_for_allowed base_t_opt);
      assert (not fd.function_is_primitive); (* just a check *)
      assert (not fd.function_is_method); (* = function from library *)
      let fd' =
        match fd.function_params with
        | (_ft, _id_opt) :: fp ->
            { fd with function_params = fp }
        | _ ->
            error pos "type_and_annot_of_id_desc: invariant broken"
      in
      TFunction (fd', fun_opt base_t_opt true fd'), false, AFunction (fd, true)
  | Function (fd) when fd.function_is_primitive ->
      TFunction (fd, fun_opt base_t_opt false fd), false, APrimitive
  | Function (fd) ->
      TFunction (fd, fun_opt base_t_opt false fd), false, AFunction (fd, false)
  | Field (fd) ->
      fd.field_type, true, AField (fd)
  | Constr (cd) ->
      cd.constr_type, false, AConstr (cd)

let resolve_overloads pos opt base_t_opt id iddl uf_iddl =
  (* To mimic the official compiler messages, we use different
     messages depending on the context: plain ident vs member ident *)
  let err_notfound, err_notunique, err_nomatch, err_manymatch =
    match base_t_opt with
    | None ->
        (* No result *)
        (fun () ->
          error pos "Undeclared identifier: %s" (Ident.to_string id)),
(*        error "Undeclared identifier. \"%s\" is not (or not yet) \
                 visible at this point" (Ident.to_string id)) *)
        (* Multiple results and no args given (resolution impossible) *)
        (fun () ->
          error pos
            "No matching declaration found after variable lookup"),
        (* Multiple results and no match (resolution failed) *)
        (fun () ->
          error pos
            "No matching declaration found after argument-dependent lookup"),
        (* Multiple results and multiple match *)
        (fun () ->
          error pos
            "No unique declaration found after argument-dependent lookup")
    | Some (t) ->
        (* No result or multiple results and no match *)
        let err_notfound () =
          error pos "Member %s not found or not visible after \
                     argument-dependent lookup in %s" (Ident.to_string id)
            (Solidity_type_printer.string_of_type t)
        in
        (* Multiple results and no args or multiple match *)
        let err_notunique () =
          error pos "Member %s not unique after argument-dependent \
                     lookup in %s" (Ident.to_string id)
            (Solidity_type_printer.string_of_type t)
        in
        err_notfound, err_notunique, err_notfound, err_notunique
  in
  match iddl, uf_iddl with
  | [], [] -> err_notfound ()
  | [idd], [] -> idd, false
  | [], [idd] -> idd, true
  | _ ->
      let args =
        match opt.call_args with
        | None -> err_notunique ()
        | Some (args) -> args
      in
      let add_if_compatible idd iddl fd args =
        if compatible_function_type fd args then
          idd :: iddl
        else
          iddl
      in
      let iddl =
        List.fold_left (fun iddl idd ->
            match idd with
            (* Function *)
            | Function (fd) ->
                add_if_compatible idd iddl fd args
            (* Variable getter *)
            | Variable (vd) when is_contract_instance base_t_opt ->
                let fd = get_variable_getter pos vd in
                add_if_compatible idd iddl fd args
            (* Variable *)
            | Variable (vd) ->
                begin
                  (* Variables of type function *)
                  match vd.variable_type with
                  | TFunction (fd, _fo) ->
                      add_if_compatible idd iddl fd args
                  (* Non-function variables and primitives *)
                  | _ ->
                      idd :: iddl
                end
            (* Structure field *)
            | Field (fd) ->
                begin
                  match fd.field_type with
                  (* Field of type function *)
                  | TFunction (fd, _fo) ->
                      add_if_compatible idd iddl fd args
                  (* Non-function field *)
                  | _ ->
                      idd :: iddl
                end
            (* Event *)
            | Event (ed) ->
                let fd = Solidity_type_builder.event_desc_to_function_desc ed in
                add_if_compatible idd iddl fd args
            | _ ->
                iddl
          ) [] iddl
      in
      let uf_iddl =
        List.fold_left (fun uf_iddl idd ->
            match idd with
            | Function (fd) ->
                assert (using_for_allowed base_t_opt);
                assert (not fd.function_is_primitive); (* just a check *)
                assert (not fd.function_is_method); (* = function from library*)
                begin
                  match base_t_opt, fd.function_params with
                  | Some (at), (ft, _id_opt) :: fp
                    when Solidity_type_conv.implicitly_convertible
                           ~from:at ~to_:ft () ->
                      let fd = { fd with function_params = fp } in
                      add_if_compatible idd uf_iddl fd args
                  | _ ->
                      uf_iddl
                end
            | _ ->
                uf_iddl
          ) [] uf_iddl
      in
      match iddl, uf_iddl with
      | [idd], [] -> idd, false
      | [], [idd] -> idd, true
      | [], [] -> err_nomatch ()
      | _ -> err_manymatch ()

let get_primitive opt base_t_opt id_node =
  match prim_of_ident (strip id_node) with
  | Some (pid, _prim) ->
      begin
        match Solidity_tenv.prim_desc.(pid) id_node.pos opt base_t_opt with
        | Some (t) -> [t]
        | None -> []
      end
  | None ->
      []


let type_ident opt env base_t_opt id_node =

  let id = strip id_node in
  let pos = id_node.pos in

  (* Look for a user ident based on the current environment and base type *)
  let iddl =
    match base_t_opt with
    | None ->
        Solidity_tenv.find_ident env ~lookup:LInternal id

    | Some (base_t) ->

        match base_t with

        (* Contract field (through a variable of type contract) *)
        | TContract (_lid, cd, false (* super *)) ->
            Solidity_tenv.find_ident cd.contract_env ~lookup:LExternal id

        (* Parent contract field (through "super") *)
        | TContract (_lid, cd, true (* super *)) ->
            let env =
              match cd.contract_hierarchy with
              | _ :: (_lid, cd) :: _ -> cd.contract_env
              | _ -> Solidity_tenv.new_env ()
            in
            Solidity_tenv.find_ident env ~lookup:LSuper id

        (* Static contract field (through a contract type name) *)
        | TType (TContract (lid, cd, _super)) -> (* super should be false *)
            let is_parent = List.mem lid opt.current_hierarchy in
            let lookup = Solidity_tenv.LStatic (
                             cd.contract_def.contract_kind, is_parent) in
            Solidity_tenv.find_ident cd.contract_env ~lookup id

        (* Enum value *)
        | TType (TEnum (_lid, ed) as t) ->
            begin
              match IdentAList.find_opt id ed.enum_values with
              | Some (i) ->
                  let cd = {
                    constr_enum_desc = ed;
                    constr_name = id; constr_value = i; constr_type = t; }
                  in
                  [Constr (cd)]
              | None ->
                  []
            end

        (* Struct member access *)
        | TStruct (_lid, sd, _loc) ->
            begin
              match IdentAList.find_opt id sd.struct_fields with
              | Some (t) ->
                  let fd = {
                      field_struct_desc = sd;
                      field_name = id; field_type = t; }
                  in
                  [Field (fd)]
              | None ->
                  []
            end

        | _ ->
            []
  in

  (* Look for a primitive ONLY IF no ident found
     (primitives can be shadowed by user idents, except if
     the ident comes from a "using for", in which case
     the primitive is overloaded instead of shadowed *)
  let iddl =
    match iddl with
    | [] -> get_primitive opt base_t_opt id_node
    | _ -> iddl
  in

  (* If we are performing a member lookup, then also look into "using for".
     We do this only if "using for" is allowed on the base type *)
  let uf_iddl =
    match base_t_opt with
    | Some (t) when using_for_allowed base_t_opt ->
        let uf =
          match opt.current_contract with
          | None -> env.using_for
          | Some (cd) -> cd.contract_env.using_for
        in
        let envs =
          AbsLongIdentMap.fold (fun _lid (env, tl) envs ->
              if tl = [] ||
                   List.exists (fun t' ->
                       Solidity_type_conv.implicitly_convertible
                         ~from:t ~to_:t' ()) tl then
                env :: envs
              else
                envs
            ) uf []
        in
        List.fold_left (fun iddl env ->
            Solidity_tenv.find_ident env ~lookup:LUsingFor id @ iddl
          ) [] envs
    | Some (_) | None ->
        []
  in

  (* Then, perform overload resolution (if needed) *)
  let idd, is_uf = resolve_overloads pos opt base_t_opt id iddl uf_iddl in

  (* Finally, retrive the type and annotation for this ident *)
  let t, lv, a = type_and_annot_of_id_desc id_node.pos base_t_opt idd is_uf in
  set_annot id_node a;
  t, lv

let rec type_expression opt env exp : type_ =
  let t, _lv = type_expression_lv opt env exp in
  t

and type_expression_lv opt env exp : type_ * bool =
  let pos = exp.pos in
  let t, lv = match strip exp with

  (* Literals *)

  | BooleanLiteral (_b) ->
      TBool, false

  | NumberLiteral (q, unit, sz_opt) ->
      (* Note: size set only if hex *)
      let q = apply_unit q unit in
      let sz_opt =
        match sz_opt with
        | Some (i) ->
            if (i mod 2 = 0) then
              Some (i / 2)
            else
              None (* Note: if not even, size info is no longer relevant *)
        | None ->
            None
      in
      TRationalConst (q, sz_opt), false

  | StringLiteral (s) ->
      TLiteralString (s), false

  | AddressLiteral (_a) ->
      (* Note: Valid address literals are of type address payable *)
      TAddress (true), false

  (* Array expressions *)

  | ImmediateArray (el) ->
      let tl = List.map (type_expression opt env) el in
      let t = immediate_array_element_type pos tl in
      let sz = Z.of_int (List.length tl) in
      (* Note: not an lvalue, but index access to such array is an lvalue *)
      TArray (t, Some (sz), LMemory), false

  | ArrayAccess (e, None) ->
      begin
        match type_expression opt env e with
        | TType (t) ->
            let t = Solidity_type.change_type_location LMemory t in
            replace_annot e (AType (TType t));
            TType (TArray (t, None, LMemory)), false
        | _ ->
            error pos "Index expression cannot be omitted"
      end

  | ArrayAccess (e1, Some (e2)) ->
      begin
        match type_expression opt env e1 with
        | TType (t) ->
            begin
              match expect_array_index_type opt env None e2 with
              | Some (sz) ->
                  let t = Solidity_type.change_type_location LMemory t in
                  replace_annot e1 (AType (TType t));
                  TType (TArray (t, Some (sz), LMemory)), false
              | None ->
                  error pos "Integer constant expected"
            end
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
        | TFixBytes (sz) ->
            ignore (expect_array_index_type opt env (Some (Z.of_int sz)) e2);
            TFixBytes (1), false
        | TBytes (_loc) ->
            ignore (expect_array_index_type opt env None e2);
            TFixBytes (1), true
        | TString (_loc) ->
            error pos "Index access for string is not possible"
        | t ->
            error pos "Indexed expression has to be a type, \
                       mapping or array (is %s)"
                      (Solidity_type_printer.string_of_type t)
      end

  | ArraySlice (e1, e1_opt, e2_opt) ->
      begin
        match type_expression opt env e1 with
        | TArray (t, None, (LCalldata as loc))
        | TArraySlice (t, loc) ->
            Option.iter (fun e ->
                ignore (expect_array_index_type opt env None e)) e1_opt;
            Option.iter (fun e ->
                ignore (expect_array_index_type opt env None e)) e2_opt;
            TArraySlice (t, loc), false
        | TArray (_t, _sz_opt, _loc) ->
            error pos "Index range access is only supported \
                       for dynamic calldata arrays"
        | _ ->
            error pos "Index range access is only possible \
                       for arrays and array slices"
      end

  (* Simple expressions *)

  | PrefixExpression ((UInc | UDec | UDelete as op), e)
  | SuffixExpression (e, (UInc | UDec as op)) ->
      let t, lv = type_expression_lv { opt with allow_empty = true } env e in
      if not lv then error pos "Expression has to be an lvalue";
      unop_type pos op t, false

  | PrefixExpression (op, e)
  | SuffixExpression (e, op) ->
      unop_type pos op (type_expression opt env e), false

  | BinaryExpression (e1, op, e2) ->
      let t1 = type_expression opt env e1 in
      let t2 = type_expression opt env e2 in
      binop_type pos op t1 t2, false

  | CompareExpression (e1, op, e2) ->
      let t1 = type_expression opt env e1 in
      let t2 = type_expression opt env e2 in
      let valid =
        match Solidity_type_conv.common_type
                (Solidity_type_conv.mobile_type pos t1)
                (Solidity_type_conv.mobile_type pos t2) with
        | Some (t) -> Solidity_type.is_comparable op t
        | None -> false
      in
      if not valid then
        error pos "Operator %s not compatible with types %s and %s"
          (Solidity_printer.string_of_cmpop op)
          (Solidity_type_printer.string_of_type t1)
          (Solidity_type_printer.string_of_type t2);
      TBool, false

  | AssignExpression (e1, e2) ->
      let t1, lv = type_expression_lv { opt with allow_empty = true } env e1 in
      let t2 = type_expression opt env e2 in
      if not lv then
        error pos "Assignment operator requires lvalue as left-hand side";
      (* Note: (true ? tuple : tuple) = tuple
         may become allowed in the future *)
      expect_type pos ~expected:t1 ~provided:t2;
      t1, false

  | AssignBinaryExpression (e1, op, e2) ->
      let t1, lv = type_expression_lv { opt with allow_empty = true } env e1 in
      let t2 = type_expression opt env e2 in
      if not lv then
        error pos "Assignment operator requires lvalue as left-hand side";
      if Solidity_type.is_tuple t1 then
        error pos "Compound assignment is not allowed for tuple types"
      else
        let t = binop_type pos op t1 t2 in
        expect_type pos ~expected:t1 ~provided:t;
        t1, false

  | TupleExpression (eol) ->
      let tl, lv =
        List.fold_left (fun (tl, lv) e_opt ->
            match e_opt with
            | Some (e) ->
                let t, elv = type_expression_lv opt env e in
                Some (t) :: tl, lv && elv
            | None when opt.allow_empty ->
                None :: tl, lv
            | None ->
                error pos "Tuple component cannot be empty"
          ) ([], true) eol
      in
      TTuple (List.rev tl), lv

  | IfExpression (e_if, e_then, e_else) ->
      (* Note: may become an lvalue in the future *)
      expect_expression_type opt env e_if TBool;
      let t1 = type_expression opt env e_then in
      let t2 = type_expression opt env e_else in
      begin
        match Solidity_type_conv.common_type
                (Solidity_type_conv.mobile_type pos t1)
                (Solidity_type_conv.mobile_type pos t2) with
        | Some (t) ->
            t, false
        | None ->
            error pos "True expression's type %s does not \
                       match false expression's type %s"
              (Solidity_type_printer.string_of_type t1)
              (Solidity_type_printer.string_of_type t2)
      end

  | NewExpression (t) ->
      (* Note: this produces a function that takes the
         constructor arguments or array size as parameter *)
      (* Note: for arrays, only one parameter, even if multidimensional *)
      let t = Solidity_type_builder.ast_type_to_type pos ~loc:LMemory env t in
      begin
        match t with
        | TArray (_, None, _) | TBytes (_) | TString (_) ->
            let t = Solidity_type_builder.primitive_type [TUint 256] [t] MPure in
            (t, false)
        | TContract (_lid, cd, false (* super *)) ->
            if cd.contract_def.contract_abstract then
              error pos "Cannot instantiate an abstract contract";
            if is_interface cd.contract_def.contract_kind then
              error pos "Cannot instantiate an interface";
            if is_library cd.contract_def.contract_kind then
              error pos "Instantiating libraries is not supported yet";
            let ctor = Solidity_tenv.find_constructor pos cd in
            let atl = List.map fst ctor.function_params in
            let t = Solidity_type_builder.primitive_type
                      ~kind:KNewContract atl [t] MPayable in
            (t, false)
        | TArray (_, Some (_), _) ->
            error pos "Length has to be placed in parentheses \
                       after the array type for new expression"
        | TStruct (_) | TEnum _ ->
            error pos "Identifier is not a contract"
        | _ ->
            error pos "Contract or array type expected"
      end

  | TypeExpression (t) ->
      TType (Solidity_type_builder.ast_type_to_type pos ~loc:LMemory env t),
      false

  | IdentifierExpression (id_node) ->
      type_ident opt env None id_node

  | FieldExpression (e, id_node) ->
      let t = type_expression opt env e in
      type_ident opt env (Some t) id_node

  | FunctionCallExpression (e, args) ->
      let args = type_function_args opt env args in
      let t = type_expression { opt with call_args = Some (args) } env e in
      begin
        match t, args with

        (* Function call *)
        | TFunction (fd, _fo), args ->
            check_function_application pos "function call"
              fd.function_params args;
            begin
              match fd.function_returns with
              | [t, _id_opt] -> t, fd.function_returns_lvalue
              | tl -> TTuple (List.map (fun (t, _id_opt) -> Some (t)) tl),
                      fd.function_returns_lvalue
            end

        (* Event invocation *)
        | TEvent (ed), args ->
            check_function_application pos "function call"
              ed.event_params args;
            TTuple [], false

        (* Struct constructor *)
        | TType (TStruct (_lid, sd, _loc) as t), args ->
            let t = Solidity_type.change_type_location LMemory t in
            replace_annot e (AType (TType t));
            let fp =
              List.map (fun (fid, ft) ->
                  (Solidity_type.change_type_location LMemory ft, Some (fid))
                ) sd.struct_fields
            in
            check_function_application pos "struct constructor" fp args;
            t, false

        (* Type conversion *)
        | TType (t), AList ([at]) ->
            begin
              let loc = Solidity_type.get_type_location e.pos at in
              let t = Solidity_type.change_type_location loc t in
              replace_annot e (AType (TType t));
              match Solidity_type_conv.explicitly_convertible
                      ~from:at ~to_:t with
              | Some (t) -> t, false
              | None ->
                  error pos "Explicit type conversion not \
                             allowed from \"%s\" to \"%s\""
                    (Solidity_type_printer.string_of_type at)
                    (Solidity_type_printer.string_of_type t)
            end

        | TType (_), AList (_) ->
            error pos "Exactly one argument expected \
                       for explicit type conversion"

        | TType (_), ANamed (_) ->
            error pos "Type conversion cannot allow named arguments"

        | (TRationalConst _ | TLiteralString _ |
           TBool | TInt _ | TUint _ | TFixed _ | TUfixed _ |
           TAddress _ | TFixBytes _ | TBytes _ | TString _ |
           TEnum _ | TStruct _ | TContract _ | TArray _ | TMapping _ |
           TTuple _ | TModifier _ | TArraySlice _ | TMagic _
          ), _ ->
            error pos "Type is not callable"
      end

  | CallOptions (e, opts) ->
      begin
        match type_expression opt env e with
        | TFunction (fd, fo) ->
            let is_payable = is_payable fd.function_mutability in
            let fo = List.fold_left (fun fo (id, e) ->
                let id = strip id in
                let fo, already_set =
                  match Ident.to_string id, fo.kind with
                  | "value", KExtContractFun when not is_payable ->
                      error pos "Cannot set option \"value\" \
                                 on a non-payable function type"
                  | "value", KNewContract when not is_payable ->
                      error pos "Cannot set option \"value\", since the \
                                 constructor of contract is non-payable"
                  | "value", (KExtContractFun | KNewContract) ->
                      expect_expression_type opt env e (TUint 256);
                      { fo with value = true }, fo.value
                  | "gas", KExtContractFun ->
                      expect_expression_type opt env e (TUint 256);
                      { fo with gas = true }, fo.gas
                  | "salt", KNewContract ->
                      expect_expression_type opt env e (TFixBytes 32);
                      { fo with salt = true }, fo.salt
                  | "gas", KNewContract ->
                      error pos "Function call option \"%s\" cannot \
                                 be used with \"new\""
                        (Ident.to_string id);
                  | "salt", KExtContractFun ->
                      error pos "Function call option \"%s\" can \
                                 only be used with \"new\""
                        (Ident.to_string id);
                  | _, KOther ->
                      error pos "Function call options can only be set on \
                                 external function calls or contract creations"
                        (Ident.to_string id);
                  | _ ->
                      error pos "Unknown option \"%s\". Valid options are \
                                 \"salt\", \"value\" and \"gas\""
                        (Ident.to_string id);
                in
                if already_set then
                  error pos "Option \"%s\" has already been set"
                    (Ident.to_string id);
                fo
              ) fo opts
            in
            TFunction (fd, fo), false
        | _ ->
            error pos "Expected callable expression before call options"
      end

  in
  set_annot exp (AType t);
  t, lv

and type_function_args opt env args =
  match args with
  | ExpressionList (el) ->
      AList (List.map (type_expression opt env) el)
  | NameValueList (nel) ->
      let ntl =
        List.fold_left (fun ntl (id, e) ->
            IdentAList.add_uniq (strip id) (type_expression opt env e) ntl
          ) [] nel in
      ANamed (List.rev ntl)

and expect_array_index_type opt env sz_opt exp =
  let pos = exp.pos in
  let t = type_expression opt env exp in
  expect_type pos ~expected:(TUint 256) ~provided:t;
  match t, sz_opt with
  | TRationalConst (q, _), _ when not (ExtQ.is_int q) ->
      error pos "Non-integer array index"
  | TRationalConst (q, _), _ when ExtQ.is_neg q ->
      error pos "Negative array index"
  | TRationalConst (q, _), Some sz ->
      let n = Q.num q in
      if Z.equal (Z.min n sz) sz then
        error pos "Out of bounds array access";
      Some (n)
  | TRationalConst (q, _), None ->
      Some (Q.num q)
  | _ ->
      None

and expect_expression_type opt env exp expected =
  expect_type exp.pos ~expected ~provided:(type_expression opt env exp)

and expect_type pos ~expected ~provided =
  if not (Solidity_type_conv.implicitly_convertible
            ~from:provided ~to_:expected ()) then
    error pos "Type %s is not implicitly convertible to expected type %s"
      (Solidity_type_printer.string_of_type provided)
      (Solidity_type_printer.string_of_type expected)

(* Check statements *)

let rec type_statement opt env s =
  let pos = s.pos in
  match strip s with
  | Block (sl) ->
      let env = Solidity_tenv.new_env ~upper_env:env () in
      List.iter (type_statement opt env) sl

  | Continue ->
      if not opt.in_loop then
        error pos "\"continue\" has to be in a \"for\" or \"while\" loop"

  | Break ->
      if not opt.in_loop then
        error pos "\"break\" has to be in a \"for\" or \"while\" loop"

  | PlaceholderStatement ->
      if not opt.in_modifier then
        error pos "\"_\" has to be in a modifier"

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

  | TryStatement (e, returns, body, catch_clauses) ->

      (* Typecheck the expression and ensure it is an external call *)
      let t = type_expression opt env e in
      let fd =
        match t with
        | TFunction (fd, { kind = (KNewContract | KExtContractFun); _ }) ->
            fd
        | _ ->
            error pos "Try can only be used with external function \
                       calls and contract creation calls"
      in

      (* Check the expression matches the type(s) in the return clause *)
      let returns =
        match returns with
        | [] ->
            []
        | _ ->
            let nb_ret_fun = List.length fd.function_returns in
            let nb_ret_clause = List.length returns in
            if nb_ret_fun <> nb_ret_clause then
              error pos "Function returns %d values, but returns clause \
                         has %d variables" nb_ret_fun nb_ret_clause;
            let returns =
              List.map (fun (t, loc_opt, name_opt) ->
                  Solidity_type_builder.var_type_to_type
                    pos env ~arg:true ~ext:false loc_opt t,
                  Option.map strip name_opt
                ) returns
            in
            List.iter2 (fun (rt, _id_opt1) (t, _id_opt2) ->
                if not (Solidity_type.same_type rt t) then
                  error pos "Invalid type, expected %s but got %s"
                (Solidity_type_printer.string_of_type rt)
                (Solidity_type_printer.string_of_type t)
              ) returns fd.function_returns;
            returns
      in

      (* Typecheck the body in a new environment
         containing the return value names *)
      let env' = Solidity_tenv.new_env ~upper_env:env () in
      List.iter (fun (t, var_opt) ->
          Option.iter (fun var_name ->
              Solidity_tenv.add_variable pos env' ~inherited:false
                var_name (Solidity_type_builder.local_variable_desc t)
            ) var_opt
        ) returns;
      List.iter (type_statement opt env') body;

      (* Typecheck each catch clauses in a new environment
         containing the clause parameters *)
      List.iter (fun (_id_opt, params, body) ->
          let env' = Solidity_tenv.new_env ~upper_env:env () in
          List.iter (fun (t, loc_opt, name_opt) ->
              Option.iter (fun name ->
                  let t = Solidity_type_builder.var_type_to_type
                            pos env ~arg:true ~ext:false loc_opt t in
                  Solidity_tenv.add_variable pos env' ~inherited:false
                    (strip name) (Solidity_type_builder.local_variable_desc t)
                ) name_opt
            ) params;
          List.iter (type_statement opt env') body
        ) catch_clauses

  | Return (e) ->
      let annot =
        match opt.fun_returns with
        | [t] -> t
        | tl -> TTuple (List.map Option.some tl)
      in
      set_annot s (AType annot);
      begin
        match (e, opt.fun_returns, opt.in_modifier) with
        | (None, [], _) ->
            ()
        | (None, _ :: _, _) ->
            error pos "Return arguments required"
        | (Some (_), _, true) ->
            error pos "Return arguments not allowed"
        | (Some (e), [rt], _) ->
            begin
              try expect_expression_type opt env e rt
              with Failure (s) -> error pos "%s in return" s
            end
        | (Some e, rtl, _) ->
            begin
              try expect_expression_type opt env e
                    (TTuple (List.map Option.some rtl))
              with Failure (s) -> error pos "%s in return" s
            end
      end

  | VariableDefinition (def) ->
      let var_decl_list =
        match def with
        | VarInfer (var_name_list, e) ->
            let tl =
              match Solidity_type.unpromote_type
                      (type_expression opt env e) with
              | TTuple (tl) ->
                  (* Note: unless opt.allow_empty is true,
                     tuple components will never be None *)
                  List.map (function
                      | Some (t) -> t
                      | None -> error pos "type_statement: invariant broken"
                    ) tl
              | t -> [t]
            in
            if not (ExtList.same_lengths tl var_name_list) then
              error pos "Left hand side and right hand side \
                         must have the same number of elements"
            else
              List.map2 (fun var_name_opt t ->
                  Option.map (fun var_name ->
                      (Solidity_type_conv.mobile_type pos t, var_name)
                    ) var_name_opt
                ) var_name_list tl

        | VarType (var_decl_list, exp_opt) ->
            let var_decl_list =
              List.map (fun var_decl_opt ->
                  Option.map (fun (t, loc_opt, var_name) ->
                      Solidity_type_builder.var_type_to_type
                        pos env ~arg:false ~ext:false loc_opt t,
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
                          | None -> error pos "type_statement: invariant broken"
                        ) tl
                  | t -> [t]
                in
                if not (ExtList.same_lengths tl var_decl_list) then
                  error pos "Left hand side and right hand side \
                             must have the same number of elements"
                else
                  List.iter2 (fun var_decl_opt t ->
                      Option.iter (fun (t', _var_name) ->
                          if not (Solidity_type_conv.implicitly_convertible
                                    ~from:t ~to_:t' ()) then
                            error pos "Incompatible types in assignment"
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
      set_annot s (AType annot);
      List.iter (function
          | None -> ()
          | Some (t, var_name) ->
              Solidity_tenv.add_variable pos env ~inherited:false
                (strip var_name) (Solidity_type_builder.local_variable_desc t)
        ) var_decl_list

  | Emit (e, args) ->
      let args = type_function_args opt env args in
      let t = type_expression { opt with call_args = Some (args) } env e in
      begin
        match t with
        | TEvent (ed) ->
            check_function_application pos "function call" ed.event_params args
        | _ ->
            error pos "Expression has to be an event invocation"
      end





let constructor_params env lid =
  match Solidity_tenv.find_lident env ~lookup:LInternal (strip lid) with
  | [Contract (cd)] ->
      let fd = Solidity_tenv.find_constructor lid.pos cd in
      (* set_annot lid (AFunction fd); *)
      (* already set *)
      fd.function_params
  | [_] ->
      error lid.pos "Contract expected"
  | _ :: _ :: _ ->
      error lid.pos "Multiple definitions found for contract !"
  | [] ->
      error lid.pos "Identifier not found"

let modifier_or_constructor_params ~constructor env lid =
  match Solidity_tenv.find_lident env ~lookup:LInternal (strip lid) with
  | [Contract (cd)] when constructor ->
      let fd = Solidity_tenv.find_constructor lid.pos cd in
      set_annot lid (AFunction (fd, false));
      fd.function_params, true
  | [Modifier (md)] ->
      set_annot lid (AModifier md);
      md.modifier_params, false
  | [_] when not constructor ->
      error lid.pos "Referenced declaration is not a modifier"
  | [_] ->
      error lid.pos "Referenced declaration is neither \
                     a modifier nor a base contract"
  | _ :: _ :: _ ->
      error lid.pos "Multiple definitions found for contract/modifier !"
  | [] ->
      error lid.pos "Undeclared identifier: %a" LongIdent.printf lid.contents

let type_function_body pos opt contract_env id params returns modifiers block =
  let env = Solidity_tenv.new_env ~upper_env:contract_env () in

  (* Add parameters to env *)
  List.iter (fun (t, var_opt) ->
      Option.iter (fun var_name ->
          Solidity_tenv.add_variable pos env ~inherited:false
            var_name (Solidity_type_builder.local_variable_desc t)
        ) var_opt
    ) params;

  (* Add return values to env *)
  List.iter (fun (t, var_opt) ->
      Option.iter (fun var_name ->
          Solidity_tenv.add_variable pos env ~inherited:false
            var_name (Solidity_type_builder.local_variable_desc t)
        ) var_opt
    ) returns;

  (* Typecheck modifier arguments *)
  let constructor = Ident.equal (Ident.constructor) id in
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
      check_function_application lid.pos kind params (AList args)
    ) modifiers;

  (* Typecheck actual body *)
  List.iter (type_statement opt env) block



(* Check contracts *)


(* Type state variable initializers and function bodies *)
let type_contract_code (c : contract_desc) =
  let opt = { default_options with
              current_hierarchy = List.map fst c.contract_hierarchy;
              current_contract = Some (c) } in

  (* Check base constructor arguments *)
  List.iter (fun (lid, el) ->
      match el with
      | [] -> () (* No args provided: don't check *)
      | _ ->
          let params = constructor_params c.contract_env lid in
          let args = List.map (type_expression opt c.contract_env) el in
          check_function_application lid.pos "constructor call"
            params (AList args)
    ) c.contract_def.contract_inheritance;

  IdentMap.iter (fun id iddl ->
      List.iter (fun (id_desc, inh) ->
          if not inh then
            match id_desc with
            | Variable ({ variable_init = Some (e); _ } as v) ->
                expect_expression_type opt c.contract_env e v.variable_type
            | Variable (_) ->
                () (* Note: variable without initializer or inherited variable*)
            | Function ({ function_def =
                            Some { fun_body = Some (body);
                                   fun_modifiers; _ }; _ } as f) ->
                let pos = Solidity_tenv.node_list_pos body in
                let opt = { opt with
                            in_function = true;
                            fun_returns = List.map fst f.function_returns } in
                type_function_body pos opt c.contract_env id
                  f.function_params f.function_returns
                  fun_modifiers body
            | Function (_) ->
                () (* Note: either no body or a builtin function *)
            | Modifier ({ modifier_def =
                            { mod_body = Some (body); _ }; _ } as m) ->
                let opt = { opt with in_modifier = true } in
                let pos = Solidity_tenv.node_list_pos body in
                type_function_body pos opt c.contract_env id
                  m.modifier_params [] [] body
            | Modifier (_) ->
                () (* Note: no body *)
            | Type (_)
            | Event (_)
            | Contract (_) ->
                ()
            | Field _ | Constr _ ->
                failwith "Invariant broken"
        ) iddl
    ) c.contract_env.ident_map

let type_free_function_code module_env (fd : function_desc) =
  match fd.function_def with
  | Some { fun_body = Some (body); fun_modifiers; _ } ->
      let pos = Solidity_tenv.node_list_pos body in
      let opt = { default_options with
                  current_hierarchy = [];
                  current_contract = None;
                  in_function = true;
                  fun_returns = List.map fst fd.function_returns } in
      type_function_body pos opt module_env
        (LongIdent.last fd.function_abs_name)
        fd.function_params fd.function_returns
        fun_modifiers body
  | _ ->
      ()



(* Type state variables and functions definition (not initializers/bodies) *)
let type_contract_definitions pos c =
  Solidity_tenv.add_parent_definitions pos ~preprocess:false c;
  List.iter (fun part_node ->
      match strip part_node with
      | StateVariableDeclaration (variable_def) ->
          let vd = Solidity_type_builder.state_variable_def_to_desc
                     pos c variable_def in
          begin
            match c.contract_def.contract_kind with
            | Library ->
                if not (is_constant vd.variable_mutability) then
                error pos "Library cannot have non-constant state variables"
            | Interface ->
                error pos "Variables can not be declared in interfaces"
            | _ ->
                ()
          end;
          if is_external vd.variable_visibility then
            error pos "Variable visibility set to external";
          if is_constant vd.variable_mutability && is_none vd.variable_init then
            error pos "Uninitialized \"constant\" variable";
          if not (is_public vd.variable_visibility) &&
             is_some variable_def.var_override then
            error pos "Override can only be used with public state variables";
          Solidity_tenv.add_variable pos c.contract_env
            ~inherited:false (strip variable_def.var_name) vd;
          set_annot part_node (AVariable (vd, false))

      | FunctionDefinition (function_def) ->
          let function_name =
            if Ident.equal (strip function_def.fun_name)
                (strip c.contract_def.contract_name) then
              match function_def.fun_returns with
              | [] -> Ident.constructor
              | _ -> error pos "Non-empty \"returns\" directive for constructor"
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
                  error pos "Constructor can not be defined in libraries";
                if is_fallback then
                  error pos "Libraries cannot have fallback functions";
                if is_receive then
                  error pos "Libraries cannot have receive ether functions";
                if function_def.fun_virtual then
                  error pos "Library functions can not be virtual";
                if has_override then
                  error pos "Library functions can not override";
                if not has_body then
                  error pos "Library functions must be implemented if declared"
            | Interface ->
                if is_construct then
                  error pos "Constructor can not be defined in interfaces";
                if function_def.fun_virtual then
                  error pos "Interface functions are implicitly virtual";
                if has_body then
                  error pos "Functions in interfaces cannot \
                             have an implementation";
                if not is_external then
                  error pos "Functions in interfaces must be declared external"
            | Contract ->
                (* Note: may be abstract even if all functions implemented *)
                if not has_body && not function_def.fun_virtual then
                  error pos "Functions without implementation \
                             must be marked virtual";
                if not has_body && not c.contract_def.contract_abstract then
                  error pos "Contract %s should be marked as \
                             abstract because %s is virtual"
                    (LongIdent.to_string c.contract_abs_name)
                    (Ident.to_string function_name);
          end;
          if is_private && function_def.fun_virtual then
            error pos "\"virtual\" and \"private\" can not be used together";
          if is_construct then
            begin
              if not has_body then
                error pos "Constructor must be implemented if declared";
              if function_def.fun_virtual then
                error pos "Constructors cannot be virtual";
              if is_private || is_external then
                error pos "Constructor cannot have visibility";
              if is_internal && not c.contract_def.contract_abstract then
                error pos "Non-abstract contracts cannot have internal \
                           constructors. Remove the \"internal\" keyword \
                           and make the contract abstract to fix this";
              if not (is_payable function_def.fun_mutability ||
                      is_nonpayable function_def.fun_mutability) then
                error pos "Constructor must be payable or \
                           non-payable, but is \"%s\""
                  (Solidity_printer.string_of_fun_mutability
                     function_def.fun_mutability)
            end;
          if is_fallback then
            begin
              if not is_external then
                error pos "Fallback function must be defined as \"external\"";
              if not (is_payable function_def.fun_mutability ||
                      is_nonpayable function_def.fun_mutability) then
                error pos "Fallback function must be payable or \
                           non-payable, but is \"%s\""
                  (Solidity_printer.string_of_fun_mutability
                     function_def.fun_mutability)
            end;
          if is_receive then
            begin
              if not is_external then
                error pos "Receive ether function must be \
                           defined as \"external\"";
              if is_receive && not (is_payable function_def.fun_mutability) then
                error pos "Receive ether function must be \
                           payable, but is \"%s\""
                  (Solidity_printer.string_of_fun_mutability
                     function_def.fun_mutability)
            end;
          let fd =
            Solidity_type_builder.function_def_to_desc pos c function_def in
          Solidity_tenv.add_function pos c.contract_env
            ~inherited:false function_name fd;
          set_annot part_node (AFunction (fd, false))

      | ModifierDefinition (modifier_def) ->
          let modifier_name = strip modifier_def.mod_name in
          let has_body = is_some modifier_def.mod_body in
          let has_override = is_some modifier_def.mod_override in
          if not has_body && not modifier_def.mod_virtual then
            error pos "Modifiers without implementation \
                       must be marked virtual";
          begin
            match c.contract_def.contract_kind with
            | Library ->
                if modifier_def.mod_virtual then
                  error pos "Modifiers in a library can not be virtual";
                if has_override then
                  error pos "Modifiers in a library can not override";
                if not has_body then
                  error pos
                    "Modifiers in a library must be implemented if declared"
            | Interface ->
                ()
            | Contract ->
                (* Note: may be abstract even if all functions implemented *)
                if not has_body && not c.contract_def.contract_abstract then
                  error pos "Contract %s should be marked as \
                             abstract because %s is virtual"
                    (LongIdent.to_string c.contract_abs_name)
                    (Ident.to_string modifier_name);
          end;
          let md =
            Solidity_type_builder.modifier_def_to_desc pos c modifier_def in
          Solidity_tenv.add_modifier pos c.contract_env
            ~inherited:false modifier_name md;
          set_annot part_node (AModifier md)

      | EventDefinition (event_def) ->
          let ed = Solidity_type_builder.event_def_to_desc pos c event_def in
          Solidity_tenv.add_event pos c.contract_env
            ~inherited:false (strip event_def.event_name) ed;
          set_annot part_node (AEvent ed)

      | UsingForDeclaration (lid_node, type_opt) ->
          let lid = strip lid_node in
          let pos = lid_node.pos in
          begin
            match Solidity_tenv.find_contract c.contract_env lid with
            | None ->
                error pos "Identifier not found or not unique"
            | Some (c) when not (is_library c.contract_def.contract_kind) ->
                error pos "Library name expected"
            | Some (lib) ->
                set_annot lid_node (AContract lib);
                let type_opt =
                  Option.map (fun t ->
                      Solidity_type_builder.ast_type_to_type pos
                        ~loc:(LStorage (true)) c.contract_env t) type_opt
                in
                Solidity_tenv.add_using_for c.contract_env lib type_opt;
          end

      | TypeDefinition (_td) ->
          () (* Note: already handled during preprocessing *)

    ) c.contract_def.contract_parts;

  if not c.contract_def.contract_abstract &&
       not (is_interface c.contract_def.contract_kind) then
      match Solidity_tenv.has_abstract_function c with
      | None -> ()
      | Some (function_name) ->
          error pos "Contract %s should be marked as \
                     abstract because %s is virtual"
            (LongIdent.to_string c.contract_abs_name)
            (Ident.to_string function_name)

let type_free_function_definition pos mlid module_env function_def =
  let function_name = strip function_def.fun_name in
  let function_def =
    { function_def with
      fun_name = { function_def.fun_name with
                   contents = function_name } }
  in
  let has_body = is_some function_def.fun_body in
  let has_override = is_some function_def.fun_override in
  if function_def.fun_virtual then
    error pos "Free functions can not be virtual";
  if has_override then
    error pos "Free functions can not override";
  if not has_body then
    error pos "Free functions must be implemented";
  if is_payable function_def.fun_mutability then
    error pos "Free functions can not be payable";
  let fd =
    Solidity_type_builder.make_function_desc pos module_env
      ~funtype:false ~library:false ~is_method:false
      function_name (LongIdent.append mlid function_name)
      function_def.fun_params function_def.fun_returns false
      function_def.fun_visibility function_def.fun_mutability
      (Some function_def)
  in
  Solidity_tenv.add_function pos module_env ~inherited:false function_name fd;
  fd




let preprocess_type_definition pos env
    (mlid : absolute LongIdent.t) type_def _parents =
  match type_def with
  | StructDefinition (name, fields) ->
      let struct_abs_name = LongIdent.append mlid (strip name) in
      Solidity_tenv.add_struct pos env ~inherited:false (strip name)
        struct_abs_name (strip name, fields)
  | EnumDefinition (name, values) ->
      let enum_abs_name = LongIdent.append mlid (strip name) in
      Solidity_tenv.add_enum pos env ~inherited:false (strip name)
        enum_abs_name (List.map strip values)


let preprocess_contract_definition
    pos ~module_env (mlid : absolute LongIdent.t) contract_def =
  let contract_name = strip contract_def.contract_name in

  begin
    match contract_def.contract_kind with
    | Library ->
        if contract_def.contract_abstract then
          error pos "Libraries can not be abstract";
        begin
          match contract_def.contract_inheritance with
          | _ :: _ -> error pos "Library is not allowed to inherit"
          | _ -> ()
        end;
    | Interface ->
        if contract_def.contract_abstract then
          error pos "Interfaces do not need the \"abstract\" keyword, \
                     they are abstract implicitly";
        List.iter (fun (lid, _el) ->
            match Solidity_tenv.find_contract module_env (strip lid) with
            | None ->
                error lid.pos "Interface %s parent interface %s is undefined"
                  (Ident.to_string contract_name)
                  (LongIdent.to_string (strip lid))
            | Some (c) ->
                set_annot lid (AContract c);
                if not (is_interface c.contract_def.contract_kind) then
                  error lid.pos
                    "Interfaces can only inherit from other interfaces"
          ) contract_def.contract_inheritance
    | Contract ->
        List.iter (fun (lid, _el) ->
            match Solidity_tenv.find_contract module_env (strip lid) with
            | None ->
                error lid.pos "Contract %s parent contract %s is undefined"
                  (Ident.to_string contract_name)
                  (LongIdent.to_string (strip lid))
            | Some (c) ->
                set_annot lid (AContract c);
                if is_library c.contract_def.contract_kind then
                  error lid.pos "Libraries can not be inherited from"
          ) contract_def.contract_inheritance
  end;

  let c = Solidity_tenv.{
    contract_abs_name = LongIdent.append mlid contract_name;
    contract_env = new_env ~upper_env:module_env ();
    contract_def; contract_hierarchy = [];
  }
  in

  (* Perform the linearization of the contract hierarchy *)
  Solidity_c3.linearize pos c;

  (* Add parent contracts contents to derived contract env *)
  Solidity_tenv.add_parent_definitions pos ~preprocess:true c;

  Solidity_tenv.add_contract pos module_env contract_name c;

  (* Iterate over contents to preprocess type definitions only *)
  List.iter (fun part_node ->
      match strip part_node with
      | TypeDefinition (td) ->
          preprocess_type_definition part_node.pos c.contract_env
            (c.contract_abs_name) td c.contract_hierarchy
      | StateVariableDeclaration (_)
      | FunctionDefinition (_)
      | ModifierDefinition (_)
      | EventDefinition (_)
      | UsingForDeclaration (_) ->
          (* Nothing to do here, we just care about contract and types *)
          ()
    ) contract_def.contract_parts;
  c




let rec update_struct_fields ~env =
  IdentMap.iter (fun _id iddl ->
      List.iter (fun (id_desc, _inh) ->
          match id_desc with
          | Contract (c) ->
              update_struct_fields ~env:c.contract_env
          | Type (TDStruct (s)) ->
              let fields =
                List.map (fun (t, id_node) ->
                    strip id_node,
                    (Solidity_type_builder.ast_type_to_type id_node.pos
                       ~loc:(LStorage (false)) s.struct_env t)
                  ) (snd s.struct_def)
              in
              Solidity_tenv.add_struct_fields s fields
          | Type (TDEnum _)
          | Event (_)
          | Variable (_)
          | Function (_)
          | Modifier (_) -> ()
          | Field _ | Constr _ ->
              failwith "Invariant broken"
        ) iddl
    ) env.ident_map





let check_types_acyclicity ~env =
  (* We only consider direct dependencies
     (recursive types are allowed under indirection *)
  let rec add_field_type_deps struct_ field_name field_type ty_deps =
    match field_type with
    | UserDefinedType (lid_node) ->
        let rel_lid = strip lid_node in
        let abs_lid =
          match Solidity_tenv.find_type env rel_lid with
          | Some (TEnum (abs_lid, _))
          | Some (TStruct (abs_lid, _, _))
          | Some (TContract (abs_lid, _, _)) -> abs_lid
          | Some (_) | None -> failwith "Invariant broken"
        in
        AbsLongIdentSet.add abs_lid ty_deps
    | Array (type_, Some (_)) ->
        add_field_type_deps struct_ field_name type_ ty_deps
    | Array (_, None) -> ty_deps
    | Mapping (_) -> ty_deps
    | FunctionType (_) -> ty_deps
    | ElementaryType (_) -> ty_deps
  in
  let rec compute_types_deps deps ~env =
    IdentMap.fold (fun _name idl deps ->
        List.fold_left (fun deps (id_desc, _inh) ->
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
            | Event (_)
            | Variable (_)
            | Function (_)
            | Modifier (_) -> deps
            | Field _ | Constr _ ->
                failwith "Invariant broken"
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
        error dummy_pos "Type definition %s is cyclic" (LongIdent.to_string ty)
        (* todo: provide correct position *)
    ) deps
  in
  ()




(* Add contracts and types to environments *)
let preprocess_module pos mlid module_ =
  let module_env = Solidity_tenv.new_env () in
  let contents = List.rev (List.fold_left (fun contents unit_node ->
      match strip unit_node with
      | Pragma (_) ->
          contents
      | Import (_) ->
          failwith "Imports are not supported yet"
          (* set_annot unit_node (AImport (Ident.root 0)); *)
      | GlobalTypeDefinition (td) ->
          preprocess_type_definition pos module_env mlid td [];
          contents
      | GlobalFunctionDefinition (fd) ->
          (`Function (fd, unit_node) :: contents)
      | ContractDefinition (cd) ->
          let cd = preprocess_contract_definition pos ~module_env mlid cd in
          set_annot unit_node (AContract (cd));
          (`Contract (cd) :: contents)
    ) [] module_)
  in
  update_struct_fields ~env:module_env; (* This also ensures user types exist *)
  check_types_acyclicity ~env:module_env;
  contents, module_env

let type_module_units pos mlid module_ =
  (* Types and contract linearization *)
  let contents, module_env = preprocess_module pos mlid module_ in
  (* State variables, functions, modifiers, events *)
  let contents =
    List.map (function
        | `Contract (cd) ->
            type_contract_definitions pos cd;
            `Contract (cd)
        | `Function (fd, unit_node) ->
            let fd = type_free_function_definition pos mlid module_env fd in
            set_annot unit_node (AFunction (fd, false));
            `Function (fd)
      ) contents
  in
  (* Code *)
  List.iter (function
      | `Contract (cd) -> type_contract_code cd
      | `Function (fd) -> type_free_function_code module_env fd
    ) contents;
  module_env

let type_module m =
  let mlid = LongIdent.of_ident_abs m.module_id in
  let pos = Solidity_tenv.node_list_pos m.module_units in
  ignore (type_module_units pos mlid m.module_units)

let type_program p =
  List.iter (fun m ->
      type_module m
    ) p.program_modules


let () =
  Solidity_primitives.init ()
