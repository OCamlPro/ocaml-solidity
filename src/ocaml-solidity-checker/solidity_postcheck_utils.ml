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
open Solidity_visitor

(** 1 Type definitions *)

type fun_params = (Solidity_checker_TYPES.type_ * Ident.t option) list

type ast_annot = annot * pos

type expr_details = {
  ed_read : ast_annot list IdentMap.t;
  (* The map of variables read in the expression *)

  ed_writ : ast_annot list IdentMap.t;
  (* The map of variables written in the expression *)

  ed_fun_calls : (fun_params * ast_annot) list IdentMap.t;
  (* The functions called in the expression *)

  ed_deep_writ : ast_annot list IdentMap.t;
  (* A submap of ed_writ.
     Registers memory-updated variables (for ex. a[0] = 42). *)

  ed_read_access : pos list;
  (*  Position for each :
      1/ Accessing address(this).balance or <address>.balance.
      2/ Accessing any of the members of block, tx, msg
         (with the exception of msg.sig and msg.data). *)

  ed_writ_state : pos list
  (* Position for each :
     1/ Emitting events.
     2/ Creating other contracts.
     3/ Using selfdestruct.
     4/ Sending Ether via calls.
     5/ Calling any function not marked view or pure.
     6/ Using low-level calls. *)
}

type global_def =
  | GDeclared
  | GDefined of expr_details * expression

type local_def =
  | LDeclared
  | LParam
  | LDefined of expression

type fun_kind =
  | Modifier of modifier_definition
  | Method of (function_definition * string) (* string is selector *)
  | Getter of state_variable_definition

type local_details = {
  loc_def : local_def;
  loc_mem : storage_location option
}

type global_details = {
  gd_def : global_def;
  gd_mutab : var_mutability;

  (* Updated during check *)
  mutable gd_updates : ast_annot list (* todo: set? *)
}

type modifier_details =
  | Constructor of ast_annot
  | Modifier of ast_annot

type function_details = {
  fd_details : expr_details;
  fd_kind : fun_kind;
  fd_purity : fun_mutability;
  fd_defined: bool; (* If false, function declaration only *)
  fd_modifiers: (fun_params * modifier_details) list AbsLongIdentMap.t
}

type fun_identity = {
  fi_name : Ident.t;
  fi_params : fun_params
}

type contract_env = {
  env_funs: (fun_params * function_details) list IdentMap.t;
  env_glob: global_details IdentMap.t;

  env_inherited : (absolute LongIdent.t * contract_env) list;
  env_ctr : contract_definition;
}

type env = contract_env AbsLongIdentMap.t

type annot += ANew of Solidity_checker_TYPES.type_

(** 2. Exceptions raised by the postprocessor *)

exception InvariantBroken of string

exception ImmutableUpdatedOutsideConstructor of Ident.t * pos
exception ImmutableUpdatedTwice of Ident.t * pos * pos
exception ConstantUpdatedTwice of Ident.t * pos * pos
exception ConstantUpdated of Ident.t * pos
exception ReadImmutable of Ident.t * pos
exception UndefinedConstant of Ident.t
exception UndefinedImmutable of Ident.t
exception ConstantCycle of Ident.t list
exception ConstantRequiringComputation of Ident.t
exception CalldataModified of Ident.t * pos
exception UninitializedReadLocal of storage_location * Ident.t * pos
exception VariableAlreadyDefined of Ident.t * pos
exception FunctionAlreadyDefined of Ident.t * pos
exception ImmutableDefinedInInheritingContract of Ident.t * (Ident.t * pos)
exception OverridingNonVirtual of
  Ident.t * (* Fun name *)
  pos * (* Pos of the override *)
  pos (* Pos of the virtual *)

exception UnexpectedOverride of Ident.t * pos
exception ExpectedOverride of Ident.t * pos
exception WrongOverride of Ident.t * pos * string * string

exception NoOverrideMultipleFunDefs of
  IdentSet.t * (* the contracts inherited *)
  Ident.t * (* the inheriting contract *)
  Ident.t (* the function *)

exception PureFunctionReadsGlobal of
    Ident.t * (* The function *)
    Ident.t * (* The global *)
    pos (* The read position *)

exception ForbiddenGlobalWrite of
    Ident.t * (* The function *)
    Ident.t * (* The global *)
    pos (* The read position *)

exception ForbiddenCall of
    Ident.t * fun_mutability * (* Caller function & its purity *)
    Ident.t * fun_mutability * (* Called function & its purity *)
    pos (* Call position *)

exception ForbiddenReadAccess of pos

exception ForbiddenWritState of pos

exception InconsistentVisibility of
    Ident.t * (* Name of the function *)
    string * (* Name of the selector *)
    pos * (* Position of first definition *)
    pos (* Position of second definition *)

exception MissingPlaceholderStatement of
    Ident.t * (* Modifier name with an empty body *)
    pos

exception FileGlobalNotConstant of
    Ident.t * (* Global name *)
    pos

let failOnAnnot = function
  | AType _ -> raise (InvariantBroken "AType")
  | AImport _ -> raise (InvariantBroken "AImport")
  | AContract _ -> raise (InvariantBroken "AContract")
  | AFunction _ -> raise (InvariantBroken "AFunction")
  | AModifier _ -> raise (InvariantBroken "AModifier")
  | AVariable _ -> raise (InvariantBroken "AVariable")
  | APrimitive -> raise (InvariantBroken "APrimitive")
  | ANone -> raise (InvariantBroken "ANone")
  | ANew _ -> raise (InvariantBroken "ANew")
  | _ -> raise (InvariantBroken "Unknown")

(** 3 Miscellaneous *)

let removeListPrefix (=) elt l =
  let rec loop l =
    match l with
    | [] -> []
    | hd :: _ when elt = hd -> l
    | _ :: tl -> loop tl
  in loop l

let list_compare compare l1 l2 =
  let l1 = List.fast_sort compare l1 in
  let l2 = List.fast_sort compare l2 in
  let rec loop l1 l2 = match l1, l2 with
    | [], [] -> 0
    | _, [] -> 1
    | [], _ -> -1
    | hd1 :: tl1, hd2 :: tl2 ->
      let cmp = compare hd1 hd2 in
      if cmp = 0 then
        loop tl1 tl2
      else
        cmp
  in loop l1 l2

let list_equal compare l1 l2 =
  list_compare compare l1 l2 = 0

let the = function
  | None -> raise (InvariantBroken "Deserialized None")
  | Some e -> e

let identmap_add_list_unique (=) key elt map =
  match IdentMap.find_opt key map with
    | None -> IdentMap.add key [elt] map
    | Some l ->
        match List.find_opt (fun (e1, _) -> e1 = fst elt) l with
          | None -> IdentMap.add key (elt :: l) map
          | Some _ -> raise (InvariantBroken "add_unique in map failed")

let longidentmap_add_list key elt map =
  match AbsLongIdentMap.find_opt key map with
  | None -> AbsLongIdentMap.add key [elt] map
  | Some l -> AbsLongIdentMap.add key (elt :: l) map

let equal_opt (=) o1 o2 =
  match o1, o2 with
    | None, None -> true
    | Some e1, Some e2 -> e1 = e2
    | _ -> false

let typeOf elt =
  match elt.annot with
    | AType t -> t
    | _ -> raise (InvariantBroken "Annot is not a type")

let list_assoc_opt (=) key l =
  let rec loop = function
    | [] -> None
    | (k, e) :: tl -> if k = key then Some e else loop tl in
  loop l

let list_mem (=) elt l =
  List.exists
    (fun e -> e = elt)
    l

let identmap_list_partition f map =
  IdentMap.fold
    (fun key bnd (acctrue, accfalse) ->
       let ltrue, lfalse = List.partition (f key) bnd in
       let add key l map =
         match l with
         | [] -> map
         | _ -> IdentMap.add key l map in
         add key ltrue acctrue,
         add key lfalse accfalse)
    map
    (IdentMap.empty, IdentMap.empty)

(** 3.5 Utils on previously defined types *)

let empty_expr_details = {
  ed_read = IdentMap.empty;
  ed_writ = IdentMap.empty;
  ed_fun_calls = IdentMap.empty;
  ed_deep_writ = IdentMap.empty;
  ed_read_access = [];
  ed_writ_state = []
}

let empty_contract_env env_ctr = {
  env_funs = IdentMap.empty;
  env_glob = IdentMap.empty;
  env_inherited = [];
  env_ctr
}

let empty_project_env : env = AbsLongIdentMap.empty

let equalParams ~check_ident (params1 : fun_params) (params2 : fun_params) =
  let rec loop p1 p2 =
    match p1, p2 with
    | [], [] -> true
    | (t1, io1) :: tl1, (t2, io2) :: tl2 ->
      Solidity_type.same_type t1 t2 &&
      (not check_ident || equal_opt Ident.equal io1 io2) &&
      loop tl1 tl2
    | _ -> false
  in loop params1 params2

let equalSortedParams (params1 : fun_params) (params2 : fun_params) =
  let compare (_, io1) (_, io2) =
    match io1, io2 with
      | Some i1, Some i2 -> Ident.compare i1 i2
      | _ -> raise (InvariantBroken "Inconsistent sorted parameters")
  in
  equalParams ~check_ident:true
    (List.fast_sort compare params1)
    (List.fast_sort compare params2)

let addContractEnv
    (contract : absolute LongIdent.t)
    (contract_env : contract_env)
    (env : env) : env =
  match AbsLongIdentMap.find_opt contract env with
  | None ->
      AbsLongIdentMap.add contract contract_env env
  | Some _ -> begin
      raise (InvariantBroken "Cannot save two contracts with the same absolute ident")
  end

let getInInherited get env =
  let rec loop = function
    | [] -> None
    | (ctr, env) :: tl ->
      match get env with
        | None -> loop tl
        | Some res -> Some (ctr, res)
  in loop env.env_inherited

(* Returns a value in the env given the 'get' function by
   searching in the current environment and then on the inherited ones.
   Also returns the eventual name of the contract value has been inherited from. *)
let getInEnv ?(in_inherited=true) get env =
  match get env with
  | None -> begin
    if in_inherited then
      match getInInherited get env with
        | None -> None
        | Some (ctr, elt) -> Some (elt, Some ctr)
    else None
    end
  | Some elt -> Some (elt, None)

let getGlobal ?in_inherited g env =
  let get env = IdentMap.find_opt g env.env_glob in
  getInEnv ?in_inherited get env

let getFun ?in_inherited (fun_identity : fun_identity) (env : contract_env) =
  let get env =
    match IdentMap.find_opt fun_identity.fi_name env.env_funs with
      | None -> None
      | Some l ->
          List.find_opt
            (fun (params, _) -> equalParams ~check_ident:false params fun_identity.fi_params)
            l
  in
  getInEnv ?in_inherited get env

let fromCurrentContract
  (cabsname : absolute LongIdent.t) (id : absolute LongIdent.t)
  : Ident.t list option =
  match LongIdent.to_ident_list id with
    | [] -> assert false
    | _ :: [] -> None
    | at_id :: name :: relative_id ->
      let id_loc = LongIdent.of_ident_list_abs [at_id; name] in
      if LongIdent.equal cabsname id_loc then
        Some relative_id
      else None

let paramsFromExprs (args : expression list) =
  List.map
    (fun (exp : expression) ->
      match exp.annot with
        | AType t -> t, None
        | a -> failOnAnnot a) args

let getFunInEnvs (id : absolute LongIdent.t) (fi_params : fun_params) (envs : env) =
  let contract, fi_name =
    let l = LongIdent.to_ident_list id in
    match List.rev l with
      | [] -> assert false
      | hd :: tl -> LongIdent.of_ident_list_abs (List.rev tl), hd in

  match AbsLongIdentMap.find_opt contract envs with
  | None ->
     let str = LongIdent.to_string contract in
     raise (InvariantBroken ("Contract " ^ str ^ " not found in environment"))
  | Some env ->
    let fi_ident = {fi_name; fi_params} in
    match getFun ~in_inherited:false fi_ident env with
    | None -> None
    | Some ((_params, dets), _(*None*)) ->
      Some (fi_ident, dets)

let getFunAtCall
  ?in_inherited
  (fname : Ident.t)
  (fca : function_call_arguments)
  (env : contract_env) =
  let get env =
    match IdentMap.find_opt fname env.env_funs with
      | None -> None
      | Some l ->
          let finder =
            match fca with
              | ExpressionList l ->
                let l = List.map (fun e -> typeOf e, None) l in
                fun (params, _) ->
                  equalParams ~check_ident:false params l
              | NameValueList l ->
                let l = List.map (fun (i, e) -> typeOf e, Some i.contents) l in
                fun (params, _) ->
                  equalParams ~check_ident:true params l in
          List.find_opt
            finder
            l
  in
  getInEnv ?in_inherited get env

let iterBySelector
  (f : absolute LongIdent.t option -> function_definition -> unit)
  (selector : string)
  (env : contract_env) =
  let rec loop (name : absolute LongIdent.t option) (env : contract_env) =
    let () =
      IdentMap.iter
        (fun _ ->
           List.iter (fun (_, fun_details) ->
               match fun_details.fd_kind with
               | Method (fd, select) when String.equal select selector -> f name fd
               | _ -> ()))
        env.env_funs in
    List.iter
      (fun (i, env) -> loop (Some i) env) env.env_inherited in
  loop None env

let getVisibility (f : fun_kind) =
  match f with
  | Method (m,_) -> m.fun_visibility
  | Modifier _ -> VInternal
  | Getter svd -> svd.var_visibility

let is_constructor (fundef : function_definition) : bool =
  Ident.equal Ident.constructor fundef.fun_name.contents

let addFun
    (fun_name : ident)
    (params : fun_params)
    (fundet : function_details)
    (env : contract_env) =
  let () = (* Checking if there is no public/external function
              with the same selector *)
    match fundet.fd_kind with
    | Method (({fun_visibility = visibility; _} as fd), selector) ->
        if is_constructor fd then () else
        iterBySelector (fun cname fundef ->
            match cname with
            | Some _ when fundef.fun_virtual -> ()
            | _ ->
              match fundef.fun_visibility, visibility with
              | VExternal, VExternal
              | VPublic, VPublic ->
                  raise (
                    InconsistentVisibility (
                      fun_name.contents,
                      selector,
                      fundef.fun_name.pos,
                      fun_name.pos))
              | _ -> ())
            selector
            env
    | Getter _ | Modifier _ -> ()
  in
  {
  env with
  env_funs =
    identmap_add_list_unique
      (equalParams ~check_ident:true)
      fun_name.contents
      (params, fundet)
      env.env_funs
}

let pp_annot_list fmt l = Format.fprintf fmt "Updates: %i" (List.length l)

let pp_ident_map pp fmt m =
  IdentMap.iter
    (fun g k -> Format.fprintf fmt "%a -> %a" Ident.printf g pp k)
    m

let pp_ident_set fmt s =
  IdentSet.iter
    (fun g -> Format.fprintf fmt "%a," Ident.printf g)
    s

let pp_longident_map pp fmt m =
  AbsLongIdentMap.iter
    (fun g k -> Format.fprintf fmt "%a -> %a" LongIdent.printf g pp k)
    m

let pp_expr_details fmt ad =
  Format.fprintf fmt "{read = %a; writ = %a; call = %a; deep_writ = %a; writ_state = %a}"
    (pp_ident_map pp_annot_list) ad.ed_read
    (pp_ident_map pp_annot_list) ad.ed_writ
    (pp_ident_map pp_annot_list) ad.ed_fun_calls
    (pp_ident_map pp_annot_list) ad.ed_deep_writ
    pp_annot_list ad.ed_writ_state

let pp_global_def fmt = function
  | GDeclared -> Format.fprintf fmt "Declared"
  | GDefined _ -> Format.fprintf fmt "Defined"

let pp_mutab fmt = function
  | MImmutable -> Format.fprintf fmt "Immutable"
  | MMutable -> Format.fprintf fmt "Mutable"
  | MConstant -> Format.fprintf fmt "Constant"

let pp_global_details fmt gd =
  Format.fprintf fmt "{def = %a; mutab = %a; annots = %a}"
    pp_global_def gd.gd_def
    pp_mutab gd.gd_mutab
    pp_annot_list gd.gd_updates

let pp_fun_details fmt e  = pp_expr_details fmt e.fd_details

let pp_list pp fmt = List.iter (pp fmt)

let pp_opt pp fmt = function | None -> () | Some e -> pp fmt e

let pp_ident fmt id = Format.fprintf fmt "%a" Ident.printf id

let pp_fun_params =
  pp_list
    (fun fmt (t, i) ->
       Format.fprintf fmt "%a%s" (pp_opt pp_ident) i
         (Solidity_type_printer.string_of_type t))

let pp_pair pp1 pp2 fmt (x,y) = Format.fprintf fmt "(%a, %a)" pp1 x pp2 y

let rec pp_env fmt env =
  Format.fprintf fmt "{funs  = %a; glob = %a; inherited = %a}"
    (pp_ident_map (pp_list @@ pp_pair pp_fun_params pp_fun_details)) env.env_funs
    (pp_ident_map pp_global_details) env.env_glob
    (pp_longident_map pp_env) (AbsLongIdentMap.of_bindings env.env_inherited)

let (++) a elt =
  match IdentMap.find_opt elt.contents a with
  | None -> IdentMap.add elt.contents [elt.annot, elt.pos] a
  | Some elts -> IdentMap.add elt.contents ((elt.annot, elt.pos) :: elts) a

let (--) a elt = IdentMap.remove elt a

let (+++) (x : 'a list IdentMap.t) (y : 'a list IdentMap.t) =
  IdentMap.union (fun _k al1 al2 -> Some (al1 @ al2)) x y

let (---) a set = IdentMap.filter (fun v _ -> not @@ IdentMap.mem v set) a

let unionAssignDetails a1 a2 = {
  ed_read        = a1.ed_read      +++ a2.ed_read;
  ed_writ        = a1.ed_writ      +++ a2.ed_writ;
  ed_fun_calls   = a1.ed_fun_calls +++ a2.ed_fun_calls;
  ed_deep_writ   = a1.ed_deep_writ +++ a2.ed_deep_writ;
  ed_read_access = a1.ed_read_access @ a2.ed_read_access;
  ed_writ_state  = a1.ed_writ_state @ a2.ed_writ_state
}

let removeFromAssignDetails elts a = {
  a with
  ed_read      = a.ed_read      --- elts;
  ed_writ      = a.ed_writ      --- elts;
  ed_fun_calls = a.ed_fun_calls --- elts;
  ed_deep_writ = a.ed_deep_writ --- elts;
}

let getPos al =
  match al with
  | [] -> raise (InvariantBroken "getPos failed")
  | (_,hd) :: _ -> hd

let addWrit w ad = {ad with ed_writ = ad.ed_writ ++ w}
let addRead w ad = {ad with ed_read = ad.ed_read ++ w}
let addFunc (fi : fun_identity) annot ad = {
  ad with
  ed_fun_calls =
    match IdentMap.find_opt fi.fi_name ad.ed_fun_calls with
      | None -> IdentMap.add fi.fi_name [fi.fi_params, annot] ad.ed_fun_calls
      | Some l -> IdentMap.add fi.fi_name ((fi.fi_params, annot) :: l) ad.ed_fun_calls
}

let isVirtual fd env =
  match env.env_ctr.contract_kind with
    | Interface -> true
    | Library -> false
    | Contract ->
    match fd.fd_kind with
      | Modifier md -> md.mod_virtual
      | Method (fd, _) -> fd.fun_virtual
      | Getter _ -> false

let isConstructor fdet =
  match fdet.fd_kind with
    | Method (fd, _) -> is_constructor fd
    | Modifier _
    | Getter _ -> false

let getName fd =
  match fd.fd_kind with
    | Modifier md -> md.mod_name
    | Method (fd, _) -> fd.fun_name
    | Getter svd -> svd.var_name

let sortContractParts parts =
  let rec loop (vars, rest) = function
    | [] -> List.rev @@ rest @ vars
    | ({contents = (Solidity_ast.StateVariableDeclaration _); _} as hd) :: tl ->
      loop ((hd :: vars), rest) tl
    | hd :: tl -> loop (vars, (hd :: rest)) tl
  in loop ([],[]) parts

let getAbsoluteContractName cnode =
  match cnode.annot with
  | AContract cd -> cd.contract_abs_name
  | a -> failOnAnnot a

let minPurity (p1 : fun_mutability) (p2 : fun_mutability) =
  match p1, p2 with
  | MPure, _ | _, MPure -> MPure
  | MView, _ | _, MView -> MView
  | MPayable, _ | _, MPayable -> MPayable
  | MNonPayable, MNonPayable -> p1

let purityToString = function
  | MPure -> "pure"
  | MView -> "view"
  | MPayable -> "payable"
  | MNonPayable -> "non payable"

let purity (fd : function_definition) : fun_mutability =
  fd.fun_mutability

(* Returns true if a function with 'pcaller' purity can call
   a function of purity 'pcalled' *)
let callablePurity (pcaller : fun_mutability) (pcalled : fun_mutability) =
  match pcaller, pcalled with
  | MPure, (MView | MPayable | MNonPayable)
  | MView, (MPayable | MNonPayable) -> false

  | (MPure | MView | MPayable | MNonPayable),
    (MPure | MView | MPayable | MNonPayable) -> true


(** 4. Analysers *)

(* Returns all the variables in an expression, plus the set of variables
   that are accessed (i.e. a[0]). *)
let rec variablesInExpression (e : expression) =
  let visit = object
    inherit Ast.init_ast_visitor
    val mutable vars : ast_annot list IdentMap.t = IdentMap.empty

    val mutable accessed : ast_annot list IdentMap.t = IdentMap.empty
    (* Could be a set, it would me more memory-friendly *)

    method getVars () = vars
    method getAccessed () = accessed

    method! visitExpression e =
      match e.contents with
        | IdentifierExpression i -> begin
            let () =
              match i.annot with
              | AVariable _ ->
                  vars <- vars ++ i
              | _a -> () in
            SkipChildren
          end
        | ArrayAccess (e, eo) ->
            let (v, acc) = variablesInExpression e in
            let (v', acc') =
              match eo with
              | None -> IdentMap.empty, IdentMap.empty
              | Some e -> variablesInExpression e in
            vars <- vars +++ v +++ v';
            accessed <- accessed +++ vars +++ acc +++ acc';
            SkipChildren
        | FieldExpression (e, _) ->
            let (v, acc) = variablesInExpression e in
            vars <- vars +++ v;
            accessed <- accessed +++ vars +++ acc;
            SkipChildren
        | _ -> DoChildren
  end in
  let () = Solidity_visitor.Ast.visitExpression (visit :> Solidity_visitor.Ast.ast_visitor) e in
  (visit#getVars ()), (visit#getAccessed ())

let rec getExpressionDetails e =
  let visit = object
    inherit Ast.init_ast_visitor

    val mutable expr_details : expr_details = empty_expr_details

    method getDetails () = expr_details

    method! visitExpression e =
      match e.contents with
      | IdentifierExpression i -> begin
          let () =
            match e.annot, i.annot with

            | _, AVariable _
            | AFunction _, _
            | AType (TFunction _), _ ->
                expr_details <- addRead {i with annot = e.annot} expr_details
            | _ -> () in
          SkipChildren
        end
        | AssignExpression (le, re)
        | AssignBinaryExpression (le, _, re) ->
            let writ, accessed = variablesInExpression le in
            let re_details = getExpressionDetails re in
            let res =
              unionAssignDetails
                expr_details
                {re_details with
                 ed_writ = re_details.ed_writ +++ writ;
                 ed_deep_writ = re_details.ed_deep_writ +++ accessed} in
            expr_details <- res;
            SkipChildren
        | NewExpression _d ->
            let annot =
              match e.annot with
              | AType t -> ANew t
              | a -> failOnAnnot a in
            let new_node = {
              contents = Ident.of_string "@new";
              annot;
              pos = e.pos
            } in
            expr_details <- {
              expr_details with
              ed_read = expr_details.ed_read ++ new_node
            };
            SkipChildren
        | FunctionCallExpression ({contents = IdentifierExpression i; _}, _)
          when
            Ident.equal i.contents (Ident.of_string "selfdestruct") ->
            expr_details <- {
              expr_details with
              ed_writ_state = e.pos :: expr_details.ed_writ_state
            };
            DoChildren
        | FunctionCallExpression (e, l) -> begin
            let l_dets, rev_params =
              match l with
              | ExpressionList l ->
                  List.fold_left
                    (fun (acc_dets, acc_params) e ->
                      let acc_dets = unionAssignDetails acc_dets (getExpressionDetails e) in
                      let acc_params =
                        match e.annot with
                          | AType t -> (t, None) :: acc_params
                          | _ -> raise (InvariantBroken "Annot of expression should be a type") in
                      acc_dets, acc_params
                    )
                    (empty_expr_details,[])
                    l
              | NameValueList l ->
                  List.fold_left
                    (fun (acc_dets, acc_params) (name, e) ->
                      let acc_dets = unionAssignDetails acc_dets (getExpressionDetails e) in
                      let acc_params =
                        match e.annot with
                          | AType t -> (t, Some name.contents) :: acc_params
                          | _ ->
                              raise (
                                InvariantBroken
                                  "Annot of expression value should be a type"
                              ) in
                      acc_dets, acc_params
                    )
                    (empty_expr_details,[])
                    l in
            let params : fun_params = List.rev rev_params in
            let expression_details = getExpressionDetails e in
            let funs_read_without_call, ed_read =
              identmap_list_partition
                (fun _id -> function
                   | (ANew _
                     | AFunction _
                     | AType (TFunction _)
                     | APrimitive), _ -> true
                  | _ -> false)
                expression_details.ed_read in
            let funs : (fun_params * ast_annot) list IdentMap.t =
              IdentMap.map (List.map (fun a -> params, a)) funs_read_without_call in
            let expression_details = {
              expression_details with
              ed_fun_calls = funs;
              ed_read} in
            let new_dets = unionAssignDetails expression_details l_dets in
            expr_details <- unionAssignDetails expr_details new_dets;
            SkipChildren
          end
        | CallOptions (e, params) -> begin
          let l_dets =
            List.fold_left
              (fun acc_dets (_name, e) ->
                 unionAssignDetails acc_dets (getExpressionDetails e)
                 )
                 empty_expr_details
                 params in
          let expression_details = getExpressionDetails e in
          let new_dets = {l_dets with ed_read = expression_details.ed_read +++ l_dets.ed_read} in
          expr_details <- unionAssignDetails expr_details new_dets;
          SkipChildren
        end
        | FieldExpression (e', field) -> begin
            let () = (* Checking if there is a balance, block, tx or msg access *)
              match e.annot with
              | AType (TAddress _) when
                  (Ident.equal field.contents (Ident.of_string "balance")) ->
                  expr_details <- {
                    expr_details with
                    ed_read_access = e'.pos :: expr_details.ed_read_access
                  }
              | AType (TAddress _) when
                  (Ident.equal field.contents (Ident.of_string "transfer") ||
                   Ident.equal field.contents (Ident.of_string "send")) ->
                  (* Not optimal : maybe there is an unused reference to such a call,
                     which is legal. *)
                  expr_details <- {
                    expr_details with
                    ed_writ_state = e'.pos :: expr_details.ed_writ_state
                  };
              | AType (TMagic (TBlock | TTx)) ->
                  expr_details <- {
                    expr_details with
                    ed_read_access = e'.pos :: expr_details.ed_read_access
                  }
              | AType (TMagic TMsg) when
                  not (Ident.equal field.contents (Ident.of_string "sig") ||
                       Ident.equal field.contents (Ident.of_string "data")) ->
                  expr_details <- {
                    expr_details with
                    ed_read_access = e'.pos :: expr_details.ed_read_access
                  }
              | AType (TFunction _) ->
                 (* Adding the field as 'read' with the annotation of the
                    whole expression visited.
                    Ex : a.pop -> save '@pop' with the annotation of 'a.pop' *)
                 let field = {
                   field with
                   contents = Ident.of_string ("@"^Ident.to_string field.contents) } in
                 expr_details <- {
                    expr_details with
                      ed_read = expr_details.ed_read ++ {field with annot = e.annot}
                  }
              | AType _ -> ()
              | a -> failOnAnnot a in
            DoChildren
          end
        | _ -> DoChildren

  end in
  let () = Solidity_visitor.Ast.visitExpression (visit :> Solidity_visitor.Ast.ast_visitor) e in
  let res = visit#getDetails () in
  res

let isInherited (cname : absolute LongIdent.t) ctrct =
  let rec loop = function
    | [] -> false
    | (c,_) :: tl ->
        let name = getAbsoluteContractName c in
        LongIdent.equal cname name || loop tl in
  loop ctrct.contract_inheritance


let getterOfVariable (svd : state_variable_definition) (pos : pos) : expr_details = {
      empty_expr_details with
      ed_read = IdentMap.singleton svd.var_name.contents [svd.var_name.annot, pos]
  }

(* Returns the contracts defining the virtual equivalent of the function in argument *)
let getOverriddenContracts
  (env : contract_env)
  (fun_name : ident)
  (fun_params : fun_params)
  (is_getter : visibility option) =
  let rec loop
    (acc : visibility IdentMap.t)
    (env : contract_env) =
    let cname = env.env_ctr.contract_name.contents in
    if IdentMap.mem cname acc then acc else
    match getFun
            ~in_inherited:false
            {fi_name = fun_name.contents; fi_params = fun_params}
            env
    with
      | Some (_, Some _) -> assert false (* because in_inherited = false *)
      | Some ((_, fundet), None) -> (* Found locally *)
          let fd_visibility = getVisibility fundet.fd_kind in
          if isVirtual fundet env || isConstructor fundet then
            IdentMap.add cname fd_visibility acc
          else begin
            (* Allowing coexistence of variable & non virtual method with the
               same identifier iff the method is external/private & the
               variable internal/private *)
            match is_getter, fd_visibility with
            | Some (VInternal | VPrivate), (VExternal | VPrivate) ->
                IdentMap.add cname fd_visibility acc
            | None, _ (* Not a getter *)
            | Some (VPublic | VExternal), _ (* Getter is public/external *)
            | _, (VInternal | VPublic ) -> (* Method is not external *)
                raise (
                  OverridingNonVirtual (
                    fun_name.contents,
                    fun_name.pos,
                    (getName fundet).pos))
          end
      | None -> (* Not found in current module, searching above *)
        List.fold_left
          (fun acc (id, env') ->
             if isInherited id env.env_ctr then
               loop acc env'
             else
               acc) acc env.env_inherited in
  loop IdentMap.empty env

(* Returns the details of updated globals by the function/modifier. *)
let getDetails
  (contract_env : contract_env)
  (fd_kind : fun_kind)
  (fun_params : fun_params)
  (pos : pos) : function_details =
  let
    name, overriding, params, visit_function,
    is_constructor, returns, fd_purity, fd_defined,
    is_getter, modifiers_called =
  (* Returns details on the function in argument and a function that
     takes a visitor object, visits the value and returns its function_details *)
    match fd_kind with
      | Method (fd, _) ->
        fd.fun_name,
        fd.fun_override,
        fd.fun_params,
        (fun v ->
          let () =
            Solidity_visitor.Ast.visitFunctionDef
              (v :> Solidity_visitor.Ast.ast_visitor)
              fd in
          v#getDetails ()
        ),
        is_constructor fd,
        fd.fun_returns,
        fd.fun_mutability,
        (match fd.fun_body with | None -> false | Some _ -> true),
        None,
        fd.fun_modifiers
      | Modifier md ->
        md.mod_name,
        md.mod_override,
        md.mod_params,
        (fun v ->
          let () =
            Solidity_visitor.Ast.visitModifierDef
              (v :> Solidity_visitor.Ast.ast_visitor)
              md in
          v#getDetails ()
        ),
        false,
        [],
        MPayable,
        true,
        None,
        []
      | Getter svd ->
        svd.var_name,
        svd.var_override,
        [],
        (fun _ -> getterOfVariable svd pos),
        false,
        [],
        MPayable,
        true,
        (Some svd.var_visibility),
        []
  in
  let () = (* Check : are virtual/override keyworkds used correctly? *)
    if is_constructor then () else

      let overrides =
        getOverriddenContracts contract_env name fun_params is_getter in

    match (* overrides ,*) overriding with
    | None ->
        if IdentMap.is_empty overrides then () (* No override *)
        else begin
          (* Allowing silent definition of non public variables
             when overloading non internal method *)
          match is_getter with
          | None
          | Some (VPublic | VExternal) ->
              raise (ExpectedOverride (name.contents, name.pos))
          | Some _ ->
              IdentMap.iter
                (fun _ -> function
                   | VExternal | VPublic | VPrivate -> ()
                   | VInternal ->
                       raise (ExpectedOverride (name.contents, name.pos)))
                overrides
        end

    | Some [] when IdentMap.cardinal overrides = 1 ->
        (* A single override detected, but none specified *)
        ()
      (* todo: compare with absolute idents from AFunction annotation instead
         of relative idents  *)
    | Some declared_overrides ->
        if IdentMap.is_empty overrides then
          raise (UnexpectedOverride (name.contents, name.pos))
        else
          (* Lists must be equal *)
          let overrides =
            overrides
            |> IdentMap.bindings
            |> List.split
            |> fst
            |> List.map Ident.to_string in
          let declared_overrides =
            List.map (fun c -> LongIdent.to_string c.contents) declared_overrides in
          if list_equal String.compare overrides declared_overrides then
            ()
          else
            raise
              (WrongOverride
                 (name.contents,
                  name.pos,
                  String.concat " & " overrides,
                  String.concat " & " declared_overrides))
  in
  (* Defining the visitor *)
  let visit =
    let local_vars =
      List.fold_left
        (fun acc (_, loc_mem, i) ->
           match i with
           | None -> acc
           | Some i -> IdentMap.add i.contents {loc_mem; loc_def = LParam} acc)
        IdentMap.empty
        (params @ returns) in
    object
      inherit Ast.init_ast_visitor

      val mutable local_vars : local_details IdentMap.t = local_vars
      val mutable expr_details : expr_details = empty_expr_details

      method getDetails () = expr_details

      method! visitStatement s =
        match s.contents with
        | VariableDefinition vd ->
          let () =
            match vd with
              | VarType  (l, eo) ->
                (* We need to add defined variabled to the locally_defined_variables set *)
                  let vset =
                    List.fold_left
                      (fun acc ->
                         function
                           | None -> acc
                           | Some (_,loc_mem,v) ->
                               match eo with
                               | None ->
                                   IdentMap.add
                                     v.contents
                                     {loc_mem; loc_def = LDeclared}
                                     acc
                                 | Some e ->
                                   IdentMap.add
                                     v.contents
                                     {loc_mem; loc_def = LDefined e}
                                     acc)
                      IdentMap.empty
                      l
                  in
                  local_vars <-
                    IdentMap.union
                      (fun _v _ _ -> raise (InvariantBroken "Maps should be distinct (1)"))
                      local_vars
                      vset
              | VarInfer (l, e) ->
                  let vmap =
                    List.fold_left
                      (fun acc ->
                         function
                           | None -> acc
                           | Some v ->
                               IdentMap.add
                                 v.contents
                                 {loc_mem = None; loc_def = LDefined e}
                                 acc)
                      IdentMap.empty
                      l
                  in
                  local_vars <-
                    IdentMap.union
                      (fun _v _ _ ->  raise (InvariantBroken "Maps should be distinct (2)"))
                      local_vars
                      vmap in
          DoChildren
        | Emit _ ->
            expr_details <- {
              expr_details with
              ed_writ_state = s.pos :: expr_details.ed_writ_state
            };
            DoChildren
      | _ -> DoChildren

    method! visitExpression e =
      let expr_det = getExpressionDetails e in
      let () = (* Checking that local vars are not accessed without being initialized *)
        IdentMap.iter
          (fun read _annots ->
             match IdentMap.find_opt read local_vars with
             | None
             | Some {loc_def = (LDefined _ | LParam); _}
             | Some {loc_mem = None; _}
             | Some {loc_def = LDeclared; loc_mem = Some Memory} -> ()
             | Some {loc_def = LDeclared; loc_mem = Some loc} ->
               raise (UninitializedReadLocal (loc, read, e.pos)))
          expr_det.ed_read in
      let () =
        IdentMap.iter
          (fun deep_writ _annots ->
             match IdentMap.find_opt deep_writ local_vars with
               | Some {loc_mem = Some Calldata; _} ->
                   raise (CalldataModified (deep_writ, e.pos))
               | _ -> ())
        expr_det.ed_deep_writ in
      let ad = removeFromAssignDetails local_vars expr_det in
      expr_details <- unionAssignDetails ad expr_details;
      SkipChildren
  end in
  let fd_details = visit_function visit in
  let fd_modifiers =
    List.fold_left
      (fun fd_mods (i, args) ->
         let params =
           match args with
           | None -> []
           | Some l -> paramsFromExprs l in
         let ast_annot = i.annot, i.pos in
         match i.annot with
         | AModifier md ->
             longidentmap_add_list md.modifier_abs_name (params, Modifier ast_annot) fd_mods
         | AFunction (fd, _from_using_for) ->
             longidentmap_add_list fd.function_abs_name (params, Constructor ast_annot) fd_mods
          | a -> failOnAnnot a
      )
      AbsLongIdentMap.empty
      modifiers_called in
  {fd_details; fd_kind; fd_purity; fd_defined; fd_modifiers}

(*
type modifier_details =
  | Constructor of ast_annot
  | Modifier of ast_annot * fun_mutability *)
let inheritFrom
  (id : absolute LongIdent.t)
  (env : contract_env)
  (envs : env)
  : contract_env =
  let inherit_env =
    match AbsLongIdentMap.find_opt id envs with
    | None -> raise (InvariantBroken ("Cannot find inherited contract " ^ LongIdent.to_string id))
    | Some e -> e in
  {env with env_inherited = env.env_inherited @ [id, inherit_env]}

