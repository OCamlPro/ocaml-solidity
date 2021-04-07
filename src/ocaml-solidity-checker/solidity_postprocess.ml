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
open Solidity_postcheck_utils
open Solidity_exceptions

(* Checks : Are there immutable variables defined in a interiting contract ?
            Are there immutable variables updated outside 'constructor' ? *)
let checkDetails
    (env : contract_env)
    (_fun_name : Ident.t)
    (fundet : function_details)
  : unit =
  let () = (* Checking that written variables were not immutable *)
    IdentMap.iter
      (fun writ annots -> try
          let gd, inherited = the (getGlobal writ env) in
          match gd.gd_mutab with
          | MImmutable -> begin
              if not (Solidity_postcheck_utils.isConstructor fundet) then
                raise (ImmutableUpdatedOutsideConstructor (writ, getPos annots))
              else match inherited with
                | Some ctrct ->
                    raise
                      (ImmutableDefinedInInheritingContract
                         (Ident.of_string (LongIdent.to_string ctrct),
                          (writ, getPos annots)))
                | None -> ()
            end
          | _ -> ()
        with Not_found -> () (* The global is not yet declared, we will check that after *)
      )
      fundet.fd_details.ed_writ in
  ()


let checkNoRead (env : contract_env) (fname : Ident.t) (fdetails : function_details) =
  let () =
    match fdetails.fd_details.ed_read_access with
    | [] -> ()
    | pos :: _ -> raise (ForbiddenReadAccess pos) in
  let () =
    match IdentMap.find_first_opt (fun _ -> true) fdetails.fd_details.ed_read with
    | None -> ()
    | Some (g, ((annot, pos) :: _)) ->
        begin
          match annot with
          (* New is a valid key word *)
          | ANew _ -> ()
          (* Function are allowed if they are not called *)
          | AFunction _
          | AType (TFunction _) -> ()
          | _ -> (* Pure function can read globals iff these globals are not mutable *)
              match IdentMap.find_opt g env.env_glob with
              | None -> (* This global is not registered ; must be an imported constant *)
                  ()
              | Some {gd_mutab = MMutable; _} ->
                  raise (PureFunctionReadsGlobal (fname, g, pos))
              | Some _ -> ()
        end
    | _ -> invariant_broken "Empty binding in ed_read" in
  ()


let checkNoWrite (fname : Ident.t) (fdetails : function_details) =
  let () =
    match fdetails.fd_details.ed_writ_state with
    | [] -> ()
    | pos :: _ -> raise (ForbiddenWritState pos) in
  let () =
    match IdentMap.find_first_opt (fun _ -> true) fdetails.fd_details.ed_writ with
    | None -> ()
    | Some (g, ((_, pos) :: _)) -> raise (ForbiddenGlobalWrite (fname, g, pos))
    | _ -> invariant_broken "Empty binding in ed_write" in
  ()

let stateVariableAnalyser ?current_position env svd annot =
  let () = (* Checking the variable has not been defined before. *)
    match getGlobal svd.var_name.contents env with
    | None -> ()
    | Some _ ->
        raise (VariableAlreadyDefined (svd.var_name.contents, svd.var_name.pos)) in
  let gd_def, gd_updates =
    match svd.var_init, svd.var_mutability with
    | None, MConstant -> raise (UndefinedConstant svd.var_name.contents)
    | None, _ -> GDeclared, []
    | Some e, _ ->
        let ed = getExpressionDetails e in
        GDefined (ed, e), [e.annot, e.pos] in
  let new_env =
    {env with
     env_glob =
       IdentMap.add
         svd.var_name.contents
         {gd_def; gd_mutab = svd.var_mutability; gd_updates}
         env.env_glob} in
  let type_ =
    match annot with
    | AType t -> t
    | AVariable (v, _is_getter) -> v.variable_type
    | a -> failOnAnnot a in
  let new_env =
    match svd.var_visibility with
    | VPublic ->
        let params, _ =
          Solidity_type_builder.variable_type_to_function_type
            svd.var_name.pos type_ in
        let getter_details =
          getDetails new_env (Getter svd) params (the current_position) in
        let () =
          checkDetails new_env svd.var_name.contents getter_details in
        addFun
          svd.var_name
          params
          getter_details
          new_env
    | VPrivate | VInternal | VExternal -> new_env in
  new_env


(* Computes the environment for a given contract *)
let analyseContract
  (env : contract_env)
  (contract : contract_definition) =
  let visit = object
    inherit Ast.init_ast_visitor
    val mutable env = env

    method getEnv () = env

    method! visitFunctionDef fd =
      let fd =
        match contract.contract_kind with
        | Contract | Library -> fd
        | Interface -> {fd with fun_virtual = true} in
      let params, selector = match current_annot with
        | Some (AFunction ({function_params; function_selector; _}, _)) ->
            let function_selector =
              Option.value ~default:"" function_selector in
            function_params, function_selector
        | _ -> invariant_broken "Function should have function annot" in
      let fundet =
        getDetails env (Method (fd, selector)) params (the current_position) in
      let () = checkDetails env fd.fun_name.contents fundet in
      env <-
        addFun
          fd.fun_name
          params
          fundet
          env;
      SkipChildren

    method! visitModifierDef md =
      let () =
        let there_is_a_placeholder =
          match md.mod_body with
            | None -> true (* Should not fail here *)
            | Some l ->
          List.exists
            (fun {contents; _} ->
               match contents with
                 | PlaceholderStatement -> true
                 | _ -> false) l in
        if not there_is_a_placeholder then
          raise (MissingPlaceholderStatement (md.mod_name.contents, md.mod_name.pos)) in
      let md =
        match contract.contract_kind with
        | Contract | Library -> md
        | Interface -> {md with mod_virtual = true} in
      let params = match current_annot with
        | Some (AModifier {modifier_params; _}) -> modifier_params
        | _ -> invariant_broken "Modifier should have modifier annot" in
      let fundet = getDetails env (Modifier md) params (the current_position) in
      let () = checkDetails env md.mod_name.contents fundet in
      let fd_purity = (* Inferring modifier real mutability *)
        let no_write () = try
            ignore @@ checkNoWrite md.mod_name.contents fundet; true
          with
          | ForbiddenWritState _
          | ForbiddenGlobalWrite _ -> false in
        let no_read () = try
            ignore @@ checkNoRead env md.mod_name.contents fundet; true
          with
          | ForbiddenReadAccess _
          | PureFunctionReadsGlobal _ -> false in
        if not (no_write ()) then
          MPayable
        else if not (no_read ()) then
          MView
        else
          MPure in
      let fundet = {fundet with fd_purity = fd_purity} in
      env <-
        addFun
          md.mod_name
          params
          fundet
          env;
      SkipChildren

    method! visitStateVariableDef svd =
      let annot = the current_annot in
      let new_env = stateVariableAnalyser ?current_position env svd annot in
      env <- new_env;
      SkipChildren
  end in
  let () = Ast.visitContractDef (visit :> Ast.ast_visitor) contract in
  visit#getEnv ()

let hasConstructor (env : contract_env) =
  match IdentMap.find_opt Ident.constructor env.env_funs with
    | None -> None
    | Some [] -> invariant_broken "There should be at least 1 annot"
    | Some ((fi_params, _) :: _) ->
      Some {fi_params; fi_name = Ident.constructor }

(* Checks that a function does not writes an immutable/constant *)
let checkWrittenVar
    ~(in_constructor : bool)
    ~(env : contract_env)
    (written : Ident.t)
    (a_list : ast_annot list) =
  let gd, _ = the (getGlobal written env) in
  match gd.gd_mutab with
  | MImmutable -> begin
      if not in_constructor then
        raise (ImmutableUpdatedOutsideConstructor (written, (getPos a_list)))
      else (* Checking it is written once *)
        match gd.gd_def with
        | GDefined (_, e) -> raise (ImmutableUpdatedTwice (written, e.pos, (getPos a_list)))
        | GDeclared ->
            begin
              match gd.gd_updates, a_list with
              | _, [] -> invariant_broken "There should be at least 1 annot"
              | [], [annot] -> gd.gd_updates <- [annot]
              | annot1 :: _, annot2 :: _
              | [], annot1 :: annot2 :: _ ->
                  raise (ImmutableUpdatedTwice (written, snd annot1, snd annot2))
            end
    end
  | MConstant ->
      raise (ConstantUpdated (written, (getPos a_list)))
  | MMutable -> ()


(* To call once on each function *)
let checkFun (env : contract_env) (f : Ident.t) ((_, fdet) : fun_params * function_details) =
  let in_constructor = Ident.equal Ident.constructor f in
  let () = (* Checking that written vars are not immutable or constants *)
    IdentMap.iter
      (checkWrittenVar ~in_constructor ~env)
      fdet.fd_details.ed_writ in
  ()


let checkFuns (env : contract_env) =
  IdentMap.iter (fun f -> List.iter (checkFun env f)) env.env_funs

(* Checks that the variable is read iff it is not immutable *)
let checkUnreadVar
    ~(env : contract_env)
    (read : Ident.t)
    (a_list : ast_annot list) =
  let gd, _ =
    try the @@ getGlobal read env
    with InvariantBroken s ->
      invariant_broken (
        Format.sprintf "Cannot find %s: %s" (Ident.to_string read) s
      ) in
  match gd.gd_mutab with
  | MImmutable -> raise (ReadImmutable (read, getPos a_list))
  | _ -> ()

(* Checks that a function does not read an immutable variable in its body
   and through calls. *)
let checkFlowFun =
  let exception AlreadyExists in
  let addInCheckedFuns (checked_funs : fun_params list IdentMap.t) (f : fun_identity) =
    match IdentMap.find_opt f.fi_name checked_funs with
      | None -> IdentMap.add f.fi_name [f.fi_params] checked_funs
      | Some l ->
        if List.exists (equalParams ~check_ident:true f.fi_params) l then
          raise AlreadyExists
        else
          IdentMap.add f.fi_name (f.fi_params :: l) checked_funs in
  fun ~(env : contract_env) (f : fun_identity) ->
    let rec loop (checked_funs : fun_params list IdentMap.t) (f : fun_identity) : fun_params list IdentMap.t  =
      try
        let checked_funs = addInCheckedFuns checked_funs f in
        (* This may fail with AlreadyExists, but is eventually catched *)
        match getFun f env with
        | None -> (* A read function that is not in the environment is a primitive *)
            checked_funs
        | Some ((_, fun_details), _) ->
            (* Should never fail if not a primitive, hence not catched *)
            IdentMap.iter (checkUnreadVar ~env) fun_details.fd_details.ed_read;

            IdentMap.fold (fun f l (checked : fun_params list IdentMap.t)->
                List.fold_left (fun (checked : fun_params list IdentMap.t) (fi_params, _) ->
                    loop checked {fi_params; fi_name = f})
                  checked
                  l
              )
              fun_details.fd_details.ed_fun_calls
              checked_funs
      with AlreadyExists -> checked_funs in
    loop IdentMap.empty f

let checkConstructionFlow (env : contract_env) =
  match hasConstructor env with
    | None -> ()
    | Some cstr ->
      let _checked = checkFlowFun ~env cstr in
      ()

let checkDefExpression ~(env : contract_env) (ad : expr_details) =
  let () = IdentMap.iter (checkUnreadVar ~env) ad.ed_read in
  IdentMap.iter (fun fi_name l ->
    List.iter
      (fun (fi_params, _a) ->
         ignore @@ checkFlowFun ~env {fi_params; fi_name}
      )
      l
    )
    ad.ed_fun_calls

let checkGlobals (env : contract_env) =
    IdentMap.iter
      (fun glob gd ->
         match gd.gd_def, gd.gd_mutab, gd.gd_updates with
         | GDeclared, MConstant, _ -> raise (UndefinedConstant glob)
         | GDefined _, MConstant, [] ->
             invariant_broken "There should be at least 1 update if constant is defined"
         | GDefined (ad, _e), MConstant, [_a'] -> (* assert e.annot = a'; *)
             ignore @@ checkDefExpression ~env ad
         | GDefined _, MConstant, a1 :: a2 :: _ ->
             raise (ConstantUpdatedTwice (glob, snd a1, snd a2))

         | GDeclared, MImmutable, [] -> raise (UndefinedImmutable glob)
         | GDeclared, MImmutable, [_] -> ()
         | GDefined (ad, _e), MImmutable, [_a'] -> (* assert e.annot = a'; *)
             ignore @@ checkDefExpression ~env ad
         | GDefined _, MImmutable, [] ->
             invariant_broken "There should be at least 1 update if immutable is defined"
         | GDeclared, MImmutable, (a1 :: a2 :: _)
         | GDefined _, MImmutable, (a1 :: a2 :: _) ->
             raise (ImmutableUpdatedTwice (glob, snd a1, snd a2))
         | GDeclared, MMutable, _ -> ()
         | GDefined (ad, _e), MMutable, _ -> ignore @@ checkDefExpression ~env ad)
      env.env_glob

let getConstants (env : contract_env) =
  IdentMap.filter
    (fun _g gd ->
       match gd.gd_mutab with
       | MConstant -> true
       | _ -> false)
    env.env_glob

let validConstantCalls env (calls : (fun_params * ast_annot) list IdentMap.t)  =
  let allowed_calls =
    IdentSet.of_list [
      Ident.of_string "keccak256";
      Ident.of_string "ecrecover";
      Ident.of_string "sha256";
      Ident.of_string "ripdemd160";
      Ident.of_string "addmod";
      Ident.of_string "mulmod";
      Ident.of_string "new"
    ] in

  let isAllowedCall (annot : annot) : bool =
      match annot with
      | AType (TMagic (TMetaType _)) -> true
      | _ -> false in

  IdentMap.for_all
    (fun call l ->
       let is_allowed_primitive = IdentSet.mem call allowed_calls in
       List.for_all
         (fun (args, (annot, _)) ->
            (is_allowed_primitive || isAllowedCall annot) && begin
              match getFun {fi_name = call; fi_params = args} env with
              | None -> true
              | Some _ -> false
            end
         )
         l
    )
    calls

let checkConstantFlow (env : contract_env) =
  let constants = getConstants env in
  let rec loop
      (studied_constants : IdentSet.t) (* Variables studied from the beginning *)
      (challenged_constants : Ident.t list) (* Variables studied in this loop search *)
      (cst : Ident.t) =
    if List.mem cst challenged_constants then
      raise (ConstantCycle (removeListPrefix Ident.equal cst challenged_constants))
    else if IdentSet.mem cst studied_constants then
      studied_constants
    else begin
      let studied_constants = IdentSet.add cst studied_constants in
      let challenged_constants = cst :: challenged_constants in
      let gd = the @@ IdentMap.find_opt cst constants in
        match gd.gd_def with
        | GDeclared -> raise (UndefinedConstant cst)
        | GDefined (ad, _) ->
            let () = (* che *)
              if not (validConstantCalls env ad.ed_fun_calls) then
                raise (ConstantRequiringComputation cst) in
            IdentMap.fold
              (fun read _ studied ->
                 if not (IdentMap.mem read constants) then
                   raise (ConstantRequiringComputation cst)
                 else
                   loop studied challenged_constants read)
              ad.ed_read
              studied_constants
    end
  in
  let _studied =
    IdentMap.fold
      (fun c _ studied -> loop studied [] c)
      constants
      IdentSet.empty in
  (* assert _studied = constants; *)
  ()

(* Returns the declared functions in inherited contracts. *)
let getFunDeclarations =
  let union
    (l1 : (fun_params * IdentSet.t) list)
    (l2 : (fun_params * IdentSet.t) list) : (fun_params * IdentSet.t) list =
      let l2' = (* l2 + l1 common elements *)
        List.fold_left
          (fun acc (p2, s2) ->
             match list_assoc_opt (equalParams ~check_ident:true) p2 l1 with
             | None -> (p2, s2) :: acc
             | Some s1 -> (p2, IdentSet.union s1 s2) :: acc)
          []
          l2 in
      let l1' = (* l1 - l2 common elements *)
      List.filter
         (fun (p, _) ->
           not @@ List.exists (fun (p',_) -> equalParams ~check_ident:true p p') l2) l1 in
      l1' @ l2'
  in
  let add_if_not_mem
    (cname : Ident.t)
    (f : fun_identity)
    (map : (fun_params * IdentSet.t) list IdentMap.t)
    : (fun_params * IdentSet.t) list IdentMap.t =
    match IdentMap.find_opt f.fi_name map with
      | None -> IdentMap.add f.fi_name [f.fi_params, IdentSet.singleton cname] map
      | Some l ->
        let exists =
          List.exists
            (fun (fparams, _) -> equalParams ~check_ident:true fparams f.fi_params)
            l in
        if exists then
          map
        else IdentMap.add f.fi_name ((f.fi_params, IdentSet.singleton cname) :: l) map in

  fun (env : contract_env) : (fun_params * IdentSet.t) list IdentMap.t ->
  let rec loop
    (acc : (fun_params * IdentSet.t) list IdentMap.t)
    contract_env : (fun_params * IdentSet.t) list IdentMap.t =
    let deps = contract_env.env_ctr.contract_inheritance in

    let branches =
      List.map
        (fun (c, _) ->
          let cname = getAbsoluteContractName c in
          let cname_env = the (List.assoc_opt cname contract_env.env_inherited) in
          let new_funs =
            IdentMap.fold
              (fun f l acc ->
                 List.fold_left
                   (fun acc (fi_params, fd) ->
                      if fd.fd_defined then
                        add_if_not_mem
                          (Ident.of_string (LongIdent.to_string cname))
                          {fi_name = f; fi_params}
                          acc
                      else acc
                   )
                acc l)
                cname_env.env_funs
                acc
          in
          loop new_funs cname_env
        )
    deps in
    List.fold_left
      (IdentMap.union (fun _f s1 s2 -> Some (union s1 s2)))
      acc
      branches in
  loop IdentMap.empty env

let checkMultipleInheritedFuns (env : contract_env) =
  let fun_decl = getFunDeclarations env in
  IdentMap.iter
    (fun f l ->
       if not (Ident.equal Ident.constructor f) then
         List.iter
           (fun (params, set) ->
              if IdentSet.cardinal set >= 2 then
                match getFun ~in_inherited:false {fi_name = f; fi_params = params} env with
                | None ->
                    (* Inheriting 2 function without overriding them: error *)
                    raise (NoOverrideMultipleFunDefs (set, env.env_ctr.contract_name.contents, f))
                | Some _ -> ()
           ) l
    ) fun_decl

type funs_tested = (fun_params * fun_mutability) list IdentMap.t

let isTested (fi : fun_identity) (ft : funs_tested) : fun_mutability option =
  match IdentMap.find_opt fi.fi_name ft with
  | None -> None
  | Some l -> list_assoc_opt (equalParams ~check_ident:true) fi.fi_params l

let addTested
    (fi : fun_identity) (p : fun_mutability) (ft : funs_tested) : funs_tested =
  match IdentMap.find_opt fi.fi_name ft with
  | None -> IdentMap.add fi.fi_name [fi.fi_params, p] ft
  | Some l -> IdentMap.add fi.fi_name ((fi.fi_params, p) :: l) ft

let checkPurity =
  (* Checks the purity of function calls *)
  let rec function_calls
      (funs_tested : funs_tested)
      (max_purity : fun_mutability)
      (fident : fun_identity)
      (fdetails : function_details)
      (env : contract_env) : funs_tested =
    let () =
      match fdetails.fd_purity with
      | MPure -> begin
          checkNoRead env fident.fi_name fdetails;
          checkNoWrite fident.fi_name fdetails
        end
      | MView ->
          checkNoWrite fident.fi_name fdetails
      | _ -> () in
    (* Check passed, now checking called functions *)
    let funs_tested = addTested fident fdetails.fd_purity funs_tested in
    IdentMap.fold
      (fun fi_name l funs_tested ->
         List.fold_left (fun funs_tested (fi_params, (annot, pos)) ->
             let studied = {fi_name; fi_params} in
             match isTested studied funs_tested with
             | Some purity -> (* Already tested, checking valid purity *)
                 if callablePurity max_purity purity then
                   funs_tested
                 else
                   raise (
                     ForbiddenCall (
                       fident.fi_name, max_purity, fi_name, purity, pos
                     )
                   )
             | None -> begin
                 match getFun ~in_inherited:true studied env with
                 | None -> begin
                   (* It should be a primitive *)
                     match annot with
                       | AType
                           (TFunction ({function_mutability; _},_))
                       | AFunction ({function_mutability; _}, _) ->
                           if callablePurity max_purity function_mutability then
                             funs_tested
                           else
                             raise (
                               ForbiddenCall (
                                 fident.fi_name, max_purity,
                                 fi_name, function_mutability, pos))
                       | ANew _ ->
                           if callablePurity max_purity MPayable then
                             funs_tested
                           else
                             raise (
                               ForbiddenCall (
                                 fident.fi_name, max_purity,
                                 fi_name, MPayable, pos))
                       | _a ->
                           invariant_broken (
                             (Ident.to_string fi_name)
                             ^ " was expected to be a function")
                   end
                 | Some ((_, studied_details), _) ->
                     if callablePurity max_purity studied_details.fd_purity then
                       function_calls
                         funs_tested
                         (minPurity max_purity studied_details.fd_purity)
                         fident
                         studied_details
                         env
                     else
                       raise
                         (ForbiddenCall
                            (fident.fi_name,
                             max_purity,
                             fi_name,
                             studied_details.fd_purity,
                             pos))
               end
           )
           funs_tested
           l)
      fdetails.fd_details.ed_fun_calls
      funs_tested in

  (* Checks the purity of modifiers *)
  let modifiers
    (whole_envs : env)
    (env : contract_env)
    (max_purity : fun_mutability)
    (mod_name : absolute LongIdent.t)
    ((mod_params, _mod_details) : fun_params * modifier_details) =
    match getFunInEnvs mod_name mod_params whole_envs with
    | None ->
        invariant_broken (
          Format.sprintf
            "Cannot find modifier %s"
            (LongIdent.to_string mod_name)
        )
    | Some (fident, fdetails) -> begin
        match max_purity with
        | MPure -> begin
            checkNoRead env fident.fi_name fdetails;
            checkNoWrite fident.fi_name fdetails
          end
        | MView ->
            checkNoWrite fident.fi_name fdetails
        | _ -> ()
      end
  in
  fun (envs : env) (env : contract_env) ->
  let () =
    ignore @@
    IdentMap.fold
      (fun fi_name l funs_tested ->
         List.fold_left
           (fun funs_tested (fi_params, fdets) ->
              function_calls
                funs_tested
                fdets.fd_purity
                {fi_name; fi_params}
                fdets
                env
           )
           funs_tested
           l)
      env.env_funs
      IdentMap.empty in
  let () =
    IdentMap.iter (
      (fun _ ->
         List.iter
           (fun (_, {fd_modifiers; fd_purity; _}) ->
              AbsLongIdentMap.iter
                (fun mod_name ->
                   List.iter
                     (modifiers envs env fd_purity mod_name)
                )
                fd_modifiers
           )
      )
    )
      env.env_funs in
  ()

let assertGlobalIsConstant svd =
  match svd.var_mutability with
    | MConstant -> ()
    | MMutable | MImmutable ->
        raise (FileGlobalNotConstant (svd.var_name.contents, svd.var_name.pos))

let checkEnv _name (envs : env) (env : contract_env) =
  let () = checkFuns env in
  let () = checkConstructionFlow env in
  let () = checkGlobals env in
  let () = checkConstantFlow env in
  let () = checkMultipleInheritedFuns env in
  let () = checkPurity envs env in
  ()

let checkModule (env : env) (m : module_) : env =
  let _, env = List.fold_left
    (fun
      (* 'globals' is a function building an empty environment with the global
         definitions ;
         'env' is the whole environment to which we add the module *)
      ((globals, env) : (contract_definition -> contract_env) * env)

      {contents; annot; pos} ->
      match contents, annot with
      | ContractDefinition contract, AContract cd ->
          let name = cd.contract_abs_name in
          let contract = {
              contract with
              contract_parts = sortContractParts contract.contract_parts
            } in
          let initial_env : contract_env =
            List.fold_left
              (fun (acc : contract_env) (id, _) ->
                if LongIdent.equal id name then acc
                else
                  inheritFrom id acc env)
              (globals contract)
              cd.contract_hierarchy in
          let ctrct_env = analyseContract initial_env contract in
          let env = addContractEnv name ctrct_env env in
          checkEnv name env ctrct_env;
          globals, env
      | ContractDefinition _, _ ->
          invariant_broken "Contract should have contract annot"
      | GlobalVariableDefinition svd, annot -> (* Updates the global function *)
          assertGlobalIsConstant svd;
          let globals contract =
            stateVariableAnalyser ~current_position:pos (globals contract) svd annot
          in
          globals, env

      | _ -> globals, env)
    (empty_contract_env, env)
    m.module_units
  in
  env

let checkProgram (p : program) : unit =
  let _env = List.fold_left checkModule empty_project_env p.program_modules in
  ()
