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

let error_module_already_declared pos ident =
  error pos "Identifier %s already declared in module" (Ident.to_string ident)

let error_local_already_declared pos ident =
  error pos "Identifier %s already declared in scope" (Ident.to_string ident)

let error_contract_already_declared pos ident =
  error pos "Identifier %s already declared in contract" (Ident.to_string ident)

let error_inheritance_already_declared pos ident =
  error pos "Identifier %s already declared in inheritance" (Ident.to_string ident)

let error_defined_twice pos kind =
  error pos "%s with same name and arguments defined twice" kind


let is_defined = function
  | Defined -> true
  | Imported | Inherited -> false

let is_imported = function
  | Imported -> true
  | Defined | Inherited -> false

let is_inherited = function
  | Inherited -> true
  | Defined | Imported -> false


let idd_pos = function
  | Field (_) | Constr (_) -> dummy_pos
  | Alias (ad) -> ad.alias_pos
  | Module (md) -> md.module_pos
  | Contract (cd) -> cd.contract_def.contract_name.pos
  | Type (TDStruct (sd)) -> (fst sd.struct_def).pos
  | Type (TDEnum (ed)) -> ed.enum_pos
  | Variable ({ variable_def = Some (vd); _ }) -> vd.var_name.pos
  | Variable (_) -> dummy_pos
  | Function ({ function_def = Some (fd); _ }) -> fd.fun_name.pos
  | Function (_) -> dummy_pos
  | Modifier (md) -> md.modifier_def.mod_name.pos
  | Event (ed) -> ed.event_def.event_name.pos


let new_env ?upper_env () =
  { upper_env;  ident_map = IdentMap.empty; using_for = AbsLongIdentMap.empty }



(* Functions for building and checking module environments *)

let add_module_ident env id idd =
  let iddl = Option.value ~default:[] (IdentMap.find_opt id env.ident_map) in
  let iddl = List.rev ((idd, Defined) :: (List.rev iddl)) in
  env.ident_map <- IdentMap.add id iddl env.ident_map

let add_imported_definitions menvs m iml =
  let menv = IdentMap.find m.module_id menvs in
  let new_ident_map =
    List.fold_left (fun new_ident_map im ->
        let imenv = IdentMap.find im.module_id menvs in
        let new_origin =
          if Ident.equal m.module_id im.module_id then
            Defined
          else
            Imported
        in
        IdentMap.fold (fun id iddl new_ident_map ->
            let new_iddl =
              Option.value ~default:[] (IdentMap.find_opt id new_ident_map) in
            let new_iddl =
              List.fold_left (fun new_iddl (idd, id_origin) ->
                  if is_imported id_origin then new_iddl
                  else List.rev ((idd, new_origin) :: (List.rev new_iddl))
                ) new_iddl iddl
            in
            IdentMap.add id new_iddl new_ident_map
          ) imenv.ident_map new_ident_map
      ) IdentMap.empty iml
  in
  menv.ident_map <- new_ident_map

let resolve_aliases menvs m =
  let rec aux seen iddl =
    List.fold_left (fun seen (idd, _id_origin) ->
        match idd with
        | Alias ({ alias_targets = []; _ } as ad) ->
            if AbsLongIdentSet.mem ad.alias_abs_name seen then
              error ad.alias_pos "Alias declaration %s is cyclic"
                (Ident.to_string (LongIdent.last ad.alias_abs_name));
            let seen = AbsLongIdentSet.add ad.alias_abs_name seen in
            let at_iddl =
              match IdentMap.find_opt ad.alias_target_id
                      ad.alias_target_env.ident_map with
              | Some (at_iddl) ->
                  at_iddl
              | None ->
                  error ad.alias_pos "Declaration %s not found in %s"
                    (Ident.to_string ad.alias_target_id) ad.alias_target_file
            in
            let seen = aux seen at_iddl in
            ad.alias_targets <- at_iddl;
            seen
        | _ ->
            seen
      ) seen iddl
  in
  let menv = IdentMap.find m.module_id menvs in
  IdentMap.iter (fun _id iddl ->
      let _seen = aux AbsLongIdentSet.empty iddl in
      ()
    ) menv.ident_map;
  let rec aux iddl =
    List.flatten @@
      List.map (fun (idd, id_origin) ->
          match idd with
          | Alias ({ alias_abs_name; alias_pos; alias_targets = []; _ }) ->
              error alias_pos "Alias %s not resolved"
                (Ident.to_string (LongIdent.last alias_abs_name))
          | Alias ({ alias_targets; _ }) ->
              let at_iddl = aux alias_targets in
              List.map (fun (idd, _id_origin) -> (idd, Imported)) at_iddl
          | _ ->
              [(idd, id_origin)]
        ) iddl
  in
  menv.ident_map <- IdentMap.map aux menv.ident_map

let check_clashes_in_module menvs (m : Solidity_ast.module_) =
  let menv = IdentMap.find m.module_id menvs in
  IdentMap.iter (fun id iddl ->
      let _iddl =
        List.fold_left (fun iddl (idd, id_origin) ->
            begin
              match idd with
              | Field (_) | Constr (_) | Modifier (_) | Event (_) ->
                  invariant_broken __LOC__
              | Alias (ad) ->
                  error ad.alias_pos "Alias %s not resolved"
                    (Ident.to_string (LongIdent.last ad.alias_abs_name))
              | Module (_) | Contract (_) | Type (_) | Variable (_) ->
                  if not (ExtList.is_empty iddl) then
                    error_module_already_declared (idd_pos idd) id
              | Function (_fd) ->
                  ()
            end;
            List.rev ((idd, id_origin) :: (List.rev iddl))
          ) [] iddl
      in
      ()
    ) menv.ident_map



(* Functions for building and checking contract environments *)

(* Types are inheritable, but not overridable not overloadable *)
let can_add_type iddl _td =
  ExtList.is_empty iddl

(* Modifiers are inheritable and overridable, but not overloadable *)
let can_add_modifier iddl _md =
  List.for_all (fun (idd, id_origin) ->
      match idd with
      | Field (_) | Constr (_) | Module (_) | Contract (_) | Alias (_) ->
          invariant_broken __LOC__
      | Type (_) | Event (_) | Function (_) | Variable (_) ->
          false
      | Modifier (_) ->
          is_inherited id_origin
    ) iddl

(* Events are inheritable and overloadable, but not overridable *)
let can_add_event iddl _ed =
  List.for_all (fun (idd, _id_origin) ->
      match idd with
      | Field (_) | Constr (_) | Module (_) | Contract (_) | Alias (_) ->
          invariant_broken __LOC__
      | Type (_) | Modifier (_) | Function (_) | Variable (_) ->
          false
      | Event (_) ->
          true
    ) iddl

(* Variables are inheritable, but not overridable not overloadable.
   However, public variables can override external functions,
   and internal or private variables can co-exist with inherited
   external functions. *)
let can_add_variable iddl vd =
  List.for_all (fun (idd, id_origin) ->
      match idd with
      | Field (_) | Constr (_) | Module (_) | Contract (_) | Alias (_) ->
          invariant_broken __LOC__
      | Type (_) | Event (_) | Modifier (_) | Variable (_) ->
          false
      (* Public variables are valid overrides
         for inherited (external) functions *)
      | Function (_) when is_public vd.variable_visibility ->
          is_inherited id_origin
      (* Internal and private variables can co-exist with an
         an inherited external function sharing the same name *)
      | Function (fd) ->
          is_inherited id_origin && is_external fd.function_visibility
    ) iddl

(* Functions are inheritable, overloadable and overridable *)
let can_add_function iddl _fd =
  List.for_all (fun (idd, _id_origin) ->
      match idd with
      | Field (_) | Constr (_) | Module (_) | Contract (_) | Alias (_) ->
          invariant_broken __LOC__
      | Type (_) | Event (_) | Modifier (_) | Variable (_) ->
          false
      | Function (_) ->
          true
    ) iddl

type action =
  | Add
  | Skip
  | Fail

let add_inherited_definitions cd =
  let cenv = cd.contract_env in
  let new_ident_map =
    List.fold_left (fun new_ident_map (_lid, cd') ->
        let icenv = cd'.contract_env in
        IdentMap.fold (fun id iddl new_ident_map ->
            let new_iddl =
              Option.value ~default:[] (IdentMap.find_opt id new_ident_map) in
            let new_iddl =
              List.fold_left (fun new_iddl (idd, id_origin) ->
                  if is_inherited id_origin then
                    new_iddl
                  else
                    begin
                      let action =
                        match idd with
                        | Field (_) | Constr (_) | Alias (_)
                        | Module (_) | Contract (_) ->
                            invariant_broken __LOC__
                        | Type (td) ->
                            if can_add_type new_iddl td then Add
                            else Fail
                        | Modifier (md) ->
                            if can_add_modifier new_iddl md then Add
                            else Fail
                        | Event (ed) ->
                            if can_add_event new_iddl ed then Add
                            else Fail
                        | Variable ({ variable_visibility = VPrivate; _ }) ->
                            Skip
                        | Variable (vd) ->
                            if can_add_variable new_iddl vd then Add
                            else Fail
                        | Function ({ function_visibility = VPrivate; _ }) ->
                            Skip
                        | Function (_fd)
                          when Ident.equal id Ident.constructor ->
                            Skip
                        | Function (fd) ->
                            if can_add_function new_iddl fd then Add
                            else Fail
                      in
                      match action with
                      | Fail -> error_inheritance_already_declared
                                  (idd_pos idd) id
                      | Skip -> new_iddl
                      | Add ->
                          List.rev ((idd, Inherited) :: (List.rev new_iddl))
                    end
                ) new_iddl iddl
            in
            IdentMap.add id new_iddl new_ident_map
          ) icenv.ident_map new_ident_map
    ) IdentMap.empty (List.rev (List.tl (cd.contract_hierarchy)))
  in
  cenv.ident_map <- new_ident_map

let add_contract_ident cd id idd =
  let cenv = cd.contract_env in
  let iddl = Option.value ~default:[] (IdentMap.find_opt id cenv.ident_map) in
  let can_add =
    match idd with
    | Field (_) | Constr (_) | Alias (_)
    | Module (_) | Contract (_) ->
        invariant_broken __LOC__
    | Type (td) ->
        can_add_type iddl td
    | Modifier (md) ->
        can_add_modifier iddl md
    | Event (ed) ->
        can_add_event iddl ed
    | Variable (vd) ->
        can_add_variable iddl vd
    | Function (fd) ->
        can_add_function iddl fd
  in
  if can_add then
    cenv.ident_map <-
      IdentMap.add id
        (List.rev ((idd, Defined) :: (List.rev iddl))) cenv.ident_map
  else
    error_contract_already_declared (idd_pos idd) id

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
        if List.exists (Solidity_type.same_type ~ignore_loc:true t) tl then
          env, tl
        else
          env, t :: tl
  in
  env.using_for <-
    AbsLongIdentMap.add lib.contract_abs_name (lib_env, tl) env.using_for



(* Function for finalizing contract and module environments *)

let finalize_definitions menvs m =
  let menv = IdentMap.find m.module_id menvs in
  let rec aux kind_opt env =
    IdentMap.iter (fun _id iddl ->
        List.iter (fun (idd, id_origin) ->
            match id_origin with
            | Imported | Inherited ->
                (* Imported and inherited definitions will be
                   processed in their original environment *)
                ()
            | Defined ->
                begin
                  let open Solidity_type_builder in
                  match idd with
                  | Field (_) | Constr (_) | Alias (_) ->
                      invariant_broken __LOC__
                  | Module (_) ->
                      (* Modules in environments are just pointers to top-level
                         modules, they don't need to be processed here *)
                      ()
                  | Contract (cd) ->
                      aux (Some cd.contract_def.contract_kind) cd.contract_env;
                  | Type (_) ->
                      (* Nothing to do on types  *)
                      ()
                  | Modifier (md) ->
                      update_modifier_desc (idd_pos idd) env md
                  | Event (ed) ->
                      update_event_desc (idd_pos idd) env ed
                  | Variable (vd) ->
                      update_variable_desc (idd_pos idd) env vd kind_opt
                  | Function (fd) ->
                      update_function_desc (idd_pos idd) env fd kind_opt
                end
          ) iddl
      ) env.ident_map
  in
  aux None menv



(* Functions for checking and cleaning up overloads
   in module and contract environments *)

(* Modules can only be defined in modules and are not overloadable *)
let add_module iddl md id_origin =
  if not (ExtList.is_empty iddl) then
    invariant_broken __LOC__;
  match id_origin with
  | Inherited ->
      invariant_broken __LOC__
  | Imported | Defined ->
      [(Module (md), id_origin)]

(* Contracts can only be defined in modules and are not overloadable *)
let add_contract iddl cd id_origin =
  if not (ExtList.is_empty iddl) then
    invariant_broken __LOC__;
  match id_origin with
  | Inherited ->
      invariant_broken __LOC__
  | Imported | Defined ->
      [(Contract (cd), id_origin)]

(* Types are inheritable, but not overridable not overloadable *)
let add_type iddl td id_origin =
  if not (ExtList.is_empty iddl) then
    invariant_broken __LOC__;
  [(Type (td), id_origin)]

(* Modifiers are inheritable and overridable, but not overloadable *)
let add_modifier iddl md id_origin =
  List.iter (fun (idd, id_origin') ->
      match idd, id_origin' with
      | _, (Imported | Defined) ->
          invariant_broken __LOC__
      | Modifier (md'), _
        when not (Solidity_type.same_signature
                    md'.modifier_params md.modifier_params) ->
          error (idd_pos idd) "Override changes modifier signature"
      | Modifier (_md'), _ ->
          ()
      | _ ->
          invariant_broken __LOC__
    ) iddl;
  match id_origin with
  | Imported ->
      invariant_broken __LOC__
  | Inherited ->
      List.rev ((Modifier (md), id_origin) :: (List.rev iddl))
  | Defined ->
      [(Modifier (md), id_origin)]

(* Events are inheritable and overloadable, but not overridable *)
let add_event iddl ed id_origin =
  let iddl_rev =
    List.fold_left (fun iddl (idd, id_origin') ->
        match idd, id_origin' with
        | _, Imported ->
            invariant_broken __LOC__
        | _, Defined when is_inherited id_origin ->
            invariant_broken __LOC__
        | Event (ed'), _
          when not (Solidity_type.same_signature
                      ed'.event_params ed.event_params) ->
            (* Note: overload, because signature is different *)
            (Event (ed'), id_origin') :: iddl
        | Event (ed'), _
          when is_inherited id_origin && is_inherited id_origin &&
               not (LongIdent.equal ed.event_abs_name ed'.event_abs_name) ->
            (* Note: both events inherited, just don't keep the old one *)
            iddl
        | Event (_ed'), _ ->
            (* Note: multiple definition in the same contract *)
            error_defined_twice (idd_pos idd) "Event"
        | _ ->
            invariant_broken __LOC__
      ) [] iddl
  in
  match id_origin with
  | Imported ->
      invariant_broken __LOC__
  | Inherited | Defined ->
      List.rev ((Event (ed), id_origin) :: iddl_rev)

(* Variables are inheritable, but not overridable not overloadable.
   However, public variables can override external functions,
   and internal or private variables can co-exist with inherited
   external functions. *)
let add_variable iddl vd id_origin =
  match vd.variable_visibility with
  | VPublic ->
      let fd =
        match vd.variable_getter with
        | None -> invariant_broken __LOC__
        | Some (fd) -> fd
      in
      let iddl_rev =
        List.fold_left (fun iddl (idd, id_origin') ->
            match idd, id_origin' with
            | _, (Imported | Defined) ->
                invariant_broken __LOC__
            | Function (fd'), _
              when not (Solidity_type.same_signature
                          fd'.function_params fd.function_params) ->
                (* Note: overload, because signature is different *)
                (Function (fd'), id_origin') :: iddl
            | Function (_fd'), _
              when is_inherited id_origin && is_inherited id_origin' ->
                (* Note: both functions inherited, just don't keep the old one*)
                iddl
            | Function (fd'), _ ->
                (* Note: override because previous function is inherited *)
                begin
                  match fd'.function_def with
                  | None ->
                      invariant_broken __LOC__
                  | Some (fd'') ->
                      if not fd''.fun_virtual then
                        error (idd_pos idd)
                          "Trying to override non-virtual function"
                end;
                if is_none vd.variable_override then
                  error (idd_pos idd)
                    "Overriding public state variable \
                     is missing \"override\" specifier";
                if not (is_external fd'.function_visibility) then
                  error (idd_pos idd)
                    "Public state variables can only override \
                     functions with external visibility";
                if not (convertible_mutability
                          ~from:fd'.function_mutability
                          ~to_:fd.function_mutability) then
                  error (idd_pos idd)
                    "Overriding public state variable changes \
                     state mutability from \"%s\" to \"%s\""
                    (Solidity_printer.string_of_fun_mutability
                       fd'.function_mutability)
                    (Solidity_printer.string_of_fun_mutability
                       fd.function_mutability);
                iddl
            | _ ->
                invariant_broken __LOC__
          ) [] iddl
      in
      List.rev ((Variable (vd), id_origin) :: iddl_rev)
  | _ ->
      List.rev ((Variable (vd), id_origin) :: (List.rev iddl))

(* Functions are inheritable, overloadable and overridable *)
let add_function iddl fd id_origin =
  let iddl_rev =
    List.fold_left (fun iddl (idd, id_origin') ->
        match idd, id_origin' with
        | _, Defined when (is_inherited id_origin || is_imported id_origin) ->
            invariant_broken __LOC__
        | Function (fd'), _
          when not (Solidity_type.same_signature
                      fd'.function_params fd.function_params) ->
            (* Note: overload, because signature is different *)
            (Function (fd'), id_origin') :: iddl
        | Function (_fd'), _
          when is_inherited id_origin && is_inherited id_origin' ->
            (* Note: both functions inherited, just don't keep the old one *)
            iddl
        | Function (_fd'), _
          when not (is_inherited id_origin') ->
            (* Note: multiple definition in the same contract *)
            error_defined_twice (idd_pos idd) "Function";
        | Function (fd'), _ ->
            (* Note: override because previous function is inherited *)
            begin
              match fd'.function_def with
              | None ->
                  invariant_broken __LOC__
              | Some (fd'') ->
                  if not fd''.fun_virtual then
                    error (idd_pos idd)
                      "Trying to override non-virtual function"
            end;
            begin
              match fd.function_def with
              | None ->
                  invariant_broken __LOC__
              | Some (fd'') ->
                  if is_none fd''.fun_override then
                    error (idd_pos idd)
                      "Overriding function is missing \"override\" specifier"
            end;
            if not (convertible_visibility
                      ~from:fd'.function_visibility
                      ~to_:fd.function_visibility) then
              error (idd_pos idd)
                "Overriding function visibility differs";
            if not (convertible_mutability
                      ~from:fd'.function_mutability
                      ~to_:fd.function_mutability) then
              error (idd_pos idd)
                "Overriding function changes state \
                 mutability from \"%s\" to \"%s\""
                (Solidity_printer.string_of_fun_mutability
                   fd'.function_mutability)
                (Solidity_printer.string_of_fun_mutability
                   fd.function_mutability);
            iddl
        | _ ->
            invariant_broken __LOC__
      ) [] iddl
  in
  List.rev ((Function (fd), id_origin) :: iddl_rev)

let check_and_filter_overloads menvs m =
  let menv = IdentMap.find m.module_id menvs in
  let rec aux env =
    let new_ident_map =
      IdentMap.mapi (fun _id iddl ->
          List.fold_left (fun new_iddl (idd, id_origin) ->
              match idd with
              | Field (_) | Constr (_) | Alias (_) ->
                  invariant_broken __LOC__
              | Module (md) ->
                  (* Modules in environments are just pointers to top-level
                     modules, they don't need to be processed here *)
                  add_module new_iddl md id_origin
              | Contract (cd) ->
                  aux cd.contract_env;
                  add_contract new_iddl cd id_origin
              | Type (td) ->
                  add_type new_iddl td id_origin
              | Modifier (md) ->
                  add_modifier new_iddl md id_origin
              | Event (ed) ->
                  add_event new_iddl ed id_origin
              | Variable (vd) ->
                  add_variable new_iddl vd id_origin
              | Function (fd) ->
                  add_function new_iddl fd id_origin
            ) [] iddl
        ) env.ident_map
    in
    env.ident_map <- new_ident_map
  in
  aux menv



(* Functions for building function environments *)

let add_local_variable pos env id vd =
  match IdentMap.find_opt id env.ident_map with
  | Some (_) ->
      error_local_already_declared pos id
  | None ->
      env.ident_map <- IdentMap.add id [(Variable (vd), Defined)] env.ident_map
