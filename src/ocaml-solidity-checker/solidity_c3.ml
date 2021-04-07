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
open Solidity_checker_TYPES
open Solidity_exceptions

let error = type_error

(* Perform linearization of inheritance diagram *)
let linearize pos ({ contract_abs_name; contract_def; _ } as c) =
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
    | Some (lident_contract :: _) -> Some (lident_contract)
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
            error pos "Linearization failed for %s"
               (LongIdent.to_string contract_abs_name)
        | Some (lident_contract) ->
            merge (lident_contract :: res)
              (filter_out lident_contract lident_contract_ll)
  in
  let parents_linearization, contract_parents =
    List.split (List.rev (List.map (fun (p, _) ->
        match get_annot p with
        | AContract (c) ->
            c.contract_hierarchy, (c.contract_abs_name, c)
        | _ ->
            error pos "Contract %s parent contract %s is undefined"
              (LongIdent.to_string contract_abs_name)
              (LongIdent.to_string (strip p))
      ) contract_def.contract_inheritance))
  in
  c.contract_hierarchy <-
    merge [contract_abs_name, c]
      (filter_out_empty (parents_linearization @ [contract_parents]))
