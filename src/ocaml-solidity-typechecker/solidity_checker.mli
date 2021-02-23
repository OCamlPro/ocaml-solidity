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

type args =
  | AList of Solidity_tenv.type_ list
  | ANamed of (Solidity_common.Ident.t * Solidity_tenv.type_) list

type options = {
  allow_empty: bool; (* whether to allow empty elements in tuple *)
  call_args: args option;    (* could just have an in_lvalule flag *)
  fun_returns : Solidity_tenv.type_ list;
  in_loop: bool;
  in_function: bool;
  in_modifier: bool;
  current_hierarchy: Solidity_common.absolute Solidity_common.LongIdent.t list;
  current_contract: Solidity_tenv.contract_desc option;
}

val change_type_location :
  Solidity_tenv.location -> Solidity_tenv.type_ -> Solidity_tenv.type_

val add_primitive_type :
  int ->
  (Solidity_common.loc ->
   options ->
   Solidity_tenv.type_ option ->
   Solidity_tenv.type_ option) ->
  unit

val type_module : Solidity_ast.module_ -> unit

val variable_type_to_function_type :
  Solidity_common.loc ->
  Solidity_tenv.type_ ->
  (Solidity_tenv.type_ * Solidity_common.Ident.t option) list *
  (Solidity_tenv.type_ * Solidity_common.Ident.t option) list
