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

(*
val change_type_location :
  Solidity_checker_TYPES.location ->
  Solidity_checker_TYPES.type_ ->
  Solidity_checker_TYPES.type_
*)
(*
val add_primitive_type :
  int ->
  (Solidity_common.pos ->
   Solidity_checker_TYPES.options ->
   Solidity_checker_TYPES.type_ option ->
   Solidity_checker_TYPES.type_ option) ->
  unit
*)
val type_module : Solidity_ast.module_ -> unit
(*
val variable_type_to_function_type :
  Solidity_common.pos ->
  Solidity_checker_TYPES.type_ ->
  (Solidity_checker_TYPES.type_ * Solidity_common.Ident.t option) list *
  (Solidity_checker_TYPES.type_ * Solidity_common.Ident.t option) list
*)
