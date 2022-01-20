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

(** Types a program and, if successful, returns the
    annoted program where the program_modules are ordered wrt.
    their dependencies. *)
val type_program : ?freeton:bool ->
  ?init:(?freeton:bool -> unit -> unit) ->
  Solidity_ast.program -> Solidity_ast.program


val expect_expression_type :
  Solidity_checker_TYPES.options ->
  Solidity_checker_TYPES.env ->
  Solidity_ast.expression -> Solidity_checker_TYPES.type_ -> unit

val type_options_ref :
  (Solidity_checker_TYPES.options ->
   Solidity_checker_TYPES.env ->
   Solidity_common.pos ->
   bool ->
   Solidity_checker_TYPES.function_options ->
   (Solidity_ast.ident * Solidity_ast.expression) list ->
   Solidity_checker_TYPES.function_options)
    ref
