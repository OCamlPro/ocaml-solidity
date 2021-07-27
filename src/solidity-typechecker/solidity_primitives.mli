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

val init : unit -> unit

module UTILS : sig
  val register :
    int ->
    Solidity_common.primitive ->
    (Solidity_common.pos ->
     Solidity_checker_TYPES.options ->
     Solidity_checker_TYPES.type_ option ->
     Solidity_checker_TYPES.ident_desc option) ->
    unit
  val primitive_fun_named :
    ?returns_lvalue:bool ->
    (Solidity_checker_TYPES.type_ *
     Solidity_common.IdentSet.elt option)
      list ->
    Solidity_checker_TYPES.type_ list ->
    Solidity_ast.fun_mutability -> Solidity_checker_TYPES.ident_desc

  val make_var :
    Solidity_checker_TYPES.type_ -> Solidity_checker_TYPES.ident_desc
  val make_fun :
    ?returns_lvalue:bool ->
    Solidity_checker_TYPES.type_ list ->
    Solidity_checker_TYPES.type_ list ->
    Solidity_ast.fun_mutability -> Solidity_checker_TYPES.ident_desc
  val make_prim_args :
    Solidity_common.pos ->
    Solidity_checker_TYPES.options ->
    Solidity_checker_TYPES.type_ list option
  val preprocess_arg_0 : 'a -> 'b list option -> 'b list
  val preprocess_arg_1 :
    Solidity_common.pos -> 'a -> 'a list option -> 'a list

end
