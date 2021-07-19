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

val string_of_storage_location : Solidity_ast.storage_location -> string

val string_of_fun_mutability : Solidity_ast.fun_mutability -> string

val string_of_var_mutability : Solidity_ast.var_mutability -> string

val string_of_visibility : Solidity_ast.visibility -> string

val string_of_unop : Solidity_ast.unary_operator -> string

val string_of_binop : Solidity_ast.binary_operator -> string

val string_of_cmpop : Solidity_ast.compare_operator -> string

val string_of_elementary_type : Solidity_ast.elementary_type -> string

val string_of_type : Solidity_ast.type_ -> string

val string_of_expression :
  ?paren:bool -> Solidity_ast.expression -> string

val string_of_module_units :
  ?freeton:bool -> Solidity_ast.module_units -> string

val string_of_program :
  ?freeton:bool -> Solidity_ast.program -> string
