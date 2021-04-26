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

(**
  Checks that a typed solidity AST verifies the Solidity standard properties.
  The list of exceptions this function may raise is defined in
  Solidity_exceptions
*)
val checkProgram : Solidity_ast.program -> unit
