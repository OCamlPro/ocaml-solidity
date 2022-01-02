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

val init : freeton:bool -> unit
val init2 : ?list:(string * Solidity_raw_parser.token) list -> unit -> unit

val reset : unit -> unit

val token : Lexing.lexbuf -> Solidity_raw_parser.token

val recursive_comments : bool ref
