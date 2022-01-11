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

(** Parse a Solidity file and all its imported files. *)
val parse_file :
  ?freeton:bool ->
  ?preprocess:( string -> string ) ->
  ?cpp:bool ->
  string -> Solidity_ast.program

(** Parse a list of Solidity files and all their imported files. *)
val parse_files :
  ?freeton:bool ->
  ?preprocess:( string -> string ) ->
  ?cpp:bool ->
  string list -> Solidity_ast.program

val add_temporary_file : string -> unit
val keep_temporary_files : unit -> unit
