(**************************************************************************)
(*                                                                        *)
(*    Copyright 2017-2018 OCamlPro                                        *)
(*                                                                        *)
(*  All rights reserved. This file is distributed under the terms of the  *)
(*  GNU Lesser General Public License version 2.1, with the special       *)
(*  exception on linking described in the file LICENSE.                   *)
(*                                                                        *)
(**************************************************************************)

val digest :
  [< `SHA256 | `SHA3_KEC | `SHA3_KEC384 | `SHA3_KEC512 ] -> string -> string

module type HASH = sig
  type t
  val hash : string -> t
  val hash_bytes : bytes -> t (* typed *)
  val raw : t -> string
  val size : int
  val digest : string -> string (* untyped *)
  end

module SHA256 : HASH
module SHA3KEC : HASH
module SHA3KEC512 : HASH

(*
module BLAKE2B : HASH

module RAW : sig
  type blake2b_ctx
  val blake2b_init : ?key:string -> ?size:int -> unit -> blake2b_ctx * bytes
  val blake2b_update : blake2b_ctx * bytes -> string -> unit
  val blake2b_final : blake2b_ctx * bytes -> string
  val blake2b : ?key:string -> string -> string
end
*)
