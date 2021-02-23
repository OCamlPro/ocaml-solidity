(**************************************************************************)
(*                                                                        *)
(*    Copyright 2017-2018 OCamlPro                                        *)
(*                                                                        *)
(*  All rights reserved. This file is distributed under the terms of the  *)
(*  GNU Lesser General Public License version 2.1, with the special       *)
(*  exception on linking described in the file LICENSE.                   *)
(*                                                                        *)
(**************************************************************************)

module Hex : sig

  type t = string

  val compare : t -> t -> int
  val equal : t -> t -> bool


  (** [encode s] converts a string to a lowercase hexadecimal notation *)
  val encode : string -> t

  (** [encodeU s] converts a string to an uppercase hexadecimal notation *)
  val encodeU : string -> t

  (** [decode hex] converts a string in hexadecimal notation into its
     corresponding decoded string. Can raise Invalid_argument. *)
  val decode : t -> string

  (** [encode s] converts a string to a lowercase hexadecimal notation *)
  val encode_bytes : bytes -> t

  (** [encodeU s] converts a string to an uppercase hexadecimal notation *)
  val encodeU_bytes : bytes -> t

  (** [decode hex] converts a string in hexadecimal notation into its
     corresponding decoded string. Can raise Invalid_argument. *)
  val decode_bytes : t -> bytes

end
