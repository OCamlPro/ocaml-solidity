(**************************************************************************)
(*                                                                        *)
(*    Copyright 2017-2018 OCamlPro                                        *)
(*                                                                        *)
(*  All rights reserved. This file is distributed under the terms of the  *)
(*  GNU Lesser General Public License version 2.1, with the special       *)
(*  exception on linking described in the file LICENSE.                   *)
(*                                                                        *)
(**************************************************************************)

module Hex = struct

  type t = string

  let compare = String.compare
  (* let equal = String.equal *)
  let equal = (=)

  let char_hex n =
    Char.unsafe_chr (n + if n < 10 then Char.code '0' else (Char.code 'a' - 10))

  let encode d =
    let len = String.length d in
    let result = Bytes.create (len*2) in
    for i = 0 to len-1 do
      let x = Char.code d.[i] in
      Bytes.unsafe_set result (i*2) (char_hex (x lsr 4));
      Bytes.unsafe_set result (i*2+1) (char_hex (x land 0x0f));
    done;
    Bytes.unsafe_to_string result

  let char_hexU n =
    Char.unsafe_chr (n + if n < 10 then Char.code '0' else (Char.code 'A' - 10))

  let encodeU d =
    let len = String.length d in
    let result = Bytes.create (len*2) in
    for i = 0 to len-1 do
      let x = Char.code d.[i] in
      Bytes.unsafe_set result (i*2) (char_hexU (x lsr 4));
      Bytes.unsafe_set result (i*2+1) (char_hexU (x land 0x0f));
    done;
    Bytes.unsafe_to_string result

  let decode s =
    let len = String.length s in
    if len mod 2 <> 0 then invalid_arg "Hex.decode";
    let digit c =
      match c with
      | '0'..'9' -> Char.code c - Char.code '0'
      | 'A'..'F' -> Char.code c - Char.code 'A' + 10
      | 'a'..'f' -> Char.code c - Char.code 'a' + 10
      | _ -> raise (Invalid_argument "Hex.decode")
    in
    let byte i = digit s.[i] lsl 4 + digit s.[i+1] in
    let result = Bytes.create (len/2) in
    for i = 0 to len/2 - 1 do
      Bytes.set result i (Char.chr (byte (2 * i)));
    done;
    Bytes.unsafe_to_string result

  let encode_bytes b = encode (Bytes.unsafe_to_string b)
  let encodeU_bytes b = encodeU (Bytes.unsafe_to_string b)
  let decode_bytes s = Bytes.unsafe_of_string (decode s)

end
