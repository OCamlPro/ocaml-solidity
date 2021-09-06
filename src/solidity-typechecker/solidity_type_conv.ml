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

open Solidity_common
open Solidity_checker_TYPES
open Solidity_exceptions

let error = type_error



(* ---------- Utility functions for type conversion ---------- *)

let is_storage = function
  | LMemory -> false
  | LStorage (_b) -> true
  | LCalldata -> false

let is_storage_ptr = function
  | LMemory -> false
  | LStorage (b) -> b
  | LCalldata -> false

let convertible_location ~from ~to_ =
  !for_freeton ||
  match from, to_ with
  | LCalldata, LCalldata -> true
  | _, (LMemory | LStorage (false)) -> true
  | LStorage _, _ -> true
  | _ -> false

(* Returns the number of bits taken by the decimals of a fixed *)
let decimals_space (decimals : int) =
  let max : Z.t = Z.pow (Z.of_int 10) decimals in
  let rec loop (cpt : int) (two_to_cpt : Z.t) =
    if (>=) ((Z.compare (Z.min two_to_cpt Z.one)) max) 0 then
      cpt
    else
      loop (cpt + 1) (Z.shift_left two_to_cpt 1)
  in loop 0 Z.one

(* Returns the size (in bits) of the integer part of a fixed
   encoded in 'size' bits with 'dec' decimals (type float'size'x'dec') *)
let integer_part_size (size : int) (dec : int) =
  size - (decimals_space dec)

(* Check if a string literal is a valid UTF-8 string *)
let valid_utf8_string s =
  let rec aux d =
    match Uutf.decode d with
    | `Uchar _u -> aux d
    | `End -> true
    | `Malformed _ -> false
    | `Await -> assert false
  in
  aux (Uutf.decoder (`String s))



(* ---------- Implicit conversion check ---------- *)

(* Check whether implicit conversion can occur between two types *)
let rec implicitly_convertible ?(ignore_loc=false) ~from ~to_ () =
  match from, to_ with
  | _, TAny -> true
  | TUint (size1), TInt (size2) ->
      size1 < size2
  | TUint (size1), TUint (size2)
  | TInt (size1), TInt (size2) ->
      (size1 <= size2)
  | (TInt (size1) | TUint (size1)), TFixed (size2, dec2)
  | TUint (size1), TUfixed (size2, dec2) ->
      (size1 <= integer_part_size size2 dec2)
  | TUfixed (size1, udec1), (TUfixed (size2, udec2) | TFixed (size2, udec2))
  | TFixed (size1, udec1), TFixed (size2, udec2) ->
      (udec1 <= udec2) &&
      (integer_part_size size1 udec1 <= integer_part_size size2 udec2)
  | TRationalConst (q, sz_opt), TFixBytes (bsz) ->
      ExtQ.is_int q &&
      not (ExtQ.is_neg q) &&
      (Option.fold ~none:false ~some:(fun sz -> sz = bsz) sz_opt)
  | TRationalConst (q, _), TUint (sz) ->
      ExtQ.is_int q &&
      not (ExtQ.is_neg q) &&
      (Z.numbits (Q.num q) <= sz)
  | TRationalConst (q, _), TInt (sz) ->
      (* Note: when negative, add one to correctly count bits *)
      let n = if ExtQ.is_neg q then Z.succ (Q.num q) else Q.num q in
      ExtQ.is_int q &&
      (Z.numbits n < sz)
  | TLiteralString (s), TString (loc) ->
      valid_utf8_string s &&
      (ignore_loc || convertible_location ~from:LMemory ~to_:loc)
  | TLiteralString (_s), TBytes (loc) ->
      (ignore_loc || convertible_location ~from:LMemory ~to_:loc)
  | TLiteralString (s), TFixBytes (sz) ->
      (String.length s <= sz)
  | TAddress (true), TAddress (_payable) ->
      true
  | TAddress (false), TAddress (_payable) when !for_freeton ->
      true
  | TContract (_, derived, _), TContract (base, _, _) ->
      List.exists (fun (derived, _) ->
          LongIdent.equal derived base) derived.contract_hierarchy
  | TContract _, TAddress _ -> !for_freeton
  | TString (loc1), TString (loc2)
  | TBytes (loc1), TBytes (loc2) ->
      (ignore_loc || convertible_location ~from:loc1 ~to_:loc2)
  | TStruct (lid1, _, loc1), TStruct (lid2, _, loc2) ->
      (ignore_loc || convertible_location ~from:loc1 ~to_:loc2) &&
      LongIdent.equal lid1 lid2
  | TArray (from, _, loc1), TArray (to_, _, loc2) ->
      (ignore_loc || convertible_location ~from:loc1 ~to_:loc2) &&
       implicitly_convertible ~ignore_loc ~from ~to_ ()
  | TMapping (tk1, tv1, loc1), TMapping (tk2, tv2, loc2) ->
      (ignore_loc ||
       ( !for_freeton ||
         ( is_storage loc1 && is_storage_ptr loc2 ) )
      ) &&
       implicitly_convertible ~ignore_loc ~from:tk1 ~to_:tk2 () &&
       implicitly_convertible ~ignore_loc ~from:tv1 ~to_:tv2 ()
  | TTuple (tl1), TTuple (tl2) ->
      implicitly_convertible_ol ~ignore_loc ~from:tl1 ~to_:tl2 ()
  | TOptional t1, TOptional t2 ->
      implicitly_convertible ~ignore_loc ~from:t1 ~to_:t2 ()
  | t1, TOptional t2 ->
      implicitly_convertible ~ignore_loc ~from:t1 ~to_:t2 ()
  | TUint _, TBytes _ -> true
  | TBytes _, TString _ when !for_freeton -> true
  | TString _, TBytes _ when !for_freeton -> true
  | _, TDots when !for_freeton -> true
  | _ ->
      Solidity_type.same_type from to_

and implicitly_convertible_ol ?(ignore_loc=false) ~from ~to_ () =
  List.length from = List.length to_ &&
  List.for_all2 (fun from_opt to_opt ->
      match from_opt, to_opt with
      | None, None -> true
      | Some (_), None -> true
      | None, Some (_) -> false
      | Some (from), Some (to_) ->
          implicitly_convertible ~ignore_loc ~from ~to_ ()
    ) from to_



(* ---------- Explicit conversion check ---------- *)

(* Check whether explicit conversion can occur
   between two types and returns the casted type *)
let rec explicitly_convertible ~from ~to_ : type_ option =
  let if_true cond = if cond then Some (to_) else None in

  match from, to_ with
  | (TInt (isz) | TUint (isz)), TFixBytes (bsz) ->
      if_true (bsz = (isz / 8))

  | TAddress _, TFixBytes (bsz) ->
      if_true (bsz = 20 || bsz = 21)

  | TFixBytes (bsz), TAddress (_) ->
      if bsz = 20 || bsz = 21 then
        Some (TAddress (true))
      else
        None

  | TAddress (_), TContract (_) -> Some (to_)
  | TContract (_, cd, _), TAddress (payable) ->
      if not payable then Some (to_)
      else
        let idl = Solidity_tenv.lookup_ident cd.contract_env
                    ~upper:false ~lookup:LAny Ident.receive in
        let payable =
          List.exists (function
              | Function { function_mutability = MPayable; _ } -> true
              | _ -> false
            ) idl
        in
        Some (TAddress (payable))

  | TContract (_, derived, _), TContract (base, _, _) ->
      if_true (List.exists (fun (derived, _) ->
                   LongIdent.equal derived base) derived.contract_hierarchy)

  | (TInt _ | TUint _), TAddress (false) ->
      Some (TAddress (true))

  | TRationalConst (q, _), TAddress (_) ->
      if ExtQ.is_int q then
        Some (TAddress true)
      else
        None

  | TRationalConst (q, sz_opt), TFixBytes (bsz) ->
      if_true (
        ExtQ.is_int q &&
        not (ExtQ.is_neg q) &&
        (Option.fold ~none:false ~some:(fun sz -> sz = bsz) sz_opt))

  | TRationalConst (q, _), (TInt _ | TUint _ | TContract _ | TEnum _) ->
      if_true (ExtQ.is_int q)

  | TLiteralString (s), TString (LMemory | LStorage (false)) ->
      if_true (valid_utf8_string s)

  | TLiteralString (_s), TBytes (LMemory | LStorage (false)) ->
      Some (to_)

  | TLiteralString (s), TFixBytes (bsz) ->
      if_true (String.length s <= bsz)

  | (TString (loc1) | TBytes (loc1)),
    (TString (loc2) | TBytes (loc2)) ->
      if_true (convertible_location ~from:loc1 ~to_:loc2)

  | TArray (from, sz_from, loc1), TArray (to_, sz_to, loc2) ->
      let test_size () =
        match sz_from, sz_to with
        | None, None -> true
        | Some (s1), Some (s2) -> Z.equal s1 s2
        | _ -> false in
      let test_loc () = convertible_location ~from:loc1 ~to_:loc2 in
      if test_size () && test_loc () then
        Option.map (fun t -> TArray (t, sz_to, loc2))
          (explicitly_convertible ~from ~to_)
      else
        None

  | TTuple (tl1), TTuple (tl2) ->
      Option.map (fun l -> TTuple (l))
        (explicitly_convertible_ol ~from:tl1 ~to_:tl2)

  | TStruct (lid1, _, loc1), TStruct (lid2, _, loc2) ->
      if_true (convertible_location ~from:loc1 ~to_:loc2 &&
                 LongIdent.equal lid1 lid2)

  | (TInt _ | TUint _), (TInt _ | TUint _ | TAddress _ | TContract _ | TEnum _)
  | TFixBytes _, TFixBytes _
  | TAddress _, (TInt _ | TUint _ | TAddress _)
  | TEnum _, (TInt _ | TUint _) ->
      Some (to_)

  | TFixBytes 1, TUint 8 when !for_freeton -> Some (to_)

  | _ ->
      if_true (Solidity_type.same_type from to_)

and explicitly_convertible_ol ~from ~to_ : type_ option list option =
  if List.length from = List.length to_ then
    let exception Stop in
    let rec loop acc froml tol =
      match froml, tol with
      | [], [] ->
          List.rev acc
      | from :: tl_from, to_ :: tl_to ->
          let acc =
            match from, to_ with
            | None, None -> None :: acc (* Ok, but there is no type *)
            | Some (t), None
            | None, Some (t) -> Some (t) :: acc
            | Some (from), Some (to_) ->
                match explicitly_convertible ~from ~to_ with
                | None -> raise Stop
                | res -> res :: acc
          in
          loop acc tl_from tl_to
      | _ :: _, []
      | [], _ :: _ ->
          assert false (* List have the same size *)
    in
    try Some (loop [] from to_)
    with Stop -> None
  else
    None

let explicitly_convertible_bool ~from ~to_ =
  Option.is_some (explicitly_convertible ~from ~to_)



(* ---------- Determine a type's mobile type ---------- *)

let rec mobile_type pos t =
  match t with
  | TRationalConst (q, _sz_opt) ->
      if ExtQ.is_int q then
        (*         let sz = ExtZ.numbits_mod8 (Q.num q) in *)
        let sz = Z.numbits ( Q.num q ) in
        if sz > 256 then
          error pos "Invalid rational number";
        if ExtQ.is_neg q then TInt (sz)
        else TUint (sz)
      else
        let z, nb_dec = ExtQ.to_fixed q in
        let sz = ExtZ.numbits_mod8 z in
        if sz > 256 then
          error pos "Invalid rational number";
        if ExtQ.is_neg q then TFixed (sz, nb_dec)
        else TUfixed (sz, nb_dec)
  | TLiteralString (_s) ->
      (* Note: even if not a valid string *)
      TString (LMemory)
  | TArraySlice (bt, LCalldata) ->
      (* Array slices of dynamic calldata arrays are of type array *)
      TArray (bt, None, LCalldata)
  | TTuple (tl) ->
      TTuple (List.map (Option.map (mobile_type pos)) tl)
  | _ -> t



(* ----- Determine the common type between two types ----- *)

let common_type t1 t2 =
  if implicitly_convertible ~from:t1 ~to_:t2 () then
    Some (t2)
  else if implicitly_convertible ~from:t2 ~to_:t1 () then
    Some (t1)
  else
    None
