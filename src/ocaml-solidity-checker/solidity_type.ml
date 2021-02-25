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
open Solidity_ast
open Solidity_checker_TYPES

let error pos fmt =
  Format.kasprintf (fun s -> raise (TypecheckError (s, pos))) fmt



(* ---------- Equality between types (internal use) ---------- *)

let same_location l1 l2 =
  match l1, l2 with
  | LMemory, LMemory -> true
  | LStorage (ptr1), LStorage (ptr2) -> ptr1 = ptr2
  | LCalldata, LCalldata -> true
  | _ -> false

let same_options o1 o2 =
  o1.value = o2.value &&
  o1.gas = o2.gas &&
  o1.salt = o2.salt

let rec same_type ?(ignore_loc=false) t1 t2 =
  match t1, t2 with
  | TBool, TBool ->
      true
  | TInt (sz1), TInt (sz2)
  | TUint (sz1), TUint (sz2) ->
      sz1 = sz2
  | TFixed (sz1, dec1), TFixed (sz2, dec2)
  | TUfixed (sz1, dec1), TUfixed (sz2, dec2) ->
      sz1 = sz2 && dec1 = dec2
  | TAddress (payable1), TAddress (payable2) ->
      payable1 = payable2
  | TFixBytes (sz1), TFixBytes (sz2) ->
      sz1 = sz2
  | TBytes (loc1), TBytes (loc2)
  | TString (loc1), TString (loc2) ->
      ignore_loc || same_location loc1 loc2
  | TEnum (lid1, _ed1), TEnum (lid2, _ed2) ->
      LongIdent.equal lid1 lid2
  | TStruct (lid1, _ed1, loc1), TStruct (lid2, _ed2, loc2) ->
      LongIdent.equal lid1 lid2 &&
      (ignore_loc || same_location loc1 loc2)
  | TContract (lid1, _ed1, super1), TContract (lid2, _ed2, super2) ->
      LongIdent.equal lid1 lid2 && super1 = super2
  | TArray (t1, None, loc1), TArray (t2, None, loc2) ->
      same_type ~ignore_loc t1 t2 &&
      (ignore_loc || same_location loc1 loc2)
  | TArray (t1, Some (sz1), loc1), TArray (t2, Some (sz2), loc2) ->
      Z.equal sz1 sz2 &&
      same_type ~ignore_loc t1 t2 &&
      (ignore_loc || same_location loc1 loc2)
  | TMapping (src1, dst1, loc1), TMapping (src2, dst2, loc2) ->
      same_type ~ignore_loc src1 src2 &&
      same_type ~ignore_loc dst1 dst2 &&
      (ignore_loc || same_location loc1 loc2)
(* TODO: be more accurate *)
(* TODO: options ? *)
  | TFunction (fd1, fo1),
    TFunction (fd2, fo2) ->
      same_type_pl ~ignore_loc fd1.function_params fd2.function_params &&
      same_type_pl ~ignore_loc fd1.function_returns fd2.function_returns &&
      same_mutability fd1.function_mutability fd2.function_mutability &&
(* TODO: only external counts (use kind instead) *)
      same_visibility fd1.function_visibility fd2.function_visibility &&
      same_options fo1 fo2
  | TModifier (md1), TModifier (md2) ->
      same_type_pl ~ignore_loc md1.modifier_params md2.modifier_params
  | TArraySlice (t1, loc1), TArraySlice (t2, loc2) ->
      same_type ~ignore_loc t1 t2 &&
      (ignore_loc || same_location loc1 loc2)
  | TType (t1), TType (t2) ->
      same_type ~ignore_loc t1 t2
  | TMagic (mt1), TMagic (mt2) ->
      same_magic_type ~ignore_loc mt1 mt2
  | TRationalConst (q1, sz_opt1), TRationalConst (q2, sz_opt2) ->
      Q.equal q1 q2 &&
      (match sz_opt1, sz_opt2 with
       | Some (sz1), Some (sz2) -> (sz1 = sz2)
       | _ -> false)
  | TLiteralString (s1), TLiteralString (s2) ->
      String.equal s1 s2
  | TTuple (tl1), TTuple (tl2) ->
      same_type_ol ~ignore_loc tl1 tl2

  (* TON-specific *)
  | TTvmCell, TTvmCell
  | TTvmSlice, TTvmSlice
  | TTvmBuilder, TTvmBuilder
  | TExtraCurrencyCollection, TExtraCurrencyCollection ->
      true
  | TOptional (t1), TOptional (t2) ->
      same_type ~ignore_loc t1 t2

  | _ ->
      false

and same_type_ol ?(ignore_loc=false) tl1 tl2 =
  List.length tl1 = List.length tl2 &&
  List.for_all2 (fun t1_opt t2_opt ->
      match t1_opt, t2_opt with
      | Some (t1), Some (t2) -> same_type ~ignore_loc t1 t2
      | Some _, None | None, Some _ -> false
      | None, None -> true
    ) tl1 tl2

and same_type_pl ?(ignore_loc=false) tl1 tl2 =
  List.length tl1 = List.length tl2 &&
  List.for_all2 (fun (t1, _) (t2, _) ->
      same_type ~ignore_loc t1 t2
    ) tl1 tl2

and same_magic_type ?(ignore_loc=false) t1 t2 =
  match t1, t2 with
  | TMetaType (t1), TMetaType (t2) ->
      same_type ~ignore_loc t1 t2
  | TMsg, TMsg
  | TBlock, TBlock
  | TTx, TTx
  | TAbi, TAbi ->
      true

  (* TON-specific *)
  | TTvm, TTvm
  | TMath, TMath
  | TRnd, TRnd ->
      true

  | _ ->
      false



(* ---------- Equality between signatures (internal use) ---------- *)

let same_signature fd1 fd2 =
  if not (ExtList.same_lengths fd1.function_params fd2.function_params) then
    false
  else
    List.for_all2 (fun (t1, _) (t2, _) -> same_type t1 t2)
      fd1.function_params fd2.function_params



(* ---------- Check if type has a mapping (internal/external use) ---------- *)

let rec has_mapping = function
  | TBool | TInt _ | TUint _ | TFixed _ | TUfixed _
  | TAddress _ | TFixBytes _ | TBytes _ | TString _ | TEnum _
  | TContract _ | TFunction _ | TModifier _ | TMagic _ | TType _
  | TRationalConst _ | TLiteralString _ ->
      false
  | TMapping _ ->
      true
  | TArray (t, _, _)
  | TArraySlice (t, _) ->
      has_mapping t
  | TStruct (_, s, _) ->
      s.has_mapping
  | TTuple (tl) ->
      List.exists (function
          | None -> false
          | Some (t) -> has_mapping t
        ) tl

  (* TON-specific *)
  | TTvmCell | TTvmSlice | TTvmBuilder | TExtraCurrencyCollection ->
      false
  | TOptional (t) ->
      has_mapping t



(* ----- Determine if a type is valid for comparison (external) ----- *)

(* In fact, only value types, with bool and fun restricted to ==/!= *)
let is_comparable op t =
  let open Solidity_ast in
  match t with
  | TBool | TFunction _ ->
  (* TODO: only internal functions can be compared *)
      begin
        match op with
        | CEq | CNeq -> true
        | _ -> false
      end
  | TInt _ | TUint _ | TRationalConst _
  | TFixed _ | TUfixed _ | TFixBytes _
  | TAddress _ | TEnum _ | TContract _ ->
      true
  | TTuple _ (* may become comparable in the future *)
  | TBytes _ | TString _ | TLiteralString _
  | TArray _ | TArraySlice _ | TMapping _ | TStruct _
  | TType _ | TMagic _ | TModifier _  ->
      false
  (* TON-specific *)
  | TTvmCell | TTvmSlice | TTvmBuilder | TExtraCurrencyCollection ->
      true
  | TOptional (_t) ->
      false



(* ---------- Check if type has storage location (external) ---------- *)

let rec is_storage_type = function
  (* Value types and literals are never in storage *)
  | TBool | TInt _ | TUint _ | TFixed _ | TUfixed _
  | TAddress _ | TFixBytes _ | TEnum _ | TContract _
  | TFunction _ | TModifier _ | TMagic _ | TType _
  | TRationalConst _ | TLiteralString _ ->
      false

  (* Reference types in storage *)
  | TBytes (LStorage _)
  | TString (LStorage _)
  | TStruct (_, _, LStorage _)
  | TArray (_, _, LStorage _)
  | TArraySlice (_, LStorage _)
  | TMapping (_, _, LStorage _) ->
      true

  (* Reference types in memory *)
  | TBytes _ | TString _ | TStruct _ | TArray _ | TArraySlice _ ->
      false

  (* Mappings can not exist outside storage *)
  | TMapping (_, _, (LMemory | LCalldata)) ->
      failwith "Mapping can not have memory/calldata location"

  (* Tuple: has storage location if at least one member has *)
  | TTuple (tl) ->
      List.exists (function
          | None -> false
          | Some (t) -> is_storage_type t
        ) tl

  (* TON-specific *)
  | TTvmCell | TTvmSlice | TTvmBuilder | TExtraCurrencyCollection ->
      false
  | TOptional (t) ->
      is_storage_type t




let is_tuple = function
  | TTuple _ -> true
  | _ -> false




(* Turn storage pointer to storage ref *)
let promote_loc : location -> location =
  function
  | LMemory ->
      LMemory
  | LCalldata ->
      LCalldata
  | LStorage (_) ->
      LStorage (false)

(* Turn storage ref to storage pointer *)
let unpromote_loc : location -> location =
  function
  | LMemory ->
      LMemory
  | LCalldata ->
      LCalldata
  | LStorage (_) ->
      LStorage (true)

(* only needed to determine inferred types for variable *)
(* this basically turns storage ref to storage pointer on the root type *)
(* child types with storage location are assumed to be storage ref *)
let rec unpromote_type : type_ -> type_ = function
  | TString (loc) ->
      TString (unpromote_loc loc)
  | TBytes (loc) ->
      TBytes (unpromote_loc loc)
  | TStruct (lid, sd, loc) ->
      TStruct (lid, sd, unpromote_loc loc)
  | TArray (t, sz_opt, loc) ->
      TArray (t, sz_opt, unpromote_loc loc)
  | TArraySlice (t, loc) ->
      TArraySlice (t, unpromote_loc loc)
  | TMapping (tk, tv, loc) ->
      TMapping (tk, tv, unpromote_loc loc)
  | TTuple (tl) ->
      TTuple (List.map (Option.map unpromote_type) tl)
  | t ->
      t

(* only needed to determine the type of immediate array elements *)
(* and to change location of structure fields *)
(* whenever the root becomes storage *, child become storage ref *)
let rec change_type_location loc : type_ -> type_ = function
  | TString (_loc) ->
      TString (loc)
  | TBytes (_loc) ->
      TBytes (loc)
  | TStruct (lid, sd, _loc) ->
      TStruct (lid, {
          sd with struct_fields =
                    List.map (fun (id, t) ->
                        (id, change_type_location (promote_loc loc) t)
                      ) sd.struct_fields }, loc)
  | TArray (t, sz_opt, _loc) ->
      TArray (change_type_location (promote_loc loc) t, sz_opt, loc)
  | TArraySlice (t, _loc) ->
      TArraySlice (change_type_location (promote_loc loc) t, loc)
  | TMapping (tk, tv, _loc) ->
      TMapping (tk, change_type_location (promote_loc loc) tv, loc)
  | TTuple (tl) ->
      TTuple (List.map (Option.map (change_type_location loc)) tl)
  | t ->
      t

let get_type_location pos : type_ -> location = function
  | TString (loc) -> loc
  | TBytes (loc) -> loc
  | TStruct (_lid, _sd, loc) -> loc
  | TArray (_t, _sz_opt, loc) -> loc
  | TArraySlice (_t, loc) -> loc
  | TMapping (_tk, _tv, loc) -> loc
  | TTuple (_tl) -> error pos "Unexpected tuple type"
  | _t -> LMemory


