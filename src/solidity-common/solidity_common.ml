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

type pos = string * (int * int) * (int * int)

let dummy_pos = "", (-1, -1), (-1, -1)

exception GenericError of string

let error fmt =
  Format.kasprintf (fun s -> raise (GenericError s)) fmt

type relative = [`Relative]
type absolute = [`Absolute]

module ExtMap = struct
  module type OrderedType = sig
    type t
    val compare : t -> t -> int
    val to_string : t -> string
  end
  module type S = sig
    include Map.S
    val of_bindings : (key * 'a) list -> 'a t
    val map_fold : ('a -> 'b -> 'a * 'c) -> 'a -> 'b t -> 'a * 'c t
    val add_uniq_opt : key -> 'a -> 'a t -> 'a t option
    val add_uniq : key -> 'a -> 'a t -> 'a t
  end
  module Make (Ord : OrderedType) : S with type key = Ord.t = struct
    include Map.Make (Ord)

    let of_bindings list =
      List.fold_left (fun map (key, v) -> add key v map) empty list

    let map_fold f a m =
      fold (fun k b (a, m) ->
          let a, c = f a b in
          a, add k c m
        ) m (a, empty)

    let add_uniq_opt key v map =
      if mem key map then
        None
      else
        Some (add key v map)

    let add_uniq key v map =
      match add_uniq_opt key v map with
      | None -> error "ExtMap.add_uniq %S: not uniq" (Ord.to_string key)
      | Some map -> map
  end

end

module ZMap = ExtMap.Make (Z)

module ZSet = Set.Make (Z)

module IntMap = ExtMap.Make (struct
    type t = int
    let compare = Stdlib.compare
    let to_string = string_of_int
  end)

module StringMap = ExtMap.Make (struct
    type t = string
    let compare = String.compare
    let to_string s = s
  end)

module StringSet = Set.Make (String)

module Ident = struct
  type t = string
  let compare = String.compare
  let equal = String.equal
  let root i = Format.sprintf "@%d" i
  let to_string id = id
  let of_string id = id
  let printf fmt id = Format.fprintf fmt "%s" id
  let constructor = "#"
  let onBounce = "!"
  let receive = "@"
  let fallback = "*"
end

module LongIdent = struct

  type 'kind t = Ident.t list

  let rec compare lid1 lid2 =
    match lid1, lid2 with
    | [], [] -> 0
    | [], _ :: _ -> -1
    | _ :: _, [] -> 1
    | id1 :: lid1, id2 :: lid2 ->
        let res = Ident.compare id1 id2 in
        if res <> 0 then res
        else compare lid1 lid2

  let equal lid1 lid2 =
    compare lid1 lid2 = 0

  let empty = []

  let root i = [Ident.root i]

  let to_string lid = String.concat "." lid

  let of_string_rel lid = String.split_on_char '.' lid

  let of_string_abs lid = String.split_on_char '.' lid

  let of_ident_rel id = [id]

  let of_ident_abs id = [id]

  let to_ident_list idl = idl

  let of_ident_list_rel idl = idl

  let of_ident_list_abs idl = idl

  let append lid id = lid @ [id]

  let prepend id lid = id :: lid

  let is_empty lid =
    match lid with
    | [] -> true
    | _ -> false

  let first lid =
    match lid with
    | id :: _ -> id
    | _ -> error "LongIdent.first: invalid long identifier"

  let last lid =
    match List.rev lid with
    | id :: _ -> id
    | _ -> error "LongIdent.last: invalid long identifier"

  let split_first lid =
    match lid with
    | id :: lid -> id, lid
    | _ -> error "LongIdent.split_first: invalid long identifier"

  let split_last lid =
    match List.rev lid with
    | id :: rlid -> List.rev rlid, id
    | _ -> error "LongIdent.split_last: invalid long identifier"

  let printf fmt lid =
    Format.fprintf fmt "%s" (to_string lid)

end

module IdentMap = ExtMap.Make (Ident)

module IdentAList = struct
  type 'a t = (Ident.t * 'a) list

  let length = List.length
  let rev = List.rev
  let mem = List.mem_assoc
  let find_opt = List.assoc_opt

  let map f list =
    List.map (fun (key, v) -> (key, f v)) list

  let fold_left f acc list =
    List.fold_left (fun acc (key, v) -> f acc key v) acc list

  let add_uniq key v list =
    if mem key list then error "Identifier %s already declared" key;
    (key, v) :: list
end

module IdentSet = Set.Make (Ident)

module AbsLongIdentMap = ExtMap.Make (struct
    type t = absolute LongIdent.t
    let compare = LongIdent.compare
    let to_string = LongIdent.to_string
  end)

module RelLongIdentMap = ExtMap.Make (struct
    type t = relative LongIdent.t
    let compare = LongIdent.compare
    let to_string = LongIdent.to_string
  end)

module AbsLongIdentSet = Set.Make (struct
    type t = absolute LongIdent.t
    let compare = LongIdent.compare
  end)

module RelLongIdentSet = Set.Make (struct
    type t = relative LongIdent.t
    let compare = LongIdent.compare
  end)

module ExtList = struct
  include List

  let is_empty = function
    | [] -> true
    | _ -> false

  let same_lengths l1 l2 =
    List.compare_lengths l1 l2 = 0

  let for_all2 f l1 l2 =
    same_lengths l1 l2 && List.for_all2 f l1 l2

  let rec iter3 f l1 l2 l3 =
    match (l1, l2, l3) with
    | ([], [], []) -> ()
    | (a1::l1, a2::l2, a3::l3) -> f a1 a2 a3; iter3 f l1 l2 l3
    | (_, _, _) -> invalid_arg "ExtList.iter3"

  let rec fold_left3 f a l1 l2 l3 =
    match (l1, l2, l3) with
    | ([], [], []) -> a
    | (a1::l1, a2::l2, a3::l3) -> fold_left3 f (f a a1 a2 a3) l1 l2 l3
    | (_, _, _) -> invalid_arg "ExtList.fold_left3"

  let opt_fold_left f a l =
    List.fold_left (fun a b_opt ->
        match b_opt with
        | None -> a
        | Some b -> f a b
      ) a l

  let map_fold f a l =
    let a, l =
      List.fold_left (fun (a, l) b ->
          let a, c = f a b in
          a, c :: l
        ) (a, []) l
    in
    a, List.rev l

  let map_fold2 f a l1 l2 =
    let a, l =
      List.fold_left2 (fun (a, l) b c ->
          let a, d = f a b c in
          a, d :: l
        ) (a, []) l1 l2
    in
    a, List.rev l

  let rec compare cmp l1 l2 =
    match l1, l2 with
    | [], [] -> 0
    | hd1 :: tl1, hd2 :: tl2 ->
       let hd_cmp = cmp hd1 hd2 in
       if hd_cmp = 0
       then compare cmp tl1 tl2
       else hd_cmp
    | [], _ -> -1
    | _, [] -> 1

  let find (type a) f f_err l : a =
    let exception Found of a in
    try
      List.iter (fun e ->
          match f e with
          | Some res -> raise (Found res)
          | None -> ()
        ) l;
      f_err ()
    with
      Found res -> res

  let pos f l =
    let exception Found of int in
    try
      let _ =
        List.fold_left (fun i e ->
            if f e then raise (Found i)
            else i + 1
          ) 0 l
      in
      None
    with
      Found res -> Some res


end

module ExtInt = struct

  let rec fold f s e a =
    if s <= e then
      fold f (s+1) e (f s a)
    else
      a

end

module ExtZ = struct

  let _2 = Z.of_int 2
  let _5 = Z.of_int 5
  let _7 = Z.of_int 7
  let _8 = Z.of_int 8
  let _10 = Z.of_int 10
  let _60 = Z.of_int 60
  let _255 = Z.of_int 255
  let _3600 = Z.of_int 3600
  let _24x3600 = Z.of_int (24 * 3600)
  let _7x24x3600 = Z.of_int (7 * 24 * 3600)
  let _365x24x3600 = Z.of_int (365 * 24 * 3600)
  let _10_3 = Z.pow _10 3
  let _10_6 = Z.pow _10 6
  let _10_9 = Z.pow _10 9
  let _10_12 = Z.pow _10 12
  let _10_15 = Z.pow _10 15
  let _10_18 = Z.pow _10 18

  let is_neg z =
    Z.sign z < 0

  let is_pos z =
    Z.sign z >= 0

  let rec fold f s e a =
    if s <= e then
      fold f (Z.succ s) e (f s a)
    else
      a

  let numbits_mod8 z =
    let nb = Z.min Z.one (Z.of_int (Z.numbits z)) in
    Z.to_int (Z.mul (Z.div (Z.add nb _7) _8) _8)

  let num_zeros z =
    let n = ref 0 in
    let r = ref (snd (Z.ediv_rem z _10)) in
    while not (Z.equal !r Z.zero) do
      n := !n + 1;
      r := snd (Z.ediv_rem z _10)
    done;
    !n

  let of_binary b =
    let res = ref Z.zero in
    let l = String.length b in
    for i = 0 to (l-1) do
      let v = Z.of_int (Char.code (b.[i])) in
      res := Z.add (Z.shift_left !res 8) v
    done;
    !res

  let to_binary sz z =
    (* Invariant: a buffer of sz bytes should be large enough to store Z *)
    let res = Bytes.create sz in
    let z = ref z in
    for i = sz-1 downto 0 do
      Bytes.set_int8 res i (Z.to_int (Z.logand !z _255));
      z := Z.shift_right !z 8;
    done;
    Bytes.to_string res

  let print_hex fmt z =
    let s = to_binary (numbits_mod8 z) z in
    for i = 0 to (String.length s - 1) do
      Format.fprintf fmt "%02x" (Char.code (s.[i]))
    done

  include Z

end

module ExtQ = struct

  let is_int q =
    Z.equal Z.one (Q.den q)

  let is_neg q =
    Q.sign q < 0

  let is_pos q =
    Q.sign q >= 0

  let to_fixed_with_dec dec q =
    let n = Q.num q in
    let d = Q.den q in
    let z, r = Z.ediv_rem (Z.mul n (Z.pow ExtZ._10 dec)) d in
    (* properly handle rounding *)
    if (Z.mul r ExtZ._2 < d) then z
    else Z.succ z

  let to_fixed q =
    let z = to_fixed_with_dec 80 q in
    if Z.equal Z.zero z then z, 0
    else
      let nz = ExtZ.num_zeros z in
      Z.mul z (Z.pow ExtZ._10 nz), (80 - nz)

  include Q

end



type annot = ..
type annot += ANone

type 'a node = {
  contents : 'a;
  mutable annot : annot;
  pos : pos;
}

let annot contents annot pos =
  { contents; annot; pos }

let strip n =
  n.contents

let get_annot n =
  n.annot

let string_of_pos (file, pos1, pos2)  =
  let source =
    try
      let line1 = fst pos1 in
      let line2 = fst pos2 in
      let lines = EzFile.read_lines file in
      let b = Buffer.create 1000 in
      Array.iteri (fun l line ->
          let l = l+1 in
          if l >= line1 - 3 && l < line2 + 3 then
            Printf.bprintf b "%4d %c %s\n" l
              (if l>=line1 && l<=line2 then '>' else ' ')
              line
        ) lines;
      Buffer.contents b
    with _ -> ""
  in
  Printf.sprintf "%s:%d-%d:%d-%d"
    file
    (fst pos1) (snd pos1)
    (fst pos2) (snd pos2),
  source

let set_annot n annot =
  match n.annot with
  | ANone -> n.annot <- annot
  | _ ->
      let loc, source = string_of_pos n.pos in
      error "%sNode annotation already set at %s" source loc

let replace_annot n annot =
  match n.annot with
  | ANone ->
      let loc, source = string_of_pos n.pos in
      error "%sNode annotation not set at %s" source loc
  | _ -> n.annot <- annot




let make_absolute_path base path =
  FilePath.reduce ~no_symlink:true @@
    if FilePath.is_relative path then
      FilePath.make_absolute base path
    else
      path




let is_some = function
  | Some _ -> true
  | None -> false

let is_none = function
  | None -> true
  | Some _ -> false



type primitive_kind =
  | PrimFunction
  | PrimMemberFunction
  | PrimVariable
  | PrimMemberVariable

type primitive = {
  prim_name : string;
  prim_kind : primitive_kind;
}

let max_primitives = 256
let max_prim_id = ref 0

let prim_by_id = Array.make (max_primitives + 1) None
let prim_by_name = ref StringMap.empty

let prim_of_id id : primitive option =
  prim_by_id.(id)

let prim_of_ident prim : (int * primitive) option =
  StringMap.find_opt (Ident.to_string prim) !prim_by_name

let add_primitive id p =
  if id < 0 then
    error "Negative primitive id";
  if id > max_primitives then
    error "Primitive id above limit";
  begin
    match prim_by_id.(id) with
    | None -> prim_by_id.(id) <- Some p;
    | Some _ -> error "Primitive id already defined"
  end;
  begin
    match prim_of_ident (Ident.of_string p.prim_name) with
    | None -> prim_by_name := StringMap.add p.prim_name (id, p) !prim_by_name
    | Some _ -> error "Primitive name already defined"
  end;
  if id > !max_prim_id then
    max_prim_id := id

let for_freeton = ref false
