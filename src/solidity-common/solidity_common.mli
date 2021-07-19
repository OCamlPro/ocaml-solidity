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

val dummy_pos : pos

exception GenericError of string

val error : ('a, Format.formatter, unit, 'b) format4 -> 'a

type relative = [`Relative]
type absolute = [`Absolute]

module ExtMap : sig
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
  module Make (Ord : OrderedType) : S with type key = Ord.t
end

module ZMap : ExtMap.S with type key = Z.t

module ZSet : Set.S with type elt = Z.t

module IntMap : ExtMap.S with type key = int

module StringMap : ExtMap.S with type key = string

module StringSet : Set.S with type elt = string

module Ident : sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val root : int -> t
  val to_string : t -> string
  val of_string : string -> t
  val printf : Format.formatter -> t -> unit
  val constructor : t
  val onBounce: t (* freeton *)
  val receive : t
  val fallback : t
end

module LongIdent : sig
  type 'kind t
  val compare : 'kind t -> 'kind t -> int
  val equal : 'kind t -> 'kind t -> bool
  val empty : 'kind t
  val root : int -> absolute t
  val to_string : 'kind t -> string
  val of_string_rel : string -> relative t
  val of_string_abs : string -> absolute t
  val of_ident_rel : Ident.t -> relative t
  val of_ident_abs : Ident.t -> absolute t
  val to_ident_list : 'kind t -> Ident.t list
  val of_ident_list_rel : Ident.t list -> relative t
  val of_ident_list_abs : Ident.t list -> absolute t
  val append : 'kind t -> Ident.t -> 'kind t
  val prepend : Ident.t -> relative t -> relative t
  val is_empty : 'kind t -> bool
  val first : 'kind t -> Ident.t
  val last : 'kind t -> Ident.t
  val split_first : 'kind t -> Ident.t * relative t
  val split_last : 'kind t -> 'kind t * Ident.t
  val printf : Format.formatter -> 'kind t -> unit
end

module IdentAList : sig
  type 'a t = (Ident.t * 'a) list
  val length : 'a t -> int
  val rev : 'a t -> 'a t
  val mem : 'a -> ('a * 'b) list -> bool
  val find_opt : 'a -> ('a * 'b) list -> 'b option
  val map : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
  val fold_left : ('a -> 'b -> 'c -> 'a) -> 'a -> ('b * 'c) list -> 'a
  val add_uniq : Ident.t -> 'a -> (Ident.t * 'a) list -> (Ident.t * 'a) list
end

module IdentMap : ExtMap.S with type key = Ident.t

module IdentSet : Set.S with type elt = Ident.t

module AbsLongIdentMap : ExtMap.S with type key = absolute LongIdent.t

module RelLongIdentMap : ExtMap.S with type key = relative LongIdent.t

module AbsLongIdentSet : Set.S with type elt = absolute LongIdent.t

module RelLongIdentSet : Set.S with type elt = relative LongIdent.t

module ExtList : sig
  include module type of List
  val is_empty : 'a list -> bool
  val same_lengths : 'a list -> 'b list -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val iter3 :
    ('a -> 'b -> 'c -> unit) -> 'a list -> 'b list -> 'c list -> unit
  val fold_left3 :
    ('a -> 'b -> 'c -> 'd -> 'a) ->
    'a -> 'b list -> 'c list -> 'd list -> 'a
  val opt_fold_left : ('a -> 'b -> 'a) -> 'a -> 'b option list -> 'a
  val map_fold : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  val map_fold2 :
    ('a -> 'b -> 'c -> 'a * 'd) ->
    'a -> 'b list -> 'c list -> 'a * 'd list
  val compare : ('a -> 'b -> int) -> 'a list -> 'b list -> int
  val find : ('a -> 'b option) -> (unit -> 'b) -> 'a list -> 'b
  val pos : ('a -> bool) -> 'a list -> int option
end

module ExtInt : sig
  val fold : (int -> 'a -> 'a) -> int -> int -> 'a -> 'a
end

module ExtZ : sig
  include (module type of Z with type t = Z.t)
  val _2 : Z.t
  val _5 : Z.t
  val _7 : Z.t
  val _8 : Z.t
  val _10 : Z.t
  val _60 : Z.t
  val _255 : Z.t
  val _3600 : Z.t
  val _24x3600 : Z.t
  val _7x24x3600 : Z.t
  val _365x24x3600 : Z.t
  val _10_3 : Z.t
  val _10_6 : Z.t
  val _10_9 : Z.t
  val _10_12 : Z.t
  val _10_15 : Z.t
  val _10_18 : Z.t
  val is_neg : Z.t -> bool
  val is_pos : Z.t -> bool
  val fold : (t -> 'a -> 'a) -> t -> t -> 'a -> 'a
  val numbits_mod8 : t -> int
  val of_binary : string -> Z.t
  val print_hex : Z.t -> string
end

module ExtQ : sig
  include (module type of Q with type t = Q.t)
  val is_int : Q.t -> bool
  val is_neg : Q.t -> bool
  val is_pos : Q.t -> bool
  val to_fixed_with_dec : int -> Q.t -> Z.t
  val to_fixed : Q.t -> Z.t * int
end



type annot = ..
type annot += ANone
type 'a node = { contents : 'a; mutable annot : annot; pos : pos }

val annot : 'a -> annot -> pos -> 'a node
val strip : 'a node -> 'a
val get_annot : 'a node -> annot
val set_annot : 'a node -> annot -> unit
val replace_annot : 'a node -> annot -> unit


val make_absolute_path : string -> string -> string


val is_some : 'a option -> bool
val is_none : 'a option -> bool


type primitive_kind =
  | PrimFunction
  | PrimMemberFunction
  | PrimVariable
  | PrimMemberVariable

type primitive = {
  prim_name : string;
  prim_kind : primitive_kind;
}

val max_primitives : int
val max_prim_id : int ref

val prim_of_id : int -> primitive option
val prim_of_ident : Ident.t -> (int * primitive) option

val add_primitive : int -> primitive -> unit

val for_freeton : bool ref

val string_of_pos : pos -> string * string

val to_pos : Lexing.position * Lexing.position -> pos
