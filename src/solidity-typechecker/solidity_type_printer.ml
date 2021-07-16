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
open Solidity_tenv
open Solidity_checker_TYPES

let string_of_location = function
  | LMemory ->          "memory"
  | LStorage (false) -> "storage ref"
  | LStorage (true) ->  "storage pointer"
  | LCalldata ->        "calldata"


let string_of_abstract_type = function
  | TvmCell -> "TvmCell"
  | TvmSlice -> "TvmSlice"
  | TvmBuilder -> "TvmBuilder"

let rec string_of_magic_type = function
  | TMetaType (t) -> Format.sprintf "type(%s)" (string_of_type t)
  | TMsg ->   "msg"
  | TBlock -> "block"
  | TTx ->    "tx"
  | TAbi ->   "msg"
  | TTvm ->   "tvm"
  | TStatic _ -> assert false

and string_of_type = function
  | TBool ->
      "bool"
  | TInt (sz)->
      Format.sprintf "int%d" sz
  | TUint (sz)->
      Format.sprintf "uint%d" sz
  | TFixed (sz, dec) ->
      Format.sprintf "fixed%dx%d" sz dec
  | TUfixed (sz, dec) ->
      Format.sprintf "ufixed%dx%d" sz dec
  | TAddress (false) ->
      "address"
  | TAddress (true) ->
      "address payable"
  | TFixBytes (sz) ->
      Format.sprintf "bytes%d" sz
  | TBytes (loc) ->
      Format.sprintf "bytes %s" (string_of_location loc)
  | TString (loc) ->
      Format.sprintf "string %s" (string_of_location loc)
  | TStruct (lid, _, loc) ->
      Format.sprintf "struct %s %s"
        (LongIdent.to_string lid) (string_of_location loc)
  | TEnum (lid, _) ->
      Format.sprintf "enum %s" (LongIdent.to_string lid)
  | TContract (lid, _, super) ->
      if super then
        Format.sprintf "contract super %s" (LongIdent.to_string lid)
      else
        Format.sprintf "contract %s" (LongIdent.to_string lid)
  | TArray (t, sz_opt, loc) ->
      Format.sprintf "%s[%s] %s"
        (string_of_type t)
        (match sz_opt with
         | None -> ""
         | Some i -> Z.to_string i)
        (string_of_location loc)
  | TMapping (tk, tv, _loc) -> (* Note: loc is only LStorage*)
      Format.sprintf "mapping (%s => %s)"
        (string_of_type tk) (string_of_type tv)
  | TFunction (fd, _fo) ->
      Format.sprintf "function(%s) %s%s %s"
        (string_of_param_list fd.function_params)
        (match fd.function_returns with
         | [] -> ""
         | rtl -> string_of_param_list rtl ^ " ")
        (Solidity_printer.string_of_fun_mutability fd.function_mutability)
        (match fd.function_visibility with
         | VExternal -> "external"
         | _ -> "")
  | TModifier (md) ->
      Format.sprintf "modifier(%s)" (string_of_param_list md.modifier_params)
  | TEvent (ed) ->
      Format.sprintf "event(%s)" (string_of_param_list ed.event_params)
  | TArraySlice (t, loc) ->
      Format.sprintf "%s[] %s" (string_of_type t) (string_of_location loc)
  | TType (t) ->
      Format.sprintf "type(%s)" (string_of_type t)
  | TMagic mt ->
      string_of_magic_type mt
  | TModule (_lid, md) ->
      Format.sprintf "module \"%s\"" md.module_file
  | TRationalConst (q, _) when ExtQ.is_int q ->
      Format.sprintf "int_const %s" (Q.to_string q)
  | TRationalConst (q, _) ->
      Format.sprintf "rational_const %s" (Q.to_string q)
  | TLiteralString (s) ->
      Format.sprintf "literal_string \"%s\"" s
  | TTuple (tl) ->
      Format.sprintf "(%s)"
        (String.concat ", " (List.map (function
             | Some (t) -> string_of_type t
             | None -> "") tl))

  | TAbstract abstract_type -> string_of_abstract_type abstract_type
  | TOptional t ->
      Printf.sprintf "optional(%s)"
        (string_of_type t)
  | TAny -> "'a"
  | TDots -> ".."

and string_of_param_list pl =
  String.concat "," (List.map (fun (t, _) -> string_of_type t) pl)

let storage_suffix library = function
  | LStorage (_) when library -> " storage"
  | _ -> ""

let string_of_type_canonical pos ~library t =
  let rec aux seen t =
    match t with
    | TBool ->
        "bool"
    | TInt (sz) ->
        Format.sprintf "int%d" sz
    | TUint (sz) ->
        Format.sprintf "uint%d" sz
    | TFixed (sz, dec) ->
        Format.sprintf "fixed%dx%d" sz dec
    | TUfixed (sz, dec) ->
        Format.sprintf "ufixed%dx%d" sz dec
    | TAddress (_) ->
        "address"
    | TFixBytes (sz)->
        Format.sprintf "bytes%d" sz
    | TBytes (l) ->
        Format.sprintf "bytes%s" (storage_suffix library l)
    | TString (l) ->
        Format.sprintf "string%s" (storage_suffix library l)
    | TArray (t, None, l) ->
        Format.sprintf "%s[]%s" (aux seen t) (storage_suffix library l)
    | TArray (t, Some sz, l) ->
        Format.sprintf "%s[%s]%s"
          (aux seen t) (Z.to_string sz) (storage_suffix library l)
    | TContract (lid, _cd, false) ->
        if library then
          LongIdent.to_string lid
        else
          "address"
    | TEnum (lid, ed) ->
        if library then
          LongIdent.to_string lid
        else
          let n = List.length ed.enum_values in
          let sz = ExtZ.numbits_mod8 (Z.of_int n) in
          Format.sprintf "uint%d" sz
    | TStruct (lid, sd, l) ->
        if AbsLongIdentSet.mem lid seen then
          error pos "Recursive type not allowed for \
                     public or external functions";
        let seen = AbsLongIdentSet.add lid seen in
        if library then
          Format.sprintf "%s%s"
            (LongIdent.to_string lid) (storage_suffix library l)
        else
          let tl = List.map (fun (_id, t) -> aux seen t) sd.struct_fields in
          Format.sprintf "(%s)" (String.concat "," tl)
    | TFunction (fd, _fd_opt) ->
        let tl = List.map (fun (t, _id) -> aux seen t) fd.function_params in
        Format.sprintf "function(%s)" (String.concat "," tl)
    | TMapping (t1, t2, _loc) -> (* Note: loc is only LStorage*)
        Format.sprintf "mapping(%s => %s) storage" (aux seen t1) (aux seen t2)
    | TContract (_, _, true)
    | TModifier (_)
    | TEvent (_)
    | TTuple (_)
    | TArraySlice (_)
    | TType (_)
    | TMagic (_)
    | TModule (_)
    | TRationalConst (_)
    | TLiteralString (_) ->
        error pos "Internal type can not be canonized"


    | TAbstract abstract_type -> string_of_abstract_type abstract_type
    | TOptional t ->
        Printf.sprintf "optional(%s)"
          ( aux seen t )
    | TAny -> assert false
    | TDots -> assert false
  in
  aux AbsLongIdentSet.empty t
