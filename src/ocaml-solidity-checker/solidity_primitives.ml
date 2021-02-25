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

let register id p f_type =
  Solidity_common.add_primitive id p;
  Solidity_tenv.add_primitive_type id f_type

let make_prim_args pos opt =
  match opt.call_args with
  | None -> None
  | Some (AList atl) ->
      Some (List.map (Solidity_type_conv.mobile_type pos) atl)
  | Some (ANamed _) ->
      error pos "Named arguments not allowed on primitive"

let preprocess_arg_0 _pos atl_opt =
  match atl_opt with
  | None -> []
  | Some (atl) -> atl

let preprocess_arg_1 pos t atl_opt =
  match atl_opt with
  | None -> []
  | Some (_ :: atl) -> t :: atl
  | Some ([]) ->
      error pos "Need at least 1 argument for function \
                 call, but provided only 0"

let register_primitives () =

  (* Error handling *)

  register 1
    { prim_name = "assert";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (Solidity_tenv.primitive_type [TBool] [] MPure)
       | _ -> None);

  register 2
    { prim_name = "require";
      prim_kind = PrimFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | None, Some ((AList [_] | ANamed [_])) ->
           Some (Solidity_tenv.primitive_type [TBool] [] MPure)
       | None, Some ((AList [_;_] | ANamed [_;_])) ->
           Some (Solidity_tenv.primitive_type [TBool; TString LMemory] [] MPure)
       | _ -> None);

  register 3
    { prim_name = "revert";
      prim_kind = PrimFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | None, Some ((AList [] | ANamed [])) ->
           Some (Solidity_tenv.primitive_type [] [] MPure)
       | None, Some ((AList [_] | ANamed [_])) ->
           Some (Solidity_tenv.primitive_type [TString LMemory] [] MPure)
       | _ -> None);

  (* Block/transaction properties *)

  register 4
    { prim_name = "blockhash";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (Solidity_tenv.primitive_type [TUint 256] [TFixBytes 32] MView)
       | _ -> None);

  register 5
    { prim_name = "gasleft";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (Solidity_tenv.primitive_type [] [TUint 256] MView)
       | _ -> None);

  register 6
    { prim_name = "block";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (TMagic (TBlock))
       | _ -> None);

  register 7
    { prim_name = "coinbase";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (TAddress (true))
       | _ -> None);

  register 8
    { prim_name = "difficulty";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (TUint 256)
       | _ -> None);

  register 9
    { prim_name = "gaslimit";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (TUint 256)
       | _ -> None);

  register 10
    { prim_name = "number";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (TUint 256)
       | _ -> None);

  register 11
    { prim_name = "timestamp";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (TUint 256)
       | _ -> None);

  register 12
    { prim_name = "msg";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (TMagic (TMsg))
       | _ -> None);

  register 13
    { prim_name = "data";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMsg)) -> Some (TBytes (LCalldata))
       | _ -> None);

  register 14
    { prim_name = "sender";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMsg)) -> Some (TAddress (true))
       | _ -> None);

  register 15
    { prim_name = "sig";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMsg)) -> Some (TFixBytes 4)
       | _ -> None);

  register 16
    { prim_name = "value";
      prim_kind = PrimMemberVariable }
    (fun pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMsg)) ->
           Some (TUint 256)
       | Some (TFunction (fd, _fo)) when is_external fd.function_visibility ->
           error pos "Using \".value(...)\" is deprecated. \
                      Use \"{value: ...}\" instead"
       | _ -> None);

  register 17
    { prim_name = "tx";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (TMagic (TTx))
       | _ -> None);

  register 18
    { prim_name = "gasprice";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTx)) -> Some (TUint 256)
       | _ -> None);

  register 19
    { prim_name = "origin";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTx)) -> Some (TAddress (true))
       | _ -> None);

  (* ABI encoding/decoding *)

  register 20
    { prim_name = "abi";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (TMagic (TAbi))
       | _ -> None);

  register 21
    { prim_name = "decode";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       | Some (TMagic (TAbi)) ->
           let atl, rtl =
             match make_prim_args pos opt with
             | None -> [], []
             | Some ([TBytes (LMemory|LCalldata); rt] as atl) ->
                 let rtl =
                   match rt with
                   | TTuple (rtl) -> rtl
                   | _ -> [Some (rt)]
                 in
                 let rtl =
                   List.map (function
                       | Some (TType (t)) ->
                           t
                       | Some (_t) ->
                           error pos "The second argument to abi.decode \
                                      has to be a tuple of types"
                       | None ->
                           error pos "Tuple component can not be empty"
                     ) rtl
                 in
                 atl, rtl
             | Some ([t1; _]) ->
                 error pos "The first argument to abi.decode must be \
                            implicitly convertible to bytes memory \
                            or bytes calldata, but is of type %s"
                   (Solidity_type_printer.string_of_type t1)
             | Some (atl) ->
                 error pos "This function takes two arguments, \
                            but %d were provided" (List.length atl)
           in
           Some (Solidity_tenv.primitive_type atl rtl MPure)
       | _ -> None);

  register 22
    { prim_name = "encode";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       | Some (TMagic (TAbi)) ->
           let atl = preprocess_arg_0 pos (make_prim_args pos opt) in
           Some (Solidity_tenv.primitive_type atl [TBytes LMemory] MPure)
       | _ -> None);

  register 23
    { prim_name = "encodePacked";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       | Some (TMagic (TAbi)) ->
           let atl = preprocess_arg_0 pos (make_prim_args pos opt) in
           Some (Solidity_tenv.primitive_type atl [TBytes LMemory] MPure)
       | _ -> None);

  register 24
    { prim_name = "encodeWithSelector";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       | Some (TMagic (TAbi)) ->
           let atl = preprocess_arg_1 pos (TFixBytes 4)
               (make_prim_args pos opt) in
           Some (Solidity_tenv.primitive_type atl [TBytes LMemory] MPure)
       | _ -> None);

  register 25
    { prim_name = "encodeWithSignature";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       | Some (TMagic (TAbi)) ->
           let atl = preprocess_arg_1 pos (TString (LMemory))
               (make_prim_args pos opt) in
           Some (Solidity_tenv.primitive_type atl [TBytes LMemory] MPure)
       | _ -> None);


  (* Mathematical/cryptographic functions *)

  register 26
    { prim_name = "addmod";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (Solidity_tenv.primitive_type
                   [TUint 256; TUint 256; TUint 256] [TUint 256] MPure)
       | _ -> None);

  register 27
    { prim_name = "mulmod";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (Solidity_tenv.primitive_type
                   [TUint 256; TUint 256; TUint 256] [TUint 256] MPure)
       | _ -> None);

  register 28
    { prim_name = "keccak256";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (Solidity_tenv.primitive_type
                   [TBytes LMemory] [TFixBytes 32] MPure)
       | _ -> None);

  register 29
    { prim_name = "sha256";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (Solidity_tenv.primitive_type
                   [TBytes LMemory] [TFixBytes 32] MPure)
       | _ -> None);

  register 30
    { prim_name = "ripemd160";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (Solidity_tenv.primitive_type
                   [TBytes LMemory] [TFixBytes 20] MPure)
       | _ -> None);

  register 31
    { prim_name = "ecrecover";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (Solidity_tenv.primitive_type
                   [TFixBytes 32; TUint 8; TFixBytes 32; TFixBytes 32]
                   [TAddress (false)] MPure)
       | _ -> None);

  (* Contract related *)

  register 32
    { prim_name = "this";
      prim_kind = PrimVariable }
    (fun _pos opt t_opt ->
       match t_opt, opt.current_contract with
       | None, Some (c) ->
           Some (TContract (c.contract_abs_name, c, false (* super *)))
       | _ ->
           None);

  register 33
    { prim_name = "super";
      prim_kind = PrimVariable }
    (fun _pos opt t_opt ->
       match t_opt, opt.current_contract with
       | None, Some (c) ->
           Some (TContract (c.contract_abs_name, c, true (* super *)))
       | _ ->
           None);

  register 34
    { prim_name = "selfdestruct";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (Solidity_tenv.primitive_type [TAddress (true)] [] MNonPayable)
       | _ -> None);

  (* Members of address type *)

  register 35
    { prim_name = "balance";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (_)) ->
           Some (TUint 256)
       | _ -> None);

  register 36
    { prim_name = "transfer";
      prim_kind = PrimMemberFunction }
    (fun pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (true)) ->
           Some (Solidity_tenv.primitive_type [TUint 256] [] MNonPayable)
       | Some (TAddress (false)) ->
           error pos "\"send\" and \"transfer\" are only available \
                      for objects of type \"address payable\", \
                      not \"address\""
       | _ -> None);

  register 37
    { prim_name = "send";
      prim_kind = PrimMemberFunction }
    (fun pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (true)) ->
           Some (Solidity_tenv.primitive_type
                   [TUint 256] [TBool] MNonPayable)
       | Some (TAddress (false)) ->
           error pos "\"send\" and \"transfer\" are only available \
                      for objects of type \"address payable\", \
                      not \"address\""
       | _ -> None);

  register 38
    { prim_name = "call";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (_)) ->
           Some (Solidity_tenv.primitive_type
                   [TBytes (LMemory)] [TBool; TBytes (LMemory)] MPayable)
       | _ -> None);

  register 39
    { prim_name = "delegatecall";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (_)) ->
           Some (Solidity_tenv.primitive_type
                   [TBytes (LMemory)] [TBool; TBytes (LMemory)] MNonPayable)
       | _ -> None);

  register 40
    { prim_name = "staticcall";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (_)) ->
           Some (Solidity_tenv.primitive_type
                   [TBytes (LMemory)] [TBool; TBytes (LMemory)] MView)
       | _ -> None);

  (* Type information (members of type) *)

  register 41
    { prim_name = "name";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TContract (_, _, _)))) ->
           Some (TString (LMemory))
       | _ -> None);

  register 42
    { prim_name = "creationCode";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TContract (_, _, _)))) ->
           Some (TBytes (LMemory))
       | _ -> None);

  register 43
    { prim_name = "runtimeCode";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TContract (_, _, _)))) ->
           Some (TBytes (LMemory))
       | _ -> None);

  register 44
    { prim_name = "interfaceId";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TContract (_, _, _)))) ->
           Some (TFixBytes (4))
       | _ -> None);

  register 45
    { prim_name = "min";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TInt (_) | TUint (_) as t))) ->
           Some (t)
       | _ -> None);

  register 46
    { prim_name = "max";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TInt (_) | TUint (_) as t))) ->
           Some (t)
       | _ -> None);

  register 47
    { prim_name = "length";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TArray (_) | TBytes (_)) ->
           Some (TUint 256)
       | Some (TFixBytes (_)) ->
           Some (TUint 8)
       | _ -> None);

  register 48
    { prim_name = "push";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TArray (t, None, (LStorage _))),
         (None | Some (AList [] | ANamed [])) ->
           (* Note: since push only works on storage arrays,
              the argument has a location of storage ref *)
           let t =
             Solidity_type.change_type_location (LStorage false) t in
           Some (Solidity_tenv.primitive_type ~returns_lvalue:true
                   [] [t] MNonPayable)
       | Some (TArray (t, None, (LStorage _))),
         Some (_) ->
           (* Note: since push only works on storage arrays,
              the argument has a location of storage ref *)
           let t =
             Solidity_type.change_type_location (LStorage false) t in
           Some (Solidity_tenv.primitive_type [t] [] MNonPayable)
       | Some (TBytes (LStorage _)),
         (None | Some (AList [] | ANamed [])) ->
           Some (Solidity_tenv.primitive_type ~returns_lvalue:true
                   [] [TFixBytes (1)] MNonPayable)
       | Some (TBytes (LStorage _)),
         Some (_) ->
           Some (Solidity_tenv.primitive_type [TFixBytes (1)] [] MNonPayable)
       | _ -> None);

  register 49
    { prim_name = "pop";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TArray (_, None, (LStorage _)) | TBytes (LStorage _)) ->
           Some (Solidity_tenv.primitive_type [] [] MNonPayable)
       | _ -> None);

  register 50
    { prim_name = "address";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TFunction (fd, _fo)) when is_external fd.function_visibility ->
           Some (TAddress (false))
       | _ -> None);

  register 51
    { prim_name = "selector";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TFunction (fd, _fo)) when is_external fd.function_visibility ->
           Some (TFixBytes (4))
       | _ -> None);

  register 52
    { prim_name = "gas";
      prim_kind = PrimMemberFunction }
    (fun pos _opt t_opt ->
       match t_opt with
       | Some (TFunction (fd, _fo)) when is_external fd.function_visibility ->
           error pos "Using \".gas(...)\" is deprecated. \
                      Use \"{gas: ...}\" instead"
       | _ -> None);

  (* Dune extension *)
  register 53
    { prim_name = "isqrt";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (Solidity_tenv.primitive_type
                   [TUint 256] [TUint 256] MPure)
       | _ -> None);

  (* Dune extension *)
  register 54
    { prim_name = "chainId";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (TFixBytes 4)
       | _ -> None);

  ()

let init () =
  register_primitives ()

(*
 (* FreeTON-specific *)

* TvmCell

<TvmCell>.depth() returns(uint64);
<TvmCell>.dataSize(uint n) returns (uint /*cells*/, uint /*bits*/, uint /*refs*/);
<TvmCell>.dataSizeQ(uint n) returns (optional(uint /*cells*/, uint /*bits*/, uint /*refs*/));
<TvmCell>.toSlice() returns (TvmSlice);

* TvmSlice

<TvmSlice>.size() returns (uint16 /*bits*/, uint8 /*refs*/);
<TvmSlice>.dataSize(uint n) returns (uint /*cells*/, uint /*bits*/, uint /*refs*/);
<TvmSlice>.dataSize(uint n) returns (optional(uint /*cells*/, uint /*bits*/, uint /*refs*/));
<TvmSlice>.bits() returns (uint16);
<TvmSlice>.refs() returns (uint8);
<TvmSlice>.depth() returns (uint64);
<TvmSlice>.decode(TypeA, TypeB, ...) returns (TypeA /*a*/, TypeB /*b*/, ...);
<TvmSlice>.loadRef() returns (TvmCell);
<TvmSlice>.loadRefAsSlice() returns (TvmSlice);
<TvmSlice>.loadSigned(uint16 bitSize) returns (int);
<TvmSlice>.loadSigned(uint16 bitSize) returns (uint);
<TvmSlice>.loadTons() returns (uint128);
<TvmSlice>.loadSlice(uint16 length) returns (TvmSlice);

// Decode parameters of the public function which doesn't return values
<TvmSlice>.decodeFunctionParams(functionName) returns (TypeA /*a*/, TypeB /*b*/, ...);

// Decode parameters of the public function which returns values
<TvmSlice>.decodeFunctionParams(functionName) returns (uint32 callbackFunctionId, TypeA /*a*/, TypeB /*b*/, ...);

// Decode constructor parameters
<TvmSlice>.decodeFunctionParams(ContractName) returns (TypeA /*a*/, TypeB /*b*/, ...);


* TvmBuilder

<TvmBuilder>.toSlice() returns (TvmSlice);
<TvmBuilder>.toCell() returns (TvmCell);
<TvmBuilder>.bits() returns (uint16);
<TvmBuilder>.refs() returns (uint8);
<TvmBuilder>.bitsAndRefs() returns (uint16 /*bits*/, uint8 /*refs*/);
<TvmBuilder>.remBits() returns (uint16);
<TvmBuilder>.remRefs() returns (uint8);
<TvmBuilder>.remBitsAndRefs() returns (uint16 /*bits*/, uint8 /*refs*/);
<TvmBuilder>.depth() returns (uint64);
<TvmBuilder>.store(/*list_of_values*/);
<TvmBuilder>.storeSigned(int256 value, uint16 bitSize);
<TvmBuilder>.storeUnsigned(uint256 value, uint16 bitSize);
<TvmBuilder>.storeRef(TvmBuilder refBuilder);
<TvmBuilder>.storeTons(uint128 value);

* ExtraCurrencyCollection

ExtraCurrencyCollection curCol;
uint32 key;
uint256 value;
optional(uint32, uint256) res = curCol.min();
optional(uint32, uint256) res = curCol.next(key);
optional(uint32, uint256) res = curCol.prev(key);
optional(uint32, uint256) res = curCol.nextOrEq(key);
optional(uint32, uint256) res = curCol.prevOrEq(key);
optional(uint32, uint256) res = curCol.delMin();
optional(uint32, uint256) res = curCol.delMax();
optional(uint256) optValue = curCol.fetch(key);
bool exists = curCol.exists(key);
bool isEmpty = curCol.empty();
bool success = curCol.replace(key, value);
bool success = curCol.add(key, value);
optional(uint256) res = curCol.getSet(key, value);
optional(uint256) res = curCol.getAdd(key, value);
optional(uint256) res = curCol.getReplace(key, value);
uint256 uintValue = curCol[index];


* optional(Type)

<optional(Type)>.hasValue() returns (bool);
<optional(Type)>.get() returns (Type);
<optional(Type)>.set(Type value);
<optional(Type)>.reset();


* <struct>

<struct>.unpack() returns (TypeA /*a*/, TypeB /*b*/, ...);


* <bytes>

<bytes>.operator[](uint8 index) returns (byte);
<bytes>.length returns (uint)
<bytes>.toSlice() returns (TvmSlice);
<bytes>.dataSize(uint n) returns (uint /*cells*/, uint /*bits*/, uint /*refs*/);
<bytes>.dataSizeQ(uint n) returns (optional(uint /*cells*/, uint /*bits*/, uint /*refs*/));


* <string>

<string>.byteLength() returns (uint8);
<string>.substr(uint8 from, uint8 count) returns (string);
<string>.append(string tail);
string(int value) returns (string);
hexstring(Type value) returns (string);
format(string template, TypeA a, TypeB b, ...) returns (string);
stoi(string inputStr) returns (uint /*result*/, bool /*status*/);


* address

address addrStd = address(address_value);
address addrStd = address.makeAddrStd(wid, address);
address addrNone = address.makeAddrNone();
address addrExtern = address.makeAddrExtern(addrNumber, bitCnt);
<address>.wid returns (int8);
<address>.value returns (uint);
address(this).balance returns (uint128);
address(this).currencies returns (ExtraCurrencyCollection);
<address>.getType() returns (uint8);
<address>.isStdZero() returns (bool);
<address>.isStdAddrWithoutAnyCast() returns (bool);
<address>.isExternZero() returns (bool);
<address>.isNone() returns (bool);
<address>.unpack() returns (int8 /*wid*/, uint256 /*value*/);
<address>.transfer(uint128 value, bool bounce, uint16 flag, TvmCell body, ExtraCurrencyCollection currencies);


* mapping

<map>.operator[](KeyType index) returns (ValueType);
<map>.operator[](KeyType index) returns (ValueType);
<map>.min() returns (optional(KeyType, ValueType));
<map>.max() returns (optional(KeyType, ValueType));
<map>.next(KeyType key) returns (optional(KeyType, ValueType));
<map>.prev(KeyType key) returns (optional(KeyType, ValueType));
<map>.nextOrEq(KeyType key) returns (optional(KeyType, ValueType));
<map>.prevOrEq(KeyType key) returns (optional(KeyType, ValueType));
<map>.delMin() returns (optional(KeyType, ValueType));
<map>.delMax() returns (optional(KeyType, ValueType));
<map>.fetch(KeyType key) returns (optional(ValueType));
<map>.exists(KeyType key) returns (bool);
<map>.empty() returns (bool);
<map>.replace(KeyType key, ValueType value) returns (bool);
<map>.add(KeyType key, ValueType value) returns (bool);
<map>.getSet(KeyType key, ValueType value) returns (optional(ValueType));
<map>.getAdd(KeyType key, ValueType value) returns (optional(ValueType));
<map>.getReplace(KeyType key, ValueType value) returns (optional(ValueType));


* function

require(bool condition, [uint errorCode = 100, [Type exceptionArgument]]);
revert(uint errorCode = 100, [Type exceptionArgument]);


* library

???


* pragmas

pragma ton-solidity
pragma ignoreIntOverflow;
pragma AbiHeader time/pubkey/expire;
pragma msgValue <value>;


* constant / static / public


* receive / fallback
* onBounce / onTickTock / onCodeUpgrade / afterSignatureCheck

* pure / view / (default)

* inline

* functionID (custom ID instead of hash)


* events

emit EventName(arguments).extAddr(address);
emit EventName(arguments);


function f(uint n) public pure {
    return{value: 0, flag: 64} n <= 1? 1 : n * f(n - 1);
}


...


* for ( range_declaration : range_expression ) loop_statement

* repeat( bool_condition ) statements

* extended return

* new options : code, stateInit + value, currencies, bounce, wid, flag

* selfdestruct(address dest_addr);

* sha256(TvmSlice slice) returns (uint256)






* msg

msg.value returns (uint128);
msg.currencies returns (ExtraCurrencyCollection);
msg.pubkey() returns (uint256);
msg.createdAt returns (uint32);
msg.data returns (TvmSlice);


* tvm

tvm.accept();
tvm.commit();
tvm.log(string log); / logtvm(string log);
tvm.setcode(TvmCell newCode);
tvm.transLT() returns (uint64);
tvm.configParam(uint8 paramNumber) returns (TypeA a, TypeB b, ...);
tvm.rawConfigParam(uint8 paramNumber) returns (TvmCell cell, bool status);
tvm.rawReserve(uint value,[ExtraCurrencyCollection currency,] uint8 flag);
tvm.hash(TvmCell cellTree) returns (uint256);
tvm.hash(string data) returns (uint256);
tvm.hash(bytes data) returns (uint256);
tvm.checkSign(uint256 hash, uint256 SignHighPart, uint256 SignLowPart, uint256 pubkey) returns (bool);
tvm.checkSign(uint256 hash, TvmSlice signature, uint256 pubkey) returns (bool);
tvm.checkSign(TvmSlice data, TvmSlice signature, uint256 pubkey) returns (bool);
tvm.insertPubkey(TvmCell stateInit, uint256 pubkey) returns (TvmCell);
tvm.buildStateInit(TvmCell code, TvmCell data) returns (TvmCell stateInit);
tvm.buildStateInit(TvmCell code, TvmCell data, uint8 splitDepth) returns (TvmCell stateInit);
tvm.buildStateInit({code: TvmCell code, data: TvmCell data, splitDepth: uint8 splitDepth,
    pubkey: uint256 pubkey, contr: contract Contract, varInit: {VarName0: varValue0, ...}});
tvm.buildEmptyData(uint256 publicKey) returns (TvmCell);
tvm.deploy(TvmCell stateInit, TvmCell payload, uint128 value, int8 wid) returns(address);
tvm.pubkey() returns (uint256);
tvm.setCurrentCode(TvmCell newCode);
tvm.resetStorage();
tvm.functionId(functionName) returns (uint32);
tvm.functionId(ContractName) returns (uint32);
tvm.encodeBody(function, arg0, arg1, arg2, ...) returns (TvmCell);
tvm.encodeBody(function, callbackFunction, arg0, arg1, arg2, ...) returns (TvmCell);
tvm.exit();
tvm.exit1();
tvm.buildExtMsg({
    dest: address,
    time: uint64,
    expire: uint32,
    call: {functionIdentifier [, list of function arguments]},
    sign: bool,
    pubkey: optional(uint256),
    abiVer: uint8,
    callbackId: uint32.
    onErrorId: uint32,
    stateInit: TvmCell
})


* math

math.min(int a, int b, ...) returns (int);
math.max(int a, int b, ...) returns (int);
math.min(uint a, uint b, ...) returns (uint);
math.max(uint a, uint b, ...) returns (uint);
math.minmax(uint, uint) returns (uint /*min*/, uint /*max*/);
math.minmax(int, int) returns (int /*min*/, int /*max*/);
math.abs(int val) returns (int);
math.modpow2(uint value, uint power) returns (uint);
math.divc(int a, int b) returns (int);
math.divr(int a, int b) returns (int);
math.muldiv(int a, int b, int c) returns (int);
math.muldivr(int a, int b, int c) returns (int);
math.muldivc(int a, int b, int c) returns (int);
math.muldivmod(T a, T b, T c) returns (T /*result*/, T /*remainder*/);
math.divmod(T a, T b) returns (T /*result*/, T /*remainder*/);


* tx

tx.timestamp returns (uint64);


* block

block.timestamp returns (uint64);


* rnd

rnd.next([Type mod]) returns (Type);
rnd.getSeed() returns (uint256);
rnd.setSeed(uint256 x);
rnd.shuffle(uint someNumber);
rnd.shuffle();





TvmCell (is value type)
TvmSlice (is value type)
TvmBuilder (is value type)
ExtraCurrencyCollection (is value type)
Optional<t> -> optional(t) (NOT a value type ; ref ?)

VarInteger ? (is value type)
initializerlisttype ? (is value type)
calllisttype ? (is value type)

MagicType : block, msg, tx, abi, +tvm, +math, +rnd


!! memory access modifiers have no effect in ton !

*)
