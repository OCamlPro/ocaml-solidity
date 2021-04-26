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
open Solidity_exceptions

let error = type_error

let register id p f_desc =
  Solidity_common.add_primitive id p;
  Solidity_tenv.add_primitive_desc id f_desc

let make_fun = Solidity_type_builder.primitive_fun

let make_var = Solidity_type_builder.primitive_var

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
           Some (make_fun [TBool] [] MPure)
       | _ -> None);

  register 2
    { prim_name = "require";
      prim_kind = PrimFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | None, Some ((AList [_] | ANamed [_])) ->
           Some (make_fun [TBool] [] MPure)
       | None, Some ((AList [_;_] | ANamed [_;_])) ->
           Some (make_fun [TBool; TString LMemory] [] MPure)
       | _ -> None);

  register 3
    { prim_name = "revert";
      prim_kind = PrimFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | None, Some ((AList [] | ANamed [])) ->
           Some (make_fun [] [] MPure)
       | None, Some ((AList [_] | ANamed [_])) ->
           Some (make_fun [TString LMemory] [] MPure)
       | _ -> None);

  (* Block/transaction properties *)

  register 4
    { prim_name = "blockhash";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TUint 256] [TFixBytes 32] MView)
       | _ -> None);

  register 5
    { prim_name = "gasleft";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [] [TUint 256] MView)
       | _ -> None);

  register 6
    { prim_name = "block";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TMagic (TBlock)))
       | _ -> None);

  register 7
    { prim_name = "coinbase";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (make_var (TAddress (true)))
       | _ -> None);

  register 8
    { prim_name = "difficulty";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (make_var (TUint 256))
       | _ -> None);

  register 9
    { prim_name = "gaslimit";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (make_var (TUint 256))
       | _ -> None);

  register 10
    { prim_name = "number";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (make_var (TUint 256))
       | _ -> None);

  register 11
    { prim_name = "timestamp";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (make_var (TUint 256))
       | _ -> None);

  register 12
    { prim_name = "msg";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TMagic (TMsg)))
       | _ -> None);

  register 13
    { prim_name = "data";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMsg)) -> Some (make_var (TBytes (LCalldata)))
       | _ -> None);

  register 14
    { prim_name = "sender";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMsg)) -> Some (make_var (TAddress (true)))
       | _ -> None);

  register 15
    { prim_name = "sig";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMsg)) -> Some (make_var (TFixBytes 4))
       | _ -> None);

  register 16
    { prim_name = "value";
      prim_kind = PrimMemberVariable }
    (fun pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMsg)) ->
           Some (make_var (TUint 256))
       | Some (TFunction (fd, _fo)) when is_external fd.function_visibility ->
           error pos "Using \".value(...)\" is deprecated. \
                      Use \"{value: ...}\" instead"
       | _ -> None);

  register 17
    { prim_name = "tx";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TMagic (TTx)))
       | _ -> None);

  register 18
    { prim_name = "gasprice";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTx)) -> Some (make_var (TUint 256))
       | _ -> None);

  register 19
    { prim_name = "origin";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTx)) -> Some (make_var (TAddress (true)))
       | _ -> None);

  (* ABI encoding/decoding *)

  register 20
    { prim_name = "abi";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TMagic (TAbi)))
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
           Some (make_fun atl rtl MPure)
       | _ -> None);

  register 22
    { prim_name = "encode";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       | Some (TMagic (TAbi)) ->
           let atl = preprocess_arg_0 pos (make_prim_args pos opt) in
           Some (make_fun atl [TBytes LMemory] MPure)
       | _ -> None);

  register 23
    { prim_name = "encodePacked";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       | Some (TMagic (TAbi)) ->
           let atl = preprocess_arg_0 pos (make_prim_args pos opt) in
           Some (make_fun atl [TBytes LMemory] MPure)
       | _ -> None);

  register 24
    { prim_name = "encodeWithSelector";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       | Some (TMagic (TAbi)) ->
           let atl = preprocess_arg_1 pos (TFixBytes 4)
               (make_prim_args pos opt) in
           Some (make_fun atl [TBytes LMemory] MPure)
       | _ -> None);

  register 25
    { prim_name = "encodeWithSignature";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       | Some (TMagic (TAbi)) ->
           let atl = preprocess_arg_1 pos (TString (LMemory))
               (make_prim_args pos opt) in
           Some (make_fun atl [TBytes LMemory] MPure)
       | _ -> None);


  (* Mathematical/cryptographic functions *)

  register 26
    { prim_name = "addmod";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TUint 256; TUint 256; TUint 256] [TUint 256] MPure)
       | _ -> None);

  register 27
    { prim_name = "mulmod";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TUint 256; TUint 256; TUint 256] [TUint 256] MPure)
       | _ -> None);

  register 28
    { prim_name = "keccak256";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TBytes LMemory] [TFixBytes 32] MPure)
       | _ -> None);

  register 29
    { prim_name = "sha256";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TBytes LMemory] [TFixBytes 32] MPure)
       | _ -> None);

  register 30
    { prim_name = "ripemd160";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TBytes LMemory] [TFixBytes 20] MPure)
       | _ -> None);

  register 31
    { prim_name = "ecrecover";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun
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
           Some (make_var (TContract (
                               c.contract_abs_name, c, false (* super *))))
       | _ ->
           None);

  register 33
    { prim_name = "super";
      prim_kind = PrimVariable }
    (fun _pos opt t_opt ->
       match t_opt, opt.current_contract with
       | None, Some (c) ->
           Some (make_var (TContract (
                               c.contract_abs_name, c, true (* super *))))
       | _ ->
           None);

  register 34
    { prim_name = "selfdestruct";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TAddress (true)] [] MNonPayable)
       | _ -> None);

  (* Members of address type *)

  register 35
    { prim_name = "balance";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (_)) ->
           Some (make_var (TUint 256))
       | _ -> None);

  register 36
    { prim_name = "transfer";
      prim_kind = PrimMemberFunction }
    (fun pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (true)) ->
           Some (make_fun [TUint 256] [] MNonPayable)
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
           Some (make_fun [TUint 256] [TBool] MNonPayable)
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
           Some (make_fun [TBytes (LMemory)] [TBool; TBytes (LMemory)] MPayable)
       | _ -> None);

  register 39
    { prim_name = "delegatecall";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (_)) ->
           Some (make_fun
                   [TBytes (LMemory)] [TBool; TBytes (LMemory)] MNonPayable)
       | _ -> None);

  register 40
    { prim_name = "staticcall";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (_)) ->
           Some (make_fun [TBytes (LMemory)] [TBool; TBytes (LMemory)] MView)
       | _ -> None);

  (* Type information (members of type) *)

  register 41
    { prim_name = "type";
      prim_kind = PrimFunction }
    (fun pos opt t_opt ->
       match t_opt, make_prim_args pos opt with
       | None, None ->
           Some (make_fun [] [] MPure)
       | None, Some ([TType ((TInt _ | TUint _ | TContract _) as t)]) ->
           Some (make_fun [TType (t)] [TMagic (TMetaType (t))] MPure)
       | None, Some (_) ->
           Some (make_fun [TType (TTuple [])] [] MPure)
       | _ -> None);

  register 42
    { prim_name = "name";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TContract (_, _, _)))) ->
           Some (make_var (TString (LMemory)))
       | _ -> None);

  register 43
    { prim_name = "creationCode";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TContract (_, _, _)))) ->
           Some (make_var (TBytes (LMemory)))
       | _ -> None);

  register 44
    { prim_name = "runtimeCode";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TContract (_, _, _)))) ->
           Some (make_var (TBytes (LMemory)))
       | _ -> None);

  register 45
    { prim_name = "interfaceId";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TContract (_, _, _)))) ->
           Some (make_var (TFixBytes (4)))
       | _ -> None);

  register 46
    { prim_name = "min";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TInt (_) | TUint (_) as t))) ->
           Some (make_var (t))
       | _ -> None);

  register 47
    { prim_name = "max";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TInt (_) | TUint (_) as t))) ->
           Some (make_var (t))
       | _ -> None);

  (* Members of array type *)

  register 48
    { prim_name = "length";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TArray (_) | TBytes (_)) ->
           Some (make_var (TUint 256))
       | Some (TFixBytes (_)) ->
           Some (make_var (TUint 8))
       | _ -> None);

  register 49
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
           Some (make_fun ~returns_lvalue:true [] [t] MNonPayable)
       | Some (TArray (t, None, (LStorage _))),
         Some (_) ->
           (* Note: since push only works on storage arrays,
              the argument has a location of storage ref *)
           let t =
             Solidity_type.change_type_location (LStorage false) t in
           Some (make_fun [t] [] MNonPayable)
       | Some (TBytes (LStorage _)),
         (None | Some (AList [] | ANamed [])) ->
           Some (make_fun ~returns_lvalue:true [] [TFixBytes (1)] MNonPayable)
       | Some (TBytes (LStorage _)),
         Some (_) ->
           Some (make_fun [TFixBytes (1)] [] MNonPayable)
       | _ -> None);

  register 50
    { prim_name = "pop";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TArray (_, None, (LStorage _)) | TBytes (LStorage _)) ->
           Some (make_fun [] [] MNonPayable)
       | _ -> None);

  (* Members of function type *)

  register 51
    { prim_name = "address";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TFunction (fd, _fo)) when is_external fd.function_visibility ->
           Some (make_var (TAddress (false)))
       | _ -> None);

  register 52
    { prim_name = "selector";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TFunction (fd, _fo)) when is_external fd.function_visibility ->
           Some (make_var (TFixBytes (4)))
       | _ -> None);

  register 53
    { prim_name = "gas";
      prim_kind = PrimMemberFunction }
    (fun pos _opt t_opt ->
       match t_opt with
       | Some (TFunction (fd, _fo)) when is_external fd.function_visibility ->
           error pos "Using \".gas(...)\" is deprecated. \
                      Use \"{gas: ...}\" instead"
       | _ -> None);

  ()

let init () =
  register_primitives ()
