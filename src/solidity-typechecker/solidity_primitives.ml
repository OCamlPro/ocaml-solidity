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

module UTILS = struct

  let prim_id_cnt = ref 0
  let next_pid () = incr prim_id_cnt; !prim_id_cnt

  let register id p f_desc =
    Solidity_common.add_primitive id p;
    Solidity_tenv.add_primitive_desc id f_desc

  let primitive_fun_named ?(returns_lvalue=false)
      ?(purity=PurityPure)
      arg_type_opts ret_types function_mutability =
    Function { function_abs_name = LongIdent.empty;
               function_params = arg_type_opts;
               function_returns = List.map (fun t -> (t, None)) ret_types;
               function_returns_lvalue = returns_lvalue;
               function_visibility = VPublic;
               function_mutability;
               function_override = None;
               function_selector = None;
               function_is_method = false; (* can be true *)
               function_is_primitive = true;
               function_def = None;
               function_ops = [];
               function_purity = purity;
             }

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

  let is_numeric ty =
    match ty with
    | TInt _ | TUint _
    | TFixed _ | TUfixed _
    | TRationalConst _ -> true
    | _ -> false

  let to_upper_bound ty =
    match ty with
    | TInt _ -> TInt 256
    | TUint _ -> TUint 256
    | _ -> ty

end
open UTILS

let register_primitives ~(freeton: bool) () =

  (* Error handling *)

  register (next_pid ())
    { prim_name = "assert";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TBool] [] MPure)
       | _ -> None);

  register (next_pid ())
    { prim_name = "require";
      prim_kind = PrimFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       (* freeton/everscale:
          require(bool cond, int error_code);  *)
       | None, Some ((AList [_; (TInt _ | TUint _ | TRationalConst _)]))
         when freeton ->
           Some (make_fun [TBool; TUint 256] [] MPure)
       (* freeton/everscale:
          require(bool cond, int error_code; exceptionArgument arg);  *)
       | None, Some ((AList [_; (TInt _ | TUint _ | TRationalConst _); _]))
         when freeton ->
           Some (make_fun [TBool; TUint 256; TAny] [] MPure)

       | None, Some ((AList [_] | ANamed [_])) ->
           Some (make_fun [TBool] [] MPure)
       | None, Some ((AList [_;_] | ANamed [_;_])) ->
           Some (make_fun [TBool; TString LMemory] [] MPure)
       | _ -> None);

  register (next_pid ())
    { prim_name = "revert";
      prim_kind = PrimFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | None, Some (AList [_]) when freeton ->
           Some (make_fun [TUint 256] [] MPure)
       | None, Some (AList [_; _]) when freeton ->
           Some (make_fun [TUint 256; TAny] [] MPure)
       | None, Some ((AList [] | ANamed [])) ->
           Some (make_fun [] [] MPure)
       | None, Some ((AList [_] | ANamed [_])) ->
           Some (make_fun [TString LMemory] [] MPure)
       | _ -> None);

  (* Block/transaction properties *)

  register (next_pid ())
    { prim_name = "blockhash";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TUint 256] [TFixBytes 32] MView)
       | _ -> None);

  register (next_pid ())
    { prim_name = "gasleft";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [] [TUint 256] MView)
       | _ -> None);

  register (next_pid ())
    { prim_name = "block";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TMagic (TBlock)))
       | _ -> None);

  register (next_pid ())
    { prim_name = "coinbase";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (make_var (TAddress (true)))
       | _ -> None);

  register (next_pid ())
    { prim_name = "difficulty";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (make_var (TUint 256))
       | _ -> None);

  register (next_pid ())
    { prim_name = "gaslimit";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (make_var (TUint 256))
       | _ -> None);

  register (next_pid ())
    { prim_name = "number";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (make_var (TUint 256))
       | _ -> None);

  register (next_pid ())
    { prim_name = "timestamp";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TBlock)) -> Some (make_var (TUint 256))
       | Some (TMagic (TTx)) -> Some (make_var (TUint 256))
       | _ -> None);

  (*  the "now" keyword has been deprecated in solidity ^0.7.0 but it's still
      used in ton-solidity. It's an alias for "block.timestamp".
      And since ton-solidity 0.31 (2020-09-16)
        it returns a uint32 instead of a uint256 *)
  register (next_pid ())
    { prim_name = "now";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None when freeton -> Some (make_var (TUint 32))
       | _ -> None);

  register (next_pid ())
    { prim_name = "msg";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TMagic (TMsg)))
       | _ -> None);

  register (next_pid ())
    { prim_name = "data";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMsg)) -> Some (make_var (TBytes (LCalldata)))
       | _ -> None);

  register (next_pid ())
    { prim_name = "sender";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMsg)) -> Some (make_var (TAddress (true)))
       | _ -> None);

  register (next_pid ())
    { prim_name = "sig";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMsg)) -> Some (make_var (TFixBytes 4))
       | _ -> None);

  register (next_pid ())
    { prim_name = "value";
      prim_kind = PrimMemberVariable }
    (fun pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TMsg) when freeton ->
           Some (make_var (TUint 128))
       | Some (TAddress _) when freeton ->
           Some (make_var (TUint 256))
       | Some (TMagic (TMsg)) ->
           Some (make_var (TUint 256))
       | Some (TFunction (fd, _fo)) when is_external fd.function_visibility ->
           error pos "Using \".value(...)\" is deprecated. \
                      Use \"{value: ...}\" instead"
       | _ -> None);

  register (next_pid ())
    { prim_name = "tx";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TMagic (TTx)))
       | _ -> None);

  register (next_pid ())
    { prim_name = "gasprice";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTx)) -> Some (make_var (TUint 256))
       | _ -> None);

  register (next_pid ())
    { prim_name = "origin";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTx)) -> Some (make_var (TAddress (true)))
       | _ -> None);

  (* ABI encoding/decoding *)

  register (next_pid ())
    { prim_name = "abi";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TMagic (TAbi)))
       | _ -> None);

  register (next_pid ())
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
       | Some (TAbstract TvmSlice) when freeton ->
           let is_supported_type = function
             | TInt _ | TUint _ | TFixBytes _ | TBool | TUfixed _ | TFixed _
             | TAddress _ | TContract _ | TAbstract TvmCell | TBytes _ | TString _
             | TMapping _ | TArray _ | TOptional _ | TStruct _ -> true
             | _ -> false
           in
           (* <TvmSlice>.decode(TypeA, TypeB, ...) returns (TypeA, TypeB, ...) *)
           let rec aux = function
             | [] -> Some []
             | TType h :: t when is_supported_type h ->
                 begin match aux t with
                   | Some l -> Some (h :: l)
                   | None -> None
                 end
             | _ :: _ -> None
           in
           begin match opt.call_args with
             | Some (AList args) ->
                 begin match aux args with
                   | Some l ->
                       Some (make_fun args l MPure)
                   | _ ->
                       error pos
                         "<TvmSlice>.decode(...) expects types as arguments"
                 end
             | _ -> None
           end
       | _ -> None);

  register (next_pid ())
    { prim_name = "encode";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       | Some (TMagic (TAbi)) ->
           let atl = preprocess_arg_0 pos (make_prim_args pos opt) in
           Some (make_fun atl [TBytes LMemory] MPure)
       | _ -> None);

  register (next_pid ())
    { prim_name = "encodePacked";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       | Some (TMagic (TAbi)) ->
           let atl = preprocess_arg_0 pos (make_prim_args pos opt) in
           Some (make_fun atl [TBytes LMemory] MPure)
       | _ -> None);

  register (next_pid ())
    { prim_name = "encodeWithSelector";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       | Some (TMagic (TAbi)) ->
           let atl = preprocess_arg_1 pos (TFixBytes 4)
               (make_prim_args pos opt) in
           Some (make_fun atl [TBytes LMemory] MPure)
       | _ -> None);

  register (next_pid ())
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

  register (next_pid ())
    { prim_name = "addmod";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TUint 256; TUint 256; TUint 256] [TUint 256] MPure)
       | _ -> None);

  register (next_pid ())
    { prim_name = "mulmod";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TUint 256; TUint 256; TUint 256] [TUint 256] MPure)
       | _ -> None);

  register (next_pid ())
    { prim_name = "keccak256";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TBytes LMemory] [TFixBytes 32] MPure)
       | _ -> None);

  register (next_pid ())
    { prim_name = "sha256";
      prim_kind = PrimFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | None, Some (AList [TAbstract TvmSlice]) when freeton ->
           Some (make_fun [TAbstract TvmSlice] [TUint 256] MPure)
       | None, Some (AList [TBytes LMemory]) when freeton ->
           Some (make_fun [TBytes LMemory] [TUint 256] MPure)
       | None, Some (AList [TString LMemory]) when freeton ->
           Some (make_fun [TString LMemory] [TUint 256] MPure)
       | None, _ ->
           Some (make_fun [TBytes LMemory] [TFixBytes 32] MPure)
       | _ -> None);

  register (next_pid ())
    { prim_name = "ripemd160";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TBytes LMemory] [TFixBytes 20] MPure)
       | _ -> None);

  register (next_pid ())
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

  register (next_pid ())
    { prim_name = "this";
      prim_kind = PrimVariable }
    (fun _pos opt t_opt ->
       match t_opt, opt.current_contract with
       | None, Some (c) ->
           Some (make_var (TContract (
               c.contract_abs_name, c, false (* super *))))
       | _ ->
           None);

  register (next_pid ())
    { prim_name = "super";
      prim_kind = PrimVariable }
    (fun _pos opt t_opt ->
       match t_opt, opt.current_contract with
       | None, Some (c) ->
           Some (make_var (TContract (
               c.contract_abs_name, c, true (* super *))))
       | _ ->
           None);

  register (next_pid ())
    { prim_name = "selfdestruct";
      prim_kind = PrimFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None ->
           Some (make_fun [TAddress (true)] [] MNonPayable)
       | _ -> None);

  (* Members of address type *)

  register (next_pid ())
    { prim_name = "balance";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (_)) when freeton ->
           Some (make_var (TUint 128))
       | Some (TAddress (_)) ->
           Some (make_var (TUint 256))
       | _ -> None);

  register (next_pid ())
    { prim_name = "transfer";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt with
       (* <address>.transfer(uint128 value, bool bounce,
            uint16 flag, TvmCell body, ExtraCurrencyCollection currencies,
            TvmCell stateInit) *)
       | Some (TAddress _) when freeton ->
           begin
             match opt.call_args with
             | Some (AList [_])  ->
                 Some (make_fun [TUint 128] [] MNonPayable)
             | Some (AList [_; _]) ->
                 Some (make_fun [TUint 128; TBool] [] MNonPayable)
             | Some (AList [_; _; _]) ->
                 Some (make_fun [TUint 128; TBool; TUint 16] [] MNonPayable)
             | Some (AList [ _; _; _; _]) ->
                 Some (
                   make_fun
                     [TUint 128; TBool; TUint 16; TAbstract TvmCell]
                     [] MNonPayable
                 )
             | Some (AList [_; _; _; _; _]) ->
                 Some (
                   make_fun
                     [ TUint 128; TBool; TUint 16; TAbstract TvmCell;
                       TMapping (TUint 32, TUint 256, LStorage false)]
                     [] MNonPayable
                 )
             | Some (AList [_; _; _; _; _; _]) ->
                 Some (
                   make_fun
                     [ TUint 128; TBool; TUint 16; TAbstract TvmCell;
                       TMapping (TUint 32, TUint 256, LStorage false);
                       TAbstract TvmCell] [] MNonPayable
                 )

             | Some (ANamed args) ->
                 let pair_to_ty (id, ty) =
                   match Ident.to_string id, ty with
                   | "value", _ -> Some (TUint 128)
                   | "bounce", _ -> Some TBool
                   | "flag", _ -> Some (TUint 16)
                   | "body", _ -> Some (TAbstract TvmCell)
                   | "currencies", _ ->
                       Some (TMapping (TUint 32, TUint 256, LStorage false)) (*?*)
                   | "stateInit", _ -> Some (TAbstract TvmCell)
                   |  _ -> None
                 in
                 let ss =
                   StringSet.of_list
                     (List.map (fun (id, _) -> Ident.to_string id) args)
                 in
                 if StringSet.cardinal ss < List.length args
                 then error pos
                     "<address>.transfer(...): duplicated \
                      field in named parameters"
                 else
                 if StringSet.mem "value" ss
                 then
                   let supported_fields = StringSet.of_list [
                       "body"; "bounce"; "currencies";
                       "flag"; "stateInit"; "value" ]
                   in
                   StringSet.iter (
                     fun str ->
                       if StringSet.mem str supported_fields
                       then ()
                       else error pos
                           "<address>.transfer(...): unknown parameter \
                            \"%s\"" str
                   ) ss;
                   Some (
                     make_fun (
                       List.map (fun p -> Option.get (pair_to_ty p)) args
                     ) [] MNonPayable
                   )
                 else error pos
                     "<address>.transfer(...): missing \
                      mandatory parameter \"value\""
             | _ -> None
           end
       | Some (TAddress (true)) ->
           Some (make_fun [TUint 256] [] MNonPayable)
       | Some (TAddress (false)) ->
           error pos "\"send\" and \"transfer\" are only available \
                      for objects of type \"address payable\", \
                      not \"address\""
       | _ -> None);

  register (next_pid ())
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

  register (next_pid ())
    { prim_name = "call";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (_)) ->
           Some (make_fun [TBytes (LMemory)] [TBool; TBytes (LMemory)] MPayable)
       | _ -> None);

  register (next_pid ())
    { prim_name = "delegatecall";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (_)) ->
           Some (make_fun
                   [TBytes (LMemory)] [TBool; TBytes (LMemory)] MNonPayable)
       | _ -> None);

  register (next_pid ())
    { prim_name = "staticcall";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress (_)) ->
           Some (make_fun [TBytes (LMemory)] [TBool; TBytes (LMemory)] MView)
       | _ -> None);

  (* Type information (members of type) *)

  register (next_pid ())
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

  register (next_pid ())
    { prim_name = "name";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TContract (_, _, _)))) ->
           Some (make_var (TString (LMemory)))
       | _ -> None);

  register (next_pid ())
    { prim_name = "creationCode";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TContract (_, _, _)))) ->
           Some (make_var (TBytes (LMemory)))
       | _ -> None);

  register (next_pid ())
    { prim_name = "runtimeCode";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TContract (_, _, _)))) ->
           Some (make_var (TBytes (LMemory)))
       | _ -> None);

  register (next_pid ())
    { prim_name = "interfaceId";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TMetaType (TContract (_, _, _)))) ->
           Some (make_var (TFixBytes (4)))
       | _ -> None);

  register (next_pid ())
    { prim_name = "min";
      prim_kind = PrimMemberVariable }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic (TMetaType (TInt (_) | TUint (_) as t))), _ ->
           Some (make_var (t))
       (* math.min(T a, T b, ...) returns (T) *)
       (* PrimMemberFunction *)
       | Some (TMagic TMath), Some (AList ((_ :: _) as args)) when freeton ->
           let n_args = List.map to_upper_bound args in
           begin match n_args with
             | arg_l_hd :: arg_l_tl ->
                 if is_numeric arg_l_hd &&
                    List.for_all ((=) arg_l_hd) arg_l_tl
                 then None
                 else Some (make_fun n_args [arg_l_hd] MPure)
             | _ -> None
           end
       (* <map>.min() returns (optional(KeyType, ValueType)) *)
       (* PrimMemberFunction *)
       | Some (TMapping (ty1, ty2, _)), _ when freeton ->
           Some (make_fun [] [TOptional (TTuple [Some ty1; Some ty2])] MView)
       | _ -> None);

  register (next_pid ())
    { prim_name = "max";
      prim_kind = PrimMemberVariable }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic (TMetaType (TInt (_) | TUint (_) as t))), _ ->
           Some (make_var (t))
       (* math.max(T a, T b, ...) returns (T)  *)
       (* PrimMemberFunction *)
       | Some (TMagic TMath), Some (AList ((_ :: _) as args)) when freeton ->
           let n_args = List.map to_upper_bound args in
           begin match n_args with
             | arg_l_hd :: arg_l_tl ->
                 if is_numeric arg_l_hd &&
                    List.for_all ((=) arg_l_hd) arg_l_tl
                 then None
                 else Some (make_fun n_args [arg_l_hd] MPure)
             | _ -> None
           end
       (* <map>.max() returns (optional(KeyType, ValueType)) *)
       (* PrimMemberFunction *)
       | Some (TMapping (ty1, ty2, _)), _ when freeton ->
           Some (make_fun [] [TOptional (TTuple [Some ty1; Some ty2])] MView)
       | _ -> None);

  (* Members of array type *)

  register (next_pid ())
    { prim_name = "length";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TArray (_) | TBytes (_)) ->
           Some (make_var (TUint 256))
       | Some (TFixBytes (_)) ->
           Some (make_var (TUint 8))
       | _ -> None);

  register (next_pid ())
    { prim_name = "push";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TArray (t, _, LMemory)), Some _ when freeton ->
           Some (make_fun [t] [] MNonPayable)
       | Some (TBytes (LStorage _)), Some _ when freeton->
           Some (make_fun [TFixBytes (1)] [] MNonPayable)
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

  register (next_pid ())
    { prim_name = "pop";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TArray (_, _, LMemory) | TBytes LMemory) when freeton ->
           Some (make_fun [] [] MNonPayable)
       | Some (TArray (_, None, (LStorage _)) | TBytes (LStorage _)) ->
           Some (make_fun [] [] MNonPayable)
       | _ -> None);

  (* Members of function type *)

  register (next_pid ())
    { prim_name = "address";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TFunction (fd, _fo)) when is_external fd.function_visibility ->
           Some (make_var (TAddress (false)))
       | _ -> None);

  register (next_pid ())
    { prim_name = "selector";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TFunction (fd, _fo)) when is_external fd.function_visibility ->
           Some (make_var (TFixBytes (4)))
       | _ -> None);

  register (next_pid ())
    { prim_name = "gas";
      prim_kind = PrimMemberFunction }
    (fun pos _opt t_opt ->
       match t_opt with
       | Some (TFunction (fd, _fo)) when is_external fd.function_visibility ->
           error pos "Using \".gas(...)\" is deprecated. \
                      Use \"{gas: ...}\" instead"
       | _ -> None);
  ()

let register_additional_freeton_primitives () =
  (* Evescale/Freeton specific primitives *)

  (* address.makeAddrStd() *)
  register (next_pid ())
    { prim_name = "makeAddrStd";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TType (TAddress _)) ->
           Some (make_fun [TInt 8; TUint 256] [TAddress true] MPure)
       | _ -> None);

  (* address.makeAddrNone() *)
  register (next_pid ())
    { prim_name = "makeAddrNone";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TType (TAddress _)) ->
           Some (make_fun [] [TAddress true] MPure)
       | _ -> None);

  (* address.makeAddrExtern() *)
  register (next_pid ())
    { prim_name = "makeAddrExtern";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TType (TAddress _)) ->
           Some (make_fun [TUint 256; TUint 256] [TAddress true] MPure)
       | _ -> None);

  (* TvmCell *)
  register (next_pid ())
    { prim_name = "TvmCell";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TAbstract TvmCell))
       | _ -> None);

  (* TvmSlice *)
  register (next_pid ())
    { prim_name = "TvmSlice";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TAbstract TvmSlice))
       | _ -> None);

  (* TvmBuilder *)
  register (next_pid ())
    { prim_name = "TvmBuilder";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TAbstract TvmBuilder))
       | _ -> None);

  (*  <TvmCell>.depth() returns(uint16)
      <TvmSlice>.depth() returns (uint16)
      <TvmBuilder>.depth() returns (uint16)*)
  register (next_pid ())
    { prim_name = "depth";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmCell) ->
           Some (make_fun [] [TUint 16] MView)
       | Some (TAbstract TvmSlice) ->
           Some (make_fun [] [TUint 16] MView)
       | Some (TAbstract TvmBuilder) ->
           Some (make_fun [] [TUint 16] MView)
       | _ -> None);

  (*  <TvmCell>.dataSize(uint n) returns (uint, uint, uint)
      <TvmSlice>.dataSize(uint n) returns (uint, uint, uint)
      <bytes>.dataSize(uint n) returns (uint, uint, uint)*)
  register (next_pid ())
    { prim_name = "dataSize";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmCell | TAbstract TvmSlice | TBytes _) ->
           Some (make_fun [TUint 256] [TUint 256; TUint 256; TUint 256] MView)
       | _ -> None);

  (*  <TvmCell>.dataSizeQ(uint n) returns (optional(uint, uint, uint))
      <TvmSlice>.dataSizeQ(uint n) returns (optional(uint, uint, uint))
      <bytes>.dataSizeQ(uint n) returns (optional(uint, uint, uint));
  *)
  register (next_pid ())
    { prim_name = "dataSizeQ";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmCell | TAbstract TvmSlice | TBytes _) ->
           Some (
             make_fun [TUint 256]
               [ TOptional (
                     TTuple
                       [Some (TUint 256); Some (TUint 256); Some (TUint 256)]
                   )
               ] MView
           )
       | _ -> None);

  (* <TvmCell>.toSlice() returns (TvmSlice)
     <TvmBuilder>.toSlice() returns (TvmSlice)
     <bytes>.toSlice() returns (TvmSlice) *)
  register (next_pid ())
    { prim_name = "toSlice";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmCell | TAbstract TvmBuilder | TBytes _) ->
           Some (make_fun [] [TAbstract TvmSlice] MNonPayable) (*?*)
       | _ -> None);

  (* <TvmBuilder>.toCell() returns (TvmCell) *)
  register (next_pid ())
    { prim_name = "toCell";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmBuilder) ->
           Some (make_fun [] [TAbstract TvmCell] MNonPayable) (*?*)
       | _ -> None);

  (*  <TvmSlice>.empty() returns (bool)
      <array>.empty() returns (bool)
      <bytes>.empty() returns (bool)
      <string>.empty() returns (bool)
      <map>.empty() returns (bool)
  *)
  register (next_pid ())
    { prim_name = "empty";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (
           TArray _ | TBytes _ | TString _ |
           TAbstract TvmSlice | TMapping (_, _, _)
         ) ->
           Some (make_fun [] [TBool] MView)
       | _ -> None);

  (*  <TvmSlice>.size() returns (uint16, uint8)
      <TvmBuilder>.size() returns (uint16, uint8) *)
  register (next_pid ())
    { prim_name = "size";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmSlice | TAbstract TvmBuilder) ->
           Some (make_fun [] [TUint 16; TUint 8] MView)
       | _ -> None);

  (*  <TvmSlice>.bits() returns (uint16)
      <TvmBuilder>.bits() returns (uint16) *)
  register (next_pid ())
    { prim_name = "bits";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmSlice | TAbstract TvmBuilder) ->
           Some (make_fun [] [TUint 16] MView)
       | _ -> None);

  (*  <TvmSlice>.refs() returns (uint8)
      <TvmBuilder>.refs() returns (uint8) *)
  register (next_pid ())
    { prim_name = "refs";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmSlice | TAbstract TvmBuilder) ->
           Some (make_fun [] [TUint 8] MView)
       | _ -> None);

  (* <TvmSlice>.hasNBits(uint16 bits) returns (bool) *)
  register (next_pid ())
    { prim_name = "hasNBits";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmSlice) ->
           Some (make_fun [TUint 16] [TBool] MView)
       | _ -> None);

  (* <TvmSlice>.hasNRefs(uint8 refs) returns (bool) *)
  register (next_pid ())
    { prim_name = "hasNRefs";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmSlice) ->
           Some (make_fun [TUint 8] [TBool] MView)
       | _ -> None);

  (* <TvmSlice>.hasNBitsAndRefs(uint16 bits, uint8 refs) returns (bool) *)
  register (next_pid ())
    { prim_name = "hasNBitsAndRefs";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmSlice) ->
           Some (make_fun [TUint 16; TUint 8] [TBool] MView)
       | _ -> None);

  (* <TvmSlice>.compare(TvmSlice other) returns (int8) *)
  register (next_pid ())
    { prim_name = "compare";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmSlice) ->
           Some (make_fun [TAbstract TvmSlice] [TInt 8] MView)
       | _ -> None);

  (* <TvmSlice>.loadRef() returns (TvmCell) *)
  register (next_pid ())
    { prim_name = "loadRef";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmSlice) ->
           Some (make_fun [] [TAbstract TvmCell] MView)
       | _ -> None);

  (* <TvmSlice>.loadRefAsSlice() returns (TvmSlice) *)
  register (next_pid ())
    { prim_name = "loadRefAsSlice";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmSlice) ->
           Some (make_fun [] [TAbstract TvmSlice] MView)
       | _ -> None);

  (* <TvmSlice>.loadSigned(uint16 bitSize) returns (int) *)
  register (next_pid ())
    { prim_name = "loadSigned";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmSlice) ->
           Some (make_fun [TUint 16] [TInt 256] MView)
       | _ -> None);

  (* <TvmSlice>.loadUnsigned(uint16 bitSize) returns (uint) *)
  register (next_pid ())
    { prim_name = "loadUnsigned";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmSlice) ->
           Some (make_fun [TUint 16] [TUint 256] MView)
       | _ -> None);

  (* <TvmSlice>.loadTons() returns (uint128) *)
  register (next_pid ())
    { prim_name = "loadTons";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmSlice) ->
           Some (make_fun [] [TUint 128] MView)
       | _ -> None);

  (*  <TvmSlice>.loadSlice(uint length) returns (TvmSlice)
      <TvmSlice>.loadSlice(uint length, uint refs) returns (TvmSlice) *)
  register (next_pid ())
    { prim_name = "loadSlice";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TAbstract TvmSlice), Some (AList [_]) ->
           Some (make_fun [TUint 256] [TAbstract TvmSlice] MView)
       | Some (TAbstract TvmSlice), Some (AList [_; _]) ->
           Some (make_fun [TUint 256; TUint 256] [TAbstract TvmSlice] MView)
       | _ -> None);

  (*  <TvmSlice>.decodeFunctionParams(functionName)
        returns (uint32 callbackFunctionId, TypeA, TypeB, ...) (* responsible *)
      <TvmSlice>.decodeFunctionParams(functionName) returns (TypeA, TypeB, ...)
      <TvmSlice>.decodeFunctionParams(ContractName) returns (TypeA, TypeB, ...) *)
  register (next_pid ())
    { prim_name = "decodeFunctionParams";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TAbstract TvmSlice),
         Some (
           AList [TFunction (
               { function_def = Some {fun_responsible = true; _ };
                 function_params; _
               } as desc,
               opt
             )]
         ) ->
           Some (
             make_fun [TFunction (desc, opt)]
               (TUint 32 :: List.map fst function_params)
               MView
           )
       | Some (TAbstract TvmSlice),
         Some (AList [TFunction ({ function_params; _ } as desc, opt)]) ->
           Some (
             make_fun [TFunction (desc, opt)]
               (List.map fst function_params)
               MView
           )
       | Some (TAbstract TvmSlice),
         Some (AList [TContract (id, desc, super)]) ->
           (* Should it find the constructor and get it's parameters ? *) (*?*)
           Some (make_fun [TContract (id, desc, super)] [TDots] MView)
       | _ -> None);

  (*  <TvmSlice>.skip(uint length)
      <TvmSlice>.skip(uint length, uint refs) *)
  register (next_pid ())
    { prim_name = "skip";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TAbstract TvmSlice), Some (AList [_]) ->
           Some (make_fun [TUint 256] [] MNonPayable)
       | Some (TAbstract TvmSlice), Some (AList [_; _]) ->
           Some (make_fun [TUint 256; TUint 256] [] MNonPayable)
       | _ -> None);

  (* <TvmBuilder>.remBits() returns (uint16) *)
  register (next_pid ())
    { prim_name = "remBits";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmBuilder) ->
           Some (make_fun [] [TUint 16] MNonPayable)
       | _ -> None);

  (* <TvmBuilder>.remRefs() returns (uint8) *)
  register (next_pid ())
    { prim_name = "remRefs";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmBuilder) ->
           Some (make_fun [] [TUint 8] MNonPayable)
       | _ -> None);

  (* <TvmBuilder>.remBitsAndRefs() returns (uint16, uint8) *)
  register (next_pid ())
    { prim_name = "remBitsAndRefs";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmBuilder) ->
           Some (make_fun [] [TUint 16; TUint 8] MNonPayable)
       | _ -> None);

  (* <TvmBuilder>.store(/*list_of_values*/) *)
  register (next_pid ())
    { prim_name = "store";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmBuilder) ->
           Some (make_fun [TDots] [] MNonPayable)
       | _ -> None);

  (* <TvmBuilder>.storeOnes(uint n) *)
  register (next_pid ())
    { prim_name = "storeOnes";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmBuilder) ->
           Some (make_fun [TUint 256] [] MNonPayable)
       | _ -> None);

  (* <TvmBuilder>.storeZeroes(uint n) *)
  register (next_pid ())
    { prim_name = "storeZeroes";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmBuilder) ->
           Some (make_fun [TUint 256] [] MNonPayable)
       | _ -> None);

  (* <TvmBuilder>.storeSigned(int256 value, uint16 bitSize) *)
  register (next_pid ())
    { prim_name = "storeSigned";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmBuilder) ->
           Some (make_fun [TInt 256; TUint 16] [] MNonPayable)
       | _ -> None);

  (* <TvmBuilder>.storeUnsigned(uint256 value, uint16 bitSize) *)
  register (next_pid ())
    { prim_name = "storeUnsigned";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmBuilder) ->
           Some (make_fun [TUint 256; TUint 16] [] MNonPayable)
       | _ -> None);

  (*  <TvmBuilder>.storeRef(TvmBuilder b)
      <TvmBuilder>.storeRef(TvmCell c)
      <TvmBuilder>.storeRef(TvmSlice s) *)
  register (next_pid ())
    { prim_name = "storeRef";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TAbstract TvmBuilder),
         Some (AList [TAbstract (TvmBuilder | TvmCell | TvmSlice) as ty]) ->
           Some (make_fun [ty] [] MNonPayable)
       | _ -> None);

  (* <TvmBuilder>.storeTons(uint128 value) *)
  register (next_pid ())
    { prim_name = "storeTons";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAbstract TvmBuilder) ->
           Some (make_fun [TUint 128] [] MNonPayable)
       | _ -> None);

  (* optional(Type) *)

  (* <optional(Type)>.hasValue() returns (bool) *)
  register (next_pid ())
    { prim_name = "hasValue";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TOptional _) ->
           Some (make_fun [] [TBool] MView)
       | _ -> None);

  (* <optional(Type)>.get() returns (Type) *)
  register (next_pid ())
    { prim_name = "get";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TOptional ty) ->
           Some (make_fun [] [ty] MView)
       | _ -> None);

  (* <optional(Type)>.set(Type value) *)
  register (next_pid ())
    { prim_name = "set";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TOptional ty) ->
           Some (make_fun [ty] [] MNonPayable)
       | _ -> None);

  (* <optional(Type)>.reset() *)
  register (next_pid ())
    { prim_name = "reset";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TOptional _) ->
           Some (make_fun [] [] MNonPayable)
       | _ -> None);

  (* null keyword *)
  register (next_pid ())
    { prim_name = "null";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TOptional TAny))
       | _ -> None);

  (*  <struct>.unpack() returns (TypeA, TypeB, ...)
      <address>.unpack() returns (int8, uint256) *)
  register (next_pid ())
    { prim_name = "unpack";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TStruct (_, { struct_fields; _ },_)) ->
           Some (make_fun [] (List.map snd struct_fields) MView)
       | Some (TAddress _) ->
           Some (make_fun [] [TInt 8; TUint 256] MView)
       | _ -> None);

  (*  <bytes>.append(bytes tail)
      <string>.append(string tail) *)
  register (next_pid ())
    { prim_name = "append";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TBytes loc) ->
           Some (make_fun [TBytes loc] [] MNonPayable)
       | Some (TString loc) ->
           Some (make_fun [TString loc] [] MNonPayable)
       | _ -> None);

  (* <string>.byteLength() returns (uint32) *)
  register (next_pid ())
    { prim_name = "byteLength";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TString loc) ->
           Some (make_fun [TString loc] [TUint 32] MView)
       | _ -> None);

  (* <string>.substr(uint from[, uint count]) returns (string) *)
  register (next_pid ())
    { prim_name = "substr";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TString loc), Some (AList [_]) ->
           Some (make_fun [TUint 256] [TString loc] MView)
       | Some (TString loc), Some (AList [_; _]) ->
           Some (make_fun [TUint 256; TUint 256] [TString loc] MView)
       | _ -> None);

  (*  <string>.find(bytes1 symbol) returns (optional(uint32))
      <string>.find(string substr) returns (optional(uint32)) *)
  register (next_pid ())
    { prim_name = "find";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TString _), Some (AList [TFixBytes 1]) ->
           Some (make_fun [TFixBytes 1] [TOptional (TUint 32)] MView)
       | Some (TString _), Some (AList [TString loc]) ->
           Some (make_fun [TString loc] [TOptional (TUint 32)] MView)
       | _ -> None);

  (*  <string>.findLast(bytes1 symbol) returns (optional(uint32))*)
  register (next_pid ())
    { prim_name = "findLast";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TString _), Some (AList [TFixBytes 1]) ->
           Some (make_fun [TFixBytes 1] [TOptional (TUint 32)] MView)
       | _ -> None);

  (*  format(string template, TypeA a, TypeB b, ...) returns (string) *)
  register (next_pid ())
    { prim_name = "format";
      prim_kind = PrimFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | None, Some (AList (TString loc :: ty_l)) ->
           Some (make_fun (TString loc :: ty_l) [TString LMemory] MPure)
       | _ -> None);

  (*  stoi(string inputStr) returns (optional(int)) *)
  register (next_pid ())
    { prim_name = "stoi";
      prim_kind = PrimFunction }

    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | None, Some (AList [TString loc]) ->
           Some (make_fun [TString loc] [TOptional (TInt 256)] MPure)
       | _ -> None);

  (*  <address>.wid returns (int8) *)
  register (next_pid ())
    { prim_name = "wid";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress _) ->
           Some (make_var (TInt 8))
       | _ -> None);

  (*  address(this).currencies returns (ExtraCurrencyCollection)
      msg.currencies *)
  register (next_pid ())
    { prim_name = "currencies";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress _) ->
           Some (make_var (TMapping (TUint 32, TUint 256, LStorage false)))
       | Some (TMagic TMsg) ->
           Some (
             make_var (TMapping (TUint 32, TUint 256, LStorage false))
           )
       | _ -> None);

  (* <address>.getType() returns (uint8) *)
  register (next_pid ())
    { prim_name = "getType";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress _) ->
           Some (make_fun [] [TUint 8] MView)
       | _ -> None);

  (* <address>.isStdZero() returns (bool)*)
  register (next_pid ())
    { prim_name = "isStdZero";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress _) ->
           Some (make_fun [] [TBool] MView)
       | _ -> None);

  (* <address>.isStdAddrWithoutAnyCast() returns (bool)*)
  register (next_pid ())
    { prim_name = "isStdAddrWithoutAnyCast";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress _) ->
           Some (make_fun [] [TBool] MView)
       | _ -> None);

  (* <address>.isExternZero() returns (bool)*)
  register (next_pid ())
    { prim_name = "isExternZero";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress _) ->
           Some (make_fun [] [TBool] MView)
       | _ -> None);

  (* <address>.isNone() returns (bool)*)
  register (next_pid ())
    { prim_name = "isNone";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TAddress _) ->
           Some (make_fun [] [TBool] MView)
       | _ -> None);

  (* emptyMap *)
  register (next_pid ())
    { prim_name = "emptyMap";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TMapping (TAny, TAny, LStorage false)))
       | _ -> None);

  (* <mapping>.at() *)
  register (next_pid ())
    { prim_name = "at";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, ty2, _)) ->
           Some (make_fun [ty1] [ty2] MView)
       | _ -> None);

  (* <map>.nextOrEq(KeyType key) returns (optional(KeyType, ValueType)) *)
  register (next_pid ())
    { prim_name = "nextOrEq";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, ty2, _)) ->
           Some (
             make_fun [ty1] [TOptional (TTuple [Some ty1; Some ty2])] MView
           )
       | _ -> None);

  (* <map>.prevOrEq(KeyType key) returns (optional(KeyType, ValueType)) *)
  register (next_pid ())
    { prim_name = "prevOrEq";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, ty2, _)) ->
           Some (
             make_fun [ty1] [TOptional (TTuple [Some ty1; Some ty2])] MView
           )
       | _ -> None);

  (* <map>.delMin() returns (optional(KeyType, ValueType)) *)
  register (next_pid ())
    { prim_name = "delMin";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, ty2, _)) ->
           Some (
             make_fun [] [TOptional (TTuple [Some ty1; Some ty2])] MNonPayable
           )
       | _ -> None);

  (* <map>.delMax() returns (optional(KeyType, ValueType)) *)
  register (next_pid ())
    { prim_name = "delMax";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, ty2, _)) ->
           Some (
             make_fun [] [TOptional (TTuple [Some ty1; Some ty2])] MNonPayable
           )
       | _ -> None);

  (* <map>.fetch(KeyType key) returns (optional(ValueType)) *)
  register (next_pid ())
    { prim_name = "fetch";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, ty2, _)) ->
           Some (make_fun [ty1] [TOptional ty2] MView)
       | _ -> None);

  (* <map>.exists(KeyType key) returns (bool) *)
  register (next_pid ())
    { prim_name = "exists";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, _, _)) ->
           Some (make_fun [ty1] [TBool] MView)
       | _ -> None);

  (* <map>.replace(KeyType key, ValueType value) returns (bool) *)
  register (next_pid ())
    { prim_name = "replace";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, ty2, _)) ->
           Some (make_fun [ty1; ty2] [TBool] MNonPayable)
       | _ -> None);

  (* <map>.add(KeyType key, ValueType value) returns (bool) *)
  register (next_pid ())
    { prim_name = "add";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, ty2, _)) ->
           Some (make_fun [ty1; ty2] [TBool] MNonPayable)
       | _ -> None);

  (*  <map>.getSet(KeyType key, ValueType value)
        returns (optional(ValueType)) *)
  register (next_pid ())
    { prim_name = "getSet";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, ty2, _)) ->
           Some (make_fun [ty1; ty2] [TOptional ty2] MNonPayable)
       | _ -> None);

  (*  <map>.getAdd(KeyType key, ValueType value)
        returns (optional(ValueType)) *)
  register (next_pid ())
    { prim_name = "getAdd";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, ty2, _)) ->
           Some (make_fun [ty1; ty2] [TOptional ty2] MNonPayable)
       | _ -> None);

  (*  <map>.getReplace(KeyType key, ValueType value)
        returns (optional(ValueType)) *)
  register (next_pid ())
    { prim_name = "getReplace";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, ty2, _)) ->
           Some (make_fun [ty1; ty2] [TOptional ty2] MNonPayable)
       | _ -> None);

  (* msg namespace *)

  (* msg.createdAt returns (uint32); *)
  register (next_pid ())
    { prim_name = "createdAt";
      prim_kind = PrimMemberVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TMsg) ->
           Some (make_var (TUint 32))
       | _ -> None);

  (* TVM instructions *)

  (* tvm *)
  register (next_pid ())
    { prim_name = "tvm";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TMagic (TTvm)))
       | _ -> None);

  (* msg.pubkey() returns (uint256)
     tvm.pubkey() returns (uint256) *)
  register (next_pid ())
    { prim_name = "pubkey";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic (TMsg | TTvm)), Some (AList [])->
           Some (make_fun [] [TUint 256] MPure)
       | _ -> None);

  (* tvm.accept() *)
  register (next_pid ())
    { prim_name = "accept";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TTvm) ->
           Some (make_fun [] [] MPure)
       | _ -> None);

  (* tvm.setGasLimit(uint g) *)
  register (next_pid ())
    { prim_name = "setGasLimit";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TTvm) ->
           Some (make_fun [TUint 256] [] MNonPayable)
       | _ -> None);

  (* tvm.commit() *)
  register (next_pid ())
    { prim_name = "commit";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TTvm) ->
           Some (make_fun [] [] MNonPayable)
       | _ -> None);

  (* tvm.rawCommit() *)
  register (next_pid ())
    { prim_name = "rawCommit";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TTvm) ->
           Some (make_fun [] [] MNonPayable)
       | _ -> None);

  (* tvm.getData() returns (TvmCell) *)
  register (next_pid ())
    { prim_name = "getData";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TTvm) ->
           Some (make_fun [] [TAbstract TvmCell] MView)
       | _ -> None);

  (* tvm.setData(TvmCell data) *)
  register (next_pid ())
    { prim_name = "setData";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TTvm) ->
           Some (make_fun [TAbstract TvmCell] [] MNonPayable)
       | _ -> None);

  (* tvm.log(string log) *)
  register (next_pid ())
    { prim_name = "log";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TTvm) ->
           Some (make_fun [TString LMemory] [] MView)
       | _ -> None);

  (* logtvm(string log) // alias for tvm.log(string log) *)
  register (next_pid ())
    { prim_name = "logtvm";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TTvm) ->
           Some (make_fun [TString LMemory] [] MView)
       | _ -> None);

  (* tvm.hexdump(T a) *)
  register (next_pid ())
    { prim_name = "hexdump";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TTvm), Some (AList [TAbstract TvmCell]) ->
           Some (make_fun [TAbstract TvmCell] [] MView)
       | Some (TMagic TTvm), Some (AList [TInt _ | TRationalConst _]) ->
           Some (make_fun [TInt 256] [] MView)
       | Some (TMagic TTvm), Some (AList [TUint _]) ->
           Some (make_fun [TUint 256] [] MView)
       | _ -> None);

  (* tvm.bindump(T a) *)
  register (next_pid ())
    { prim_name = "bindump";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TTvm), Some (AList [TAbstract TvmCell]) ->
           Some (make_fun [TAbstract TvmCell] [] MView)
       | Some (TMagic TTvm), Some (AList [TInt _ | TRationalConst _]) ->
           Some (make_fun [TInt 256] [] MView)
       | Some (TMagic TTvm), Some (AList [TUint _]) ->
           Some (make_fun [TUint 256] [] MView)
       | _ -> None);

  (* tvm.setcode(TvmCell newCode) *)
  register (next_pid ())
    { prim_name = "setcode";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TTvm) ->
           Some (make_fun [TAbstract TvmCell] [] MNonPayable)
       | _ -> None);

  (* tvm.configParam(uint8 paramNumber) returns (TypeA a, TypeB b, ...) *)
  register (next_pid ())
    { prim_name = "configParam";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TTvm) ->
           Some (make_fun [TUint 8] [TDots] MNonPayable)
       | _ -> None);

  (* tvm.rawConfigParam(uint8 paramNumber) returns (TvmCell cell, bool status) *)
  register (next_pid ())
    { prim_name = "rawConfigParam";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TTvm) ->
           Some (make_fun [TUint 8] [TAbstract TvmCell; TBool] MNonPayable)
       | _ -> None);

  (* tvm.rawReserve(uint value, uint8 flag)
     tvm.rawReserve(uint value, ExtraCurrencyCollection currency, uint8 flag) *)
  register (next_pid ())
    { prim_name = "rawReserve";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic (TTvm)), Some (AList [_; _]) ->
           Some (make_fun [TUint 256; TUint 8] [] MNonPayable)
       | Some (TMagic (TTvm)), Some (AList [ _; _; _]) ->
           Some (
             make_fun
               [ TUint 256;
                 TMapping (TUint 32, TUint 256, LStorage false); TUint 8
               ] [] MNonPayable
           )
       | _ -> None);

  (* Hashing and cryptography *)

  (* tvm.hash(TvmCell cellTree) returns (uint256)
     tvm.hash(string data)      returns (uint256)
     tvm.hash(bytes data)       returns (uint256)
     tvm.hash(TvmSlice data)    returns (uint256) *)
  register (next_pid ())
    { prim_name = "hash";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic (TTvm)),
         Some (
           AList [(
               TAbstract TvmCell | TString LMemory |
               TBytes LMemory | TAbstract TvmSlice
             ) as ty]
         ) ->
           Some (make_fun [ty] [TUint 256] MView)
       | _ -> None);

  (*  tvm.checkSign(uint256 hash, uint256 SignHighPart, uint256 SignLowPart,
        uint256 pubkey) returns (bool)
      tvm.checkSign(TvmSlice data, TvmSlice signature, uint256 pubkey)
        returns (bool)
      tvm.checkSign(uint256 hash, TvmSlice signature, uint256 pubkey)
        returns (bool) *)
  register (next_pid ())
    { prim_name = "checkSign";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TTvm), Some (AList [_; _; _; _]) ->
           Some (
             make_fun
               [TUint 256; TUint 256; TUint 256; TUint 256]
               [TBool] MView
           )
       | Some (TMagic TTvm),
         Some (AList [TAbstract TvmSlice; TAbstract TvmSlice; _]) ->
           Some (
             make_fun
               [TAbstract TvmSlice; TAbstract TvmSlice; TUint 256]
               [TBool] MView
           )
       | Some (TMagic TTvm),
         Some (AList [ _; TAbstract TvmSlice; _]) ->
           Some (
             make_fun
               [TUint 256; TAbstract TvmSlice; TUint 256]
               [TBool] MView
           )
       | _ -> None);

  (* Deploy contract from contract *)

  (* tvm.insertPubkey(TvmCell stateInit, uint256 pubkey) returns (TvmCell) *)
  register (next_pid ())
    { prim_name = "insertPubkey";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TTvm) ->
           Some (
             make_fun
               [TAbstract TvmCell; TUint 256]
               [TAbstract TvmCell] MView
           )
       | _ -> None);

  (*  tvm.buildStateInit(TvmCell code, TvmCell data) returns (TvmCell stateInit)
      tvm.buildStateInit(TvmCell code, TvmCell data, uint8 splitDepth)
        returns (TvmCell stateInit)
      tvm.buildStateInit({
        code: TvmCell code,
        data: TvmCell data,
        splitDepth: uint8 splitDepth,
        pubkey: uint256 pubkey,
        contr: contract Contract,
        varInit: {VarName0: varValue0, ...}
      }) returns (TvmCell stateInit)
  *)
  register (next_pid ())
    { prim_name = "buildStateInit";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       let pair_to_ty (id, ty) =
         match Ident.to_string id, ty with
         | "code", TAbstract TvmCell
         | "data", TAbstract TvmCell ->
             Some (TAbstract TvmCell)
         | "splitDepth", TUint _ -> Some (TUint 8)
         | "pubkey", TUint _ -> Some (TUint 256)
         | "contr", TContract (id, desc, super) ->
             Some (TContract (id, desc, super))
         | "varInit", _ -> Some TDots (*?*)
         |  _ -> None
       in
       match t_opt, opt.call_args with
       | Some (TMagic TTvm),
         Some (AList [TAbstract TvmCell; TAbstract TvmCell]) ->
           Some (
             make_fun
               [TAbstract TvmCell; TAbstract TvmCell]
               [TAbstract TvmCell] MView
           )

       | Some (TMagic TTvm),
         Some (AList [TAbstract TvmCell; TAbstract TvmCell; TUint _]) ->
           Some (
             make_fun
               [TAbstract TvmCell; TAbstract TvmCell; TUint 8]
               [TAbstract TvmCell] MView
           )

       | Some (TMagic TTvm),
         Some (ANamed [id, ty]) when Ident.to_string id = "code" ->
           let arg_type_opt = pair_to_ty (id, ty) in
           if Option.is_none arg_type_opt
           then None
           else Some (
               make_fun [Option.get arg_type_opt] [
                 TAbstract TvmCell] MView
             )

       | Some (TMagic TTvm), Some (ANamed args) ->
           begin
             match
               List.sort String.compare
                 (List.map (fun (id, _) -> Ident.to_string id) args)
             with
             | ["code"; "contr"; "pubkey"; "splitDepth"; "varInit"]

             | ["code"; "contr"; "data"; "splitDepth"]
             | ["code"; "contr"; "splitDepth"; "varInit"]
             | ["code"; "contr"; "pubkey"; "varInit"]
             | ["code"; "contr"; "pubkey"; "splitDepth"]

             | ["code"; "data"; "splitDepth"]
             | ["code"; "contr"; "data"]
             | ["code"; "contr"; "splitDepth"]
             | ["code"; "contr"; "varInit"]
             | ["code"; "contr"; "pubkey"]
             | ["code"; "pubkey"; "splitDepth"]

             | ["code"; "contr"]
             | ["code"; "data"]
             | ["code"; "splitDepth"]
             | ["code"; "pubkey"] ->
                 let arg_type_opts = List.map pair_to_ty args in
                 if List.exists Option.is_none arg_type_opts
                 then None
                 else Some (
                     make_fun
                       (List.map Option.get arg_type_opts)
                       [TAbstract TvmCell] MView
                   )

             | _ -> None
           end

       | _ -> None);

  (*  tvm.buildDataInit({
        pubkey: uint256 pubkey,
        contr: contract Contract,
        varInit: {VarName0: varValue0, ...}
      }) returns (TvmCell stateInit)
  *)
  register (next_pid ())
    { prim_name = "buildDataInit";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       let pair_to_ty (id, ty) =
         match Ident.to_string id, ty with
         | "contr", TContract (id, desc, super) ->
             Some (TContract (id, desc, super))
         | "pubkey", TUint _ -> Some (TUint 256)
         | "varInit", _ -> Some TDots (*?*)
         |  _ -> None
       in
       match t_opt, opt.call_args with
       | Some (TMagic TTvm),
         Some (ANamed [id, ty])
         when Ident.to_string id = "contr" || Ident.to_string id = "pubkey"
         ->
           let arg_type_opt = pair_to_ty (id, ty) in
           if Option.is_none arg_type_opt
           then None
           else Some (
               make_fun [Option.get arg_type_opt]
                 [TAbstract TvmCell] MView
             )

       | Some (TMagic TTvm), Some (ANamed args) ->
           begin match
               List.sort String.compare
                 (List.map (fun (id, _) -> Ident.to_string id) args)
             with
             | [ "contr"; "pubkey"; "varInit"]

             | [ "contr"; "varInit"]
             | [ "contr"; "pubkey"] ->
                 let arg_type_opts = List.map pair_to_ty args in
                 if List.exists Option.is_none arg_type_opts
                 then None
                 else Some (
                     make_fun
                       (List.map Option.get arg_type_opts)
                       [TAbstract TvmCell] MView
                   )
             | _ -> None
           end

       | _ -> None);

  (*  tvm.stateInitHash(
        uint256 codeHash,
        uint256 dataHash,
        uint16 codeDepth,
        uint16 dataDepth
      ) returns (uint256);
  *)
  register (next_pid ())
    { prim_name = "stateInitHash";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTvm)) ->
           Some (
             make_fun
               [TUint 256; TUint 256; TUint 16; TUint 16]
               [TUint 256] MView
           )
       | _ -> None);

  (* Misc functions from tvm *)

  (* tvm.code() returns (TvmCell) *)
  register (next_pid ())
    { prim_name = "code";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTvm)) ->
           Some (make_fun [] [TAbstract TvmCell] MView)
       | _ -> None);

  (* tvm.codeSalt(TvmCell code) returns (optional(TvmCell) optSalt) *)
  register (next_pid ())
    { prim_name = "codeSalt";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTvm)) ->
           Some (
             make_fun [TAbstract TvmCell]
               [TOptional (TAbstract TvmCell)] MView
           )
       | _ -> None);

  (* tvm.setCodeSalt(TvmCell code, TvmCell salt) returns (TvmCell newCode) *)
  register (next_pid ())
    { prim_name = "setCodeSalt";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTvm)) ->
           Some (
             make_fun [TAbstract TvmCell; TAbstract TvmCell]
               [TAbstract TvmCell] MNonPayable
           )
       | _ -> None);

  (* tvm.setPubkey(uint256 newPubkey); *)
  register (next_pid ())
    { prim_name = "setPubkey";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTvm)) ->
           Some (make_fun [TUint 256] [] MNonPayable)
       | _ -> None);

  (* tvm.setCurrentCode(TvmCell newCode) *)
  register (next_pid ())
    { prim_name = "setCurrentCode";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTvm)) ->
           Some (make_fun [TAbstract TvmCell] [] MNonPayable)
       | _ -> None);

  (* tvm.resetStorage() *)
  register (next_pid ())
    { prim_name = "resetStorage";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTvm)) ->
           Some (make_fun [] [] MNonPayable)
       | _ -> None);

  (*  tvm.functionId(functionName) returns (uint32)
      tvm.functionId(ContractName) returns (uint32) *)
  register (next_pid ())
    { prim_name = "functionId";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic (TTvm)),
         Some (AList [TFunction _ | TContract _ as ty ]) ->
           Some (make_fun [ty] [TUint 32] MView)
       | _ -> None);

  (*  tvm.encodeBody(function, callbackFunction, arg0, arg1, arg2, ...)
        returns (TvmCell)
      tvm.encodeBody(function, arg0, arg1, arg2, ...) returns (TvmCell)
      tvm.encodeBody(contract, arg0, arg1, arg2, ...) returns (TvmCell) *)
  register (next_pid ())
    { prim_name = "encodeBody";
      prim_kind = PrimMemberFunction }
    (fun pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic (TTvm)),
         Some (
           AList (TFunction (desc1, opt1) :: TFunction (desc2, opt2) :: _)
         ) ->
           Some (
             make_fun
               [TFunction (desc1, opt1); TFunction (desc2, opt2); TDots]
               [TAbstract TvmCell] MView)


       | Some (TMagic (TTvm)),
         Some (AList (TFunction (
             { function_def = Some {fun_responsible = true; _ }; _
             }, _) :: _)) ->
           error pos
             "tvm.encodeBody(function[, callbackFunction], arg0, arg1 ...):\
              when the function is responsible, callbackFunction must provided"

       | Some (TMagic (TTvm)),
         Some (AList (TFunction (desc, opt) :: _)) ->
           Some (
             make_fun
               [TFunction (desc, opt); TDots]
               [TAbstract TvmCell] MView)

       | Some (TMagic (TTvm)),
         Some (AList (TContract (id, desc, super) :: _)) ->
           Some (
             make_fun
               [TContract (id, desc, super); TDots]
               [TAbstract TvmCell] MView)

       | _ -> None);

  (* tvm.exit() *)
  register (next_pid ())
    { prim_name = "exit";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTvm)) ->
           Some (make_fun [] [] MView)
       | _ -> None);

  (* tvm.exit1() *)
  register (next_pid ())
    { prim_name = "exit1";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTvm)) ->
           Some (make_fun [] [] MView)
       | _ -> None);

  (*  tvm.buildExtMsg({
        dest: address,
        time: uint64,
        expire: uint32,
        call: {functionIdentifier [, list of function arguments]},
        sign: bool,
        pubkey: optional(uint256),
        callbackId: (uint32 | functionIdentifier),
        onErrorId: (uint32 | functionIdentifier),
        stateInit: TvmCell,
        signBoxHandle: optional(uint32)
      }) returns (TvmCell) *)
  register (next_pid ())
    { prim_name = "buildExtMsg";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       let pair_to_ty (id, ty) =
         match Ident.to_string id, ty with
         | "callbackId", TUint _ -> Some (TUint 32)
         | "callbackId", TFunction (desc, opt) ->
             Some (TFunction (desc, opt))
         | "call", TTuple (Some (TFunction (desc, opt)) :: f_arg_opts) ->
             Some (TTuple (Some (TFunction (desc, opt)) :: f_arg_opts)) (*?*)
         | "dest", TAddress b -> Some (TAddress b)
         | "expire", TUint _ -> Some (TUint 32)
         | "pubkey", TOptional (TUint _) -> Some (TOptional (TUint 256))
         | "onErrorId", TUint _ -> Some (TUint 32)
         | "onErrorId", TFunction (desc, opt) -> Some (TFunction (desc, opt))
         | "signBoxHandle", TOptional (TUint _) -> Some (TOptional (TUint 32))
         | "sign", TBool -> Some TBool
         | "stateInit", TAbstract TvmCell -> Some (TAbstract TvmCell)
         | "time", TUint _ -> Some (TUint 64)
         |  _ -> None
       in
       match t_opt, opt.call_args with
       | Some (TMagic (TTvm)),  Some (ANamed args) ->
           begin match
               List.sort String.compare
                 (List.map (fun (id, _) -> Ident.to_string id) args)
             with
             | [ "callbackId"; "call"; "dest"; "expire"; "pubkey"; "onErrorId";
                 "signBoxHandle"; "sign"; "stateInit"; "time" ]

             | [ "callbackId"; "call"; "dest"; "expire"; "onErrorId";
                 "signBoxHandle"; "sign"; "stateInit"; "time" ]
             | [ "callbackId"; "call"; "dest"; "expire"; "pubkey"; "onErrorId";
                 "signBoxHandle"; "stateInit"; "time" ]
             | [ "callbackId"; "call"; "dest"; "expire"; "pubkey"; "onErrorId";
                 "sign"; "stateInit"; "time" ]

             | [ "callbackId"; "call"; "dest"; "expire"; "onErrorId";
                 "signBoxHandle"; "stateInit"; "time" ]
             | [ "callbackId"; "call"; "dest"; "expire"; "onErrorId";
                 "sign"; "stateInit"; "time" ]
             | [ "callbackId"; "call"; "dest"; "expire"; "pubkey"; "onErrorId";
                 "stateInit"; "time" ]

             | [ "callbackId"; "call"; "dest"; "expire"; "onErrorId";
                 "stateInit"; "time" ]
               ->
                 let arg_type_opts = List.map pair_to_ty args in
                 if List.exists Option.is_none arg_type_opts
                 then None
                 else Some (
                     make_fun
                       (List.map Option.get arg_type_opts)
                       [TAbstract TvmCell] MView
                   )

             | _ -> None
           end

       | _ -> None);
  (*
  tvm.buildIntMsg({
    dest: address,
    value: uint128,
    call: {function, [callbackFunction,] arg0, arg1, arg2, ...},
    bounce: bool,
    currencies: ExtraCurrencyCollection
    stateInit: TvmCell
  }) returns (TvmCell);
  *)
  register (next_pid ())
    { prim_name = "buildIntMsg";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       let pair_to_ty (id, ty) =
         match Ident.to_string id, ty with
         | "bounce", TBool -> Some TBool
         | "call", TTuple (Some (TFunction (desc, opt)) :: f_arg_opts) ->
             Some (TTuple (Some (TFunction (desc, opt)) :: f_arg_opts)) (*?*)
         | "currencies", TMapping (TUint _, TUint _, _) ->
             Some (TMapping (TUint 32, TUint 256, LStorage false)) (*?*)
         | "dest", TAddress b -> Some (TAddress b)
         | "stateInit", TAbstract TvmCell -> Some (TAbstract TvmCell)
         | "value", TBool -> Some TBool
         |  _ -> None
       in
       match t_opt, opt.call_args with
       | Some (TMagic (TTvm)),  Some (ANamed args) ->
           begin match
               List.sort String.compare
                 (List.map (fun (id, _) -> Ident.to_string id) args)
             with
             | [ "bounce"; "call"; "currencies"; "dest"; "stateInit"; "value" ]

             | [ "call"; "currencies"; "dest"; "stateInit"; "value" ]
             | [ "bounce"; "call"; "dest"; "stateInit"; "value" ]
             | [ "bounce"; "call"; "currencies"; "dest"; "value" ]

             | [ "call"; "dest"; "stateInit"; "value" ]
             | [ "call"; "currencies"; "dest"; "value" ]
             | [ "bounce"; "call"; "dest"; "value" ]

             | [ "call"; "dest"; "value" ]
               ->
                 let arg_type_opts = List.map pair_to_ty args in
                 if List.exists Option.is_none arg_type_opts
                 then None
                 else Some (
                     make_fun
                       (List.map Option.get arg_type_opts)
                       [TAbstract TvmCell] MPure
                   )
             | _ -> None
           end
       | _ -> None);

  (* tvm.sendrawmsg(TvmCell msg, uint8 flag) *)
  register (next_pid ())
    { prim_name = "sendrawmsg";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic (TTvm)) ->
           Some (
             make_fun [TAbstract TvmCell; TUint 8]
               [TAbstract TvmCell] MNonPayable
           )
       | _ -> None);

  (* Additional arithmetic primitives (freeton's math namespace) *)

  (* math *)
  register (next_pid ())
    { prim_name = "math";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TMagic TMath))
       | _ -> None);

  (* math.abs(intM val) returns (intM)
     math.abs(fixedMxN val) returns (fixedMxN)
  *)
  register (next_pid ())
    { prim_name = "abs";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TMath), Some (AList ([TInt n])) ->
           Some (make_fun [TInt n] [TInt n] MPure)
       | Some (TMagic TMath), Some (AList ([TFixed (n, m)])) ->
           Some (make_fun [TFixed (n, m)] [TFixed (n, m)] MPure)
       | _ -> None);

  (* math.modpow2(uint value, uint power) returns (uint) *)
  register (next_pid ())
    { prim_name = "modpow2";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMagic TMath) ->
           Some (make_fun [TUint 256; TUint 256] [TUint 256] MPure)
       | _ -> None);

  (* math.divc(T a, T b) returns (T) *)
  register (next_pid ())
    { prim_name = "divc";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TMath), Some (AList ([ty1; ty2])) ->
           let rty1 = to_upper_bound ty1 in
           let rty2 = to_upper_bound ty2 in
           if is_numeric rty1 && is_numeric rty2 (*?*)
           then
             Some (make_fun [rty1; rty2] [rty1] MPure)
           else None
       | _ -> None);

  (* math.divr(T a, T b) returns (T) *)
  register (next_pid ())
    { prim_name = "divr";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TMath), Some (AList ([ty1; ty2])) ->
           let rty1 = to_upper_bound ty1 in
           let rty2 = to_upper_bound ty2 in
           if is_numeric rty1 && rty1 = rty2 (*?*)
           then
             Some (make_fun [rty1; rty1] [rty1] MPure)
           else None
       | _ -> None);

  (* math.muldiv(T a, T b, T c) returns (T) *)
  register (next_pid ())
    { prim_name = "muldiv";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TMath), Some (AList ([ty1; ty2; ty3])) ->
           let rty1 = to_upper_bound ty1 in
           let rty2 = to_upper_bound ty2 in
           let rty3 = to_upper_bound ty3 in
           if is_numeric rty1 &&
              rty1 = rty2 && rty2 = rty3 (*?*)
           then
             Some (make_fun [rty1; rty1] [rty1] MPure)
           else None
       | _ -> None);


  (* math.muldivr(T a, T b, T c) returns (T) *)
  register (next_pid ())
    { prim_name = "muldivr";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TMath), Some (AList ([ty1; ty2; ty3])) ->
           let rty1 = to_upper_bound ty1 in
           let rty2 = to_upper_bound ty2 in
           let rty3 = to_upper_bound ty3 in
           if is_numeric rty1 &&
              rty1 = rty2 && rty2 = rty3 (*?*)
           then
             Some (make_fun [rty1; rty1; rty1] [rty1] MPure)
           else None
       | _ -> None);

  (* math.muldivc(T a, T b, T c) returns (T) *)
  register (next_pid ())
    { prim_name = "muldivc";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TMath), Some (AList ([ty1; ty2; ty3])) ->
           let rty1 = to_upper_bound ty1 in
           let rty2 = to_upper_bound ty2 in
           let rty3 = to_upper_bound ty3 in
           if is_numeric rty1 &&
              rty1 = rty2 && rty2 = rty3 (*?*)
           then
             Some (make_fun [rty1; rty1; rty1] [rty1] MPure)
           else None
       | _ -> None);

  (* math.muldivmod(T a, T b, T c) returns (T /*result*/, T /*remainder*/) *)
  register (next_pid ())
    { prim_name = "muldivmod";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TMath), Some (AList ([ty1; ty2; ty3])) ->
           let rty1 = to_upper_bound ty1 in
           let rty2 = to_upper_bound ty2 in
           let rty3 = to_upper_bound ty3 in
           if is_numeric rty1 &&
              rty1 = rty2 && rty2 = rty3 (*?*)
           then
             Some (make_fun [rty1; rty1; rty1] [rty1; rty1] MPure)
           else None
       | _ -> None);

  (* math.muldivmod(T a, T b, T c) returns (T /*result*/, T /*remainder*/) *)
  register (next_pid ())
    { prim_name = "divmod";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TMath), Some (AList ([ty1; ty2])) ->
           let rty1 = to_upper_bound ty1 in
           let rty2 = to_upper_bound ty2 in
           if is_numeric rty1 && rty1 = rty2 (*?*)
           then
             Some (make_fun [rty1; rty1] [rty1; rty1] MPure)
           else None
       | _ -> None);

  (* math.sign(int val) returns (int8) *)
  register (next_pid ())
    { prim_name = "sign";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TMath), Some (AList ([TInt _])) ->
           Some (make_fun [TInt 256] [TInt 8] MPure)
       | _ -> None);

  (* rnd namespace *)

  (* rnd *)
  register (next_pid ())
    { prim_name = "rnd";
      prim_kind = PrimVariable }
    (fun _pos _opt t_opt ->
       match t_opt with
       | None -> Some (make_var (TMagic TRnd))
       | _ -> None);

  (*  rnd.next([Type limit]) returns (Type)
      <map>.next(KeyType key) returns (optional(KeyType, ValueType)) *)
  register (next_pid ())
    { prim_name = "next";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TRnd), Some (AList [(TInt _| TUint _) as ty]) ->
           let rty = to_upper_bound ty in
           Some (make_fun [rty] [rty] MPure)
       | Some (TMagic TRnd), Some (AList []) ->
           Some (make_fun [] [TUint 256] MPure)
       | Some (TMapping (ty1, ty2, _)), _ ->
           Some (
             make_fun [ty1] [TOptional (TTuple [Some ty1; Some ty2])] MView
           )
       | _ -> None);

  (* <map>.prev(KeyType key) returns (optional(KeyType, ValueType)) *)
  register (next_pid ())
    { prim_name = "prev";
      prim_kind = PrimMemberFunction }
    (fun _pos _opt t_opt ->
       match t_opt with
       | Some (TMapping (ty1, ty2, _)) ->
           Some (
             make_fun [ty1] [TOptional (TTuple [Some ty1; Some ty2])] MView
           )
       | _ -> None);

  (* rnd.getSeed() returns (uint256) *)
  register (next_pid ())
    { prim_name = "getSeed";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TRnd), Some (AList []) ->
           Some (make_fun [] [TUint 256] MPure)
       | _ -> None);

  (* rnd.setSeed(uint256 x) *)
  register (next_pid ())
    { prim_name = "setSeed";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TRnd), Some (AList [TUint _]) ->
           Some (make_fun [TUint 256] [] MPure)
       | _ -> None);

  (*  rnd.shuffle(uint someNumber)
      rnd.shuffle() *)
  register (next_pid ())
    { prim_name = "shuffle";
      prim_kind = PrimMemberFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | Some (TMagic TRnd), Some (AList [TUint _]) ->
           Some (make_fun [TUint 256] [] MPure)
       | Some (TMagic TRnd), Some (AList []) ->
           Some (make_fun [] [] MPure)
       | _ -> None);

  (* gasToValue(uint128 gas, int8 wid) returns (uint128 value) *)
  register (next_pid ())
    { prim_name = "gasToValue";
      prim_kind = PrimFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | None, Some (AList [TUint _; TInt _]) ->
           Some (make_fun [TUint 128; TInt 8] [TUint 128] MPure)
       | _ -> None);

  (* valueToGas(uint128 value, int8 wid) returns (uint128 gas) *)
  register (next_pid ())
    { prim_name = "valueToGas";
      prim_kind = PrimFunction }
    (fun _pos opt t_opt ->
       match t_opt, opt.call_args with
       | None, Some (AList [TUint _; TInt _]) ->
           Some (make_fun [TUint 128; TInt 8] [TUint 128] MPure)
       | _ -> None);

  ()

let init ?(freeton = false) () =
  register_primitives ~freeton ();
  if freeton then
    register_additional_freeton_primitives ()
