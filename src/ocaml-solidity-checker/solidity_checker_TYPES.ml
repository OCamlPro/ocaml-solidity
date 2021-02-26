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

type env = {
  mutable ident_map : ((ident_desc * bool (* inherited *)) list) IdentMap.t;
  upper_env : env option; (* i.e module/contract/fonction *)
(* add a list of contracts open with using for ? *)
}

and ident_desc =
  (* | Module of module_desc *) (* In: modules *)
  | Contract of contract_desc (* In: modules *)
  | Type of type_desc         (* In: modules, contracts*)
  | Variable of variable_desc (* In: modules, contracts, functions *)
  | Function of function_desc (* In: modules, contracts*)
  | Modifier of modifier_desc (* In: contracts *)
  | Event of event_desc       (* In: contracts*)
(* see how to deal with using for *)

(* This is just a container for things imported using the import directive *)
(* Can be imported : types, contract, libraries AND MODULES (top-level stuff) *)
(* and module_desc = {
 *   module_type_name : user_defined_type_name;
 *   module_env : env;
 * } *)

and type_desc =
  | TDEnum of enum_desc
  | TDStruct of struct_desc

and enum_desc = {
  enum_abs_name : absolute LongIdent.t;
  enum_values : (Ident.t * int) list;
}

and struct_desc = {
  struct_abs_name : absolute LongIdent.t;
  mutable struct_fields : (Ident.t * type_) list; (* Note: order is important *)
  mutable has_mapping : bool;
  struct_env : env; (* Note: needed to qualify types *)
  struct_def : Ident.t * Solidity_ast.field_definition list;
}

and contract_desc = {
  contract_abs_name : absolute LongIdent.t;
  contract_env : env;
  contract_def : Solidity_ast.contract_definition;
  mutable contract_hierarchy : (absolute LongIdent.t * contract_desc) list;
    (* Note: the most derived first, including itself *)
}

and variable_desc = {
  variable_abs_name : absolute LongIdent.t;
  variable_type : type_;
  variable_visibility : Solidity_ast.visibility;
  variable_mutability : Solidity_ast.var_mutability;
  variable_local : bool;
  variable_init : Solidity_ast.expression option;
  variable_override : absolute LongIdent.t list option;
  variable_getter : function_desc option; (* when the variable has a getter *)
}

and function_desc = {
  function_abs_name : absolute LongIdent.t;
  function_params : (type_ * Ident.t option) list;
  function_returns : (type_ * Ident.t option) list;
  function_returns_lvalue : bool;
  function_visibility : Solidity_ast.visibility;
  function_mutability : Solidity_ast.fun_mutability;
  function_def : Solidity_ast.function_definition option; (* REMOVE ? change to body ? *)
  function_override : absolute LongIdent.t list option;
  function_selector : string option;
}

and modifier_desc = {
  modifier_abs_name : absolute LongIdent.t;
  modifier_params : (type_ * Ident.t option) list;
  modifier_def : Solidity_ast.modifier_definition; (* REMOVE ? change to body ?  *)
(* TODO: override, virtual ? *)
  (* Note: Modifiers have no visibility nor mutability *)
}

and event_desc = {
  event_abs_name : absolute LongIdent.t;
  event_params : (type_ * Ident.t option) list;
  event_def : Solidity_ast.event_definition;
}

(* More kinds: regular, new, ext, event, getter, primitive *)
and fun_kind =
  | KOther
  | KNewContract
  | KExtContractFun

and function_options = {
  kind : fun_kind;
  value : bool;
  gas : bool;
  salt : bool;
}

and location =
  | LMemory
  | LStorage of bool (* false = ref, true = pointer *)
  | LCalldata (* is always a reference *)

and type_ =
  | TBool
  | TInt of int
  | TUint of int
  | TFixed of int * int
  | TUfixed of int * int
  | TAddress of bool (* false = address, true = address payable *)
  | TFixBytes of int
  | TBytes of location
  | TString of location
  | TEnum of absolute LongIdent.t * enum_desc
  | TStruct of absolute LongIdent.t * struct_desc * location
  | TContract of absolute LongIdent.t * contract_desc * bool (* super *)
  | TArray of type_ * Z.t option * location
  | TMapping of type_ * type_ * location (* storage ref or storage pointer *)
  | TFunction of function_desc * function_options

  (* TON-specific *)
  | TTvmCell
  | TTvmSlice
  | TTvmBuilder
  | TExtraCurrencyCollection
  | TOptional of type_

  (* Internal use only *)
  | TModifier of modifier_desc
  | TEvent of event_desc
  | TTuple of type_ option list
  | TArraySlice of type_ * location (* is never an lvalue *)
  | TType of type_ (* a type is an expression of type 'type' *)
  | TMagic of magic_type
  | TRationalConst of Q.t * int option (* Some _ = size in bytes (if hex) *)
  | TLiteralString of string

and magic_type =
  | TMetaType of type_ (* result of type(X) *)
  | TBlock (* type of the 'block' object *)
  | TMsg (* type of the 'msg' object *)
  | TTx (* type of the 'tx' object *)
  | TAbi (* type of the 'abi' object *)

  (* TON-specific *)
  | TTvm
  | TMath
  | TRnd



(* source_unit (Import) *)
type annot += AImport of Ident.t

(* expression, statement, ident/field (incl. contract) *)
type annot += AType of type_

(* source_unit (ContractDefinition), inheritance_specifier *)
type annot += AContract of contract_desc

(* contract_part (FunctionDefinition), constructor invocation, ident/field (functions AND getters) *)
type annot += AFunction of function_desc

(* contract_part (ModifierDefinition), ident/field *)
type annot += AModifier of modifier_desc

(* contract_part (EventDefinition), ident/field *)
type annot += AEvent of event_desc

(* contract_part (StateVariableDeclaration), ident/field *)
type annot += AVariable of variable_desc

(* ident/field *)
type annot += APrimitive (* id ? *)



type args =
  | AList of type_ list
  | ANamed of (Ident.t * type_) list

type options = {
  allow_empty: bool; (* whether to allow empty elements in tuple *)
  call_args: args option;   (* could just have an in_lvalue flag *)
  fun_returns : type_ list;
  in_loop: bool;
  in_function: bool;
  in_modifier: bool;
  current_hierarchy: absolute LongIdent.t list;
  current_contract: contract_desc option;
}
