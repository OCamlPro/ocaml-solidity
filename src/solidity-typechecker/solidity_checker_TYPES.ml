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

type origin =
  | Defined
  | Imported
  | Inherited

type env = {
  upper_env : env option; (* i.e module/contract/fonction/block *)
  mutable ident_map : ((ident_desc * origin) list) IdentMap.t;
  mutable using_for : (env * (type_ list)) AbsLongIdentMap.t;
                          (* empty list = all types = * *)
}

and ident_desc =
  | Alias of alias_desc       (* In: modules (temporary) *)
  | Module of module_desc     (* In: modules *)
  | Contract of contract_desc (* In: modules *)
  | Type of type_desc         (* In: modules, contracts*)
  | Variable of variable_desc (* In: modules, contracts, functions *)
  | Function of function_desc (* In: modules, contracts*)
  | Modifier of modifier_desc (* In: contracts *)
  | Event of event_desc       (* In: contracts *)
  | Field of field_desc       (* Internal use, not in envs *)
  | Constr of constr_desc     (* Internal use, not in envs *)

and alias_desc = {
  alias_abs_name : absolute LongIdent.t;
  alias_pos : pos;
  alias_target_id : Ident.t;
  alias_target_file : string;
  alias_target_env : env;
  mutable alias_targets : (ident_desc * origin) list;
}

(* This is just a container for things imported using the import directive *)
(* Can be imported : types, contract, libraries AND MODULES (top-level stuff) *)
and module_desc = {
  module_abs_name : absolute LongIdent.t;
  module_pos : pos;
  module_file : string;
  module_env : env; (* this aliases a module env *)
}

and type_desc =
  | TDEnum of enum_desc
  | TDStruct of struct_desc

and enum_desc = {
  enum_abs_name : absolute LongIdent.t;
  enum_pos : pos;
  enum_values : (Ident.t * int) list;
}

and constr_desc = {
  constr_enum_desc : enum_desc;
  constr_name : Ident.t;
  constr_value : int;
  constr_type : type_;
}

and struct_desc = {
  struct_abs_name : absolute LongIdent.t;
  mutable struct_fields : (Ident.t * type_) list; (* Note: order is important *)
  mutable has_mapping : bool;
  struct_def : Solidity_ast.struct_definition;
}

and field_desc = {
  field_struct_desc : struct_desc;
  field_name : Ident.t;
  field_type : type_;
}

and contract_desc = {
  contract_abs_name : absolute LongIdent.t;
  contract_env : env;
  mutable contract_hierarchy : (absolute LongIdent.t * contract_desc) list;
    (* Note: the most derived first, including itself *)
  contract_def : Solidity_ast.contract_definition;
}

and variable_desc = {
  variable_abs_name : absolute LongIdent.t;
  mutable variable_type : type_;
  variable_visibility : Solidity_ast.visibility;
  variable_mutability : Solidity_ast.var_mutability;
  variable_local : bool;
  mutable variable_override : absolute LongIdent.t list option;
  mutable variable_getter : function_desc option; (* when the variable has a getter*)
  variable_is_primitive : bool;
  variable_def : Solidity_ast.state_variable_definition option; (* module/contract*)
  mutable variable_ops : ( function_desc * variable_operation ) list ;
}

and function_desc = {
  function_abs_name : absolute LongIdent.t;
  mutable function_params : (type_ * Ident.t option) list;
  mutable function_returns : (type_ * Ident.t option) list;
  function_returns_lvalue : bool; (* some primitives (push/pop) return lvalues*)
  function_visibility : Solidity_ast.visibility;
  function_mutability : Solidity_ast.fun_mutability;
  mutable function_override : absolute LongIdent.t list option;
  mutable function_selector : string option;
  function_is_method : bool;
  function_is_primitive : bool;
  function_def : Solidity_ast.function_definition option; (* Primitives have no definition *)
  mutable function_ops : ( variable_desc * variable_operation ) list ;
  mutable function_purity : function_purity ;
}

and function_purity = (* whether it modifies its contract *)
  | PurityUnknown
  | PurityPure
  | PurityView
  | PurityMute

and variable_operation =
  | OpAssign
  | OpAccess
  | OpCall of function_desc

and modifier_desc = {
  modifier_abs_name : absolute LongIdent.t;
  mutable modifier_params : (type_ * Ident.t option) list;
  modifier_def : Solidity_ast.modifier_definition;
  (* Note: Modifiers have no visibility nor mutability *)
}

and event_desc = {
  event_abs_name : absolute LongIdent.t;
  mutable event_params : (type_ * Ident.t option) list;
  event_def : Solidity_ast.event_definition;
}

and fun_kind =
  | KOther
  | KNewContract
  | KExtContractFun
  | KReturn

and function_options = {
  kind : fun_kind;
  value : bool;
  gas : bool;
  salt : bool;
  fields : StringSet.t ;
}

and location =
  | LMemory
  | LStorage of bool (* false = ref, true = pointer *)
  | LCalldata (* is always a reference *)

and abstract_type =
  | TvmCell
  | TvmSlice
  | TvmBuilder

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
  | TAbstract of abstract_type
  | TOptional of type_
  | TAny (* one argument, but anything *)
  | TDots (* any number of arguments, and anything *)

  (* Internal use only *)
  | TModifier of modifier_desc
  | TEvent of event_desc
  | TTuple of type_ option list
  | TArraySlice of type_ * location (* is never an lvalue *)
  | TType of type_ (* a type is an expression of type 'type' *)
  | TMagic of magic_type
  | TModule of absolute LongIdent.t * module_desc
  | TRationalConst of Q.t * int option (* Some _ = size in bytes (if hex) *)
  | TLiteralString of string

and magic_type =
  | TMetaType of type_ (* result of type(X) *)
  | TBlock (* type of the 'block' object *)
  | TMsg (* type of the 'msg' object *)
  | TTx (* type of the 'tx' object *)
  | TAbi (* type of the 'abi' object *)
  | TTvm (* type of the 'tvm' object *)
  | TStatic of ( Ident.t option * type_ ) list
  | TMath
  | TRnd

(* source_unit (Import) *)
type annot += AImport of Ident.t

(* expression, statement, ident/field (incl. contract) *)
type annot += AType of type_ (* Rename to exp_type *)

type annot += ATypeId of type_desc

(* source_unit (ContractDefinition), inheritance_specifier *)
type annot += AContract of contract_desc

(* contract_part (StateVariableDeclaration), ident/field (even getter) *)
type annot += AVariable of variable_desc * bool (* true = getter *)

(* contract_part (FunctionDefinition), constructor invocation, ident/field (functions only) *)
type annot += AFunction of function_desc * bool (* true = from a using for *)

(* contract_part (ModifierDefinition), ident/field *)
type annot += AModifier of modifier_desc

(* contract_part (EventDefinition), ident/field *)
type annot += AEvent of event_desc

type annot += AField of field_desc

type annot += AConstr of constr_desc

type annot += AModule of module_desc

(* ident/field *)
type annot += APrimitive



type args =
  | AList of type_ list
  | ANamed of (Ident.t * type_) list

type options = {
  allow_empty: bool; (* whether to allow empty elements in tuple *)
  call_args: args option;   (* could just have an in_lvalue flag *)
  fun_returns : type_ list;
  in_loop: bool;
  in_function: function_desc option;
  in_modifier: bool;
  current_hierarchy: absolute LongIdent.t list;
  current_contract: contract_desc option;
}
