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

type ident = Ident.t node

type longident = relative LongIdent.t node

type program = {
  program_modules : module_ list;
  program_modules_by_id : module_ IdentMap.t;
  program_modules_by_file : module_ StringMap.t;
}

and module_ = {
  module_file : string; (* *absolute* path *)
  module_id : Ident.t; (* the module id: @n *)
  module_units : module_units;
}

and module_units = (source_unit node) list

and source_unit =
  | Pragma of (Ident.t * string)
  | Import of import_directive
  | GlobalTypeDefinition of type_definition
  | GlobalFunctionDefinition of function_definition
  | GlobalVariableDefinition of state_variable_definition
  | ContractDefinition of contract_definition

and import_directive = {
  import_pos : Solidity_common.pos ;
  import_from : string;
  import_symbols : import_symbols;
}

and import_symbols =
  | ImportAll of ident option
  | ImportIdents of (ident * ident option) list

and contract_definition = {
  contract_name : ident;
  contract_kind : contract_kind;
  contract_abstract : bool;
  contract_inheritance : inheritance_specifier list;
  contract_parts : (contract_part node) list;
}

and inheritance_specifier = longident * expression list

and contract_part =
  | TypeDefinition of type_definition
  | StateVariableDeclaration of state_variable_definition
  | FunctionDefinition of function_definition
  | ModifierDefinition of modifier_definition
  | EventDefinition of event_definition
  | UsingForDeclaration of longident * type_ option

and type_definition =
  | EnumDefinition of enum_definition
  | StructDefinition of struct_definition

and enum_definition = ident * ident list

and struct_definition = ident * field_definition list

and field_definition = type_ * ident

and state_variable_definition = {
  var_name : ident;
  var_type : type_;
  var_visibility : visibility; (* def: internal *)
  var_mutability : var_mutability; (* def: mutable *)
  var_override : longident list option;
  var_init : expression option;
  var_static : bool ; (* freeton: default is false *)
}

and function_definition = {
  fun_name : ident;
  fun_params : param list;
  fun_returns : return list;
  fun_modifiers : (longident * expression list option) list;
  fun_visibility : visibility; (* def: public (external in interface) *)
  fun_mutability : fun_mutability; (* ctor: public/forbidden ? *)
  fun_override : longident list option; (* fallback/receive: external *)
  fun_virtual : bool;                   (* but public if missing...  *)
  fun_inline : bool; (* freeton *)
  fun_responsible : bool; (* freeton *)
  fun_body : block option;        (* mutability : nonpayable by default *)
}

and modifier_definition = {
  mod_name : ident;
  mod_params : param list;
  mod_override : longident list option;
  mod_virtual : bool;
  mod_body : block option;
}

and event_definition = {
  event_name : ident;
  event_params : (type_ * bool * ident option) list; (* indexed *)
  event_anonymous : bool;
}

and param = type_ * storage_location option * ident option

and return = type_ * storage_location option * ident option

and type_ =
  | ElementaryType of elementary_type
  | Array of type_ * expression option
  | Mapping of type_ * type_
  | FunctionType of function_type
  | UserDefinedType of longident
  | Optional of type_ list (* freeton *)

and elementary_type =
  | TypeBool
  | TypeInt of int
  | TypeUint of int
  | TypeFixed of int * int
  | TypeUfixed of int * int
  | TypeAddress of bool (* false = address, true = address payable *)
  | TypeBytes of int option (* None = bytes, Some (N) = bytesN *)
  | TypeString
  | TypeAbstract of string

and function_type = {
  fun_type_params : param list;
  fun_type_returns : (type_ * storage_location option) list; (* ident forbid *)
  fun_type_visibility : visibility; (* def: internal *) (* only intern/extern *)
  fun_type_mutability : fun_mutability; (* def: non-payable *)
}

and statement = raw_statement node

and raw_statement =
  | Block of block
  | VariableDefinition of variable_definition
  | ExpressionStatement of expression
  | IfStatement of expression * statement * statement option
  | WhileStatement of expression * statement
  | DoWhileStatement of statement * expression
  | ForStatement of statement option * expression option *
                    expression option * statement
  | TryStatement of expression * return list * block * catch_clause list
  | Emit of expression * function_call_arguments
  | Return of expression option * (ident * expression) list
  | Continue
  | Break
  | PlaceholderStatement
  | RepeatStatement of expression * statement (* freeton *)
  | ForRangeStatement of variable_definition * statement (* freeton *)

and expression = raw_expression node

and raw_expression =
  | BooleanLiteral of bool
  | NumberLiteral of Q.t * number_unit * int option (* hex size / use type *)
  | StringLiteral of string
  | AddressLiteral of string
  | IdentifierExpression of ident
  | ImmediateArray of expression list
  | ArrayAccess of expression * expression option
  | ArraySlice of expression * expression option * expression option
  | TupleExpression of expression option list

  | PrefixExpression of unary_operator * expression
  | SuffixExpression of expression * unary_operator
  | CompareExpression of expression * compare_operator * expression
  | BinaryExpression of expression * binary_operator * expression
  | AssignExpression of expression * expression
  | AssignBinaryExpression of expression * binary_operator * expression

  | IfExpression of expression * expression * expression
  | FieldExpression of expression * ident
  | FunctionCallExpression of expression * function_call_arguments
  | CallOptions of expression * (ident * expression) list
  | NewExpression of type_
  | TypeExpression of type_

and block = statement list

and catch_clause = ident option * param list * block

and variable_definition =
  | VarInfer of ident option list * expression
  | VarType of (type_ * storage_location option * ident) option list *
               expression option

and function_call_arguments =
  | ExpressionList of expression list
  | NameValueList of (ident * expression) list

and contract_kind =
  | Contract
  | Library
  | Interface

and storage_location =
  | Memory
  | Storage
  | Calldata

and var_mutability =
  | MMutable
  | MConstant
  | MImmutable

and fun_mutability =
  | MPure
  | MView
  | MPayable
  | MNonPayable

and visibility =
  | VInternal
  | VExternal (* not for variables *)
  | VPublic
  | VPrivate

and number_unit =
  | Unit
  | Wei
  | Kwei (* Babbage *)
  | Mwei (* Lovelace *)
  | Gwei (* Shannon *)
  | Twei (* Szabo *)
  | Pwei (* Finney *)
  | Ether
  | Hours
  | Minutes
  | Seconds
  | Days
  | Weeks
  | Years
  | Ton (* freeton *)

and unary_operator =
  | UPlus
  | UMinus
  | UNot
  | ULNot
  | UInc
  | UDec
  | UDelete

and binary_operator =
  | BPlus
  | BMinus
  | BDiv
  | BMod
  | BTimes
  | BExp
  | BLShift
  | BRShift
  | BAnd
  | BOr
  | BXor
  | BLAnd
  | BLOr

and compare_operator =
  | CEq
  | CNeq
  | CLt
  | CGt
  | CLeq
  | CGeq


let is_contract = function
  | Contract -> true
  | Library | Interface -> false

let is_library = function
  | Library -> true
  | Contract | Interface -> false

let is_interface = function
  | Interface -> true
  | Contract | Library -> false


let is_mutable = function
  | MMutable -> true
  | MConstant | MImmutable -> false

let is_constant = function
  | MConstant -> true
  | MMutable | MImmutable -> false

let is_immutable = function
  | MImmutable -> true
  | MConstant | MMutable -> false


let is_payable = function
  | MPayable -> true
  | MNonPayable | MView | MPure -> false

let is_nonpayable = function
  | MNonPayable -> true
  | MPayable | MView | MPure -> false


let is_external = function
  | VExternal -> true
  | VInternal | VPublic | VPrivate -> false

let is_internal = function
  | VInternal -> true
  | VExternal | VPublic | VPrivate -> false

let is_private = function
  | VPrivate -> true
  | VExternal | VInternal | VPublic -> false

let is_public = function
  | VPublic -> true
  | VExternal | VInternal | VPrivate -> false

let is_inheritable = function
  | VPublic | VExternal | VInternal -> true
  | VPrivate -> false



let same_mutability m1 m2 =
  match m1, m2 with
  | MPure, MPure -> true
  | MView, MView -> true
  | MPayable, MPayable -> true
  | MNonPayable, MNonPayable -> true
  | _ -> false

(* for the purpose of overriding *)
let convertible_mutability ~from ~to_ =
  match from, to_ with
  | MNonPayable, (MView | MPure | MNonPayable) -> true
  | MNonPayable, MPayable -> false
  | MView, (MPure | MView) -> true
  | MView, (MPayable | MNonPayable) -> false
  | MPure, MPure -> true
  | MPure, (MView | MPayable | MNonPayable) -> false
  | MPayable, MPayable -> true
  | MPayable, (MPure | MView | MNonPayable) -> false



let same_visibility v1 v2 =
  match v1, v2 with
  | VExternal, VExternal -> true
  | VInternal, VInternal -> true
  | VPublic, VPublic -> true
  | VPrivate, VPrivate -> true
  | _ -> false

(* for the purpose of overriding *)
let convertible_visibility ~from ~to_ =
  match from, to_ with
  | VExternal, (VPublic | VExternal) -> true
  | VExternal, (VInternal | VPrivate) -> false
  | VPublic, VPublic -> true
  | VPublic, (VExternal | VInternal | VPrivate) -> false
  | VInternal, VInternal -> true
  | VInternal, (VExternal | VPublic | VPrivate) -> false
  | VPrivate, VPrivate -> true
  | VPrivate, (VExternal | VPublic | VInternal) -> false



let unit_factor unit =
  let z =
    match unit with
    | Unit     -> Z.one
    | Wei      -> Z.one
    | Kwei     -> ExtZ._10_3
    | Mwei     -> ExtZ._10_6
    | Gwei     -> ExtZ._10_9
    | Twei     -> ExtZ._10_12
    | Pwei     -> ExtZ._10_15
    | Ether    -> ExtZ._10_18
    | Hours    -> ExtZ._3600
    | Minutes  -> ExtZ._60
    | Seconds  -> Z.one
    | Days     -> ExtZ._24x3600
    | Weeks    -> ExtZ._7x24x3600
    | Years    -> ExtZ._365x24x3600
    | Ton      -> ExtZ._10_9
  in
  Q.of_bigint z

let apply_unit q unit =
  match unit with
  | Unit | Wei | Seconds -> q
  | _ -> Q.mul q (unit_factor unit)

let apply_unop op q =
  match op with
  | UPlus ->
      Some (q)
  | UMinus ->
      Some (Q.neg q)
  | UNot ->
      if ExtQ.is_int q then
        Some (Q.of_bigint (Z.lognot (Q.num q)))
      else
        None
  | ULNot
  | UInc | UDec
  | UDelete ->
      None

let apply_binop q1 op q2 =
  match op with
  | BPlus ->
      Some (Q.add q1 q2)
  | BMinus ->
      Some (Q.sub q1 q2)
  | BTimes ->
      Some (Q.mul q1 q2)
  | BDiv ->
      Some (Q.div q1 q2)
  | BMod ->
(* TODO: Solidity allows this on fractions *)
      if ExtQ.is_int q1 && ExtQ.is_int q2 then
        Some (Q.of_bigint (snd (Z.ediv_rem (Q.num q1) (Q.num q2))))
      else
        None
  | BExp ->
      if ExtQ.is_int q2 then
        let e = Z.to_int (Q.num q2) in (* Warning: may overflow *)
        let n = Z.pow (Q.num q1) e in
        let d = Z.pow (Q.den q1) e in
        Some (Q.make n d)
      else
        None
  | BAnd ->
      if ExtQ.is_int q1 && ExtQ.is_int q2 then
        Some (Q.of_bigint (Z.logand (Q.num q1) (Q.num q2)))
      else
        None
  | BOr ->
      if ExtQ.is_int q1 && ExtQ.is_int q2 then
        Some (Q.of_bigint (Z.logor (Q.num q1) (Q.num q2)))
      else
        None
  | BXor ->
      if ExtQ.is_int q1 && ExtQ.is_int q2 then
        Some (Q.of_bigint (Z.logxor (Q.num q1) (Q.num q2)))
      else
        None
  | BLShift ->
      if ExtQ.is_int q1 && ExtQ.is_int q2 && ExtQ.is_pos q2 then
        Some (Q.of_bigint (Z.shift_left (Q.num q1) (Q.to_int q2)))
      else
        None
  | BRShift ->
      if ExtQ.is_int q1 && ExtQ.is_int q2 && ExtQ.is_pos q2 then
        Some (Q.of_bigint (Z.shift_right (Q.num q1) (Q.to_int q2)))
      else
        None
  | BLAnd | BLOr ->
      None
