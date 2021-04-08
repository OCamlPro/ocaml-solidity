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

(** Generic identifiers *)
type ident = Ident.t node

(** Context relative identifiers *)
type longident = relative LongIdent.t node

(** The program definition.
    Modules (files) are sorted in different ways, but they all are the same. *)
type program = {
  program_modules : module_ list;
  program_modules_by_id : module_ IdentMap.t;
  program_modules_by_file : module_ StringMap.t;
}

(** A file definition *)
and module_ = {
  module_file : string;
  module_id : Ident.t;
  module_units : module_units;
}

and module_units = source_unit node list

(** The different kind of contents. *)
and source_unit =
  | Pragma of (Ident.t * string)
  (** Options for the official solidity compiler *)

  | Import of import_directive
  (** Import directive *)

  | GlobalTypeDefinition of type_definition
  (** Definition of a type for the whole file *)

  | GlobalFunctionDefinition of function_definition
  (** Definition of a function for the whole file *)

  | GlobalVariableDefinition of state_variable_definition
  (** Definition of a variable for the whole file *)

  | ContractDefinition of contract_definition
  (** Definition of a contract *)

and import_directive = {
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
  contract_parts : contract_part node list;
}

and inheritance_specifier = longident * expression list

(** Components of a contract *)
and contract_part =
  | TypeDefinition of type_definition
  (** Definition of a local type ; can be an enum or a struct *)

  | StateVariableDeclaration of state_variable_definition
  (** Declaration/definition of a state variable *)

  | FunctionDefinition of function_definition
  (** Declaration/definition of a state variable *)

  | ModifierDefinition of modifier_definition
  (** Definition of a modifier *)

  | EventDefinition of event_definition
  (** Definition of an event *)

  | UsingForDeclaration of longident * type_ option

and type_definition =
  | EnumDefinition   of enum_definition
  | StructDefinition of struct_definition

and enum_definition = ident * ident list

and struct_definition = ident * field_definition list

and field_definition = type_ * ident

(** Definition of a state variable.
    Its initializer is optional, in which case it is only a declaration. *)
and state_variable_definition = {
  var_name : ident;
  var_type : type_;
  var_visibility : visibility;
  var_mutability : var_mutability;
  var_override : longident list option;
  var_init : expression option;
}

(** Definition of a contract function.
    Its body is optional, in which case it is only a declaration. *)
and function_definition = {
  fun_name : ident;
  fun_params : param list;
  fun_returns : return list;
  fun_modifiers : (longident * expression list option) list;
  fun_visibility : visibility;
  fun_mutability : fun_mutability;
  fun_override : longident list option;
  fun_virtual : bool;
  fun_body : block option;
}

(** Definition of a modifier.
    Its body is optional, in which case it is only a declaration. *)
and modifier_definition = {
  mod_name : ident;
  mod_params : param list;
  mod_override : longident list option;
  mod_virtual : bool;
  mod_body : block option;
}

(** Definition of an event. *)
and event_definition = {
  event_name : ident;
  event_params : (type_ * bool * ident option) list;
  event_anonymous : bool;
}

and param = type_ * storage_location option * ident option

and return = type_ * storage_location option * ident option

(** Type identifiers *)
and type_ =
  | ElementaryType of elementary_type
  (** A builtin elementary type *)

  | Array of type_ * expression option
  (** Array types *)

  | Mapping of type_ * type_
  (** Type of mappings with types (key, element) *)

  | FunctionType of function_type
  (** Type of functions *)

  | UserDefinedType of longident
  (** User defined type (see type_definition) *)

and elementary_type =
  | TypeBool
  | TypeInt of int
  | TypeUint of int
  | TypeFixed of int * int
  | TypeUfixed of int * int
  | TypeAddress of bool (** bool => payable *)
  | TypeBytes of int option (** None => equivalent to byte arrays *)
  | TypeString

and function_type = {
  fun_type_params : param list;
  fun_type_returns : (type_ * storage_location option) list;
  fun_type_visibility : visibility;
  fun_type_mutability : fun_mutability;
}

and statement = raw_statement node

and raw_statement =
  | Block of block
  (** An ordered list of statements *)

  | VariableDefinition of variable_definition
  (** Local variable definition *)

  | ExpressionStatement of expression
  (** Single expression returning nothing *)

  | IfStatement of expression * statement * statement option
  (** If-then-else statement; else is optional *)

  | WhileStatement of expression * statement
  (** While loop;
      expression is the boolean condition, statement is its body *)

  | DoWhileStatement of statement * expression
  (** Do while loop;
      expression is the boolean condition, statement is its body *)

  | ForStatement of statement option * expression option *
                    expression option * statement
  (** For loop ;
      the first statement is the initializer, the next
      expression is the condition, the third is the for action
      and the last statement the loop body. *)

  | TryStatement of expression * return list * block * catch_clause list
  (** Try-catch statement *)

  | Emit of expression * function_call_arguments
  (** Event emission *)

  | Return of expression option
  (** Return statement *)

  | Continue
  (** Continue (loop statement) *)

  | Break
  (** Break (loop statement) *)

  | PlaceholderStatement
  (** Placeholder for modifiers *)


and expression = raw_expression node

and raw_expression =
  | BooleanLiteral of bool
  | NumberLiteral of Q.t * number_unit * int option
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
  (** Variable without type *)

  | VarType of (type_ * storage_location option * ident) option list *
               expression option
  (** Typed variable *)

and function_call_arguments =
  | ExpressionList of expression list
  (** Anonymous arguments *)

  | NameValueList of (ident * expression) list
  (** Named arguments *)

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

val is_contract  : contract_kind -> bool
val is_library   : contract_kind -> bool
val is_interface : contract_kind -> bool

val is_mutable   : var_mutability -> bool
val is_constant  : var_mutability -> bool
val is_immutable : var_mutability -> bool

val is_payable    : fun_mutability -> bool
val is_nonpayable : fun_mutability -> bool

val is_external    : visibility -> bool
val is_internal    : visibility -> bool
val is_private     : visibility -> bool
val is_public      : visibility -> bool

(** True iff not private *)
val is_inheritable : visibility -> bool

(** Checks the equality of mutabilities *)
val same_mutability : fun_mutability -> fun_mutability -> bool

(** Tests if a function with `from` mutability can be overridden by a
    function with `to` mutability. *)
val convertible_mutability :
  from:fun_mutability -> to_:fun_mutability -> bool

(** Checks the equality of visibilities *)
val same_visibility : visibility -> visibility -> bool

(** Tests if a function with `from` visibility can be overridden by a
    function with `to` visibility. *)
val convertible_visibility : from:visibility -> to_:visibility -> bool

(** Returns the quantity in argument with the unit in argument
    in the smallest quantity of the language of the similar
    unit.
    Examples:
    * `apply_unit 1 Minutes = 60 (Seconds)`
    * `apply_unit 1 Ether = 1e15 (Wei)`
    * `apply_unit 1 Unit = 1 (Unit)` *)
val apply_unit : Q.t -> number_unit -> Q.t

(** Apply the unary operator in argument to a zarith rational.
    Returns `None` when applying UNot on non-integers
    If the operator is not an arithmetical operator, also returns `None`. *)
val apply_unop : unary_operator -> Q.t -> Q.t option

(** Apply the binary operator in argument to a zarith rational.
    If the operator is not an arithmetical operator, returns `None`. *)
val apply_binop : Q.t -> binary_operator -> Q.t -> Q.t option
