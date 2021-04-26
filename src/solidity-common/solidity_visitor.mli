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

(** Visitors are objects providing utils for exhaustively passing through
    the Solidity AST. *)

open Solidity_ast
open Solidity_common

(** The different kind of actions to perform after each visit *)
type action =
  | SkipChildren
  (** Stops the visit of the current branch *)

  | DoChildren
  (** Visits the branch children *)

  | DoChildrenPost of (unit -> unit)
  (** Visits the branch children and, once the visit is finished,
      calls the function *)

(** The AST visitor.
    Each method is called when reaching an element of the corresponding type
    in the AST. *)
class virtual ast_visitor :
  object
    method virtual visitBinaryOperator : binary_operator -> action
    method virtual visitBool : bool -> action
    method virtual visitChar : char -> action
    method virtual visitCompareOperator : compare_operator -> action
    method virtual visitContractDef : contract_definition -> action
    method virtual visitContractKind : contract_kind -> action
    method virtual visitContractPart : contract_part -> action
    method virtual visitElementaryType : elementary_type -> action
    method virtual visitEventDef : event_definition -> action
    method virtual visitExpression : expression -> action
    method virtual visitFunMutability : fun_mutability -> action
    method virtual visitFunctionCallArguments :
      function_call_arguments -> action
    method virtual visitFunctionDef : function_definition -> action
    method virtual visitFunctionType : function_type -> action
    method virtual visitIdent : Ident.t -> action
    method virtual visitImportDirective : import_directive -> action
    method virtual visitImportSymbols : import_symbols -> action
    method virtual visitInt : int -> action
    method virtual visitList : 'a list -> action
    method virtual visitLongIdent : 'kind LongIdent.t -> action
    method virtual visitModifierDef : modifier_definition -> action
    method virtual visitNode : 'a node -> action
    method virtual visitNumberUnit : number_unit -> action
    method virtual visitOption : 'a option -> action
    method virtual visitQ : Q.t -> action
    method virtual visitSourceUnit : source_unit -> action
    method virtual visitStateVariableDef : state_variable_definition -> action
    method virtual visitStatement : statement -> action
    method virtual visitStorageLocation : storage_location -> action
    method virtual visitString : string -> action
    method virtual visitType : type_ -> action
    method virtual visitTypeDef : type_definition -> action
    method virtual visitUnaryOperator : unary_operator -> action
    method virtual visitVarMutability : var_mutability -> action
    method virtual visitVariableDef : variable_definition -> action
    method virtual visitVisibility : visibility -> action

    (** If the visitor is visiting a node, returns its annotation. *)
    method getAnnot : unit -> annot option

    (** If the visitor is visiting a node, returns its location. *)
    method getPos : unit -> pos option

    (* Do not use these methods. Todo: hide them *)
    method setAnnot : annot option -> unit
    method setPos : pos option -> unit
  end

(** A dummy visitor. Visits the whole AST and does nothing.
    You may inherit this visitor and redefine its methods to
    avoid redefining all the methods. *)
class init_ast_visitor :
  object
    method visitBinaryOperator        : binary_operator -> action
    method visitBool                  : bool -> action
    method visitChar                  : char -> action
    method visitCompareOperator       : compare_operator -> action
    method visitContractDef           : contract_definition -> action
    method visitContractKind          : contract_kind -> action
    method visitContractPart          : contract_part -> action
    method visitElementaryType        : elementary_type -> action
    method visitEventDef              : event_definition -> action
    method visitExpression            : expression -> action
    method visitFunMutability         : fun_mutability -> action
    method visitFunctionCallArguments : function_call_arguments -> action
    method visitFunctionDef           : function_definition -> action
    method visitFunctionType          : function_type -> action
    method visitIdent                 : Ident.t -> action
    method visitImportDirective       : import_directive -> action
    method visitImportSymbols         : import_symbols -> action
    method visitInt                   : int -> action
    method visitList                  : 'a list -> action
    method visitLongIdent             : 'kind LongIdent.t -> action
    method visitModifierDef           : modifier_definition -> action
    method visitNode                  : 'a node -> action
    method visitNumberUnit            : number_unit -> action
    method visitOption                : 'a option -> action
    method visitQ                     : Q.t -> action
    method visitSourceUnit            : source_unit -> action
    method visitStateVariableDef      : state_variable_definition -> action
    method visitStatement             : statement -> action
    method visitStorageLocation       : storage_location -> action
    method visitString                : string -> action
    method visitType                  : type_ -> action
    method visitTypeDef               : type_definition -> action
    method visitUnaryOperator         : unary_operator -> action
    method visitVarMutability         : var_mutability -> action
    method visitVariableDef           : variable_definition -> action
    method visitVisibility            : visibility -> action

    method getAnnot : unit -> annot option
    method getPos   : unit -> pos option

    (* Do not use these methods. Todo: hide them *)
    method setAnnot : annot option -> unit
    method setPos   : pos option -> unit
  end

(** Functions visiting the AST. *)

val visitNode : ((#ast_visitor as 'b) -> 'a -> unit) -> 'b -> 'a node -> unit

val visitType : #ast_visitor -> type_ -> unit

val visitParam : #ast_visitor -> param -> unit

val visitFunctionType : #ast_visitor -> function_type -> unit

val visitTypeDef : #ast_visitor -> type_definition -> unit

val visitContractDef : #ast_visitor -> contract_definition -> unit

val visitInheritanceSpecifier : #ast_visitor -> inheritance_specifier -> unit

val visitContractPart : #ast_visitor -> contract_part -> unit

val visitStateVariableDef : #ast_visitor -> state_variable_definition -> unit

val visitBlock : #ast_visitor -> block -> unit

val visitFunctionDef : #ast_visitor -> function_definition -> unit

val visitFunctionDefNode : #ast_visitor -> function_definition node -> unit

val visitModifierDef : #ast_visitor -> modifier_definition -> unit

val visitModifierDefNode : #ast_visitor -> modifier_definition node -> unit

val visitEventDef : #ast_visitor -> event_definition -> unit

val visitCatchClause : #ast_visitor -> catch_clause -> unit

val visitStatement : #ast_visitor -> statement -> unit

val visitExpression : #ast_visitor -> expression -> unit

val visitVariableDef : #ast_visitor -> variable_definition -> unit

val visitFunctionCallArguments : #ast_visitor -> function_call_arguments -> unit

val visitSourceUnit : #ast_visitor -> source_unit -> unit

val visitImportDirective : #ast_visitor -> import_directive -> unit

val visitImportSymbols : #ast_visitor -> import_symbols -> unit

val visitModule : #ast_visitor -> module_ -> unit
