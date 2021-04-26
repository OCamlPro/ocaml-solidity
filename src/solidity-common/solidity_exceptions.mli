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

(** 1. Generic errors *)

(** Raised when an internal invariant is broken *)
exception InvariantBroken of string

(** A syntax error *)
exception SyntaxError of string * pos

(** An error occuring during the typecheck *)
exception TypecheckError of string * pos

(** 2. Exceptions raised by the postprocessor *)

(** Raised when an immutable is updated outside a construction call *)
exception ImmutableUpdatedOutsideConstructor of Ident.t * pos

(** Raised when an immutable is set twice *)
exception ImmutableUpdatedTwice of Ident.t * pos * pos

(** Raised when a constant is set twice *)
exception ConstantUpdatedTwice of Ident.t * pos * pos

(** Raised when a constant is updated *)
exception ConstantUpdated of Ident.t * pos

(** Raised when an immutable is read during construction *)
exception ReadImmutable of Ident.t * pos

(** Raised when a constant is left undefined after construction *)
exception UndefinedConstant of Ident.t

(** Raised when an immutable is left undefined *)
exception UndefinedImmutable of Ident.t

(** Raised when constants are recursively defined *)
exception ConstantCycle of Ident.t list

(** Raised when a constant is defined with a non trivial expression *)
exception ConstantRequiringComputation of Ident.t

(** Raised when a calldata is modified *)
exception CalldataModified of Ident.t * pos

(** Raised when a local is read without having been initialized *)
exception UninitializedReadLocal of storage_location * Ident.t * pos

(** Raised when there a variable name conflict *)
exception VariableAlreadyDefined of Ident.t * pos

(** Raised when there a function name conflict *)
exception FunctionAlreadyDefined of Ident.t * pos

(** Raised when an immutable from an inherited contract is written *)
exception ImmutableDefinedInInheritingContract of Ident.t * (Ident.t * pos)

(** Raised when a non virtual function is overridden *)
exception OverridingNonVirtual of
  Ident.t * (* Fun name *)
  pos * (* Pos of the override *)
  pos (* Pos of the virtual *)

(** Raised when trying to override a function that does not exist *)
exception UnexpectedOverride of Ident.t * pos

(** Raised when trying to override a virtual function without the keyword
    'override' *)
exception ExpectedOverride of Ident.t * pos

(** Generic override error *)
exception WrongOverride of Ident.t * pos * string * string

(** Raised when there is a conflict between inherited virtual functions
    and nothing overrides them. *)
exception NoOverrideMultipleFunDefs of
  IdentSet.t * (* the contracts inherited *)
  Ident.t * (* the inheriting contract *)
  Ident.t (* the function *)

(** Raised when a pure function reads a global *)
exception PureFunctionReadsGlobal of
    Ident.t * (* The function *)
    Ident.t * (* The global *)
    pos (* The read position *)

(** Raised when a pure/view function writes a global *)
exception ForbiddenGlobalWrite of
    Ident.t * (* The function *)
    Ident.t * (* The global *)
    pos (* The read position *)

(** Raised when a function calls another one with
    a less permissive mutability *)
exception ForbiddenCall of
    Ident.t * fun_mutability * (* Caller function & its purity *)
    Ident.t * fun_mutability * (* Called function & its purity *)
    pos (* Call position *)

(** Raised when a read access is made in a pure function *)
exception ForbiddenReadAccess of pos

(** Raised when the state is written in a pure/view function *)
exception ForbiddenWritState of pos

(** Raised when there is a selector conflict between functions *)
exception InconsistentVisibility of
    Ident.t * (* Name of the function *)
    string * (* Name of the selector *)
    pos * (* Position of first definition *)
    pos (* Position of second definition *)

(** Raised when there is no placeholder in a modifier *)
exception MissingPlaceholderStatement of
    Ident.t * (* Modifier name with an empty body *)
    pos

(** Raised when a file global is not a constant *)
exception FileGlobalNotConstant of
    Ident.t * (* Global name *)
    pos

val invariant_broken : string -> 'a

val type_error :
  pos -> ('a, Format.formatter, unit, unit, unit, 'b) format6 -> 'a
