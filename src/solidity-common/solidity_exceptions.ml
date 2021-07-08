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

exception InvariantBroken of string
exception SyntaxError of string * pos
exception TypecheckError of string * pos
exception ImmutableUpdatedOutsideConstructor of Ident.t * pos
exception ImmutableUpdatedTwice of Ident.t * pos * pos
exception ConstantUpdatedTwice of Ident.t * pos * pos
exception ConstantUpdated of Ident.t * pos
exception ReadImmutable of Ident.t * pos
exception UndefinedConstant of Ident.t
exception UndefinedImmutable of Ident.t
exception ConstantCycle of Ident.t list
exception ConstantRequiringComputation of Ident.t
exception CalldataModified of Ident.t * pos
exception UninitializedReadLocal of storage_location * Ident.t * pos
exception VariableAlreadyDefined of Ident.t * pos
exception FunctionAlreadyDefined of Ident.t * pos
exception ImmutableDefinedInInheritingContract of Ident.t * (Ident.t * pos)
exception OverridingNonVirtual of Ident.t * pos * pos
exception UnexpectedOverride of Ident.t * pos
exception ExpectedOverride of Ident.t * pos
exception WrongOverride of Ident.t * pos * string * string
exception NoOverrideMultipleFunDefs of IdentSet.t * Ident.t * Ident.t
exception PureFunctionReadsGlobal of Ident.t * Ident.t *  pos
exception ForbiddenGlobalWrite of Ident.t * Ident.t * pos
exception ForbiddenCall of
    Ident.t * fun_mutability *
    Ident.t * fun_mutability *
    pos
exception ForbiddenReadAccess of pos
exception ForbiddenWritState of pos
exception InconsistentVisibility of Ident.t * string * pos * pos
exception MissingPlaceholderStatement of Ident.t * pos
exception FileGlobalNotConstant of Ident.t * pos

let invariant_broken s =
  raise (InvariantBroken s)

let type_error pos fmt =
  Format.kasprintf (fun s -> raise (TypecheckError (s, pos))) fmt

let string_of_exn = function
  | Solidity_common.GenericError (s) ->
      Printf.sprintf "Generic error: %s" s
  | SyntaxError (s, pos) ->
      let loc, source = Solidity_common.string_of_pos pos in
      Format.sprintf "%s:\nSyntax error: %s\n%s" loc s source
  | TypecheckError (s, pos ) ->
      let loc, source = Solidity_common.string_of_pos pos in
      Printf.sprintf "%s:\nType error: %s\n%s" loc s source
  | ForbiddenCall (id1, mut1,
                   id2, mut2, pos ) ->
      let loc, source = Solidity_common.string_of_pos pos in
      Printf.sprintf
        "%s:\nType error: Forbidden Call %S %s to %S %s\n%s"
        loc
        ( Ident.to_string id1 )
        ( Solidity_printer.string_of_fun_mutability mut1 )
        ( Ident.to_string id2 )
        ( Solidity_printer.string_of_fun_mutability mut2 )
        source
  | exn ->
      Printexc.to_string exn
