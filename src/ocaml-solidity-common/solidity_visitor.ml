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

(* Actions to perform during a visit *)
type action =
  (* Skips the children and goes to the next node *)
  | SkipChildren

  (* Calculates on the next node *)
  | DoChildren

  (* DoChildren and performs the function afterwards *)
  | DoChildrenPost of (unit -> unit)

class virtual base_visitor = object
  method virtual visitBool : bool -> action
  method virtual visitInt : int -> action
  method virtual visitChar : Char.t -> action
  method virtual visitZ : Z.t -> action
  method virtual visitQ : Q.t -> action
  method virtual visitString : string -> action
  method virtual visitOption : 'a. 'a option -> action
  method virtual visitList : 'a. 'a list -> action
  method virtual visitNode : 'a. 'a node -> action
  method virtual visitIdent : Ident.t -> action
  method virtual visitLongIdent : 'kind. 'kind LongIdent.t -> action
  method virtual visitContractKind : Solidity_ast.contract_kind -> action
  method virtual visitVisibility : Solidity_ast.visibility -> action
  method virtual visitFunMutability : Solidity_ast.fun_mutability -> action
  method virtual visitVarMutability : Solidity_ast.var_mutability -> action
  method virtual visitStorageLocation : Solidity_ast.storage_location -> action
  method virtual visitNumberUnit : Solidity_ast.number_unit -> action
  method virtual visitElementaryType : Solidity_ast.elementary_type -> action
  method virtual visitUnaryOperator : Solidity_ast.unary_operator -> action
  method virtual visitBinaryOperator : Solidity_ast.binary_operator -> action
  method virtual visitCompareOperator : Solidity_ast.compare_operator -> action
end

(* To include in every visitor to avoid defining every method *)
class init_base_visitor = object
  inherit base_visitor
  method visitBool _ = DoChildren
  method visitInt _ = DoChildren
  method visitChar _ = DoChildren
  method visitZ _ = DoChildren
  method visitQ _ = DoChildren
  method visitString _ = DoChildren
  method visitOption _ = DoChildren
  method visitList _ = DoChildren
  method visitNode _ = DoChildren
  method visitIdent _ = DoChildren
  method visitLongIdent _ = DoChildren
  method visitContractKind _ = DoChildren
  method visitVisibility _ = DoChildren
  method visitFunMutability _ = DoChildren
  method visitVarMutability _ = DoChildren
  method visitStorageLocation _ = DoChildren
  method visitNumberUnit _ = DoChildren
  method visitElementaryType _ = DoChildren
  method visitUnaryOperator _ = DoChildren
  method visitBinaryOperator _ = DoChildren
  method visitCompareOperator _ = DoChildren
end

(* The strategy for each action *)
let handleAction (visit : 'a -> action) (continueVisit : 'a -> unit) (node : 'a) =
  match visit node with
  | SkipChildren -> ()
  | DoChildren -> continueVisit node
  | DoChildrenPost post -> continueVisit node; post ()

let visitOpt
    (visitElt : #base_visitor -> 'a -> unit)
    (v : #base_visitor) : 'a option -> unit =
  let continueVisit = function
    | None -> ()
    | Some elt -> visitElt v elt in
  handleAction v#visitOption continueVisit

let visitList
    (visitElt : #base_visitor -> 'a -> unit)
    (v : #base_visitor) : 'a list -> unit =
  let continueVisit = List.iter (visitElt v) in
  handleAction v#visitList continueVisit

let visitXY
    (visitX : #base_visitor -> 'a -> unit)
    (visitY : #base_visitor -> 'b -> unit)
    (visitor : #base_visitor)
    ((x, y) : ('a * 'b)) : unit =
  visitX visitor x;
  visitY visitor y

let visitXYZ
    (visitX : #base_visitor -> 'a -> unit)
    (visitY : #base_visitor -> 'b -> unit)
    (visitZ : #base_visitor -> 'c -> unit)
    (visitor : #base_visitor)
    ((x, y, z) : ('a * 'b * 'c)) : unit =
  visitX visitor x;
  visitY visitor y;
  visitZ visitor z

let visitXYZT
    (visitX : #base_visitor -> 'a -> unit)
    (visitY : #base_visitor -> 'b -> unit)
    (visitZ : #base_visitor -> 'c -> unit)
    (visitT : #base_visitor -> 'd -> unit)
    (visitor : #base_visitor)
    ((x, y, z, t) : ('a * 'b * 'c * 'd)) : unit =
  visitX visitor x;
  visitY visitor y;
  visitZ visitor z;
  visitT visitor t

let visitNode
    (visitElt : #base_visitor -> 'a -> unit)
    (v : #base_visitor)
    (elt : 'a node) : unit =
  let continueVisit elt =
    let old_annot = v#getAnnot () in
    let old_pos = v#getPos () in
    let () =
      v#setAnnot (Some elt.annot);
      v#setPos   (Some elt.pos) in
    let res = visitElt v elt.contents in
    let () =
      v#setAnnot old_annot;
      v#setPos   old_pos in
    res in
  handleAction v#visitNode continueVisit elt

let leaf (visitorVisit : 'a -> action) (elt : 'a) : unit =
  handleAction visitorVisit ignore elt

let visitBool (v : #base_visitor) (b : bool) : unit = leaf v#visitBool b
let visitInt (v : #base_visitor) (i : int) : unit = leaf v#visitInt i
let visitChar (v : #base_visitor) (c : Char.t) : unit = leaf v#visitChar c
let visitZ (v : #base_visitor) (z : Z.t) : unit = leaf v#visitZ z
let visitQ (v : #base_visitor) (q : Q.t) : unit = leaf v#visitQ q
let visitString (v : #base_visitor) (s : string) = leaf v#visitString s
let visitIdent (v : #base_visitor) = leaf v#visitIdent
let visitLongIdent (v : #base_visitor) = leaf v#visitLongIdent
let visitContractKind (v : #base_visitor) = leaf v#visitContractKind
let visitVisibility (v : #base_visitor) = leaf v#visitVisibility
let visitFunMutability (v : #base_visitor) = leaf v#visitFunMutability
let visitVarMutability (v : #base_visitor) = leaf v#visitVarMutability
let visitStorageLocation (v : #base_visitor) = leaf v#visitStorageLocation
let visitNumberUnit (v : #base_visitor) = leaf v#visitNumberUnit
let visitElementaryType (v : #base_visitor) = leaf v#visitElementaryType
let visitUnaryOperator (v : #base_visitor) = leaf v#visitUnaryOperator
let visitBinaryOperator (v : #base_visitor) = leaf v#visitBinaryOperator
let visitCompareOperator (v : #base_visitor) = leaf v#visitCompareOperator

let visitIntMap
    (visitElt : #base_visitor -> 'elt -> unit)
    (v : #base_visitor)
    (map : 'elt IntMap.t) : unit =
  IntMap.iter
    (fun (key : int) (elt : 'elt) -> visitInt v key; visitElt v elt)
    map

module Ast = struct
  open Solidity_ast

  class virtual ast_visitor = object
    inherit base_visitor

    method virtual visitImportDirective : import_directive -> action
    method virtual visitImportSymbols : import_symbols -> action
    method virtual visitType : type_ -> action
    method virtual visitFunctionType : function_type -> action
    method virtual visitTypeDef : type_definition -> action
    method virtual visitContractDef : contract_definition -> action
    method virtual visitContractPart : contract_part -> action
    method virtual visitStateVariableDef : state_variable_definition -> action
    method virtual visitFunctionDef : function_definition -> action
    method virtual visitModifierDef : modifier_definition -> action
    method virtual visitEventDef : event_definition -> action
    method virtual visitStatement : statement -> action
    method virtual visitExpression : expression -> action
    method virtual visitVariableDef : variable_definition -> action
    method virtual visitFunctionCallArguments : function_call_arguments -> action
    method virtual visitSourceUnit : source_unit -> action
    val mutable current_annot : annot option = None
    val mutable current_position : pos option = None

    method getAnnot () : annot option = current_annot
    method setAnnot (annot : annot option) : unit = current_annot <- annot

    method getPos () : pos option = current_position
    method setPos (pos : pos option) : unit = current_position <- pos
  end

  class init_ast_visitor = object
    inherit init_base_visitor
    inherit ast_visitor

    method visitImportDirective _ = DoChildren
    method visitImportSymbols _ = DoChildren
    method visitType _ = DoChildren
    method visitFunctionType _ = DoChildren
    method visitTypeDef _ = DoChildren
    method visitContractDef _ = DoChildren
    method visitContractPart _ = DoChildren
    method visitStateVariableDef _ = DoChildren
    method visitFunctionDef _ = DoChildren
    method visitModifierDef _ = DoChildren
    method visitEventDef _ = DoChildren
    method visitStatement _ = DoChildren
    method visitExpression _ = DoChildren
    method visitVariableDef _ = DoChildren
    method visitFunctionCallArguments _ = DoChildren
    method visitSourceUnit _ = DoChildren
  end

  let rec visitType (v : ast_visitor) (t : Solidity_ast.type_) : unit =
    let continueVisit (t : Solidity_ast.type_) : unit =
      match t with
      | ElementaryType (e) ->
          visitElementaryType (v :> base_visitor) e
      | Array (t, e) ->
          visitType v t;
          visitOpt visitExpression v e
      | Mapping (tk, tv) ->
          visitType v tk;
          visitType v tv
      | FunctionType f ->
          visitFunctionType v f
      | UserDefinedType li ->
          visitNode visitLongIdent v li
    in
    handleAction v#visitType continueVisit t

  and visitParam (v : ast_visitor) (p : Solidity_ast.param) : unit =
    visitXYZ visitType (visitOpt visitStorageLocation) (visitOpt @@ visitNode visitIdent) v p

  and visitFunctionType (v : ast_visitor) (ft : Solidity_ast.function_type) : unit =
    let continueVisit
        ({fun_type_params;
          fun_type_returns;
          fun_type_visibility;
          fun_type_mutability} : Solidity_ast.function_type) : unit =
      visitList visitParam v fun_type_params;
      visitList (visitXY visitType (visitOpt visitStorageLocation)) v fun_type_returns;
      visitVisibility v fun_type_visibility;
      visitFunMutability v fun_type_mutability in
    handleAction v#visitFunctionType continueVisit ft

  and visitTypeDef (v : ast_visitor) (tf : type_definition) : unit =
    let continueVisit (tf : type_definition) : unit =
      match tf with
      | EnumDefinition (i, il) ->
          visitNode visitIdent v i;
          visitList (visitNode visitIdent) v il
      | StructDefinition (i, l) ->
          visitNode visitIdent v i;
          visitList (visitXY visitType (visitNode visitIdent)) v l
    in
    handleAction v#visitTypeDef continueVisit tf

  and visitContractDef (v : ast_visitor) (cd : contract_definition) : unit =
    let continueVisit
        ({contract_name;
          contract_kind;
          contract_abstract;
          contract_inheritance;
          contract_parts
         } : contract_definition) : unit =
      visitNode visitIdent v contract_name;
      visitContractKind v contract_kind;
      visitBool v contract_abstract;
      visitList visitInheritanceSpecifier v contract_inheritance;
      visitList (visitNode visitContractPart) v contract_parts;
      () in
    handleAction v#visitContractDef continueVisit cd

  and visitInheritanceSpecifier (v : ast_visitor) (is : Solidity_ast.inheritance_specifier) =
    visitXY
      (visitNode visitLongIdent)
      (visitList @@ visitExpression)
      v
      is

  and visitContractPart (v : ast_visitor) (cp : Solidity_ast.contract_part) : unit =
    let continueVisit (cp : Solidity_ast.contract_part) : unit =
      match cp with
      | Solidity_ast.TypeDefinition td -> visitTypeDef v td
      | StateVariableDeclaration svd -> visitStateVariableDef v svd
      | FunctionDefinition fd -> visitFunctionDef v fd
      | ModifierDefinition md -> visitModifierDef v md
      | EventDefinition ed -> visitEventDef v ed
      | UsingForDeclaration (li, t_opt) ->
          visitNode visitLongIdent v li;
          visitOpt visitType v t_opt
    in
    handleAction v#visitContractPart continueVisit cp

  and visitStateVariableDef (v : ast_visitor) (svd : state_variable_definition) : unit =
    let continueVisit
        ({var_name;
          var_type;
          var_visibility;
          var_mutability;
          var_override;
          var_init
         } : state_variable_definition) : unit =
      visitNode visitIdent v var_name;
      visitType v var_type;
      visitVisibility v var_visibility;
      visitVarMutability v var_mutability;
      visitOpt (visitList (visitNode visitLongIdent)) v var_override;
      visitOpt visitExpression v var_init
    in
    handleAction v#visitStateVariableDef continueVisit svd

  and visitBlock (v : ast_visitor) (b : block) : unit = visitList visitStatement v b

  and visitFunctionDef (v : ast_visitor) (fd : function_definition) : unit =
    let continueVisit
        ({fun_name;
          fun_params;
          fun_returns;
          fun_modifiers;
          fun_visibility;
          fun_mutability;
          fun_override;
          fun_virtual;
          fun_body
         } : function_definition) : unit =
      visitNode visitIdent v fun_name;
      visitList visitParam v fun_params;
      visitList visitParam v fun_returns;
      visitList
        (visitXY
           (visitNode visitLongIdent)
           (visitOpt (visitList visitExpression))
        )
        v
        fun_modifiers;
      visitVisibility v fun_visibility;
      visitFunMutability v fun_mutability;
      visitOpt (visitList (visitNode visitLongIdent)) v fun_override;
      visitBool v fun_virtual;
      visitOpt visitBlock v fun_body in
    handleAction v#visitFunctionDef continueVisit fd

  and visitFunctionDefNode (v : ast_visitor) (fdn : function_definition node) : unit =
    visitNode visitFunctionDef v fdn

  and visitModifierDef (v : ast_visitor) (md : modifier_definition) : unit =
    let continueVisit
        ({mod_name;
          mod_params;
          mod_override;
          mod_virtual;
          mod_body
         } : modifier_definition) : unit =
      visitNode visitIdent v mod_name;
      visitList visitParam v mod_params;
      visitOpt (visitList (visitNode visitLongIdent)) v mod_override;
      visitBool v mod_virtual;
      visitOpt visitBlock v mod_body in
    handleAction v#visitModifierDef continueVisit md

  and visitModifierDefNode (v : ast_visitor) (mdn : modifier_definition node) : unit =
    visitNode visitModifierDef v mdn

  and visitEventDef (v : ast_visitor) (ed : event_definition) : unit =
    let continueVisit
        ({event_name;
          event_params;
          event_anonymous
         } : event_definition) : unit =
      visitNode visitIdent v event_name;
      visitList
        (visitXYZ
           visitType
           visitBool
           (visitOpt (visitNode visitIdent)))
        v
        event_params;
      visitBool v event_anonymous;
    in
    handleAction v#visitEventDef continueVisit ed

  and visitCatchClause (v : ast_visitor) (cc : catch_clause) : unit =
    visitXYZ
      (visitOpt (visitNode visitIdent))
      (visitList visitParam)
      visitBlock
      v cc

  and visitStatement (v : ast_visitor) (s : statement) : unit =
    let continueVisit (s : statement) : unit =
      match s.contents with
      | Block b -> visitBlock v b
      | VariableDefinition vd -> visitVariableDef v vd
      | ExpressionStatement e -> visitExpression v e
      | IfStatement (if_, then_, else_) ->
          visitExpression v if_;
          visitStatement v then_;
          visitOpt visitStatement v else_
      | WhileStatement (e, s) ->
          visitExpression v e;
          visitStatement v s
      | DoWhileStatement (s, e) ->
          visitStatement v s;
          visitExpression v e
      | ForStatement (so, eo1, eo2, s) ->
          visitOpt visitStatement v so;
          visitOpt visitExpression v eo1;
          visitOpt visitExpression v eo2;
          visitStatement v s
      | TryStatement (e, rl, b, catchs) ->
          visitExpression v e;
          visitList visitParam v rl;
          visitBlock v b;
          visitList visitCatchClause v catchs
      | Emit (e, fca) ->
          visitExpression v e;
          visitFunctionCallArguments v fca
      | Return eo ->
          visitOpt visitExpression v eo
      | Continue | Break | PlaceholderStatement -> ()
    in
    handleAction v#visitStatement continueVisit s

  and visitExpression (v : ast_visitor) (e : expression) : unit =
    let continueVisit (e : expression) : unit =
      match e.contents with
      | BooleanLiteral b -> visitBool v b
      | NumberLiteral (q, u, s) ->
          visitQ v q;
          visitNumberUnit v u;
          visitOpt visitInt v s
      | StringLiteral s -> visitString v s
      | AddressLiteral s -> visitString v s
      | IdentifierExpression i -> visitNode visitIdent v i
      | ImmediateArray el -> visitList visitExpression v el
      | ArrayAccess (e, eo) ->
          visitExpression v e;
          visitOpt visitExpression v eo
      | ArraySlice (e, eo1, eo2) ->
          visitExpression v e;
          visitOpt visitExpression v eo1;
          visitOpt visitExpression v eo2
      | TupleExpression eol ->
          visitList (visitOpt visitExpression) v eol
      | PrefixExpression (u, e) -> visitUnaryOperator v u; visitExpression v e
      | SuffixExpression (e, u) -> visitExpression v e; visitUnaryOperator v u
      | CompareExpression (e1, co, e2) ->
          visitExpression v e1;
          visitCompareOperator v co;
          visitExpression v e2
      | BinaryExpression (e1, bo, e2)
      | AssignBinaryExpression (e1, bo, e2) ->
          visitExpression v e1;
          visitBinaryOperator v bo;
          visitExpression v e2
      | AssignExpression (e1, e2) ->
          visitExpression v e1;
          visitExpression v e2
      | IfExpression (e1, e2, e3) ->
          visitExpression v e1;
          visitExpression v e2;
          visitExpression v e3
      | FieldExpression (e, i) -> visitExpression v e; visitNode visitIdent v i
      | FunctionCallExpression (e, fca) ->
          visitExpression v e;
          visitFunctionCallArguments v fca
      | CallOptions (e, l) ->
          visitExpression v e;
          visitList (visitXY (visitNode visitIdent) visitExpression) v l
      | NewExpression t
      | TypeExpression t -> visitType v t
    in
    handleAction v#visitExpression continueVisit e

  and visitVariableDef (v : ast_visitor) (vd : variable_definition) : unit =
    let continueVisit (vd : variable_definition) : unit =
      match vd with
      | VarInfer (iol, e) ->
          visitList (visitOpt (visitNode visitIdent)) v iol;
          visitExpression v e
      | VarType (l, eo) ->
          visitList
            (visitOpt
               (visitXYZ
                  visitType
                  (visitOpt visitStorageLocation)
                  (visitNode visitIdent))) v l;
          visitOpt visitExpression v eo
    in
    handleAction v#visitVariableDef continueVisit vd

  and visitFunctionCallArguments (v : ast_visitor) (fca : function_call_arguments) : unit =
    let continueVisit (fca : function_call_arguments) : unit =
      match fca with
      | ExpressionList el -> visitList visitExpression v el
      | NameValueList l -> visitList (visitXY (visitNode visitIdent) visitExpression) v l
    in
    handleAction v#visitFunctionCallArguments continueVisit fca

  and visitSourceUnit (v : ast_visitor) (su : source_unit) : unit =
    let continueVisit (su : source_unit) : unit =
      match su with
      | Pragma (i, s) ->
          visitIdent v i;
          visitString v s
      | Import id ->
          visitImportDirective v id
      | GlobalTypeDefinition td -> visitTypeDef v td
      | GlobalFunctionDefinition fd -> visitFunctionDef v fd
      | GlobalVariableDefinition vd -> visitStateVariableDef v vd
      | ContractDefinition cdn -> visitContractDef v cdn
    in
    handleAction v#visitSourceUnit continueVisit su

  and visitImportDirective (v : ast_visitor) (id : import_directive) : unit =
    let continueVisit ({import_from; import_symbols} : import_directive) : unit =
      visitString v import_from;
      visitImportSymbols v import_symbols in
    handleAction v#visitImportDirective continueVisit id

  and visitImportSymbols (v : ast_visitor) (is : import_symbols) : unit =
    let continueVisit = function
      | ImportAll (io) ->
          visitOpt (visitNode visitIdent) v io
      | ImportIdents l ->
          visitList (visitXY (visitNode visitIdent) (visitOpt (visitNode visitIdent))) v l in
    handleAction v#visitImportSymbols continueVisit is

  and visitModule (v : ast_visitor) (m : module_) : unit =
    visitList (visitNode visitSourceUnit) v m.module_units
end
