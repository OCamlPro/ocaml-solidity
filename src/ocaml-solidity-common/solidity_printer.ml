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

let spaces = String.make 1000 ' '

let bprint b indent s =
  Printf.bprintf b "%s%s\n" (String.sub spaces 0 indent) s


let string_of_contract_kind = function
  | Contract ->  "contract"
  | Library ->   "library"
  | Interface -> "interface"

let string_of_storage_location = function
  | Memory ->   "memory"
  | Storage ->  "storage"
  | Calldata -> "calldata"

let string_of_fun_mutability = function
  | MPure ->       "pure"
  | MView ->       "view"
  | MPayable ->    "payable"
  | MNonPayable -> "nonpayable"

let string_of_var_mutability = function
  | MMutable ->   ""
  | MImmutable -> "immutable"
  | MConstant ->  "constant"

let string_of_visibility = function
  | VInternal -> "internal"
  | VExternal -> "external"
  | VPublic ->   "public"
  | VPrivate ->  "private"

let string_of_number_unit = function
  | Unit ->     ""
  | Wei ->      "wei"
  | Kwei ->     "kwei"
  | Mwei ->     "mwei"
  | Gwei ->     "gwei"
  | Twei ->     "szabo"
  | Pwei ->     "finney"
  | Ether ->    "ether"
  | Hours ->    "hours"
  | Minutes ->  "minutes"
  | Seconds ->  "seconds"
  | Days ->     "days"
  | Weeks ->    "weeks"
  | Years ->    "years"

let string_of_unop = function
  | UPlus ->   "+"
  | UMinus ->  "-"
  | UNot ->    "!"
  | ULNot ->   "~"
  | UInc ->    "++"
  | UDec ->    "--"
  | UDelete -> "delete"

let string_of_binop = function
  | BPlus ->   "+"
  | BMinus ->  "-"
  | BDiv ->    "/"
  | BMod ->    "%"
  | BTimes ->  "*"
  | BExp ->    "**"
  | BLShift -> "<<"
  | BRShift -> ">>"
  | BAnd ->    "&"
  | BOr ->     "|"
  | BXor ->    "^"
  | BLAnd ->   "&&"
  | BLOr ->    "||"

let string_of_cmpop = function
  | CEq ->  "="
  | CNeq -> "!="
  | CLt ->  "<"
  | CGt ->  ">"
  | CLeq -> "<="
  | CGeq -> ">="

let string_of_elementary_type = function
  | TypeBool ->
      "bool"
  | TypeInt (size)->
      Format.sprintf "int%d" size
  | TypeUint (size)->
      Format.sprintf "uint%d" size
  | TypeFixed (size, dec) ->
      Format.sprintf "fixed%dx%d" size dec
  | TypeUfixed (size, dec) ->
      Format.sprintf "ufixed%dx%d" size dec
  | TypeAddress (false) ->
      "address"
  | TypeAddress (true) ->
      "address payable"
  | TypeString ->
      "string"
  | TypeBytes (None) ->
      "bytes"
  | TypeBytes (Some size)->
      Format.sprintf "bytes%d" size



let string_of_ident id =
  Ident.to_string (strip id)

let string_of_longident lid =
  LongIdent.to_string (strip lid)

let rec bprint_contract b indent c =
  List.iter (bprint_source_unit b indent) c

and bprint_source_unit b indent su =
  match strip su with
  | Pragma (id, s) ->
      bprint b indent (Format.asprintf "pragma %a %s;" Ident.printf id s)
  | Import { import_from; import_symbols = ImportAll (None) } ->
      bprint b indent
        (Format.sprintf "import %s;" import_from)
  | Import { import_from; import_symbols = ImportAll (Some id) } ->
      bprint b indent
        (Format.sprintf "import * as %s from %s;"
           (string_of_ident id) import_from)
  | Import { import_from; import_symbols = ImportIdents import_list } ->
      bprint b indent
        (Format.sprintf "import { %s } from %s;"
           (String.concat ", "
              (List.map (fun (id, id_opt) ->
                   Format.sprintf "%s %s" (string_of_ident id)
                     (string_of_maybe_as_identifier id_opt)
                 ) import_list)) import_from)
  | GlobalTypeDefinition (td) ->
      type_definition b indent td
  | GlobalFunctionDefinition (fd) ->
      function_definition b indent fd
  | GlobalVariableDefinition (vd) ->
      variable_definition b indent vd
  | ContractDefinition (cd) ->
      bprint b indent
        (Format.sprintf "%s%s %s %s {"
           (if cd.contract_abstract then "abstract " else "")
           (string_of_contract_kind cd.contract_kind)
           (string_of_ident cd.contract_name)
           (match cd.contract_inheritance with
            | [] -> ""
            | list ->
                Format.sprintf "is %s"
                  (String.concat ", "
                     (List.map string_of_inheritance_specifier list))));
      List.iter (contract_part b (indent + 2)) cd.contract_parts ;
      bprint b indent "}"

and string_of_maybe_as_identifier = function
  | None -> ""
  | Some id -> Format.sprintf "as %s" (string_of_ident id)

and string_of_inheritance_specifier (lid, e_list) =
  Format.sprintf "%s(%s)"
    (string_of_longident lid)
    (String.concat ", " (List.map string_of_expression e_list))

and contract_part b indent cp =
  match strip cp with
  | TypeDefinition td ->
      type_definition b indent td
  | StateVariableDeclaration (vd) ->
      variable_definition b indent vd
  | FunctionDefinition (fd) ->
      function_definition b indent fd
  | ModifierDefinition {
        mod_name; mod_params; mod_virtual; mod_override; mod_body } ->
      bprint b indent
        (Format.sprintf "modifier %s(%s)%s%s%s"
           (string_of_ident mod_name)
           (String.concat ", " (List.map string_of_function_param mod_params))
           (if mod_virtual then " virtual" else "")
           (match mod_override with
            | None -> ""
            | Some [] -> " override"
            | Some ol -> " override(" ^
                           (String.concat ","
                              (List.map string_of_longident ol)) ^ ")")
           (match mod_body with
            | None -> ";"
            | Some _ -> " {"));
      begin
        match mod_body with
        | None -> ()
        | Some body ->
            block b (indent + 2) body;
            bprint b indent "}"
      end
  | EventDefinition { event_name; event_params; event_anonymous } ->
      bprint b indent
        (Format.sprintf "event %s(%s)%s;"
           (string_of_ident event_name)
           (String.concat ", "
              (List.map (fun (t, indexed, id_opt) ->
                   Format.sprintf "%s%s%s"
                     (string_of_type t)
                     (if indexed then " indexed" else "")
                     (match id_opt with
                      | None -> ""
                      | Some id -> " " ^ string_of_ident id))
                 event_params))
           (if event_anonymous then " anonymous" else ""))
  | UsingForDeclaration (lid, t_opt) ->
      bprint b indent
        (Format.sprintf "using %s %s;" (string_of_longident lid)
           (match t_opt with
            | None -> ""
            | Some t -> Format.sprintf "for %s" (string_of_type t)))

and type_definition b indent = function
  | EnumDefinition (id, id_list) ->
      bprint b indent (Format.sprintf "enum %s {" (string_of_ident id));
      List.iter (fun id ->
          bprint b (indent + 2) (string_of_ident id)) id_list;
      bprint b indent "}"
  | StructDefinition (id, var_decl_list) ->
      bprint b indent (Format.sprintf "struct %s {" (string_of_ident id));
      List.iter (fun s ->
          bprint b (indent + 2) (string_of_field_declaration s)
        ) var_decl_list;
      bprint b indent "}"

and string_of_field_declaration (t, id) =
  Format.sprintf "%s %s" (string_of_type t) (string_of_ident id)

and variable_definition b indent {
    var_name; var_type; var_visibility;
    var_mutability; var_override; var_init; } =
  bprint b indent
    (Format.sprintf "%s %s%s%s%s%s"
       (string_of_type var_type)
       (string_of_ident var_name)
       (match var_visibility with
        | VInternal -> ""
        | v -> " " ^ (string_of_visibility v))
       (match var_mutability with
        | MMutable -> ""
        | m -> " " ^ (string_of_var_mutability m))
       (match var_override with
        | None -> ""
        | Some [] -> " override"
        | Some ol -> " override(" ^
                       (String.concat ","
                          (List.map string_of_longident ol)) ^ ")")
       (match var_init with
        | None -> ";"
        | Some e -> Format.sprintf " = %s;" (string_of_expression e)))

and function_definition b indent {
    fun_name; fun_params; fun_returns; fun_modifiers; fun_visibility;
    fun_mutability; fun_override; fun_virtual; fun_body } =
  let name =
    match strip fun_name with
    | id when Ident.equal id Ident.fallback  -> "fallback"
    | id when Ident.equal id Ident.receive -> "receive"
    | id when Ident.equal id Ident.constructor -> "constructor"
    | id -> "function " ^ (Ident.to_string id)
  in
  bprint b indent
    (Format.sprintf "%s(%s) %s%s%s%s%s%s%s"
       (name)
       (String.concat ", " (List.map string_of_function_param fun_params))
       (string_of_visibility fun_visibility)
       (match fun_mutability with
        | MNonPayable -> ""
        | m -> " " ^ (string_of_fun_mutability m))
       (if fun_virtual then " virtual" else "")
       (match fun_override with
        | None -> ""
        | Some [] -> " override"
        | Some ol -> " override(" ^
                       (String.concat ","
                          (List.map string_of_longident ol)) ^ ")")
       (match fun_modifiers with
        | [] -> ""
        | _ -> " " ^
                 (String.concat " "
                    (List.map string_of_modifier fun_modifiers)))
       (match fun_returns with
        | [] -> ""
        | returns ->
            Format.sprintf " returns (%s)"
              (String.concat " * "
                 (List.map string_of_function_return returns)))
       (match fun_body with
        | None -> ";"
        | Some _ -> " {"));
  begin
    match fun_body with
    | None -> ()
    | Some body ->
        block b (indent + 2) body;
        bprint b indent "}"
  end

and string_of_function_param (t, loc_opt, id_opt) =
  Format.sprintf "%s%s %s"
    (string_of_type t)
    (match loc_opt with
     | None -> ""
     | Some loc -> " " ^ string_of_storage_location loc)
    (match id_opt with
     | None -> ""
     | Some id -> string_of_ident id)

and string_of_function_return (t, loc_opt, id_opt) =
  Format.sprintf "%s%s%s"
    (string_of_type t)
    (match loc_opt with
     | None -> ""
     | Some loc -> " " ^ string_of_storage_location loc)
    (match id_opt with
     | None -> ""
     | Some id -> " " ^ (string_of_ident id))

and string_of_modifier (lid, e_list_opt) =
  Format.sprintf "%s(%s)" (string_of_longident lid)
    (match e_list_opt with
     | None -> ""
     | Some el -> String.concat ", " (List.map string_of_expression el))

and string_of_type = function
  | ElementaryType et ->
      string_of_elementary_type et
  | UserDefinedType lid ->
      string_of_longident lid
  | Mapping (tk, tv) ->
      Format.sprintf "mapping (%s => %s)"
        (string_of_type tk) (string_of_type tv)
  | Array (t, e_opt) ->
      Format.sprintf "%s [%s]"
        (string_of_type t)
        (match e_opt with
         | None -> ""
         | Some e -> string_of_expression e)
  | FunctionType ft ->
      string_of_function_type ft

and string_of_function_type {
    fun_type_params; fun_type_returns;
    fun_type_visibility; fun_type_mutability } =
  Format.sprintf "function(%s) %s%s%s"
    (String.concat ", " (List.map string_of_function_param fun_type_params))
    (string_of_visibility fun_type_visibility)
    (match fun_type_mutability with
     | MNonPayable -> ""
     | m -> " " ^ (string_of_fun_mutability m))
    (match fun_type_returns with
     | [] -> ""
     | returns ->
         Format.sprintf " returns (%s)"
           (String.concat " * "
              (List.map string_of_funtype_return returns)))

and string_of_funtype_return (t, loc_opt) =
  Format.sprintf "%s%s"
    (string_of_type t)
    (match loc_opt with
     | None -> ""
     | Some loc -> " " ^ string_of_storage_location loc)

and statement b indent s =
  match strip s with
  | Continue ->
      bprint b indent "continue;"
  | Break ->
      bprint b indent "break;"
  | Emit (e, args) ->
      bprint b indent
        (Format.sprintf "emit %s(%s)"
           (string_of_expression e)
           (string_of_function_call_arguments args))
  | PlaceholderStatement ->
      bprint b indent "_;"
  | Return e_opt ->
      bprint b indent
        (Format.sprintf "return %s;" (string_of_expression_option e_opt))
  | Block statement_list ->
      bprint b indent "{" ;
      block b (indent + 2) statement_list;
      bprint b indent "}"
  | IfStatement (e, s1, s2_opt) -> (
    bprint b indent
      (Format.sprintf "if (%s)" (string_of_expression e));
    statement b (indent + 2) s1;
    match s2_opt with
    | None -> ()
    | Some s2 ->
        bprint b indent "else" ;
        statement b (indent + 2) s2 )
  | TryStatement (e, returns, body, catch_clause_list) ->
      bprint b indent
        (Format.sprintf "try %s %s{"
           (string_of_expression e)
           (match returns with
            | [] -> ""
            | returns ->
                Format.sprintf "returns (%s) "
                  (String.concat " * "
                     (List.map string_of_function_return returns))));
      block b (indent + 2) body;
      bprint b indent "}";
      List.iter (fun (id_opt, params, body) ->
          let p =
            String.concat ", " (List.map string_of_function_param params) in
          bprint b indent
            (Format.sprintf "catch %s{"
               (match id_opt, params with
                | None, [] -> ""
                | None, _ -> Format.sprintf "(%s)" p
                | Some id, _ -> Format.sprintf "%s(%s)"
                                  (string_of_ident id) p));
          block b (indent + 2) body;
          bprint b indent "}"
        ) catch_clause_list
  | WhileStatement (e, body) ->
      bprint b indent (Format.sprintf "while (%s)" (string_of_expression e));
      statement b (indent + 2) body
  | ForStatement (s1_opt, e1_opt, e2_opt, s2) ->
      bprint b indent "for (" ;
      (match s1_opt with None -> () | Some s -> statement b (indent + 2) s);
      bprint b (indent + 2)
        (Format.sprintf "; %s; %s)"
           (string_of_expression_option e1_opt)
           (string_of_expression_option e2_opt));
      statement b (indent + 2) s2
  | DoWhileStatement (s, e) ->
      bprint b indent "do";
      statement b (indent + 2) s;
      bprint b indent (Format.sprintf "while (%s)" (string_of_expression e))
  | VariableDefinition vardef ->
      bprint b indent
        (Format.sprintf "%s;" (string_of_variable_definition vardef))
  | ExpressionStatement e ->
      bprint b indent (Format.sprintf "%s;" (string_of_expression e))

and string_of_expression_option = function
  | None -> ""
  | Some e -> string_of_expression e

and string_of_expression e =
  match strip e with
  | BooleanLiteral bool ->
      string_of_bool bool
  | NumberLiteral (q, number_unit, None) ->
      Format.sprintf "%s%s"
        (Q.to_string q)
        (string_of_number_unit number_unit)
  | NumberLiteral (q, _number_unit, Some _size) ->
      Format.asprintf "0x%a" ExtZ.print_hex (Q.num q)
  | StringLiteral s ->
      Format.sprintf "%S" s
  | AddressLiteral s ->
      Format.sprintf "0x%s" (Hex.show (Hex.of_string s))
  | IdentifierExpression id ->
      string_of_ident id
  | ImmediateArray el ->
      Format.sprintf "[%s]"
        (String.concat ", " (List.map string_of_expression el))
  | ArrayAccess (e, None) ->
      Format.sprintf "%s[]" (string_of_expression e)
  | ArrayAccess (e1, Some e2) ->
      Format.sprintf "%s[%s]"
        (string_of_expression e1)
        (string_of_expression e2)
  | ArraySlice (tab, e1_opt, e2_opt) ->
      Format.sprintf "%s[%s:%s]"
        (string_of_expression tab)
        (match e1_opt with None -> "" | Some e -> string_of_expression e)
        (match e2_opt with None -> "" | Some e -> string_of_expression e)
  | PrefixExpression (op, e2) ->
      Format.sprintf "(%s %s)" (string_of_unop op) (string_of_expression e2)
  | SuffixExpression (e1, op) ->
      Format.sprintf "(%s %s)" (string_of_expression e1) (string_of_unop op)
  | BinaryExpression (e1, op, e2) ->
      Format.sprintf "(%s %s %s)"
        (string_of_expression e1)
        (string_of_binop op)
        (string_of_expression e2)
  | CompareExpression (e1, op, e2) ->
      Format.sprintf "(%s %s %s)"
        (string_of_expression e1)
        (string_of_cmpop op)
        (string_of_expression e2)
  | AssignExpression (e1, e2) ->
      Format.sprintf "(%s = %s)"
        (string_of_expression e1)
        (string_of_expression e2)
  | AssignBinaryExpression (e1, op, e2) ->
      Format.sprintf "(%s %s= %s)"
        (string_of_expression e1)
        (string_of_binop op)
        (string_of_expression e2)
  | FunctionCallExpression (e, args) ->
      Format.sprintf "%s(%s)"
        (string_of_expression e) (string_of_function_call_arguments args)
  | TupleExpression e_opt_list ->
      Format.sprintf "(%s)"
        (String.concat ", " (List.map string_of_expression_option e_opt_list))
  | FieldExpression (e, ident) ->
      Format.sprintf "(%s).%s"
        (string_of_expression e)
        (string_of_ident ident)
  | IfExpression (e1, e2, e3) ->
      Format.sprintf "(%s ? %s : %s)"
        (string_of_expression e1)
        (string_of_expression e2)
        (string_of_expression e3)
  | CallOptions (e, idel) ->
      Format.sprintf "%s{%s}"
        (string_of_expression e)
        (String.concat ","
           (List.map (fun (id, e) ->
                Format.sprintf "%s: %s"
                  (string_of_ident id) (string_of_expression e)
              ) idel))
  | NewExpression t ->
      Format.sprintf "new %s" (string_of_type t)
  | TypeExpression t ->
      Format.sprintf "%s" (string_of_type t)

and block b indent stmt_list =
  List.iter (statement b (indent + 2)) stmt_list

and string_of_variable_definition = function
  | VarInfer (id_opt_list, e) ->
      Format.sprintf "var %s = %s"
        (String.concat ", "
           (List.map (function
                | None -> ""
                | Some id -> string_of_ident id
              ) id_opt_list))
        (string_of_expression e)
  | VarType (var_decl_list, e_opt) ->
      let var_decls = match var_decl_list with
        | [Some variable_declaration] ->
            string_of_variable_declaration variable_declaration
        | _ ->
            Format.sprintf "(%s)"
              (String.concat ", "
                 (List.map (function
                      | None -> ""
                      | Some var_decl ->
                          string_of_variable_declaration var_decl
                    ) var_decl_list))
      in
      Format.sprintf "%s%s" var_decls
        (match e_opt with
         | None -> ""
         | Some e -> Format.sprintf " = %s" (string_of_expression e))

and string_of_variable_declaration = function
  | (t, loc_opt, id) ->
      Format.sprintf "%s%s %s"
        (string_of_type t)
        (match loc_opt with
         | None -> ""
         | Some loc -> " " ^ string_of_storage_location loc)
        (string_of_ident id)

and string_of_function_call_arguments = function
  | ExpressionList el ->
      String.concat ", " (List.map string_of_expression el)
  | NameValueList id_exp_list ->
      Format.sprintf "{%s}"
        (String.concat ","
           (List.map (fun (id, e) ->
                Format.sprintf "%s: %s"
                  (string_of_ident id) (string_of_expression e)
              ) id_exp_list))

let string_of_module_units module_units =
  let b = Buffer.create 1000 in
  let indent = 0 in
  bprint_contract b indent module_units;
  Buffer.contents b

let string_of_program p =
  let b = Buffer.create 1000 in
  List.iter (fun m ->
      bprint b 0 (Format.sprintf "%s: %s" (
                      Ident.to_string m.module_id) m.module_file);
      bprint b 0 (string_of_module_units m.module_units)
    ) p.program_modules;
  Buffer.contents b
