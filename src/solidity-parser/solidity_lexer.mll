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

{
  open Solidity_common
  open Solidity_raw_parser
  open Solidity_exceptions

  let to_loc loc =
    let open Lexing in
    let ({ pos_lnum = l1; pos_bol = b1; pos_cnum = c1; pos_fname; _ },
         { pos_lnum = l2; pos_bol = b2; pos_cnum = c2; _ }) = loc in
    let c1 = c1 - b1 in
    let c2 = c2 - b2 in
    pos_fname, (l1, c1), (l2, c2)

  let error lexbuf fmt =
    Format.kasprintf (fun s ->
      raise (SyntaxError (s, to_loc (
        lexbuf.Lexing.lex_start_p, lexbuf.Lexing.lex_curr_p)))) fmt

  let buf = Buffer.create 1000
  let reset () =
    Buffer.clear buf

  let newline lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <-
      { pos with
        Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
        Lexing.pos_bol = pos.Lexing.pos_cnum }

  let token_of_keyword = Hashtbl.create 257
  let keyword_of_token = Hashtbl.create 257

  let add_keyword kwd token =
    Hashtbl.add token_of_keyword kwd token;
    Hashtbl.add keyword_of_token token kwd;
    ()

  let update_loc lexbuf file line absolute chars =
    let pos = lexbuf.Lexing.lex_curr_p in
    let new_file = match file with
      | None -> pos.pos_fname
      | Some s -> s
    in
    lexbuf.lex_curr_p <-
      { pos with
        pos_fname = new_file;
        pos_lnum = if absolute then line else pos.pos_lnum + line;
        pos_bol = pos.pos_cnum - chars;
      }

}

let eol_comment =
  "//" [^ '\010'] *

let newline_char =
  '\010' | "\013\010"

let newline =
  eol_comment? newline_char

let space =
  [' ' '\009']

let identifier =
  ['a'-'z' 'A'-'Z' '_' '$'] ['a'-'z' 'A'-'Z' '_' '$' '0'-'9']*

let hex_digit =
  ['0'-'9' 'a'-'f' 'A'-'F']

let size_32 =
  '0'* ( "1" |  "2" |  "3" |  "4" |  "5" |  "6" |  "7" |  "8" |
         "9" | "10" | "11" | "12" | "13" | "14" | "15" | "16" |
        "17" | "18" | "19" | "20" | "21" | "22" | "23" | "24" |
        "25" | "26" | "27" | "28" | "29" | "30" | "31" | "32")

let size_256 =
  '0'* (  "8" |  "16" |  "24" |  "32" |  "40" |  "48" |  "56" |  "64" |
         "72" |  "80" |  "88" |  "96" | "104" | "112" | "120" | "128" |
        "136" | "144" | "152" | "160" | "168" | "176" | "184" | "192" |
        "200" | "208" | "216" | "224" | "232" | "240" | "248" | "256")

let dec_80 =
  '0'* (['1'-'7']? ['0'-'9'] | "80")

rule token = parse
  | eol_comment { token lexbuf }
  | space+      { token lexbuf }
  | newline     { newline lexbuf; token lexbuf }
  | "#" [' ' '\t']* (['0'-'9']+ as num) [' ' '\t']*
        ("\"" ([^ '\010' '\013' '"' ] * as name) "\"")?
        [^ '\010' '\013'] * newline
      { update_loc lexbuf name (int_of_string num) true 0;
      token lexbuf }

  | "/*"        { multiline_comment lexbuf }
  | "pragma"    { Buffer.clear buf; begin_pragma lexbuf }

  | "["   { LBRACKET }
  | "]"   { RBRACKET }
  | "&&"  { AMPERAMPER }
  | "||"  { PIPEPIPE }
  | "=="  { EQUALEQUAL }
  | "!="  { BANGEQUAL }
  | "**"  { STARSTAR }
  | "--"  { MINUSMINUS }
  | "++"  { PLUSPLUS }
  | ">="  { GREATEREQUAL }
  | "<="  { LESSEQUAL }
  | ">"   { GREATER }
  | "<"   { LESS }
  | "+="  { PLUSEQUAL }
  | "-="  { MINUSEQUAL }
  | "*="  { STAREQUAL }
  | "/="  { DIVEQUAL }
  | "%="  { PERCENTEQUAL }
  | "|="  { PIPEEQUAL }
  | "&="  { AMPEREQUAL }
  | "^="  { XOREQUAL }
  | "<<=" { LESSLESSEQUAL }
  | ">>=" { GREATERGREATEREQUAL }
  | "=>"  { EQUALGREATER }
  | "<<"  { LESSLESS }
  | ">>"  { GREATERGREATER }
  | "!"   { BANG }
  | "~"   { NOT }
  | "&"   { AMPER }
  | "|"   { PIPE }
  | "^"   { XOR }
  | "?"   { QUESTION }
  | "/"   { DIV }
  | "%"   { PERCENT }
  | "+"   { PLUS }
  | "-"   { MINUS }
  | ":"   { COLON }
  | "("   { LPAREN }
  | ")"   { RPAREN }
  | "."   { DOT }
  | "*"   { STAR }
  | "="   { EQUAL }
  | ";"   { SEMI }
  | "{"   { LBRACE }
  | "}"   { RBRACE }
  | ","   { COMMA }

  | ((['0'-'9']+ as i) ('.' (['0'-'9']+ as d))?
                     | ('.' (['0'-'9']+ as d)))
    (['e' 'E'] (['0'-'9']+ as e))?
      { let i = Option.map Z.of_string i in
        let d = Option.map Z.of_string d in
        let e = Option.map int_of_string e in
        NUMBER (i, d, e) }

  | '0' ['x' 'X'] (hex_digit+ as h)
      { (* 20-bytes literal -> translate to address *)
        if String.length h = 40 then
          ADDRESSLITERAL (Hex.to_string (`Hex h))
        else
          HEXNUMBER (h) }

  | ("hex" as h)? '\'' (([^ '\'' '\r' '\n' '\\'] | "\\" _)* as s) '\''
  | ("hex" as h)? '"' (([^ '"' '\r' '\n' '\\'] | "\\" _)* as s) '"'
      { match h with
        | None ->
            STRINGLITERAL (Scanf.unescaped s)
        | Some _ ->
            let s =
              try Hex.to_string (`Hex s)
              with _ -> error lexbuf "Expected even number of hex-nibbles"
            in
            HEXSTRINGLITERAL (s) }

  | "int" (size_256 as size)
       { INT (Some (int_of_string size)) }
  | "uint" (size_256 as size)
       { UINT (Some (int_of_string size)) }
  | "bytes" (size_32 as size)
       { BYTES (Some (int_of_string size)) }
  | "fixed" (size_256 as size) 'x' (dec_80 as dec)
       { FIXED (Some (int_of_string size, int_of_string dec)) }
  | "ufixed" (size_256 as size) 'x' (dec_80 as dec)
       { UFIXED (Some (int_of_string size, int_of_string dec)) }

  | identifier as id
      { try Hashtbl.find token_of_keyword id
        with Not_found -> IDENTIFIER (Ident.of_string id) }

  | eof
      { EOF }

  | _
      { error lexbuf "Unrecognized lexeme: \"%s\"" (Lexing.lexeme lexbuf) }

and multiline_comment = parse
  | "*/"         { token lexbuf }
  | newline_char { newline lexbuf; multiline_comment lexbuf }
  | eof          { failwith "unexpected end of file in comment" }
  | _            { multiline_comment lexbuf }

and begin_pragma = parse
  | space+     { begin_pragma lexbuf }
  | newline    { newline lexbuf; begin_pragma lexbuf }
  | identifier { let identifier = Lexing.lexeme lexbuf in
                 PRAGMA (Ident.of_string identifier, end_pragma lexbuf) }

and end_pragma = parse
  | ";" { Buffer.contents buf }
  | newline
      { newline lexbuf;
        Buffer.add_char buf '\n';
        end_pragma lexbuf }
  | _
      { Buffer.add_string buf (Lexing.lexeme lexbuf);
        end_pragma lexbuf }

 {
   let initialized = ref false
let init ~freeton =
  if not !initialized then begin
    initialized := true;
    List.iter (fun (kwd, token) ->
        add_keyword kwd token
      ) [ "import", IMPORT;
          "as", AS;
          "from", FROM;
          "abstract", ABSTRACT;
          "contract", CONTRACT;
          "interface", INTERFACE;
          "library", LIBRARY;
          "is", IS;
          "using", USING;
          "public" , PUBLIC;
          "private", PRIVATE;
          "external", EXTERNAL;
          "internal", INTERNAL;
          "payable", PAYABLE;
          "view", VIEW;
          "pure", PURE;
          "constant", CONSTANT;
          "immutable", IMMUTABLE;
          "override", OVERRIDE;
          "virtual", VIRTUAL;
          "memory", MEMORY;
          "storage", STORAGE;
          "calldata", CALLDATA;
          "indexed", INDEXED;
          "anonymous", ANONYMOUS;
          "function", FUNCTION;
          "modifier", MODIFIER;
          "constructor", CONSTRUCTOR;
          "receive", RECEIVE;
          "fallback", FALLBACK;
          "returns", RETURNS;
          "event", EVENT;
          "struct", STRUCT;
          "enum", ENUM;
          "mapping", MAPPING;
          "bool", BOOL;
          "int", INT (None);
          "uint", UINT (None);
          "fixed", FIXED (None);
          "ufixed", UFIXED (None);
          "address", ADDRESS;
          "string", STRING;
          "bytes", BYTES (None);
          "byte", BYTE;
          "var", VAR;
          "return", RETURN;
          "continue", CONTINUE;
          "break", BREAK;
          "delete", DELETE;
          "new", NEW;
          "emit", EMIT;
          "if", IF;
          "else", ELSE;
          "for", FOR;
          "while", WHILE;
          "do", DO;
          "try", TRY;
          "catch", CATCH;
          "true", BOOLEANLITERAL (true);
          "false", BOOLEANLITERAL (false);
          "ton", NUMBERUNIT (Ton);
          "wei", NUMBERUNIT (Wei);
          "gwei", NUMBERUNIT (Gwei);
          "szabo", NUMBERUNIT (Twei);
          "finney", NUMBERUNIT (Pwei);
          "ether", NUMBERUNIT (Ether);
          "hours", NUMBERUNIT (Hours);
          "minutes", NUMBERUNIT (Minutes);
          "seconds", NUMBERUNIT (Seconds);
          "days", NUMBERUNIT (Days);
          "weeks", NUMBERUNIT (Weeks);
          "years", NUMBERUNIT (Years);
        ];
if freeton then
    List.iter (fun (kwd, token) ->
        add_keyword kwd token
      ) [
        "inline", INLINE;
        "static", STATIC;
        "optional", OPTIONAL;
        "onBounce", ONBOUNCE;
        "repeat", REPEAT;
      ];
      ()
  end
}
