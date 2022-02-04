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

let tmp_files = ref []
let remove_temporary_files = ref true
let () =
  at_exit (fun () ->
      if !remove_temporary_files then
        List.iter (fun file -> Sys.remove file) !tmp_files
    )
let keep_temporary_files () = remove_temporary_files := false
let add_temporary_file file =
  tmp_files := file :: !tmp_files

let get_imported_files m =
  let base = Filename.dirname m.module_file in
  List.fold_left (fun fileset unit_node ->
      match strip unit_node with
      | Import { import_from; import_pos ; _ } ->
          let file = make_absolute_path base import_from in
          if not ( Sys.file_exists file ) then
            raise (
              Solidity_exceptions.SyntaxError
                ("File does not exist", import_pos ) );
          StringSet.add file fileset
      | _ -> fileset
    ) StringSet.empty m.module_units

(* should be replaced by Lexing.set_filename after 4.10 is deprecated *)
let set_filename lexbuf filename =
  let open Lexing in
  let lex_curr_p = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { lex_curr_p with pos_fname = filename }

let parse_module id ?(cpp=false) ?preprocess file =
  let content =
    let cpp = cpp ||
              match Sys.getenv "SOLIDITY_CPP" with
              | _ -> true
              | exception _ -> false
    in
    if cpp then
      let tmp_file = Filename.temp_file (Filename.basename file) "-cpp.sol" in
      let cmd = Printf.sprintf "cpp -E %s > %s" file tmp_file in
      let res = Sys.command cmd in
      if res = 0 then begin
        add_temporary_file tmp_file ;
        EzFile.read_file tmp_file
      end else
        Printf.kprintf
          failwith "Warning: %s failed with error %d\n%!" cmd res
    else
      EzFile.read_file file
  in
  let content = match preprocess with
    | None -> content
    | Some f -> f content
  in
  let lb = Lexing.from_string content in
  set_filename lb file ;
  let module_units =
    try
      Solidity_raw_parser.module_units
        Solidity_lexer.token lb
    with Solidity_raw_parser.Error ->
      raise ( Solidity_exceptions.SyntaxError ("Parse error",
                                               Solidity_common.to_pos
                                                 ( lb.Lexing.lex_start_p ,
                                                   lb.Lexing.lex_curr_p )))
  in
  { module_file = file; module_id = Ident.root id; module_units }

(* Parse a Solidity file and all its imported files.
   This uses a BFS strategy with cycle prevention, i.e. newly
   imported files are added at the end of the input file queue.
   The imports of a file are ordered lexicographically
   before being added to the queue. *)
let parse_file ?(freeton=false) ?preprocess ?cpp filename =

  Solidity_lexer.init ~freeton;
  Solidity_common.for_freeton := freeton ;

  let file = make_absolute_path (Sys.getcwd ()) filename in

  let files = ref (StringSet.singleton file) in

  let to_parse = Queue.create () in
  StringSet.iter (fun file -> Queue.push file to_parse) !files;

  let modules = ref [] in
  let id = ref (-1) in

  while not (Queue.is_empty to_parse) do
    let file = Queue.pop to_parse in
    let m = parse_module (id := !id + 1; !id) ?preprocess ?cpp file in
    modules := m :: !modules;
    let imported_files = get_imported_files m in
    let new_files = StringSet.diff imported_files !files in
    files := StringSet.union new_files !files;
    StringSet.iter (fun file -> Queue.push file to_parse) new_files
  done;

  let program_modules, program_modules_by_id, program_modules_by_file =
    List.fold_left (fun (mods, mods_by_id, mods_by_file) m ->
        m :: mods,
        IdentMap.add m.module_id m mods_by_id,
        StringMap.add m.module_file m mods_by_file
      ) ([], IdentMap.empty, StringMap.empty) !modules
  in

  { program_modules; program_modules_by_id; program_modules_by_file }

(* Parse a list of Solidity files and all their imported files. *)
let parse_files ?(freeton=false) ?preprocess ?cpp filenames =

  Solidity_lexer.init ~freeton;
  Solidity_common.for_freeton := freeton ;

  let files =
    ref @@
    List.fold_left (
      fun file_set filename ->
        StringSet.add
          (make_absolute_path (Sys.getcwd ()) filename)
          file_set
    ) StringSet.empty filenames
  in

  let to_parse = Queue.create () in
  StringSet.iter (fun file -> Queue.push file to_parse) !files;

  let modules = ref [] in
  let id = ref (-1) in

  while not (Queue.is_empty to_parse) do
    let file = Queue.pop to_parse in
    let m = parse_module (id := !id + 1; !id) ?preprocess ?cpp file in
    modules := m :: !modules;
    let imported_files = get_imported_files m in
    let new_files = StringSet.diff imported_files !files in
    files := StringSet.union new_files !files;
    StringSet.iter (fun file -> Queue.push file to_parse) new_files
  done;

  let program_modules, program_modules_by_id, program_modules_by_file =
    List.fold_left (fun (mods, mods_by_id, mods_by_file) m ->
        m :: mods,
        IdentMap.add m.module_id m mods_by_id,
        StringMap.add m.module_file m mods_by_file
      ) ([], IdentMap.empty, StringMap.empty) !modules
  in

  { program_modules; program_modules_by_id; program_modules_by_file }
