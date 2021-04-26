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

let get_imported_files m =
  let base = Filename.dirname m.module_file in
  List.fold_left (fun fileset unit_node ->
      match strip unit_node with
      | Import { import_from; _ } ->
          let file = make_absolute_path base import_from in
          StringSet.add file fileset
      | _ -> fileset
    ) StringSet.empty m.module_units

let parse_module id file =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  let module_units =
    Solidity_raw_parser.module_units
      Solidity_lexer.token lb
  in
  close_in c;
  { module_file = file; module_id = Ident.root id; module_units }

(* Parse a Solidity file and all its imported files.
   This uses a BFS strategy with cycle prevention, i.e. newly
   imported files are added at the end of the input file queue.
   The imports of a file are ordered lexicographically
   before being added to the queue. *)
let parse file =

  let file = make_absolute_path (Sys.getcwd ()) file in

  let files = ref (StringSet.singleton file) in

  let to_parse = Queue.create () in
  StringSet.iter (fun file -> Queue.push file to_parse) !files;

  let modules = ref [] in
  let id = ref (-1) in

  while not (Queue.is_empty to_parse) do
    let file = Queue.pop to_parse in
    let m = parse_module (id := !id + 1; !id) file in
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
