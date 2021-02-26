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

let make_absolute_path base path =
  FilePath.reduce ~no_symlink:true @@
    if FilePath.is_relative path then
      FilePath.make_absolute base path
    else
      path

let get_imported_files m =
  let base = FilePath.dirname m.module_file in
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

let parse file =

  let file = make_absolute_path (Sys.getcwd ()) file in

  let to_parse = ref (StringSet.singleton file) in
  let parsed = ref (StringSet.empty) in
  let modules = ref [] in
  let id = ref (-1) in

  while not (StringSet.is_empty !to_parse) do
    let file = StringSet.choose !to_parse in
    to_parse := StringSet.remove file !to_parse;
    let m = parse_module (id := !id + 1; !id) file in
    modules := m :: !modules;
    parsed := StringSet.add file !parsed;
    let imported_files = get_imported_files m in
    let new_files = StringSet.diff imported_files !parsed in
    to_parse := StringSet.union new_files !to_parse
  done;

  let program_modules, program_modules_by_id, program_modules_by_file =
    List.fold_left (fun (mods, mods_by_id, mods_by_file) m ->
        m :: mods,
        IdentMap.add m.module_id m mods_by_id,
        StringMap.add m.module_file m mods_by_file
      ) ([], IdentMap.empty, StringMap.empty) !modules
  in

  { program_modules; program_modules_by_id; program_modules_by_file }
