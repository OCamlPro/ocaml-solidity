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

let typecheck = ref true
let postcheck = ref true

let disable_postcheck () =
  postcheck := false

let disable_typecheck () =
  disable_postcheck ();
  typecheck := false


let main () =
  let freeton = ref false in

  let arg_list = Arg.align [
      "--version", Arg.Unit (fun () ->
          Format.eprintf "Solidity Parser & Typechecker"; exit 0),
      " Show version and exit";

      "--no-typecheck", Arg.Unit disable_typecheck,
      " Disable the typechecker";

      "--freeton", Arg.Set freeton,
      " Parse for freeton";

      "--no-postcheck", Arg.Unit disable_postcheck,
      " Disable the postchecker"
    ]
  in

  let arg_usage = String.concat "\n" [
      (Filename.basename Sys.executable_name) ^ " [OPTIONS] FILE [OPTIONS]";
      "";
      "This tool will parse and typecheck a \
       Solidity file (.sol) and print the result";
      "";
      "Available options:";
    ]
  in
  let file = ref None in
  Arg.parse arg_list (fun a ->
      Format.eprintf "Argument %s@." a;
      if !file <> None then begin
        Format.eprintf "More than one file specified";
        exit 1
      end;
      file := Some a;
    ) arg_usage;
  match !file with
  | None ->
      Arg.usage arg_list arg_usage;
      exit 1
  | Some file ->
      let freeton = !freeton in
      let program : Solidity_ast.program =
          Solidity_parser.parse_file ~freeton file
      in

      Format.printf "Parsed code:\n%s@."
        (Solidity_printer.string_of_program program);

      let program : Solidity_ast.program =
        if !typecheck then
          Solidity_typechecker.type_program ~freeton program
        else
          program
      in
      let () =
        if !typecheck && !postcheck && not !Solidity_common.for_freeton then
          Solidity_postprocess.checkProgram program
      in
      ()

let () =
  try
    main ()
  with
  | exn ->
      Printf.eprintf "%s%!" ( Solidity_exceptions.string_of_exn exn );
      exit 2
