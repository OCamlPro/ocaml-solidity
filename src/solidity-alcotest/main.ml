exception Success
exception Fail

let test_dir = "test/raw_tests"
let fail_dir = test_dir ^ "/fails"
let success_dir = test_dir ^ "/successes"

let spf = Format.sprintf

let check_file file () =
  let () =
    try
      let program = Solidity_parser.parse file in
      let program = Solidity_typechecker.type_program program in
      Solidity_postprocess.checkProgram program
    with
    | e ->
        Format.printf "Fail: %s@." (Printexc.to_string e);
        raise Fail in
  raise Success

let success f = f, fun () ->
  Alcotest.check_raises
    (spf "%s success" f)
    Success
    (check_file f)

let fail f = f, fun () ->
  Alcotest.check_raises
    (spf "%s fail" f)
    Fail
    (check_file f)

let get_files dir =
  let rec loop acc subdir : string list =
    let content = Sys.readdir subdir in
    Array.fold_left
      (
        fun acc file ->
          let full_path_file = spf "%s/%s" subdir file in
          try loop acc full_path_file with
          | Sys_error _s (* file is not a directory *) ->
              full_path_file :: acc
      )
      acc
      content
  in loop [] dir

let ok_files =
  List.map
    success
    (get_files success_dir)

let ko_files =
  List.map
    fail
    (get_files fail_dir)

let test_single_set =
  List.map
    (fun ((s, t) : (string * (unit -> unit))) ->
       (spf "OK file %s" s  , `Quick,  t))
    ok_files @
  List.map
    (fun ((s, t) : (string * (unit -> unit))) ->
       spf "Fail file %s" s , `Quick,  t )
    ko_files

(* Run it *)
let () =
  Alcotest.run "Solidity test suite" [
    "tests", test_single_set ;
  ];
