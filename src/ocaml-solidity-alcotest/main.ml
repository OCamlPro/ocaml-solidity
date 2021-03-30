exception Success
exception Fail

let test_dir = "test/raw_tests/"
let fail_dir = test_dir ^ "fails"
let success_dir = test_dir ^ "successes"

let spf = Format.sprintf

let check_file file () =
  let () =
    try
      let program = Solidity_parser.parse file in
      let program = Solidity_typechecker.type_program program in
      ignore @@ Solidity_postprocess.checkProgram program;
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


let ok_files =
  Array.to_list @@
  Array.map
    success
    (Array.map (spf "%s/%s" success_dir) (Sys.readdir success_dir))

let ko_files =
  Array.to_list @@
  Array.map
    fail
    (Array.map (spf "%s/%s" fail_dir) (Sys.readdir fail_dir))

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
