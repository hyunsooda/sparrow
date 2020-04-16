(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)
let analyzer = "../bin/sparrow"

let default_opt = "-verbose 0"

type test_suite = { opt : string; files : string list }

let test_suites =
  [
    {
      opt = "";
      files =
        [
          "basic/array_pointer.c";
          "basic/global_array.c";
          "basic/global_static_struct.c";
          "basic/global_static_struct2.c";
          "basic/local_dynamic_struct.c";
          "basic/local_static_struct.c";
          "basic/struct_pointer.c";
          "interval/prune_const.c";
          "interval/strncpy.c";
          "interval/memcpy.c";
          "interval/memset.c";
        ];
    };
    { opt = "-narrow"; files = [ "narrowing/narrow.c" ] };
    {
      opt = "-inline alloc -unsound_alloc";
      files = [ "unsoundness/unsound_alloc.c" ];
    };
    {
      opt = "-taint";
      files =
        [
          "taint/printf.c";
          "taint/varg.c";
          "taint/snprintf.c";
          "taint/strtok.c";
          "taint/fgetc.c";
          "taint/asprintf.c";
          "taint/memcpy.c";
        ];
    };
    {
      opt = "-frontend clang -il";
      files =
        [
          "clang/global-array0.c";
          "clang/local-array0.c";
          "clang/struct0.c";
          "clang/struct1.c";
          "clang/struct2.c";
          "clang/struct3.c";
          "clang/struct4.c";
          "clang/implicit-cast0.c";
          "clang/implicit-cast1.c";
          "clang/implicit-cast2.c";
          "clang/implicit-cast3.c";
          "clang/binop0.c";
          "clang/ternop0.c";
          "clang/ternop1.c";
          "clang/enum0.c";
          "clang/enum1.c";
          "clang/pointer0.c";
          "clang/pointer1.c";
          "clang/pointer2.c";
          "clang/namespace0.c";
          "clang/missing-proto0.c";
          "clang/stmtexpr0.c";
          "clang/duplication0.c";
          "clang/switch0.c";
          "clang/while0.c";
          "clang/while1.c";
          "clang/while2.c";
          "clang/goto0.c";
          "clang/goto1.c";
          "clang/goto2.c";
          "clang/goto3.c";
          "clang/attribute0.c";
          "clang/attribute1.c";
          "clang/return0.c";
          "clang/block0.c";
          "clang/function0.c";
          "clang/if0.c";
          "clang/if1.c";
          "clang/if2.c";
          "clang/init-list0.c";
          "clang/init-list1.c";
          "clang/nested-init-0.c";
          "clang/nested-init-1.c";
          "clang/nested-init-2.c";
          "clang/local-init1.c";
          "clang/local-init2.c";
          "clang/local-init3.c";
          "clang/local-init4.c";
          "clang/local-init5.c";
        ];
    };
  ]

let make_cmd opt f =
  analyzer ^ " " ^ default_opt ^ " " ^ opt ^ " " ^ f
  |> Str.split (Str.regexp "[ ]+")
  |> Array.of_list

let run opt f =
  let cmd = make_cmd opt f in
  (try Unix.unlink (f ^ ".out") with _ -> ());
  let fd = Unix.openfile (f ^ ".out") [ Unix.O_CREAT; Unix.O_RDWR ] 0o640 in
  let pid = Unix.create_process analyzer cmd Unix.stdin fd fd in
  ignore (Unix.waitpid [] pid);
  Unix.close fd

let color_green = "\x1B[32m"

let color_red = "\x1B[31m"

let color_reset = "\x1B[0m"

let msg_pass = color_green ^ "PASS" ^ color_reset

let msg_fail = color_red ^ "FAIL" ^ color_reset

let check f =
  let ic = Unix.open_process_in ("diff " ^ f ^ ".answer " ^ f ^ ".out") in
  print_string (f ^ ".....");
  match Unix.close_process_in ic with
  | Unix.WEXITED i when i = 0 ->
      print_endline msg_pass;
      Unix.unlink (f ^ ".out");
      true
  | _ ->
      print_endline (msg_fail ^ " (see " ^ f ^ ".answer and " ^ f ^ ".out)");
      false

let print_result = function
  | true -> print_endline (color_green ^ "All tests are passed" ^ color_reset)
  | false -> print_endline (color_red ^ "Test failed" ^ color_reset)

let _ =
  List.fold_left
    (fun c test_suite ->
      List.fold_left
        (fun c f ->
          run test_suite.opt f;
          check f && c)
        c test_suite.files)
    true test_suites
  |> print_result
