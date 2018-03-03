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
open Graph
open Cil
open Global
open Vocab

(* transformation based on syntactic heuristics *)
let transform_simple file =
  opt !Options.unsound_alloc UnsoundAlloc.transform file

(* transformation based on semantic heuristics *)
let transform : Global.t -> Global.t
= fun global ->
  let loop_transformed = UnsoundLoop.transform global in
  let inlined = Frontend.inline global in
  if loop_transformed || inlined then   (* something transformed *)
    Frontend.makeCFGinfo global.file    (* NOTE: CFG must be re-computed after transformation *)
    |> StepManager.stepf true "Translation to graphs (after inline)" Global.init
    |> StepManager.stepf true "Pre-analysis (after inline)" PreAnalysis.perform
  else global (* nothing changed *)

let init_analysis : Cil.file -> Global.t
= fun file ->
  let filename = Filename.basename file.Cil.fileName in
  if (!Options.marshal_in || !Options.marshal_in_global) && Sys.file_exists (!Options.marshal_dir ^ "/" ^ filename ^ ".global") then
    MarshalManager.input (filename ^ ".global")
  else
    file
    |> transform_simple
    |> StepManager.stepf true "Translation to graphs" Global.init
    |> StepManager.stepf true "Pre-analysis" PreAnalysis.perform
    |> transform
    |> opt !Options.marshal_out_global (fun global -> MarshalManager.output (filename ^ ".global") global; global)

let print_pgm_info : Global.t -> Global.t
= fun global ->
  let pids = InterCfg.pidsof global.icfg in
  let nodes = InterCfg.nodesof global.icfg in
  prerr_endline ("#Procs : " ^ string_of_int (List.length pids));
  prerr_endline ("#Nodes : " ^ string_of_int (List.length nodes));
  global

let print_il : Global.t -> Global.t
= fun global ->
  Cil.dumpFile !Cil.printerForMaincil stdout "" global.file;
  exit 0

let print_cfg : Global.t -> Global.t
= fun global ->
  `Assoc
    [ ("callgraph", CallGraph.to_json global.callgraph);
      ("cfgs", InterCfg.to_json global.icfg)]
  |> Yojson.Safe.pretty_to_channel stdout; exit 0

let finish t0 () =
  my_prerr_endline "Finished properly.";
  Profiler.report stdout;
  my_prerr_endline (string_of_float (Sys.time () -. t0) ^ "sec");
  prerr_memory_usage ()

let octagon_analysis (global,itvinputof,_,_) =
  StepManager.stepf true "Oct Sparse Analysis" OctAnalysis.do_analysis (global,itvinputof)
  |> (fun (global,_,_,alarm) -> (global, alarm))

let extract_feature : Global.t -> Global.t
= fun global ->
  if !Options.extract_loop_feat then
    let _ = UnsoundLoop.extract_feature global |> UnsoundLoop.print_feature in
    exit 0
  else if !Options.extract_lib_feat then
    let _ = UnsoundLib.extract_feature global |> UnsoundLib.print_feature in
    exit 0
  else global

let main () =
  let t0 = Sys.time () in
  let _ = Profiler.start_logger () in

  let usageMsg = "Usage: main.native [options] source-files" in

  Printexc.record_backtrace true;

  (* process arguments *)
  Arg.parse Options.opts Frontend.args usageMsg;
  List.iter (fun f -> prerr_string (f ^ " ")) !Frontend.files;
  prerr_endline "";

  Cil.initCIL ();

  try
    StepManager.stepf true "Front-end" Frontend.parse ()
    |> Frontend.makeCFGinfo
    |> init_analysis
    |> print_pgm_info
    |> opt !Options.il print_il
    |> opt !Options.cfg print_cfg
    |> extract_feature
    |> StepManager.stepf true "Itv Sparse Analysis" ItvAnalysis.do_analysis
    |> cond !Options.oct octagon_analysis (fun (global,_,_,alarm) -> (global, alarm))
    |> (fun (global, alarm) -> Report.print global alarm)
    |> finish t0
  with exc ->
    prerr_endline (Printexc.to_string exc);
    prerr_endline (Printexc.get_backtrace())

let _ = main ()
