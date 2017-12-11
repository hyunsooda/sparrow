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
open Arg

(* IL *)
let il = ref false
let cfg = ref false
let dug = ref false
let optil = ref true

(* Context & Flow Sensitivity *)
let inline = ref []
let inline_size = ref 100000
let pfs = ref 100
let pfs_wv = ref
  "100.0 -100.0 -34.988241686898462 -99.662940999334793 -100.0
   20.989776538253508 100.0 28.513793013882694 -30.30168857094921 -100.0
   27.574102626204336 -74.381386730147895 -65.270452404579814 100.0 100.0
   80.703727126015522 -13.475885118852554 -100.0 67.910455368871894 -100.0
   -100.0 -58.103715871839746 -100.0 100.0 -2.1779606787169481
   50.854271919870321 87.790748577623447 100.0 100.0 -100.0
   -100.0 100.0 70.038390871188767 -22.179572133292666 100.0
   42.647897970881758 100.0 -100.0 -100.0 32.564292030707847
   98.370519929542738 100.0 100.0 -100.0 -100.0"
let pfs_simple = ref false

(* Octagon Analysis *)
let oct = ref false
let pack_impact = ref true
let pack_manual = ref false

(* Analyzer *)
let nobar = ref false
let narrow = ref false
let profile = ref false
let scaffold = ref true

(* Unsoundness *)
let unsound_loop = ref BatSet.empty
let unsound_lib = ref BatSet.empty
let extract_loop_feat = ref false
let extract_lib_feat = ref false
let top_location = ref false
let unsound_recursion = ref false
let unsound_alloc = ref false
let bugfinder = ref 0

(* Alarm Report *)
let noalarm = ref false
let bo = ref true
let nd = ref false
let dz = ref false
let show_all_query = ref false

(* Timer *)
let print_time = ref false
let timer_iter = ref 0
let predictor = ref false
let timer_unit = ref 300
let timer_dump = ref false
let timer_extract = ref false 
let timer_iteration = ref 0
let timer_debug = ref false 
let timer_static_rank = ref false
let timer_oracle_rank = ref false
let timer_clf = ref ""
let timer_dir = ref ""
let timer_initial_coarsening = ref false
let timer_stat = ref false
let timer_counter_example = ref false
let timer_total_memory = ref 0
let timer_coeff = ref 0.0
let timer_auto_coarsen = ref false
let timer_manual_coarsen = ref ""
let timer_explore_rate = ref 0
let timer_fi_alarm = ref 0
let timer_fs_alarm = ref 0
let timer_training = ref false

(* Marshaling *)
let marshal_in = ref false
let marshal_out = ref false
let marshal_dir = ref "marshal"
let marshal_in_global = ref false
let marshal_in_dug = ref false
let marshal_in_worklist = ref false
let marshal_out_global = ref false
let marshal_out_dug = ref false
let marshal_out_worklist = ref false
let marshal_out_alarm = ref false

(* Debug *)
let debug = ref false
let oct_debug = ref false

(* ETC *)
let print_premem = ref false
let verbose = ref 1
let int_overflow = ref false

let opts =
  [
  ("-il", (Arg.Set il), "Show the input program in IL");
  ("-cfg", (Arg.Set cfg), "Print Cfg");
  ("-dug", (Arg.Set dug), "Print Def-Use graph");
  ("-noalarm", (Arg.Set noalarm), "Do not print alarms");
  ("-verbose", (Arg.Int (fun x -> verbose := x)), "Verbose level (default: 1)");
  ("-debug", (Arg.Set debug), "Print debug information");
  ("-oct_debug", (Arg.Set oct_debug), "Print debug information for octagon analysis");
  ("-pack_impact", (Arg.Set pack_impact), "Packing by impact pre-analysis");
  ("-pack_manual", (Arg.Set pack_manual), "Pacing by manual annotation");
  ("-nd", (Arg.Set nd), "Print Null-dereference alarms");
  ("-bo", (Arg.Set bo), "Print Buffer-overrun alarms");
  ("-dz", (Arg.Set dz), "Print Divide-by-zero alarms");
  ("-bugfinder", (Arg.Int (fun x -> bugfinder := x)), "Unsoundness level in bugfinding mode (default: 0)");
  ("-inline", (Arg.String (fun s -> inline := s::(!inline))), "Inline functions whose names contain X");
  ("-inline_size", (Arg.Int (fun x -> inline_size := x)), "Size constraint for function inline");
  ("-pfs", (Arg.Int (fun x -> pfs := x)), "Partial flow-sensitivity -pfs [0-100] (0: flow-insensitive, 100: fully flow-sensitive). default=100");
  ("-pfs_wv", (Arg.String (fun s -> pfs_wv := s)), "Weight vector for flow-sensitivity (e.g., \"0 1 -1 ... \"). Unspecified weights are zeros.");
  ("-pfs_simple", (Arg.Set pfs_simple), "Simple heuristic for patial flow-sensitivity");
  ("-oct", (Arg.Set oct), "Do octagon analysis");
  ("-profile", (Arg.Set profile), "Profiler");
  ("-narrow", (Arg.Set narrow), "Do narrowing");
  ("-unsound_loop", (Arg.String (fun s -> unsound_loop := BatSet.add s !unsound_loop)), "Unsound loops");
  ("-unsound_lib", (Arg.String (fun s -> unsound_lib := BatSet.add s !unsound_lib)), "Unsound libs");
  ("-unsound_recursion", (Arg.Set unsound_recursion), "Unsound recursive calls");
  ("-unsound_alloc", (Arg.Set unsound_alloc), "Unsound memory allocation (never return null)");
  ("-extract_loop_feat", (Arg.Set extract_loop_feat), "Extract features of loops for harmless unsoundness");
  ("-extract_lib_feat", (Arg.Set extract_lib_feat), "Extract features of libs for harmless unsoundness");
  ("-top_location", (Arg.Set top_location), "Treat unknown locations as top locations");
  ("-scaffold", (Arg.Set scaffold), "Use scaffolding semantics (default)");
  ("-no_scaffold", (Arg.Clear scaffold), "Do not use scaffolding semantics");
  ("-nobar", (Arg.Set nobar), "No progress bar");
  ("-show_all_query", (Arg.Set show_all_query), "Show all queries");
  ("-optil", (Arg.Set optil), "Optimize IL (default)");
  ("-timer_iter", (Arg.Int (fun x -> timer_iter := x)), "Timer in iteration");
  ("-timer_unit", (Arg.Int (fun x -> timer_unit := x)), "Time unit");
  ("-timer_dump", (Arg.Set timer_dump), "Timer dump");
  ("-timer_extract", (Arg.Set timer_extract), "Timer extract");
  ("-timer_iteration", (Arg.Int (fun x -> timer_iteration:=x)), "Timer extract init");
  ("-timer_debug", (Arg.Set timer_debug), "Timer debug");
  ("-timer_static_rank", (Arg.Set timer_static_rank), "Static ranking");
  ("-timer_oracle_rank", (Arg.Set timer_oracle_rank), "Static ranking");
  ("-timer_initial_coarsening", (Arg.Set timer_initial_coarsening), "Initial coarsening");
  ("-timer_stat", (Arg.Set timer_stat), "Print statistics");
  ("-timer_counter_example", (Arg.Set timer_counter_example), "Counter example");
  ("-timer_clf", (Arg.String (fun s -> timer_clf := s)), "Timer clf");
  ("-timer_dir", (Arg.String (fun s -> timer_dir := s)), "Timer dir");
  ("-timer_total_memory", (Arg.Int (fun x -> timer_total_memory := x)), "Maximum memory");
  ("-timer_coeff", (Arg.Float (fun x -> timer_coeff := x)), "Coefficient for memory-aware abstraction coarsening");
  ("-timer_auto_coarsen", (Arg.Set timer_auto_coarsen), "Timer scheduler");
  ("-timer_training", (Arg.Set timer_training), "Timer training");
  ("-timer_explore_rate", (Arg.Int (fun x -> timer_explore_rate := x)), "Timer scheduler");
  ("-timer_manual_coarsen", (Arg.String (fun s -> timer_manual_coarsen := s)), "Timer scheduler");
  ("-timer_fi_alarm", (Arg.Int (fun x -> timer_fi_alarm := x)), "Maximum memory");
  ("-timer_fs_alarm", (Arg.Int (fun x -> timer_fs_alarm := x)), "Maximum memory");
  ("-marshal_in", (Arg.Set marshal_in), "Read analysis results from marshaled data");
  ("-marshal_out", (Arg.Set marshal_out), "Write analysis results to marshaled data");
  ("-marshal_dir", (Arg.String (fun s -> marshal_dir := s)), "Directory where the marshaled data exists (default: marshal/)");
  ("-marshal_in_global", (Arg.Set marshal_in_global), "Marshal");
  ("-marshal_in_dug", (Arg.Set marshal_in_dug), "Marshal");
  ("-marshal_in_worklist", (Arg.Set marshal_in_worklist), "Marshal");
  ("-marshal_out_global", (Arg.Set marshal_out_global), "Marshal");
  ("-marshal_out_dug", (Arg.Set marshal_out_dug), "Marshal");
  ("-marshal_out_worklist", (Arg.Set marshal_out_worklist), "Marshal");
  ("-marshal_out_alarm", (Arg.Set marshal_out_alarm), "Marshal");
  ("-int_overflow", (Arg.Set int_overflow), "Consider integer overflow");
  ]
