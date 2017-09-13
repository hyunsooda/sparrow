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
(** timer for interval analysis *)
open Cil
open Vocab
open Global
open BasicDom
open ItvDom
open Report

module Analysis = SparseAnalysis.Make(ItvSem)
module Table = Analysis.Table
module DUGraph = Analysis.DUGraph
module Worklist = Analysis.Worklist
module Spec = Analysis.Spec
module Access = Spec.Dom.Access

type strategy = Rank | Clf
type coarsening_target = Dug | Worklist

let strategy = Rank
let coarsening_target = Dug

type t = {
  widen_start : float;
  last : float;
  threshold : int;
  time_stamp : int;
  old_inputof : Table.t;
  static_feature : PartialFlowSensitivity.feature;
  dynamic_feature : DynamicFeature.feature;
  alarm_history : (int, Report.query list) BatMap.t;
  locset : PowLoc.t;
  num_of_locset : int;
  prepare : int;
  deadline : int;
}

let empty = {
  widen_start = 0.0;
  last = 0.0;
  threshold = 0;
  time_stamp = 1;
  old_inputof = Table.empty;
  static_feature = PartialFlowSensitivity.empty_feature;
  dynamic_feature = DynamicFeature.empty_feature;
  alarm_history = BatMap.empty;
  locset = PowLoc.empty;
  num_of_locset = 0;
  prepare = 0;
  deadline = 0;
}

let timer = ref empty

let prdbg_endline x = 
  if !Options.timer_debug then
    prerr_endline ("DEBUG::"^x)
  else ()

let load_classifier global = 
  let path = "/home/khheo/project/TimerExperiment/" in
  let py = Lymp.init ~exec:"python2" path in
  let py_module = Lymp.get_module py "sparrow" in
  let classifier = Lymp.Pyref (Lymp.get_ref py_module "load" [Lymp.Pystr !Options.timer_clf]) in
  (py_module, classifier)

let predict py_module clf x feature static_feature = 
  let vec = DynamicFeature.feature_vector x feature static_feature in
  let vec = Lymp.Pylist (List.map (fun x -> Lymp.Pyfloat x) vec) in
  Lymp.get_bool py_module "predict_one" [clf; vec]
 
let predict_proba py_module clf x feature static_feature = 
  let vec = DynamicFeature.feature_vector x feature static_feature in
  let vec = Lymp.Pylist (List.map (fun x -> Lymp.Pyfloat x) vec) in
  Lymp.get_float py_module "predict_proba" [clf; vec]

module Hashtbl = DynamicFeature.Hashtbl

let clf_strategy global feature timer = 
  let (py_module, clf) = load_classifier global in 
  Hashtbl.fold (fun k _ -> 
      if predict py_module clf k feature timer.static_feature then PowLoc.add k
      else id) DynamicFeature.locset_hash PowLoc.empty 

let threshold_list () = 
  match coarsening_target with 
  | Dug when !Options.timer_threshold_abs = "" -> [0; 10; 50; 80; 100]
  | Dug -> 
    Str.split (Str.regexp "[ \t]+") (!Options.timer_threshold_time)
    |> List.map int_of_string
  | Worklist -> [0; 10; 30; 60; 100; 110; 120; 130]

let rec threshold i = 
  !timer.prepare + !timer.deadline * (try List.nth (threshold_list ()) i with _ -> 10000000) / 100

let threshold_list_loc () = 
  if !Options.timer_threshold_abs = "" then [0; 10; 50; 80; 100]
  else 
    Str.split (Str.regexp "[ \t]+") (!Options.timer_threshold_abs)
    |> List.map int_of_string

let counter_example global lst =
    let filename = Filename.basename global.file.Cil.fileName in
    let oracle = try MarshalManager.input ~dir:!Options.timer_dir (filename^".oracle") with _ -> prerr_endline "Can't find the oracle"; BatMap.empty in
    prerr_endline "== counter examples";
    List.iter (fun (x, w) ->
        let answer = try BatMap.find (!timer.time_stamp, Loc.to_string x) oracle with _ -> w in
        if abs_float (answer -. w) >= 0.5 then
          prerr_endline ("ce : " ^ Loc.to_string x ^ " : " ^ string_of_float w ^", answer : " ^ string_of_float answer)
        else ()
    ) lst; lst

let rank_strategy global spec feature timer = 
  let top = 
    match coarsening_target with 
    | Dug ->
        (try List.nth (threshold_list_loc ()) timer.time_stamp with _ -> 100) * timer.num_of_locset / 100
          - (try List.nth (threshold_list_loc ()) (timer.time_stamp -1) with _ -> 100) * timer.num_of_locset / 100
    | Worklist -> 
        (try List.nth (threshold_list ()) timer.time_stamp with _ -> 100) * timer.num_of_locset / 100 
  in
  let ranking =
    if !Options.timer_oracle_rank then
      let filename = Filename.basename global.file.Cil.fileName in
      let oracle = try MarshalManager.input ~dir:!Options.timer_dir (filename^".oracle") with _ -> prerr_endline "Can't find the oracle"; BatMap.empty in
(*      BatMap.iter (fun (idx, k) b ->
        prerr_endline ("("^string_of_int idx ^", "^k^") -> "^string_of_float b)) oracle;
*)      Hashtbl.fold (fun k _ l ->
          let score = 
            (try BatMap.find (timer.time_stamp, Loc.to_string k) oracle with _ -> 0.0)
          in
          (k, score)::l) DynamicFeature.locset_hash []
        |> List.sort (fun (_, x) (_, y) -> if x > y then -1 else if x = y then 0 else 1)
    else if !Options.timer_static_rank then
      let locset = Hashtbl.fold (fun k _ l -> k::l) DynamicFeature.locset_hash [] in
      let weights = Str.split (Str.regexp "[ \t]+") (!Options.pfs_wv) in
      PartialFlowSensitivity.assign_weight locset timer.static_feature weights
      |> List.sort (fun (_, x) (_, y) -> if x < y then -1 else if x = y then 0 else 1)
    else
      let (py_module, clf) = load_classifier global in 
      Hashtbl.fold (fun k _ l ->
(*          if PowLoc.mem k feature.DynamicFeature.eq_fi then
            (k, 1.1)::l
          else*)
            (k, predict_proba py_module clf k feature timer.static_feature)::l) DynamicFeature.locset_hash []
      |> List.sort (fun (_, x) (_, y) -> if x > y then -1 else if x = y then 0 else 1)
      |> opt !Options.timer_counter_example (counter_example global)
  in
  ranking
  |> opt !Options.timer_debug 
        (fun l -> List.fold_left (fun r (l, w) -> 
          prerr_string (string_of_int r ^ ". "^ (Loc.to_string l) ^ ", "^ (string_of_float w) ^ "\n");
          r + 1) 1 l |> ignore; prerr_endline ""; l)
  |> BatList.take top
  |> List.map fst
  |> PowLoc.of_list
(*  else PowLoc.empty*)

module AlarmSet = Dependency.AlarmSet

let old_alarms = ref AlarmSet.empty

let get_new_alarms alarms =
  let new_alarms = List.filter (fun q -> not (AlarmSet.mem q !old_alarms)) alarms in
  List.iter (fun q ->
      old_alarms := AlarmSet.add q !old_alarms; ()) new_alarms;
  new_alarms

let diff_alarms alarms1 alarms2 = 
  let alarms2_set = List.fold_left (fun set q -> AlarmSet.add q set) AlarmSet.empty alarms2 in
  List.filter (fun q -> not (AlarmSet.mem q alarms2_set)) alarms1

module History = BatMap.Make(Loc)
module HistoryAlarm = Dependency.AlarmMap

let timer_dump global dug inputof feature new_alarms locset_coarsen time = 
  let filename = Filename.basename global.file.Cil.fileName in
  let surfix = string_of_int time in
  let dir = !Options.timer_dir in
  MarshalManager.output ~dir (filename ^ ".feature." ^ surfix) feature;
  MarshalManager.output ~dir (filename ^ ".inputof." ^ surfix) inputof;
  MarshalManager.output ~dir (filename ^ ".dug." ^ surfix) dug;
  MarshalManager.output ~dir (filename ^ ".alarm." ^ surfix) new_alarms;
  let coarsen_history =
    (try MarshalManager.input ~dir (filename ^ ".coarsen_history") with _ -> History.empty)
    |> PowLoc.fold (fun x -> History.add x time) locset_coarsen
  in
  MarshalManager.output ~dir (filename ^ ".coarsen_history") coarsen_history;
  let alarm_history =
    (try MarshalManager.input ~dir (filename ^ ".alarm_history") with _ -> HistoryAlarm.empty)
    |> list_fold (fun x -> HistoryAlarm.add x time) new_alarms
  in
  MarshalManager.output ~dir (filename ^ ".alarm_history") alarm_history

(* compute coarsening targets *)
let filter locset_coarsen node dug =
  list_fold (fun p (target, dug) ->
      let locs_on_edge = DUGraph.get_abslocs p node dug in
      let target_on_edge = PowLoc.inter locs_on_edge locset_coarsen in
      if PowLoc.is_empty target_on_edge then (target, dug)
      else
        let dug = DUGraph.remove_abslocs p target_on_edge node dug in
        let target = PowLoc.union target_on_edge target in
        (target, dug)
    ) (DUGraph.pred node dug) (PowLoc.empty, dug)

(* coarsening all nodes in dug *)
let coarsening_dug global access locset_coarsen dug worklist inputof spec =
  if PowLoc.is_empty locset_coarsen then (spec,dug,worklist,inputof)
  else
    let (dug,worklist_candidate,inputof) = 
      DUGraph.fold_node (fun node (dug,worklist_candidate,inputof) ->
          let _ = Profiler.start_event "coarsening filter" in
          let (locset_coarsen, dug) = filter locset_coarsen node dug in
          let _ = Profiler.finish_event "coarsening filter" in
          if PowLoc.is_empty locset_coarsen then (dug, worklist_candidate, inputof)
          else
            let locset_coarsen = PowLoc.inter (Access.Info.useof (Access.find_node node access)) locset_coarsen in
            let old_mem = Table.find node inputof in
            let _ = Profiler.start_event "coarsening mem" in
            let new_mem = PowLoc.fold (fun l -> Mem.add l 
              (try Hashtbl.find DynamicFeature.premem_hash l with _ -> Val.bot)
              ) locset_coarsen old_mem in
            let _ = Profiler.finish_event "coarsening mem" in
            let worklist_candidate = 
(*              if Mem.unstables old_mem new_mem unstable spec.Spec.locset_fs = [] then worklist
              else*) node::worklist_candidate in
            (dug, worklist_candidate, Table.add node new_mem inputof)) dug (dug,[],inputof)
    in
    let (to_add, to_remove) = List.fold_left (fun (to_add, to_remove) node ->
        if DUGraph.pred node dug = [] && DUGraph.succ node dug = [] then (to_add, BatSet.add node to_remove)
        else (BatSet.add node to_add, to_remove)) (BatSet.empty, BatSet.empty) worklist_candidate
    in
    let worklist = 
      Worklist.remove_set to_remove worklist
      |> Worklist.push_plain_set to_add
    in
(*    let spec = { spec with Spec.locset_fs = PowLoc.diff spec.Spec.locset_fs locset_coarsen } in*)
    Hashtbl.filteri_inplace (fun k _ -> not (PowLoc.mem k locset_coarsen)) DynamicFeature.locset_hash;
(*    PowLoc.iter (fun k -> Hashtbl.replace locset_fi_hash k k) locset_coarsen;*)
    (spec,dug,worklist,inputof)

(* coarsening all nodes in worklist *)
let coarsening_worklist access locset_coarsen dug worklist inputof spec =
  if PowLoc.is_empty locset_coarsen then (dug,worklist,inputof)
  else
    let (dug,candidate) = 
      Worklist.fold (fun node (dug,candidate) ->
          let _ = Profiler.start_event "coarsening filter" in
          let (locset_coarsen, dug) = filter locset_coarsen node dug in
          let _ = Profiler.finish_event "coarsening filter" in
          if PowLoc.is_empty locset_coarsen then (dug, candidate)
      else (dug, (node,locset_coarsen)::candidate)) worklist (dug,[])
    in
    let (inputof, worklist) = 
      List.fold_left (fun (inputof,worklist) (node,locset_coarsen) ->
        let locs_on_edge = List.fold_left (fun locs s ->
                    DUGraph.get_abslocs node s dug
                    |> PowLoc.join locs) PowLoc.empty (DUGraph.succ node dug)
        in 
        let locs_used = Access.Info.useof (Access.find_node node access) in
        let locset_coarsen = PowLoc.inter locset_coarsen (PowLoc.join locs_on_edge locs_used) in
        let old_mem = Table.find node inputof in
        let _ = Profiler.start_event "coarsening mem" in
        let new_mem = PowLoc.fold (fun l -> Mem.add l 
          (try Hashtbl.find DynamicFeature.premem_hash l with _ -> Val.bot)
          ) locset_coarsen old_mem in
        let _ = Profiler.finish_event "coarsening mem" in
        let worklist = 
          if DUGraph.pred node dug = [] && DUGraph.succ node dug = [] then 
            Worklist.remove node worklist 
          else worklist
        in
        (Table.add node new_mem inputof, worklist)) (inputof, worklist) candidate
    in
    (dug,worklist,inputof)

let coarsening global access locset_coarsen dug worklist inputof spec =
  match coarsening_target with
  | Dug -> coarsening_dug global access locset_coarsen dug worklist inputof spec
  | Worklist -> 
    let (dug,worklist,inputof) = coarsening_worklist access locset_coarsen dug
        worklist inputof spec 
    in
    (spec,dug,worklist,inputof)

let print_stat spec global access dug =
  let alarm_fs = MarshalManager.input (global.file.Cil.fileName ^ ".alarm") |> flip Report.get Report.UnProven |> AlarmSet.of_list in
  let alarm_fi = spec.Spec.pre_alarm |> flip Report.get Report.UnProven |> AlarmSet.of_list in
  let locset_of_fi = Dependency.dependency_of_query_set_new false global dug access alarm_fi in
(*        AlarmSet.fold (fun q locs ->
          Dependency.dependency_of_query global dug access q global.mem
          |> PowLoc.join locs) alarm_fi PowLoc.empty
  in*)
  let locset_of_fs = Dependency.dependency_of_query_set_new false global dug access alarm_fs in
(*        AlarmSet.fold (fun q locs ->
          Dependency.dependency_of_query global dug access q global.mem
          |> PowLoc.join locs) alarm_fs PowLoc.empty
  in*)
  prerr_endline (" == Timer Stat ==");
  prerr_endline (" # Total AbsLoc : " ^ string_of_int (PowLoc.cardinal spec.Spec.locset_fs));
  prerr_endline (" # FI AbsLoc : " ^ string_of_int (PowLoc.cardinal locset_of_fi));
  prerr_endline (" # FS AbsLoc : " ^ string_of_int (PowLoc.cardinal locset_of_fs));
  exit 0

let initialize spec global access dug worklist inputof = 
  let widen_start = Sys.time () in
  let deadline = !Options.timer_deadline in (* time unit *)
  let alarm_fi = spec.Spec.pre_alarm |> flip Report.get Report.UnProven |> AlarmSet.of_list in
  let target_locset = (* target of this optimization problem *)
    Dependency.dependency_of_query_set_new true global dug access alarm_fi
  in
  prerr_endline ("\n== locset took " ^ string_of_float (Sys.time () -. widen_start)); 
  let static_feature = PartialFlowSensitivity.extract_feature global target_locset in
  let filename = Filename.basename global.file.Cil.fileName in
  let dir = !Options.timer_dir in
  MarshalManager.output ~dir (filename ^ ".static_feature") static_feature;
  let locset_coarsen = PowLoc.diff spec.Spec.locset_fs target_locset in
  (if !Options.timer_stat then print_stat spec global access dug);
  prerr_endline ("\n== feature took " ^ string_of_float (Sys.time () -. widen_start)); 
  (* for efficiency *)
  DynamicFeature.initialize_cache target_locset spec.Spec.premem;
  let (spec, dug, worklist, inputof) = coarsening global access locset_coarsen dug worklist inputof spec in
  let prepare = int_of_float (Sys.time () -. widen_start) in
(*   let deadline = !Options.timer_deadline - prepare in *)
  timer := {
    !timer with widen_start; last = Sys.time (); static_feature; locset = target_locset;
    num_of_locset = PowLoc.cardinal target_locset;
    prepare; deadline; threshold = deadline };
(*   timer := { !timer with threshold = threshold !timer.time_stamp; }; (* threshold uses prepare and deadline *) *)
  prerr_endline ("\n== Timer: Coarsening #0 took " ^ string_of_float (Sys.time () -. widen_start)); 
  prerr_endline ("== Given Deadline: " ^ (string_of_int !Options.timer_deadline));
  prerr_endline ("== Actual Target: " ^ (string_of_int !timer.num_of_locset));
  prerr_endline ("== Actual Deadline: " ^ (string_of_int !timer.deadline));
  let new_alarms = (BatOption.get spec.Spec.inspect_alarm) global spec inputof 
                   |> flip Report.get Report.UnProven in
  timer_dump global dug inputof empty new_alarms locset_coarsen 0;
  (spec, dug, worklist, inputof)

module Data = Set.Make(Loc)

let extract_type1 spec oc prev next coarsen size_coarsen coarsen_score_pos1 global dug access alarm_fi feature_prev inputof_prev inputof_idx iteration =
  output_string oc ("#\t\t\tType 1 Data. "^(string_of_int next)^" -> " ^ (string_of_int prev)^"\n");
  (* locs not related to FI-alarms *)
(*   let locs_of_fi_alarms = Dependency.dependency_of_query_set global dug access alarm_fi feature_prev inputof_prev inputof_idx in *)
  let locs_of_fi_alarms = Dependency.dependency_of_query_set_new false global dug access alarm_fi in
  let pos_locs1 = PowLoc.diff spec.Spec.locset_fs locs_of_fi_alarms in
  let inter_pos1 = PowLoc.inter pos_locs1 coarsen in
  output_string oc ("#\t\t\t\tPos1 : "^(PowLoc.cardinal pos_locs1 |> string_of_int)^"\n");
  output_string oc ("#\t\t\t\tCoarsen : "^(string_of_int size_coarsen)^"\n");
  let size_inter_pos = PowLoc.cardinal inter_pos1 in
  output_string oc ("#\t\t\t\tIntersect between Coarsen and Pos1 : "^(string_of_int size_inter_pos)^" ("^(string_of_int (size_inter_pos * 100 / size_coarsen))^"%)\n");
  let coarsen_score_pos1_new = (PowLoc.cardinal inter_pos1) * 100 / (PowLoc.cardinal coarsen) in
  output_string oc ("#\t\t\t\tPos1 Score previous iter : " ^ string_of_int coarsen_score_pos1 ^ ", this iter : " ^ string_of_int coarsen_score_pos1_new^"\n");
  let pos_locs1 =
    if iteration = 0 then pos_locs1
    else if coarsen_score_pos1 >= coarsen_score_pos1_new (*&& coarsen_score_pos1 >= 80*) then PowLoc.bot
    else PowLoc.diff pos_locs1 coarsen
  in
(*         PowLoc.iter (fun x -> output_string oc (string_of_raw_feature x feature_prev static_feature^ " : 1\n")) pos_locs; *)
  (pos_locs1, coarsen_score_pos1_new)

let is_inter_node global node =
  (InterCfg.is_entry node) || (InterCfg.is_exit node)
  || (InterCfg.is_callnode node global.icfg)
  || (InterCfg.is_returnnode node global.icfg)

let debug_info global inputof_prev feature_prev static_feature qset history_old history dep_locs =
  if !Options.timer_debug then
    begin
      AlarmSet.iter (fun q ->
        prdbg_endline ("query: "^(Report.string_of_query q));
        prdbg_endline ("node: "^(Node.to_string q.node));
        prdbg_endline ("cmd: "^(InterCfg.cmdof global.icfg q.node |> IntraCfg.Cmd.to_string));
      ) qset;
      PowLoc.iter (fun x ->
        prdbg_endline (DynamicFeature.string_of_raw_feature x feature_prev static_feature);
        prdbg_endline ("History       : "^string_of_int 
          (try History.find x history_old with _ -> -1)^ " -> " ^ string_of_int (try History.find x history with _ -> -1));
        prdbg_endline ("FI val        : "^(try Val.to_string (Mem.find x global.mem) with _ -> "Notfound"));
        let v = Table.fold (fun node mem -> 
            if is_inter_node global node then Val.join (Mem.find x mem) else id) inputof_prev Val.bot in
        prdbg_endline ("FS val (inter): "^(Val.to_string v));
        ) dep_locs
    end

(* Remove undesired variables (already imprecise ones) in negative data. *)
let refine_negative_data global inputof_prev locset =
  PowLoc.filter (fun x ->
    let fs_v = Table.fold (fun node mem -> 
      if is_inter_node global node then Val.join (Mem.find x mem) else id)
        inputof_prev Val.bot 
    in
    let fi_v = Mem.find x global.mem in
    not (Val.eq fs_v Val.bot) && not (Val.eq fs_v fi_v)) locset

let extract_data_normal spec global access oc filename lst alarm_fs alarm_fi alarms_list static_feature iteration =
  let filename = Filename.basename global.file.Cil.fileName in
  output_string oc ("# Iteration "^(string_of_int iteration)^" of "^ filename ^" begins\n");
  let dir = !Options.timer_dir in
  let final_idx = List.length alarms_list in
  let alarm_final = MarshalManager.input ~dir (filename ^ ".alarm." ^ (string_of_int final_idx)) |> AlarmSet.of_list in
  let coarsen_history = try MarshalManager.input ~dir (filename ^ ".coarsen_history") with _ -> History.empty in
  let coarsen_history_old = try MarshalManager.input ~dir (filename ^ ".coarsen_history_old") with _ -> History.empty in
  let alarm_history = try MarshalManager.input ~dir (filename ^ ".alarm_history") with _ -> HistoryAlarm.empty in
  let alarm_history_old = try MarshalManager.input ~dir (filename ^ ".alarm_history_old") with _ -> HistoryAlarm.empty in
  MarshalManager.output ~dir (filename ^ ".coarsen_history_old") coarsen_history;
  MarshalManager.output ~dir (filename ^ ".alarm_history_old") alarm_history;
  let (pos_data, neg_data) = List.fold_left (fun (pos_data, neg_data) i ->
    try 
      let (prev, idx, next) = (i, i + 1, i + 2) in
      prerr_endline ("Extract Data at " ^ string_of_int idx);
      let alarm_idx = MarshalManager.input ~dir (filename ^ ".alarm." ^ string_of_int idx) |> AlarmSet.of_list in
      let alarm_prev = MarshalManager.input ~dir (filename ^ ".alarm." ^ string_of_int prev) |> AlarmSet.of_list in
      let alarm_next = try MarshalManager.input ~dir (filename ^ ".alarm." ^ string_of_int next) |> AlarmSet.of_list with _ -> alarm_final in
      let inputof_prev = MarshalManager.input ~dir (filename ^ ".inputof." ^ string_of_int prev) in
      let dug = MarshalManager.input ~dir (filename ^ ".dug." ^ string_of_int prev) in
      let feature_prev = MarshalManager.input ~dir (filename ^ ".feature." ^ string_of_int prev) in
      if Sys.file_exists (dir^"/"^filename^".alarm."^string_of_int next) then
        let _ = output_string oc ("#\t\tIdx : " ^(string_of_int idx) ^ "\n") in
        (* 2. Update w to coarsen variables that are related to the FS alarms earlier *)
        output_string oc ("#\t\t\tPositive Data. "^(string_of_int next)^" -> " ^ (string_of_int prev)^"\n");
        prdbg_endline ("Type 2 Data at " ^ string_of_int idx);
        let inter =
          (* coarsen vars related with the FS-alarms at idx 1 and 2 *)
          if idx = 2 then AlarmSet.inter alarm_fs alarm_next
          else AlarmSet.inter alarm_fs (AlarmSet.diff alarm_next alarm_idx) 
        in
        let inter =
          AlarmSet.filter (fun x ->
              try
                let old_position = HistoryAlarm.find x alarm_history_old in
                let new_position = HistoryAlarm.find x alarm_history in
                old_position > new_position
              with _ -> true) inter
        in
(*         let inter = AlarmSet.inter alarm_fs alarm_next in *)
        output_string oc ("#\t\t\t\tnumber of alarm next: "^(string_of_int (AlarmSet.cardinal alarm_next))^"\n");
        output_string oc ("#\t\t\t\tnumber of alarm idx: "^(string_of_int (AlarmSet.cardinal alarm_idx))^"\n");
        output_string oc ("#\t\t\t\tnumber of alarm diff & fs: "^(string_of_int (AlarmSet.cardinal inter))^"\n");
        (* locs related to FS-alarms *)
        let pos_locs =
          Dependency.dependency_of_query_set_new false global dug access inter
          |> PowLoc.filter (fun x -> (PowLoc.mem x feature_prev.DynamicFeature.non_bot))
        in
        debug_info global inputof_prev feature_prev static_feature inter coarsen_history_old coarsen_history pos_locs;
        output_string oc ("#\t\t\t\tPos: "^(string_of_int (PowLoc.cardinal pos_locs))^"\n");
(*        let pos_locs =
          PowLoc.filter (fun x ->
              try
                let old_position = History.find x coarsen_history_old in
                let new_position = History.find x coarsen_history in
                old_position > new_position
              with _ -> true) pos_locs
        in*)
        output_string oc ("#\t\t\t\tPos (after filtering): "^(string_of_int (PowLoc.cardinal pos_locs))^"\n");
        prdbg_endline ("Pos Data : " ^ PowLoc.to_string pos_locs); 
        (* 3. Update w to coarsen variable *)
        output_string oc ("#\t\t\tNegative Data. "^(string_of_int idx)^" -> " ^ (string_of_int next)^"\n");
        output_string oc ("#\t\t\t\tnumber of alarm prev: "^(string_of_int (AlarmSet.cardinal alarm_prev))^"\n");
        output_string oc ("#\t\t\t\tnumber of alarm idx: "^(string_of_int (AlarmSet.cardinal alarm_idx))^"\n");
        prdbg_endline ("Negative Data at " ^ string_of_int idx);
        let diff = AlarmSet.diff (AlarmSet.diff alarm_idx alarm_prev) alarm_fs in
(*         let diff = AlarmSet.diff alarm_final alarm_fs in *)
        let diff =
          AlarmSet.filter (fun x ->
              try
                let old_position = HistoryAlarm.find x alarm_history_old in
                let new_position = HistoryAlarm.find x alarm_history in
                old_position < new_position
              with _ -> true) diff
        in
        output_string oc ("#\t\t\t\tnumber of alarm diff & non-fs: "^(string_of_int (AlarmSet.cardinal diff))^"\n");
        let locs_of_alarms =
          Dependency.dependency_of_query_set_new false global dug access diff 
          |> refine_negative_data global inputof_prev
        in
        debug_info global inputof_prev feature_prev static_feature diff coarsen_history_old coarsen_history locs_of_alarms;
        let neg_locs = locs_of_alarms in
        output_string oc ("#\t\t\t\tNeg: "^(PowLoc.cardinal neg_locs |> string_of_int)^"\n");
(*
        let neg_locs =
          PowLoc.filter (fun x ->
              try
                let old_position = History.find x coarsen_history_old in
                let new_position = History.find x coarsen_history in
                old_position < new_position
              with _ -> true) neg_locs
        in
*)
        prdbg_endline ("Neg Data : " ^ PowLoc.to_string neg_locs); 
        output_string oc ("#\t\t\t\tNeg (after filter): "^(PowLoc.cardinal neg_locs |> string_of_int)^"\n");
(*         MarshalManager.output ~dir (filename ^ ".coarsen.score." ^ string_of_int prev) (coarsen_score_pos1_new, coarsen_score_pos2_new, coarsen_score_neg_new); *)
        let conflict = PowLoc.inter pos_locs neg_locs in
        output_string oc ("#\t\t\tSummary at "^(string_of_int idx)^"\n");
        output_string oc ("#\t\t\t\tpositive : "^(string_of_int (PowLoc.cardinal pos_locs))^"\n");
        output_string oc ("#\t\t\t\tnegative : "^(string_of_int (PowLoc.cardinal neg_locs))^"\n");
        output_string oc ("#\t\t\t\tconflict : "^(string_of_int (PowLoc.cardinal conflict))^"\n");
        let pos_data = PowLoc.fold (fun x pos_data -> 
            if PowLoc.mem x conflict then pos_data
            else (prev, x, feature_prev)::pos_data) pos_locs pos_data in
        let neg_data = PowLoc.fold (fun x neg_data -> 
(*            if PowLoc.mem x conflict then neg_data
            else*) (prev, x, feature_prev)::neg_data) neg_locs neg_data in
        (pos_data, neg_data)
      else 
        (pos_data, neg_data)
    with _ -> (pos_data, neg_data)
  ) ([], []) lst
  in
  output_string oc ("# Iteration "^(string_of_int iteration)^" completes\n");
  output_string oc ("# Summary\n");
  let conflict = 
    BatSet.intersect 
      (List.fold_left (fun set (i, x, _) -> BatSet.add (i, Loc.to_string x) set) BatSet.empty pos_data)
      (List.fold_left (fun set (i, x, _) -> BatSet.add (i, Loc.to_string x) set) BatSet.empty neg_data) 
  in
  output_string oc ("# positive : "^(string_of_int (List.length pos_data))^"\n");
  output_string oc ("# negative : "^(string_of_int (List.length neg_data))^"\n");
  output_string oc ("# conflict : "^(string_of_int (BatSet.cardinal conflict))^"\n");
  (pos_data, neg_data)

let extract_data spec global access iteration  = 
  let filename = Filename.basename global.file.Cil.fileName in
  let dir = !Options.timer_dir in
  let oc = open_out_gen [Open_creat; Open_append; Open_text] 0o640 (!Options.timer_dir ^ "/" ^ filename ^ ".tr_data.dat.raw") in
  let alarm_fs = MarshalManager.input (filename ^ ".alarm") |> flip Report.get Report.UnProven |> AlarmSet.of_list in
  let alarm_fi = spec.Spec.pre_alarm |> flip Report.get Report.UnProven |> AlarmSet.of_list in
  let lst = BatList.range 1 `To (List.length (threshold_list ())) in
  let alarms_list = List.fold_left (fun l i -> 
      try 
        let a = MarshalManager.input ~dir (filename ^ ".alarm." ^ (string_of_int i)) |> AlarmSet.of_list in
        a::l
      with _ -> l) [] lst
  in
  let static_feature = MarshalManager.input ~dir (filename ^ ".static_feature") in
  let final_idx = List.length alarms_list in
  let lst = BatList.range 1 `To final_idx in
  let alarm_final = MarshalManager.input ~dir (filename ^ ".alarm." ^ (string_of_int final_idx)) |> AlarmSet.of_list in
  let (pos_data, neg_data) = 
      extract_data_normal spec global access oc filename lst alarm_fs alarm_fi alarms_list static_feature iteration
  in
  close_out oc;
  let oc = open_out_gen [Open_creat; Open_append; Open_text] 0o640 (!Options.timer_dir ^ "/" ^ filename ^ ".tr_data.dat") in
  output_string oc "# Iteration\n";
  List.iter (fun (_, x, feature) -> 
    output_string oc (DynamicFeature.string_of_raw_feature x feature static_feature ^ " : 1\n")) pos_data;
  List.iter (fun (_, x, feature) -> 
    output_string oc (DynamicFeature.string_of_raw_feature x feature static_feature ^ " : 0\n")) neg_data;
  if !Options.timer_oracle_rank || !Options.timer_counter_example then
  begin
    let filename = Filename.basename global.file.Cil.fileName in
    let oracle = try MarshalManager.input ~dir:!Options.timer_dir (filename^".oracle") with _ -> prerr_endline "Can't find the oracle"; BatMap.empty in
    let oracle = List.fold_left (fun oracle (prev, x, feature) ->
      BatMap.add (prev, Loc.to_string x) 1.0 oracle) oracle pos_data in
    let oracle = List.fold_left (fun oracle (prev, x, feature) ->
      BatMap.add (prev, Loc.to_string x) (0.0) oracle) oracle neg_data in
      MarshalManager.output ~dir (filename^".oracle") oracle
  end;
  let score = List.fold_left (fun score i ->
      try
        let (prev, idx) = (i - 1, i) in
        let alarm_idx = MarshalManager.input ~dir (filename ^ ".alarm." ^ string_of_int idx) |> AlarmSet.of_list in
        let alarm_prev = if i = 0 then AlarmSet.empty else MarshalManager.input ~dir (filename ^ ".alarm." ^ string_of_int prev) |> AlarmSet.of_list in
        let new_alarm = AlarmSet.diff alarm_idx alarm_prev in
        let inter = AlarmSet.inter alarm_fs new_alarm in
        (* score 1: for FS-alarms (d - t) / d *)
        let score1 = ((float_of_int (final_idx - idx))
                     /. float_of_int final_idx)
                     *. (float_of_int (AlarmSet.cardinal inter))
                     /. (float_of_int (AlarmSet.cardinal alarm_final))
        in
        (* score 2: for non-FS-alarms t / d *)
        let score2 = (float_of_int idx)
                     /. (float_of_int final_idx)
                     *. float_of_int (AlarmSet.cardinal (AlarmSet.diff new_alarm inter))
                     /. (float_of_int (AlarmSet.cardinal alarm_final))
        in
        prerr_endline ("idx : " ^ string_of_int idx);
        prerr_endline ("# alarms in FS-alarm before deadline: " ^ string_of_int (AlarmSet.cardinal inter));
        prerr_endline ("# alarms not in FS-alarm before deadline: " ^ string_of_int (AlarmSet.cardinal (AlarmSet.diff new_alarm inter)));
        score +. score1 +. score2
      with _ -> score) 0.0 (0::lst)
  in 
  prerr_endline ("Score of proxy: " ^ string_of_float score);
  exit 0

let coarsening_fs spec global access dug worklist inputof = 
  let (spec, dug, worklist, inputof) = 
    if !timer.widen_start = 0.0 then initialize spec global access dug worklist inputof  (* initialize *)
    else (spec, dug, worklist, inputof)
  in
  let t0 = Sys.time () in
  let elapsed = t0 -. !timer.last in
  if elapsed > (float_of_int (!timer.threshold * (!timer.time_stamp))) then
    let _ = prerr_endline ("\n== Timer: Coarsening #"^(string_of_int !timer.time_stamp)^" starts at " ^ (string_of_float elapsed)) in
    let num_of_locset_fs = PowLoc.cardinal spec.Spec.locset_fs in
    let num_of_locset = Hashtbl.length DynamicFeature.locset_hash in
    if num_of_locset_fs = 0 then 
      (spec, dug, worklist, inputof)
    else 
      let _ = Profiler.reset () in
      let alarms = (BatOption.get spec.Spec.inspect_alarm) global spec inputof |> flip Report.get Report.UnProven in
      let new_alarms = get_new_alarms alarms in
      let alarms_part = Report.partition alarms in
      let new_alarms_part = Report.partition new_alarms in
      let dynamic_feature = DynamicFeature.extract spec global elapsed alarms_part new_alarms_part !timer.old_inputof inputof !timer.dynamic_feature in
      prerr_endline ("\n== Timer: feature extraction took " ^ string_of_float (Sys.time () -. t0));
      let t1 = Sys.time () in
      (* fixted portion *)
      let locset_coarsen = 
        match strategy with
        | Rank -> rank_strategy global spec dynamic_feature !timer
        | Clf -> clf_strategy global dynamic_feature !timer
      in
      (if !Options.timer_dump then timer_dump global dug inputof dynamic_feature alarms locset_coarsen !timer.time_stamp); 
      prerr_endline ("\n== Timer: Predict took " ^ string_of_float (Sys.time () -. t1));
      let num_of_works = Worklist.cardinal worklist in
      let t2 = Sys.time () in
      let (spec, dug, worklist, inputof) = coarsening global access locset_coarsen dug worklist inputof spec in
      prerr_endline ("\n== Timer: Coarsening dug took " ^ string_of_float (Sys.time () -. t2));
      prerr_endline ("Unproven Query          : " ^ string_of_int (BatMap.cardinal new_alarms_part));
      prerr_endline ("Unproven Query (acc)    : " ^ string_of_int (BatMap.cardinal alarms_part));
      prerr_endline ("Coarsening Target       : " ^ string_of_int (PowLoc.cardinal locset_coarsen) ^ " / " ^ string_of_int num_of_locset);
(*      prerr_endline ("Coarsening Target (acc) : " ^ string_of_int (Hashtbl.length locset_fi_hash) ^ " / " ^ string_of_int num_of_locset);*)
      prerr_endline ("Analyzed Node           : " ^ string_of_int (PowNode.cardinal !SparseAnalysis.reach_node) ^ " / " ^ string_of_int !SparseAnalysis.nb_nodes);
      prerr_endline ("#Abs Locs on Dug        : " ^ string_of_int (DUGraph.nb_loc dug));
      prerr_endline ("#Node on Dug            : " ^ string_of_int (DUGraph.nb_node dug));
      prerr_endline ("#Worklist               : " ^ (string_of_int num_of_works) ^ " -> "^(string_of_int (Worklist.cardinal worklist)));
(*       prdbg_endline ("Coarsened Locs : \n\t"^PowLoc.to_string locset_coarsen); *)
      (if !Options.timer_debug then Report.display_alarms ~verbose:0 ("Alarms at "^string_of_int !timer.time_stamp) new_alarms_part);
      prerr_endline ("== Timer: Coarsening took " ^ string_of_float (Sys.time () -. t0));
      prerr_endline ("== Timer: Coarsening completes at " ^ string_of_float (Sys.time () -. !timer.widen_start));
      Profiler.report stdout;
      timer := { !timer with last = Sys.time (); 
(*         threshold = threshold (!timer.time_stamp + 1); *)
        time_stamp = !timer.time_stamp + 1;
        dynamic_feature;
        old_inputof = inputof;
(*         alarm_history = BatMap.add !timer.threshold alarms !timer.alarm_history; *)
      };
      (spec,dug,worklist,inputof) 
  else (spec, dug, worklist, inputof)

let finalize spec global dug inputof =
  let alarms = (BatOption.get spec.Spec.inspect_alarm) global spec inputof |> flip Report.get Report.UnProven in
  if !Options.timer_debug then
    begin
      let new_alarms_part = Report.partition alarms in
      Report.display_alarms ~verbose:0 ("Alarms at "^string_of_int !timer.time_stamp) new_alarms_part
    end;
  timer_dump global dug inputof DynamicFeature.empty_feature alarms PowLoc.empty !timer.time_stamp
