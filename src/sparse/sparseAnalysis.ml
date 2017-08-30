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
open Vocab
open Global
open BasicDom
open AbsSem
open Dug

let total_iterations = ref 0
let g_clock = ref 0.0
let l_clock = ref 0.0
let g_timer = ref 0.0
let widen_start = ref 0.0
let l_timer = ref 0.0
let predict_start = ref 0.0

let reach_node = ref PowNode.empty
let nb_nodes = ref 0

module type S = 
sig
  module Dom : InstrumentedMem.S
  module Table : MapDom.CPO with type t = MapDom.MakeCPO(BasicDom.Node)(Dom).t
    and type A.t = BasicDom.Node.t and type B.t = Dom.t
  module DUGraph : Dug.S with type PowLoc.t = Dom.PowA.t
  module Worklist : Worklist.S with type DUGraph.t = DUGraph.t
  module Spec : Spec.S with type Dom.t = Dom.t and type Dom.A.t = Dom.A.t
    and type Dom.PowA.t = Dom.PowA.t and type Dom.Access.t = Dom.Access.t
    and type Table.t = Table.t and type DUGraph.t = DUGraph.t
    and type Worklist.t = Worklist.t
  val perform : Spec.t -> Global.t -> Global.t * Table.t * Table.t
end

module MakeWithAccess (Sem:AccessSem.S) =
struct
  module Dom = Sem.Dom
  module AccessAnalysis = AccessAnalysis.Make (Sem)
  module Access = AccessAnalysis.Access
  module Spec = Sem.Spec
  module DUGraph = Spec.DUGraph
  module SsaDug = SsaDug.Make (DUGraph) (Access)
  module Worklist = Spec.Worklist
  module Table = Spec.Table
  module PowLoc = Sem.Dom.PowA

  let needwidening : DUGraph.node -> Worklist.t -> bool
  =fun idx wl -> Worklist.is_loopheader idx wl

  let def_locs_cache = Hashtbl.create 251
  let get_def_locs : Node.t -> DUGraph.t -> Access.PowLoc.t 
  = fun idx dug ->
    (* when coarsening, the set of def_locs changes *)
    if !Options.timer_deadline > 0 then
      let union_locs succ = PowLoc.union (DUGraph.get_abslocs idx succ dug) in
      DUGraph.fold_succ union_locs dug idx PowLoc.empty 
    else
    try Hashtbl.find def_locs_cache idx with Not_found ->
    let def_locs =
      let union_locs succ = PowLoc.union (DUGraph.get_abslocs idx succ dug) in
      DUGraph.fold_succ union_locs dug idx PowLoc.empty 
    in
    Hashtbl.add def_locs_cache idx def_locs; def_locs

  let print_iteration () = 
    total_iterations := !total_iterations + 1;
    if !total_iterations = 1 then (g_clock := Sys.time(); l_clock := Sys.time ())
    else if !total_iterations mod 10000 = 0
    then 
    begin
      let g_time = Format.sprintf "%.2f" (Sys.time() -. !g_clock) in
      let l_time = Format.sprintf "%.2f" (Sys.time() -. !l_clock) in
      my_prerr_string ("\r#iters: " ^ string_of_int !total_iterations
                        ^ " took " ^ g_time
                        ^ "s  ("  ^ l_time ^ "s / last 10000 iters), " ^ (string_of_int (PowNode.cardinal !reach_node) ^ " / " ^ (string_of_int !nb_nodes)));
      flush stderr;
      l_clock := Sys.time ();
    end

  let print_time global table = 
    if !total_iterations mod 100 = 0 then
      print_endline (global.file.Cil.fileName ^ ", " ^ (string_of_int !total_iterations) ^ ", " ^ (string_of_float (Sys.time () -. !widen_start)))

  let propagate dug idx (works,inputof,outputof) (unstables,new_output,global)= 
    let (works, inputof) =
      let update_succ succ (works, inputof) =
        let old_input = Table.find succ inputof in
        let locs_on_edge = DUGraph.get_abslocs idx succ dug in
        let is_on_edge (x, _) = DUGraph.mem_duset x locs_on_edge in
        let to_join = List.filter is_on_edge unstables in
        if to_join = [] then (works, inputof) 
        else
          let new_input = Dom.join_pairs to_join old_input in
          (Worklist.push idx succ works, Table.add succ new_input inputof) 
      in
      DUGraph.fold_succ update_succ dug idx (works, inputof)
    in
    (works, global, inputof, Table.add idx new_output outputof)

  let get_unstable dug idx works old_output (new_output, global) =
    let def_locs = Profiler.event "SparseAnalysis.widening_get_def_locs" (get_def_locs idx) dug in
    let is_unstb v1 v2 = not (Dom.B.le v2 v1) in
    let u = Profiler.event "SparseAnalysis.widening_unstable" (Dom.unstables old_output new_output is_unstb) def_locs in
    if u = [] then None
    else
      let op = if needwidening idx works then Dom.B.widen else (fun _ y -> y) in
      let _ = Profiler.start_event "SparseAnalysis.widening_new_output" in
      let u = List.map (fun (k, v1, v2) -> (k, op v1 v2)) u in
      let new_output = list_fold (fun (k, v) -> Dom.add k v) u old_output in
      let _ = Profiler.finish_event "SparseAnalysis.widening_new_output" in
      (* update unstable locations's values by widened values *)
      let u = List.map (fun (k, _) -> (k, Dom.find k new_output)) u in
      Some (u, new_output, global)

  let prdbg_input : Node.t -> (Dom.t * Global.t) -> (Dom.t * Global.t) 
  = fun node (mem, global) -> 
    prerr_endline (Node.to_string node);
    prerr_endline (IntraCfg.Cmd.to_string (InterCfg.cmdof global.icfg node));
    prerr_endline "== Input ==";
    prerr_endline (Dom.to_string mem);
    (mem, global)

  let prdbg_output : Dom.t -> (Dom.t * Global.t) -> (Dom.t * Global.t) 
  = fun old_output (new_output, global) ->
    prerr_endline "== Old Output ==";
    prerr_endline (Dom.to_string old_output);
    prerr_endline "== New Output ==";
    prerr_endline (Dom.to_string new_output);
    (new_output, global)

  (* fixpoint iterator specialized to the widening phase *)
  let analyze_node : Spec.t -> DUGraph.t -> DUGraph.node
    -> (Worklist.t * Global.t * Table.t * Table.t)
    -> (Worklist.t * Global.t * Table.t * Table.t)
  = fun spec dug idx (works, global, inputof, outputof) ->
    reach_node := PowNode.add idx !reach_node;
    (if !Options.print_time then print_time global outputof);
    let old_output = Table.find idx outputof in
    (Table.find idx inputof, global)
    |> opt !Options.debug (prdbg_input idx)
    |> Profiler.event "SparseAnalysis.run" (Sem.run Strong spec idx)
    |> opt !Options.debug (prdbg_output old_output)
    |> Profiler.event "SparseAnalysis.get_unstable" (get_unstable dug idx works old_output)
    &> Profiler.event "SparseAnalysis.propagating" (propagate dug idx (works,inputof,outputof))
    |> (function None -> (works, global, inputof, outputof) | Some x -> x)


  (* fixpoint iterator that can be used in both widening and narrowing phases *)
  let analyze_node_with_otable (widen,order) : Spec.t -> DUGraph.t -> 
    DUGraph.node
    -> (Worklist.t * Global.t * Table.t * Table.t)
    -> (Worklist.t * Global.t * Table.t * Table.t)
  =fun spec dug idx (works, global, inputof, outputof) ->
    let pred = DUGraph.pred idx dug in
    let input = List.fold_left (fun m p ->
          let pmem = Table.find p outputof in
          let locs_on_edge = DUGraph.get_abslocs p idx dug in 
          PowLoc.fold (fun l m -> 
              let v1 = Dom.find l pmem in
              let v2 = Dom.find l m in
              Dom.add l (Dom.B.join v1 v2) m) locs_on_edge m
          ) Dom.bot pred in
    let inputof = Table.add idx input inputof in
    let old_output = Table.find idx outputof in
    let (new_output, global) = Sem.run Strong spec idx (input, global) in
    let widened = widen old_output new_output in
    if order widened old_output then (works, global, inputof, outputof)
    else 
      let works = Worklist.push_set idx (BatSet.of_list (DUGraph.succ idx dug)) works in
      (works, global, inputof, Table.add idx new_output outputof)

  let rec get_todos dug todos ws = 
    if BatSet.is_empty ws then todos
    else 
      let (w, ws) = BatSet.pop ws in
      if BatSet.mem w todos then get_todos dug todos ws
      else get_todos dug (BatSet.add w todos) (BatSet.union (DUGraph.succ w dug |> BatSet.of_list) ws)

  let post dug works global inputof outputof =
    let nodes = DUGraph.nodesof dug in
    prerr_endline ("# nodes : " ^ (string_of_int (BatSet.cardinal nodes)));
    let ws = Worklist.nodesof works in
    prerr_endline ("# worklist : " ^ (string_of_int (BatSet.cardinal ws)));
(*    let todos = get_todos dug BatSet.empty ws in
    let (inputof, todos) = Table.foldi (fun node _ (inputof, todos) -> 
                  if BatSet.exists (fun w -> DUGraph.reachable w node dug) ws then 
                    (Table.add node 
                     (Sem.project_pre global.mem) 
                     inputof, 
                    BatSet.add node todos)
                  else (inputof, todos)) inputof (inputof, BatSet.empty)
    in*)
(*    let inputof = BatSet.fold (fun todo ->
    let inputof = BatSet.fold (fun todo ->
                    Table.add todo (Sem.project_pre global.mem)) todos inputof in
    prerr_endline ("# todo  : " ^ (string_of_int (BatSet.cardinal todos)));*)
    (works, global, inputof, outputof) 

  let rec iterate f : Spec.t -> Access.t -> DUGraph.t -> (Worklist.t * Global.t * Table.t * Table.t) 
     -> (Worklist.t * Global.t * Table.t * Table.t)
  =fun spec access dug (works, global, inputof, outputof) ->
    print_iteration ();
    let (spec, dug, works, inputof) = 
      match spec.Spec.coarsening_fs with 
        Some f -> f spec global access dug works inputof
      | None -> (spec, dug, works, inputof) 
    in
(*    (if (Sys.time () -. !l_timer) > 50.0 then 
      let queries = match spec.inspect_alarm with Some f -> f global spec inputof | None -> [] in
      let unproven = Report.partition (Report.get queries Report.UnProven) in
      print_endline ((string_of_float (Sys.time () -. !widen_start)) ^ ", " ^ (string_of_int (BatMap.cardinal unproven)));
      l_timer := Sys.time ()
    );*)
    match Worklist.pick works with
    | None -> (works, global, inputof, outputof)
    | Some (idx, rest) -> 
      (rest, global, inputof, outputof) 
      |> f spec dug idx
      |> iterate f spec access dug

  let widening : Spec.t -> Access.t -> DUGraph.t -> (Worklist.t * Global.t * Table.t * Table.t)
      -> (Worklist.t * Global.t * Table.t * Table.t)
  =fun spec access dug (worklist, global, inputof, outputof) ->
    total_iterations := 0;
    widen_start := Sys.time ();
    l_timer := Sys.time ();
    worklist
    |> Worklist.push_set InterCfg.start_node (DUGraph.nodesof dug)
    |> (fun init_worklist -> iterate analyze_node spec access dug (init_worklist, global, inputof, outputof))
    |> (fun x -> my_prerr_endline ("\n#iteration in widening : " ^ string_of_int !total_iterations); x)
 
  let narrowing ?(initnodes=BatSet.empty) : Spec.t -> Access.t -> DUGraph.t -> (Worklist.t * Global.t * Table.t * Table.t) 
      -> (Worklist.t * Global.t * Table.t * Table.t)
  =fun spec access dug (worklist, global, inputof, outputof) ->
    total_iterations := 0;
    worklist
    |> Worklist.push_set InterCfg.start_node (if (BatSet.is_empty initnodes) then DUGraph.nodesof dug else initnodes)
    |> (fun init_worklist -> iterate (analyze_node_with_otable (Dom.narrow, fun x y -> Dom.le y x)) spec
        access dug (init_worklist, global, inputof, outputof))
    |> (fun x -> my_prerr_endline ("#iteration in narrowing : " ^ string_of_int !total_iterations); x)

  let print_dug (access,global,dug) = 
    if !Options.dug then 
    begin
      `Assoc 
        [ ("callgraph", CallGraph.to_json global.callgraph); 
          ("cfgs", InterCfg.to_json global.icfg);
          ("dugraph", DUGraph.to_json dug);
(*          ("dugraph-inter", DUGraph.to_json_inter dug access);*)
        ]
      |> Yojson.Safe.pretty_to_channel stdout;
      exit 0
    end
    else
    begin
      prerr_memory_usage ();
      prerr_endline ("#Nodes in def-use graph : " ^ i2s (DUGraph.nb_node dug));
      prerr_endline ("#Locs on def-use graph : " ^ i2s (DUGraph.nb_loc dug));
    end

  let bind_fi_locs global mem_fi dug access inputof =
    DUGraph.fold_node (fun n t ->
      let used = Access.Info.useof (Access.find_node n access) in
      let pred = DUGraph.pred n dug in
      let locs_on_edge = list_fold (fun p -> PowLoc.union (DUGraph.get_abslocs p n dug)) pred PowLoc.empty in
      let locs_not_on_edge = PowLoc.diff used locs_on_edge in
      let mem_with_locs_not_on_edge =
        PowLoc.fold (fun loc mem ->
          Dom.add loc (Dom.find loc mem_fi)  mem
        ) locs_not_on_edge (Table.find n inputof) in
      Table.add n mem_with_locs_not_on_edge t
    ) dug inputof

  (* add pre-analysis memory to unanalyzed nodes *)
  let bind_unanalyzed_node global mem_fi dug access inputof =
    let nodes = InterCfg.nodesof global.icfg in
    let nodes_in_dug = DUGraph.nodesof dug in
    list_fold (fun node t -> 
      if BatSet.mem node nodes_in_dug then t
      else 
        let mem_with_access = 
          PowLoc.fold (fun loc -> 
            Dom.add loc (Dom.find loc mem_fi) 
          ) (Access.Info.useof (Access.find_node node access)) Dom.bot in
          Table.add node mem_with_access t 
    ) nodes inputof

  let initialize : Spec.t -> Global.t -> DUGraph.t -> Access.t -> Table.t 
  = fun spec global dug access ->
    Table.add InterCfg.start_node (Sem.initial spec.Spec.locset) Table.empty
    |> cond (!Options.pfs < 100 || !Options.timer_deadline > 0) (bind_fi_locs global spec.Spec.premem dug access) id

  let finalize spec global dug access (worklist, global, inputof, outputof) = 
    let inputof = 
      if !Options.pfs < 100 || !Options.timer_deadline > 0 then bind_unanalyzed_node global spec.Spec.premem dug access inputof
      else inputof
    in
    (if !Options.timer_deadline > 0 then 
      match spec.Spec.timer_finalize with 
      | Some f -> f spec global dug inputof
      | None -> ());
    (worklist, global, inputof, outputof)

  let print_spec : Spec.t -> unit 
  = fun spec -> 
    my_prerr_endline ("#total abstract locations  = " ^ string_of_int (PowLoc.cardinal spec.Spec.locset));
    my_prerr_endline ("#flow-sensitive abstract locations  = " ^ string_of_int (PowLoc.cardinal spec.Spec.locset_fs))

  let perform : Spec.t -> Global.t -> Global.t * Table.t * Table.t
  =fun spec global -> 
    print_spec spec;
    let access = StepManager.stepf false "Access Analysis" (AccessAnalysis.perform global spec.Spec.locset (Sem.run Strong spec)) spec.Spec.premem in
    (match spec.Spec.extract_timer_data with
     | Some f -> f spec global access !Options.timer_iteration
     | None -> ());
    let filename = Filename.basename global.file.Cil.fileName in
    let dug = (* for experiment *)
      if (!Options.marshal_in || !Options.marshal_in_dug)
        && Sys.file_exists (!Options.marshal_dir ^ "/" ^ filename ^ ".dug") then 
        MarshalManager.input (filename ^ ".dug")
      else
        StepManager.stepf false "Def-use graph construction" SsaDug.make (global, access, spec.Spec.locset_fs) 
    in
    print_dug (access,global,dug);
    let worklist = 
      if (!Options.marshal_in || !Options.marshal_in_worklist)
        && Sys.file_exists (!Options.marshal_dir ^ "/" ^ filename ^ ".worklist") then 
        MarshalManager.input (filename ^ ".worklist")
      else
        StepManager.stepf false "Workorder computation" Worklist.init dug 
    in  
    (if !Options.marshal_out || (!Options.marshal_out_dug && !Options.marshal_out_worklist)
     then 
    begin
      MarshalManager.output (filename^".dug") dug;
      MarshalManager.output (filename^".worklist") worklist
    end
    );
    
    (worklist, global, initialize spec global dug access, Table.empty) 
    |> StepManager.stepf false "Fixpoint iteration with widening" (widening spec access dug)
    |> finalize spec global dug access
    |> StepManager.stepf_opt !Options.narrow false "Fixpoint iteration with narrowing" (narrowing spec access dug)
    |> (fun (_,global,inputof,outputof) -> (global, inputof, outputof))
end

module Make (Sem:AbsSem.S) = MakeWithAccess (AccessSem.Make (Sem))
