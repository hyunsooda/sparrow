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

open BasicDom
open Cil
open Global
open Report
open ItvDom
open Vocab

module Analysis = SparseAnalysis.Make(ItvSem)
module Table = Analysis.Table
module DUGraph = Analysis.DUGraph
module Worklist = Analysis.Worklist
module Spec = Analysis.Spec
module Access = Spec.Dom.Access

let compare_query a b = 
  if Pervasives.compare a.loc.file b.loc.file = 0 then 
    if Pervasives.compare a.loc.line b.loc.line = 0 then 
      Pervasives.compare (AlarmExp.to_string a.exp) (AlarmExp.to_string b.exp)
    else Pervasives.compare a.loc.line b.loc.line
  else Pervasives.compare a.loc.file b.loc.file

module AlarmSet = BatSet.Make(struct type t = Report.query let compare = compare_query end)
module AlarmMap = BatMap.Make(struct type t = Report.query let compare = compare_query end)

let prdbg_endline x = 
  if !Options.timer_debug then
    prerr_endline ("DEBUG::"^x)
  else ()

let rec locs_of_exp pid e mem = 
  match e with 
  | Cil.Lval l -> ItvSem.eval_lv pid l mem
  | Cil.UnOp (_, e, _) -> locs_of_exp pid e mem
  | Cil.BinOp (_, e1, e2, _) ->
      PowLoc.join (locs_of_exp pid e1 mem) (locs_of_exp pid e2 mem)
  | Cil.Question (e1, e2, e3, _) -> 
      PowLoc.join (locs_of_exp pid e1 mem) (locs_of_exp pid e2 mem)
      |> PowLoc.join (locs_of_exp pid e3 mem)
  | Cil.CastE (_, e) -> locs_of_exp pid e mem 
  | Cil.AddrOf l -> ItvSem.eval_lv pid l mem
  | Cil.StartOf l -> ItvSem.eval_lv pid l mem
  | _ -> PowLoc.bot

let locs_of_alarm_exp q mem =
  let pid = InterCfg.Node.get_pid q.node in
  match q.exp with 
    AlarmExp.ArrayExp (l, e, _) -> 
      PowLoc.join (ItvSem.eval_lv pid l mem) (locs_of_exp pid e mem)
  | AlarmExp.DerefExp (e, _) -> locs_of_exp pid e mem
  | AlarmExp.Strcpy (e1, e2, _) 
  | AlarmExp.Strcat (e1, e2, _) -> PowLoc.join (locs_of_exp pid e1 mem) (locs_of_exp pid e2 mem)
  | AlarmExp.Strncpy (e1, e2, e3, _) 
  | AlarmExp.Memcpy (e1, e2, e3, _) 
  | AlarmExp.Memmove (e1, e2, e3, _) -> PowLoc.join (locs_of_exp pid e1 mem) (locs_of_exp pid e2 mem) |> PowLoc.join (locs_of_exp pid e3 mem)
  | _ -> PowLoc.bot

let intra_edge icfg src dst =
  not ((InterCfg.is_callnode src icfg) && (InterCfg.is_entry dst))
  && not ((InterCfg.is_exit src) && (InterCfg.is_returnnode dst icfg))

module DepTable = BatMap.Make(struct type t = Node.t [@@deriving compare] end)
module DepWork = BatSet.Make(struct type t = Node.t * PowLoc.t [@@deriving compare] end)
let string_of_table t =
  DepTable.iter (fun k v ->
    prerr_endline (Node.to_string k ^ " -> " ^ PowLoc.to_string v)) t

let string_of_works t =
  DepWork.iter (fun (n, ploc) ->
    prerr_endline (Node.to_string n ^ ", " ^ PowLoc.to_string ploc)) t
module ReachDef = BatSet.Make(struct type t = Node.t * Loc.t [@@deriving compare] end)

let dependency_of_query_set_new inter global dug access qset =
(*   prerr_endline (Report.string_of_query q); *)
  let rec loop works results =
(*
    prerr_endline ("|work|: " ^ string_of_int (DepWork.cardinal works));
    prerr_endline ("result: " ^ string_of_int (PowLoc.cardinal results));
    prerr_endline ("table: ");
    string_of_table table;
    prerr_endline ("work: ");
    string_of_works works;
*)
    if ReachDef.is_empty works (*|| PowLoc.cardinal results > 100 *) then results
    else
      let ((node, use) as w, works) = ReachDef.pop works in
(*       let _ = prerr_endline ("pick work : " ^ Node.to_string node ^ ", " ^ Loc.to_string use) in *)
      DUGraph.pred node dug
      |> List.fold_left (fun (works, results) p ->
(*           prerr_endline ("p : " ^ Node.to_string p); *)
          let locs_on_edge = DUGraph.get_abslocs p node dug in
(*           prerr_endline (PowLoc.to_string locs_on_edge); *)
          if PowLoc.mem use locs_on_edge then
            if ReachDef.mem (p, use) results then 
(*               let _ = prerr_endline "qwer" in *)
              (works, results)
            else
              let access = Access.find_node p access in
              let defs_pred = Access.Info.defof access in
              if PowLoc.mem use defs_pred then
(*                 let _ = prerr_endline "first" in *)
                let uses_pred =
                  match InterCfg.cmdof global.icfg p with
                  | IntraCfg.Cmd.Ccall (_, _, args, _) when inter && InterCfg.is_entry node ->
                      if Loc.is_lvar use then   (* parameter *)
                        let callee = Node.get_pid node in
                        let caller = Node.get_pid p in
                        let params = InterCfg.argsof global.icfg callee 
                        |> List.map (fun x -> Loc.of_lvar callee x.Cil.vname x.Cil.vtype) 
                        in
                        (try
                          List.fold_left2 (fun u arg param ->
                            if Loc.compare param use = 0 then
                              locs_of_exp caller arg global.mem
                            else u) PowLoc.empty args params
                        with _ -> PowLoc.empty)
                      else PowLoc.singleton use (* others *)
                  | _ -> Access.Info.useof access
                in
                (PowLoc.fold (fun u -> ReachDef.add (p, u)) uses_pred works,
                ReachDef.add (p, use) results)
              else (* phi node or entry *)
(*                 let _ = prerr_endline "phi" in *)
                (ReachDef.add (p, use) works, ReachDef.add (p, use) results)  
          else
(*             let _ = prerr_endline "asdf" in *)
            (works, results)) (works, results)
      |> (fun (works, results) -> loop works results)
  in
  let works = 
    AlarmSet.fold (fun q ->
      let locs = locs_of_alarm_exp q global.mem in
      PowLoc.fold (fun x -> ReachDef.add (q.node, x)) locs) qset ReachDef.empty
  in
  let reach_def = loop works ReachDef.empty in
(*
  ReachDef.iter (fun (node, use) -> 
    prerr_endline ("final : " ^ Node.to_string node ^ ", " ^ Loc.to_string use)) reach_def;
*)
  let s = ReachDef.fold (fun x -> PowLoc.add (snd x)) reach_def PowLoc.empty in
(*   prerr_endline (PowLoc.to_string s); *)
  s

(* for debug *)
let dependency_of_query_set global dug access qset inputof_prev =
  AlarmSet.fold (fun q ->
(*     let mem_idx = Table.find q.node inputof_idx in *)
    let mem_prev = Table.find q.node inputof_prev in
    let set = dependency_of_query_set_new false global dug access (AlarmSet.singleton q) in
    (if !Options.timer_debug then
    let _ = prdbg_endline ("query: "^(Report.string_of_query q)) in
    prdbg_endline ("node: "^(Node.to_string q.node));
    prdbg_endline ("cmd: "^(InterCfg.cmdof global.icfg q.node |> IntraCfg.Cmd.to_string));
(*    let _ = prdbg_endline ("idx mem: "^(Mem.to_string mem_idx)) in
    let _ = prdbg_endline ("prev mem: "^(Mem.to_string mem_prev)) in
*)    let _ = prdbg_endline ("dep: "^(PowLoc.to_string set)) in
    PowLoc.iter (fun x -> 
(*      (if Mem.mem x mem_prev (*&& Random.int 10 = 0*) then
       begin*)
         prdbg_endline ("loc : " ^(Loc.to_string x));
         prdbg_endline ("FS val : "^(Val.to_string (Mem.find x mem_prev)));
         prdbg_endline ("FI val : "^(try Val.to_string (Mem.find x global.mem) with _ -> "Notfound"))
(*       end*)) set
      else ());
    set
(*    PowLoc.filter (fun x -> Mem.mem x mem_prev) set*)
    |> PowLoc.join) qset PowLoc.bot

