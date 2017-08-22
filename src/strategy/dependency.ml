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
  || not ((InterCfg.is_exit src) && (InterCfg.is_returnnode dst icfg))

let dependency_of_query global dug access q mem =
  let rec loop works visited results = 
    match works with
    | [] -> results
    | (node, uses)::t -> 
      let visited = PowNode.add node visited in
      let results = PowLoc.union results uses in
      DUGraph.pred node dug
      |> List.filter (fun p -> (intra_edge global.icfg p node) && not (PowNode.mem p visited))
      |> List.fold_left (fun works p ->
          let access = Access.find_node p access in
          let defs_pred = Access.Info.defof access in
          let inter = PowLoc.inter defs_pred uses in
          if PowLoc.is_empty inter then 
            if InterCfg.cmdof global.icfg p = IntraCfg.Cmd.Cskip then (* phi *)
              (p, uses)::works
            else works
          else (p, Access.Info.useof access)::works) t
      |> (fun works -> loop works visited results)
  in
  loop [(q.node, locs_of_alarm_exp q mem)] PowNode.bot PowLoc.bot

let dependency_of_query_set global dug access qset feature inputof_prev inputof_idx = 
  AlarmSet.fold (fun q ->
(*     let mem_idx = Table.find q.node inputof_idx in *)
    let mem_prev = Table.find q.node inputof_prev in
    let set = dependency_of_query global dug access q mem_prev in
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

