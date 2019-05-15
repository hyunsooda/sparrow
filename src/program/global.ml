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
open Yojson.Safe
open Vocab
open BasicDom
open InterCfg
open Cil
open Pretty
open Cilglobal

type t = {
  file : Cil.file;
  icfg : InterCfg.t;
  callgraph : CallGraph.t;
  dump : Dump.t;
  mem : ItvDom.Mem.t;
  table : ItvDom.Table.t;
}

let remove_node : InterCfg.node -> t -> t = fun node global ->
  { global with
    icfg = InterCfg.remove_node node global.icfg }

let remove_function : InterCfg.Proc.t -> t -> t = fun pid global ->
  { global with
    icfg = InterCfg.remove_function pid global.icfg;
    callgraph = CallGraph.remove_function pid global.callgraph;
    dump = Dump.remove pid global.dump }

let is_rec : InterCfg.pid -> t -> bool = fun pid global ->
  CallGraph.is_rec global.callgraph pid

let remove_unreachable_nodes : t -> t
=fun global ->
  let nodes_all = InterCfg.nodesof global.icfg in
  let unreachable = InterCfg.unreachable_node global.icfg in
  let global = NodeSet.fold remove_node unreachable global in
  my_prerr_newline ();
  my_prerr_string "#nodes all   : ";
  my_prerr_endline (string_of_int (List.length nodes_all));
  my_prerr_string "#unreachable : ";
  my_prerr_endline (string_of_int (NodeSet.cardinal unreachable));
(*    prerr_string "unreachable nodes : ";
  prerr_endline (string_of_set InterCfg.Node.to_string unreachable); *)
  global

class simpleCilPrinterClass = object (self)
inherit Cil.defaultCilPrinterClass as super
method pLineDirective ?(forcefile=false) l = Pretty.nil
method pGlobal () global =
match global with
| Cil.GVarDecl (vi, l) when Hashtbl.mem Cil.builtinFunctions vi.vname ->
Pretty.nil
| Cil.GVarDecl (vi, l) ->
(match vi.vtype with
 | TFun (_, _, _, attr) ->
 if List.mem (Cil.Attr ("missingproto", [])) attr then Pretty.nil
 else (super#pVDecl () vi) ++ text ";\n"
 | _ -> (super#pVDecl () vi) ++ text ";\n")
| _ -> super#pGlobal () global
end

let dumpFile pp out file =
Pretty.fastMode := true;
Cil.iterGlobals file (fun g -> Cil.dumpGlobal pp out g);
flush out


let remove_unreachable_functions : t -> t
=fun global ->
  let pids_all = PowProc.of_list (InterCfg.pidsof global.icfg) in
  let reachable = CallGraph.trans_callees InterCfg.global_proc global.callgraph in
  let unreachable = PowProc.diff pids_all reachable |> PowProc.remove InterCfg.global_proc in
  let recursive = PowProc.filter (fun pid -> is_rec pid global) reachable in
  let global = if !Options.bugfinder >= 2 then global else PowProc.fold remove_function unreachable global in
  my_prerr_newline ();
  my_prerr_endline ("#functions all : " ^ string_of_int (PowProc.cardinal pids_all));
  my_prerr_endline ("#recursive : " ^ string_of_int (PowProc.cardinal recursive));
  if PowProc.cardinal recursive > 0 then my_prerr_endline (PowProc.to_string recursive);
  my_prerr_endline ("#unreachable   : " ^ string_of_int (PowProc.cardinal unreachable));
  if PowProc.cardinal unreachable > 0 then my_prerr_endline (PowProc.to_string unreachable);
  let oc = open_out "tmp.c" in
  let globals = global.file.globals in 
  my_prerr_endline ("#old   : " ^ string_of_int (List.length globals));
  let _,globals =
    List.fold_left (fun (set, lst) glob ->
        match glob with
          Cil.GFun(fundec,_) ->
          if (PowProc.mem fundec.svar.vname unreachable) || (GlobalSet.mem glob set) then (set, lst)
          else (GlobalSet.add glob set, lst@[glob])
        | Cil.GVarDecl(vardecl,_) ->
          if (PowProc.mem vardecl.vname unreachable) || (GlobalSet.mem glob set) then (set, lst)
          else (GlobalSet.add glob set, lst@[glob])
        | _ -> (GlobalSet.add glob set, lst@[glob])
      ) (GlobalSet.empty,[]) globals
  in
  let _ = global.file.globals <- globals in 
  my_prerr_endline ("#new   : " ^ string_of_int (List.length globals));
  let _ = dumpFile (new simpleCilPrinterClass (*Cil.defaultCilPrinterClass*)) oc global.file in
  close_out oc;
  exit 0;
  global

let init file =
  { file = file;
    icfg = InterCfg.init file;
    callgraph = CallGraph.empty;
    dump = Dump.empty;
    mem = ItvDom.Mem.bot;
    table = ItvDom.Table.bot; }
  |> remove_unreachable_nodes

let is_undef : InterCfg.pid -> t -> bool = fun pid global ->
  InterCfg.is_undef pid global.icfg

let get_leaf_procs : t -> PowProc.t
=fun global ->
  let pids = PowProc.of_list (InterCfg.pidsof global.icfg) in
  PowProc.fold (fun fid ->
        if PowProc.cardinal (CallGraph.trans_callees fid global.callgraph) = 1
        then PowProc.add fid
        else id) pids PowProc.bot

let to_json : t -> json
= fun g ->
  `Assoc
      [ ("callgraph", CallGraph.to_json g.callgraph);
        ("cfgs", InterCfg.to_json g.icfg)
      ]

let print_json : out_channel -> t -> unit
= fun chan g ->
  Yojson.Safe.pretty_to_channel chan (to_json g)
