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
open Global
open ItvDom
open Vocab

module Analysis = SparseAnalysis.Make(ItvSem)
module Table = Analysis.Table
module DUGraph = Analysis.DUGraph
module Worklist = Analysis.Worklist
module Spec = Analysis.Spec
module Access = Spec.Dom.Access

type t = {
  memory_budget : float;
  memory_consumption : float;
  lattice_height : float;
  worklist_size : float;
  total_memory : float;
}

let empty = {
  memory_budget = 0.0;
  memory_consumption = 0.0;
  lattice_height = 0.0;
  worklist_size = 0.0;
  total_memory = 0.0;
}

let height_of_val v =
  (Val.itv_of_val v |> Itv.height)
  + (Val.pow_loc_of_val v |> PowLoc.cardinal)
  + (Val.array_of_val v |> ArrayBlk.cardinal)
  + (Val.struct_of_val v |> StructBlk.cardinal)
  + (Val.pow_proc_of_val v |> PowProc.cardinal)

let height_of_mem mem =
  Mem.fold (fun _ v h -> (height_of_val v) + h) mem 0

let is_sample node global worklist =
  InterCfg.is_entry node || InterCfg.is_exit node
  || Worklist.is_loopheader node worklist

let height_of_table global table worklist =
  Table.fold (fun node mem h ->
      if is_sample node global worklist then (height_of_mem mem) + h
      else h) table 0

let height_of_fi_mem global worklist dug access fi_mem =
  let t0 = Sys.time () in
  let height = DUGraph.fold_node (fun n height ->
      if is_sample n global worklist then
        let pred = DUGraph.pred n dug in
        let access = list_fold (fun p -> PowLoc.union (DUGraph.get_abslocs p n dug)) pred PowLoc.empty in
        PowLoc.fold (fun x height ->
            let h = Mem.find x fi_mem |> height_of_val in
            h + height) access height
      else
        height) dug 0
  in
  prerr_endline ("== height_of_fi_mem took " ^ string_of_float (Sys.time () -. t0));
  height

let extract_feature global inputof worklist ~total_memory ~base_memory ~fi_height ~base_height ~total_worklist =
  let height = height_of_table global inputof worklist - base_height in
  let memory = memory_usage () - base_memory in
  let works = Worklist.cardinal worklist in
  let feat = {
    memory_budget = 1.0 /. float_of_int (total_memory - base_memory);
    memory_consumption = (float_of_int memory) /. (float_of_int (total_memory - base_memory));
    lattice_height = (float_of_int height) /. (float_of_int (fi_height - base_height));
    worklist_size = (float_of_int works) /. (float_of_int total_worklist);
    total_memory = float_of_int total_memory;
  }
  in
  prerr_endline ("Current Mem1 : " ^ string_of_int (memory_usage ()));
  prerr_endline ("Height : " ^ string_of_int height);
  prerr_endline ("Mem : " ^ string_of_int memory);
  prerr_endline ("Work : " ^ string_of_int works);
  prerr_endline ("Budget : " ^ string_of_float feat.memory_budget);
  prerr_endline ("Mem : " ^ string_of_float feat.memory_consumption);
  prerr_endline ("Height : " ^ string_of_float feat.lattice_height);
  prerr_endline ("Work : " ^ string_of_float feat.worklist_size);
  feat

let to_vector feat =
  [ feat.memory_budget; feat.memory_consumption; feat.lattice_height;
    feat.worklist_size; ]
