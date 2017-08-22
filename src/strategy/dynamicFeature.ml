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
open Report
open Vocab

module Analysis = SparseAnalysis.Make(ItvSem)
module Table = Analysis.Table
module DUGraph = Analysis.DUGraph
module Worklist = Analysis.Worklist
module Spec = Analysis.Spec
module Access = Spec.Dom.Access

module Pfs = PartialFlowSensitivity

(* 24 features *)
type feature = {
(*   progress_time  : float; *)
  progress_alarm : float;
  delta_alarm    : float;
  fi_var         : float;
  (* dynamic semantic features *)
  alarm                     : PowLoc.t;
  alarm_fi                  : PowLoc.t;  (* TODO *)
  indirect_alarm            : PowLoc.t;
  eq_fi                     : PowLoc.t;
  neg_itv                   : PowLoc.t;
  right_open_itv            : PowLoc.t;
  neg_offset                : PowLoc.t;
  left_open_offset          : PowLoc.t;
  right_open_offset         : PowLoc.t;
  neg_size                  : PowLoc.t;
  zero_size                 : PowLoc.t;
  large_ptr_set             : PowLoc.t;
  large_ptr_set_val         : PowLoc.t;
  large_ptr_set_val_widen   : PowLoc.t;
  large_array_set           : PowLoc.t;
  large_array_set_val       : PowLoc.t;
  large_array_set_val_widen : PowLoc.t;
  large_array_set_val_field : PowLoc.t;
  unstable                  : PowLoc.t;
  (* static semantic features *)
  precise_pre               : PowLoc.t;
  (* syntactic features *)
  temp_var                  : PowLoc.t;
  (* not a feature *)
  non_bot                       : PowLoc.t;
}

let empty_feature = {
(*   progress_time = 0.0; *)
  progress_alarm = 0.0;
  delta_alarm = 0.0;
  fi_var = 0.0;
  (* features *)
  alarm                     = PowLoc.empty;
  alarm_fi                  = PowLoc.empty;
  indirect_alarm            = PowLoc.empty;
  eq_fi                     = PowLoc.empty;
  neg_itv                   = PowLoc.empty;
  right_open_itv            = PowLoc.empty;
  neg_offset                = PowLoc.empty;
  left_open_offset          = PowLoc.empty;
  right_open_offset         = PowLoc.empty;
  neg_size                  = PowLoc.empty;
  zero_size                 = PowLoc.empty;
  large_ptr_set             = PowLoc.empty;
  large_ptr_set_val         = PowLoc.empty;
  large_ptr_set_val_widen   = PowLoc.empty;
  large_array_set           = PowLoc.empty;
  large_array_set_val       = PowLoc.empty;
  large_array_set_val_widen = PowLoc.empty;
  large_array_set_val_field = PowLoc.empty;
  unstable                  = PowLoc.empty;
  (* static semantic *)
  precise_pre               = PowLoc.empty;
  (* syntacitc *)
  temp_var                  = PowLoc.empty;
  non_bot                       = PowLoc.empty;
}

let print_feature feat =
(*   "\nprogress_time  : " ^ string_of_float feat.progress_time ^ "\n" *)
  "progress_alarm : " ^ string_of_float feat.progress_alarm ^ "\n"
  ^ "delta_alarm    : " ^ string_of_float feat.delta_alarm ^ "\n"
  ^ "fi_variable    : " ^ string_of_float feat.fi_var ^ "\n"
  |> prerr_endline

let b2s = function true -> "1.0" | false -> "0.0"
let b2f = function true -> 1.0 | false -> 0.0

let feature_vector : Loc.t -> feature -> Pfs.feature -> float list
= fun x feat static_feature -> 
  let raw = [b2f (PowLoc.mem x feat.alarm);
   b2f (PowLoc.mem x feat.alarm_fi);
   b2f (PowLoc.mem x feat.indirect_alarm);
   b2f (PowLoc.mem x feat.eq_fi);
   b2f (PowLoc.mem x feat.neg_itv);
   b2f (PowLoc.mem x feat.right_open_itv);
   b2f (PowLoc.mem x feat.neg_offset);
   b2f (PowLoc.mem x feat.left_open_offset);
   b2f (PowLoc.mem x feat.right_open_offset);
   b2f (PowLoc.mem x feat.neg_size);  (* 10 *)
   b2f (PowLoc.mem x feat.zero_size);
   b2f (PowLoc.mem x feat.large_ptr_set);
   b2f (PowLoc.mem x feat.large_ptr_set_val);
   b2f (PowLoc.mem x feat.large_ptr_set_val_widen);
   b2f (PowLoc.mem x feat.large_array_set);
   b2f (PowLoc.mem x feat.large_array_set_val);
   b2f (PowLoc.mem x feat.large_array_set_val_widen);
   b2f (PowLoc.mem x feat.large_array_set_val_field);
   b2f (PowLoc.mem x feat.unstable);
   b2f (PowLoc.mem x feat.precise_pre); (* 20 *)
   b2f (PowLoc.mem x static_feature.Pfs.gvars);
   b2f (PowLoc.mem x static_feature.Pfs.lvars);
   b2f (PowLoc.mem x static_feature.Pfs.lvars_in_G);
   b2f (PowLoc.mem x static_feature.Pfs.fields);
   b2f (PowLoc.mem x static_feature.Pfs.ptr_type);
   b2f (PowLoc.mem x static_feature.Pfs.allocsites);
   b2f (PowLoc.mem x static_feature.Pfs.static_array);
   b2f (PowLoc.mem x static_feature.Pfs.ext_allocsites);
   b2f (PowLoc.mem x static_feature.Pfs.single_defs);
   b2f (PowLoc.mem x static_feature.Pfs.assign_const); (* 30 *)
   b2f (PowLoc.mem x static_feature.Pfs.assign_sizeof);
   b2f (PowLoc.mem x static_feature.Pfs.prune_simple);
   b2f (PowLoc.mem x static_feature.Pfs.prune_by_const);
   b2f (PowLoc.mem x static_feature.Pfs.prune_by_var);
   b2f (PowLoc.mem x static_feature.Pfs.prune_by_not);
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_alloc);
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_alloc2);
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_alloc_clos);
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_realloc);
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_realloc2); (* 40 *)
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_realloc_clos);
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_buf);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_alloc);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_alloc2);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_alloc_clos);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_realloc);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_realloc2);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_realloc_clos);
   b2f (PowLoc.mem x static_feature.Pfs.inc_itself_by_one);
   b2f (PowLoc.mem x static_feature.Pfs.inc_itself_by_var); (* 50 *)
   b2f (PowLoc.mem x static_feature.Pfs.incptr_itself_by_one);
   b2f (PowLoc.mem x static_feature.Pfs.inc);
   b2f (PowLoc.mem x static_feature.Pfs.dec);
   b2f (PowLoc.mem x static_feature.Pfs.dec_itself);
   b2f (PowLoc.mem x static_feature.Pfs.dec_itself_by_const);
   b2f (PowLoc.mem x static_feature.Pfs.mul_itself_by_const);
   b2f (PowLoc.mem x static_feature.Pfs.mul_itself_by_var);
   b2f (PowLoc.mem x static_feature.Pfs.used_as_array_index);
   b2f (PowLoc.mem x static_feature.Pfs.used_as_array_buf);
   b2f (PowLoc.mem x static_feature.Pfs.mod_in_rec_fun); (* 60 *)
   b2f (PowLoc.mem x static_feature.Pfs.read_in_rec_fun);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_ext_fun);
   b2f (PowLoc.mem x static_feature.Pfs.mod_inside_loops);
   b2f (PowLoc.mem x static_feature.Pfs.used_inside_loops); (* 64 *)
   ]
  in
  raw
(*  (List.map (fun x -> feat.progress_time *. x) raw)*)
(*  @ (List.map (fun x -> feat.progress_alarm *. x) raw) 
  @ (List.map (fun x -> feat.delta_alarm *. x) raw) 
  @ (List.map (fun x -> feat.fi_var *. x) raw) *)
(*  feat.progress_time :: feat.progress_alarm :: feat.delta_alarm :: feat.fi_var :: raw*)

let string_of_raw_feature x feat static_feature =
  List.fold_left (fun s f -> s ^ " " ^ string_of_float f) 
    (Loc.to_string x ^ " : ") (feature_vector x feat static_feature)

module Hashtbl = BatHashtbl.Make(Loc)
let premem_hash = Hashtbl.create 10000
let locset_hash = Hashtbl.create 10000  (* locset \ bot-locs *)

let initialize_cache locset premem =
  PowLoc.iter (fun k -> Hashtbl.add locset_hash k k) locset;
  Mem.iter (Hashtbl.add premem_hash) premem

let precise v = 
  let (itv,ptr,arr,proc) = (Val.itv_of_val v, Val.pow_loc_of_val v |> PowLoc.remove Loc.null, Val.array_of_val v, Val.pow_proc_of_val v) in
  (Itv.is_bot itv || Itv.is_finite itv) 
  && (PowLoc.cardinal ptr <= 1)
  && (ArrayBlk.is_empty arr || ((arr|> ArrayBlk.offsetof |> Itv.is_finite) && (arr |> ArrayBlk.sizeof |> Itv.is_finite)))
  && (PowProc.cardinal proc <= 1)
  
let precise_locs premem = 
  Mem.fold (fun k v -> 
    if precise v then PowLoc.add k 
    else id) premem PowLoc.empty

let add_precise_pre premem feat = 
  { feat with precise_pre = 
    Mem.fold (fun k v -> 
      if precise v then PowLoc.add k 
          else id) premem feat.precise_pre }

let add_neg_itv k v feat = 
  if (Val.itv_of_val v |> Itv.meet Itv.neg) <> Itv.bot then 
    { feat with neg_itv = PowLoc.add k feat.neg_itv }
  else feat

let add_right_open_itv k v feat = 
  if Val.itv_of_val v |> Itv.open_right then 
    { feat with right_open_itv = PowLoc.add k feat.right_open_itv }
  else feat

let neg_size_cache = Hashtbl.create 1000
let add_neg_size k v feat = 
  if Hashtbl.mem neg_size_cache k then feat
  else if (Val.array_of_val v |> ArrayBlk.sizeof |> Itv.meet Itv.neg) <> Itv.bot then 
    let _ = Hashtbl.add neg_size_cache k k in
    { feat with neg_size = PowLoc.add k feat.neg_size }
  else feat

let neg_offset_cache = Hashtbl.create 1000
let add_neg_offset k v feat = 
  if Hashtbl.mem neg_offset_cache k then feat
  else if (Val.array_of_val v |> ArrayBlk.offsetof |> Itv.meet Itv.neg) <> Itv.bot then 
    let _ = Hashtbl.add neg_offset_cache k k in
    { feat with neg_offset = PowLoc.add k feat.neg_offset }
  else feat

let left_open_offset_cache = Hashtbl.create 1000
let add_left_open_offset k v feat = 
  if Hashtbl.mem left_open_offset_cache k then feat
  else if Val.array_of_val v |> ArrayBlk.offsetof |> Itv.open_left then 
    let _ = Hashtbl.add left_open_offset_cache k k in
    { feat with left_open_offset = PowLoc.add k feat.left_open_offset }
  else feat

let left_right_offset_cache = Hashtbl.create 1000
let add_right_open_offset k v feat = 
  if Hashtbl.mem left_right_offset_cache k then feat
  else if Val.array_of_val v |> ArrayBlk.offsetof |> Itv.open_right then 
    let _ = Hashtbl.add left_right_offset_cache k k in
    { feat with right_open_offset = PowLoc.add k feat.right_open_offset }
  else feat

let zero_size_cache = Hashtbl.create 1000
let add_zero_size k v feat = 
  if Hashtbl.mem zero_size_cache k then feat
  else if (Val.array_of_val v |> ArrayBlk.sizeof |> Itv.meet Itv.zero) <> Itv.bot then 
    let _ = Hashtbl.add zero_size_cache k k in
    { feat with zero_size = PowLoc.add k feat.zero_size }
  else feat

let add_large_ptr_set k v feat = 
  if (Val.pow_loc_of_val v |> PowLoc.cardinal >= 3) 
    || (Val.pow_proc_of_val v |> PowProc.cardinal >= 3) then
    { feat with large_ptr_set = PowLoc.add k feat.large_ptr_set } 
  else feat

let add_large_ptr_set_val k v feat = 
  if (Val.pow_loc_of_val v |> PowLoc.cardinal >= 3) then
    { feat with large_ptr_set_val = PowLoc.join (Val.pow_loc_of_val v) (feat.large_ptr_set_val) }
  else feat

let large_ptr_set_val_widen_cache = Hashtbl.create 1000
let add_large_ptr_set_val_widen k v feat =
  if Hashtbl.mem large_ptr_set_val_widen_cache k then feat
  else if (Val.pow_loc_of_val v |> PowLoc.cardinal >= 3) then
    let _ = Hashtbl.add large_ptr_set_val_widen_cache k k in
    { feat with large_ptr_set_val_widen = PowLoc.join (Hashtbl.find premem_hash k |> Val.pow_loc_of_val) (feat.large_ptr_set_val_widen) }
  else feat

let large_array_set_cache = Hashtbl.create 1000
let add_large_array_set k v feat = 
  if Hashtbl.mem large_array_set_cache k then feat
  else if (Val.array_of_val v |> ArrayBlk.cardinal >= 3) then
    let _ = Hashtbl.add large_array_set_cache k k in
    { feat with large_array_set = PowLoc.add k feat.large_array_set } 
  else feat
 
let large_array_set_val_cache = Hashtbl.create 1000
let add_large_array_set_val k v feat = 
  if Hashtbl.mem large_array_set_val_cache k && Random.bool () then feat
  else if (Val.array_of_val v |> ArrayBlk.cardinal >= 3) then
    let _ = Hashtbl.replace large_array_set_val_cache k k in
    { feat with large_array_set_val = PowLoc.join (Val.array_of_val v |> ArrayBlk.pow_loc_of_array) feat.large_array_set_val } 
  else feat
 
let large_array_set_val_widen_cache = Hashtbl.create 1000
let add_large_array_set_val_widen k v feat = 
  if Hashtbl.mem large_array_set_val_widen_cache k then feat
  else if (Val.array_of_val v |> ArrayBlk.cardinal >= 3) then
    let _ = Hashtbl.add large_array_set_val_widen_cache k k in
    { feat with large_array_set_val_widen = PowLoc.join (Hashtbl.find premem_hash k |> Val.array_of_val |> ArrayBlk.pow_loc_of_array) feat.large_array_set_val_widen } 
  else feat

let add_large_array_set_val_field feat = 
  { feat with 
      large_array_set_val_field = 
        Hashtbl.fold (fun k _ -> match k with Loc.Field (l, _, _) 
            when (PowLoc.mem l feat.large_array_set_val_widen)
              || not (Hashtbl.mem locset_hash l)  -> PowLoc.add k | _ -> id) 
          premem_hash feat.large_array_set_val_field }

let unstable v1 v2 = not (Val.le v2 v1) 
let add_unstable k old_v new_v feat = 
  if unstable old_v new_v then 
    { feat with unstable = PowLoc.add k feat.unstable }
  else feat

let soft_eq v1 v2 = 
  (Itv.eq (Val.itv_of_val v1) (Val.itv_of_val v2)) 
  && (Val.pow_loc_of_val v1 |> PowLoc.cardinal) = (Val.pow_loc_of_val v2 |> PowLoc.cardinal)
  && (Val.array_of_val v1 |> ArrayBlk.offsetof) = (Val.array_of_val v2 |> ArrayBlk.offsetof)
  && (Val.array_of_val v1 |> ArrayBlk.sizeof) = (Val.array_of_val v2 |> ArrayBlk.sizeof)
  && (Val.array_of_val v1 |> ArrayBlk.nullof) = (Val.array_of_val v2 |> ArrayBlk.nullof)
  && (Val.struct_of_val v1 |> StructBlk.cardinal) = (Val.struct_of_val v2 |> StructBlk.cardinal)
  && (Val.pow_proc_of_val v1 |> PowProc.cardinal) = (Val.pow_proc_of_val v2 |> PowProc.cardinal)

let eq_cache = Hashtbl.create 1000
let add_eq_fi k v feat = 
  if Hashtbl.mem eq_cache k then feat
  else if soft_eq v (Hashtbl.find premem_hash k) then 
    let _ = Hashtbl.add eq_cache k k in
    { feat with eq_fi = PowLoc.add k feat.eq_fi }
  else feat

let add_temp_var k v feat = 
  if (Val.itv_of_val v |> Itv.meet Itv.neg) <> Itv.bot then 
    { feat with neg_itv = PowLoc.add k feat.neg_itv }
  else feat

let add_not_bot k feat = { feat with non_bot = PowLoc.add k feat.non_bot }

let extract spec global elapsed_time alarms new_alarms old_inputof inputof old_feature = 
(*  let t0 = Sys.time () in*)
  let total_alarms = spec.Spec.pre_alarm |> flip Report.get Report.UnProven |> Report.partition in
  let num_of_total_alarms = BatMap.cardinal total_alarms in
  let current_alarm = BatMap.cardinal alarms in
  let new_alarm = BatMap.cardinal new_alarms in
  { old_feature with
    (*!timer.dynamic_feature with *)
(*     progress_time = Pervasives.min 1.0 (elapsed_time /. (float_of_int !Options.timer_deadline));  *)
    progress_alarm = (float_of_int current_alarm) /. (float_of_int num_of_total_alarms); 
    delta_alarm = (float_of_int new_alarm) /. (float_of_int num_of_total_alarms); 
(*    fi_var = (Hashtbl.length locset_fi_hash |> float_of_int) /. (spec.Spec.locset |> PowLoc.cardinal |> float_of_int)*) }
(*  |> (fun x -> prerr_endline ("\n-- until time feature " ^ string_of_float (Sys.time () -. t0)); x)*)
  |> BatMap.foldi (fun part ql feat -> 
      let alarm_locs = 
        List.fold_left (fun alarm_locs q ->
          let mem = Table.find q.node inputof in
          match q.allocsite with
            Some a when q.status = UnProven -> 
              let locs_of_query = PowLoc.add (Loc.of_allocsite a) (Dependency.locs_of_alarm_exp q mem) in
              PowLoc.join locs_of_query alarm_locs
        | _ -> alarm_locs) PowLoc.empty ql
      in
      let indirect = 
        List.fold_left (fun indirect q ->
            match q.allocsite with 
              Some a when q.status = UnProven -> 
                let locs_of_query = PowLoc.add (Loc.of_allocsite a) (Dependency.locs_of_alarm_exp q spec.Spec.premem) in
                PowLoc.join locs_of_query indirect
            | _ -> indirect) PowLoc.empty (try BatMap.find part total_alarms with _ -> [])
      in
      { feat with alarm = alarm_locs; indirect_alarm = indirect }
     ) new_alarms
(*  |> (fun x -> prerr_endline ("\n-- until alarm features " ^ string_of_float (Sys.time () -. t0)); x)*)
  |> Table.fold (fun node new_mem feat ->
      if (InterCfg.is_entry node) || (InterCfg.is_exit node)
        || (InterCfg.is_callnode node global.icfg) || (InterCfg.is_returnnode node global.icfg)
      then 
        let old_mem = Table.find node old_inputof in
        Mem.fold (fun k v feat ->
(*            if Hashtbl.mem locset_hash k then*)
              feat
              |> (add_neg_itv k v)
              |> (add_neg_size k v)
              |> (add_neg_offset k v)
              |> (add_right_open_offset k v )
              |> (add_zero_size k v)
              |> (add_right_open_itv k v)
              |> (add_large_ptr_set k v)
              |> (add_large_ptr_set_val k v)
              |> (add_large_ptr_set_val_widen k v)
              |> (add_large_array_set k v)
              |> (add_large_array_set_val k v)
              |> (add_large_array_set_val_widen k v)
              |> (add_left_open_offset k v)
              |> (add_unstable k (Mem.find k old_mem) v )
              |> (add_eq_fi k v)
              |> (add_not_bot k)
(*            else feat*)
          ) new_mem feat
      else feat) inputof
  |> add_large_array_set_val_field
(*  |> (fun x -> prerr_endline ("\n-- until semantic features " ^ string_of_float (Sys.time () -. t0)); x)*)
