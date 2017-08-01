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
type coarsening = Dug | Worklist

let strategy = Rank
let coarsening = Dug

module Hashtbl = BatHashtbl.Make(Loc)
let premem_hash = Hashtbl.create 10000
(* locset \ bot-locs *)
let locset_hash = Hashtbl.create 10000
(*let locset_fi_hash = Hashtbl.create 10000*)
(* 24 features *)
type feature = {
  progress_time  : float;
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
}

let empty_feature = {
  progress_time = 0.0;
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
}

let print_feature feat =
  "\nprogress_time  : " ^ string_of_float feat.progress_time ^ "\n"
  ^ "progress_alarm : " ^ string_of_float feat.progress_alarm ^ "\n"
  ^ "delta_alarm    : " ^ string_of_float feat.delta_alarm ^ "\n"
  ^ "fi_variable    : " ^ string_of_float feat.fi_var ^ "\n"
  |> prerr_endline

type t = {
  threshold : int;
  time_stamp : int;
  old_inputof : Table.t;
  static_feature : PartialFlowSensitivity.feature;
  dynamic_feature : feature;
  alarm_history : (int, Report.query list) BatMap.t;
}

let empty = {
  threshold = 0;
  time_stamp = 1;
  old_inputof = Table.empty;
  static_feature = PartialFlowSensitivity.empty_feature;
  dynamic_feature = empty_feature;
  alarm_history = BatMap.empty;
}

let timer = ref empty

module Pfs = PartialFlowSensitivity

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
            when (PowLoc.mem l feat.large_array_set_val_widen) || not (Hashtbl.mem locset_hash l)  -> PowLoc.add k | _ -> id) 
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

let prdbg_endline x = 
  if !Options.timer_debug then
    prerr_endline ("DEBUG::"^x)
  else ()

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

let extract_feature spec elapsed_time alarms new_alarms inputof = 
(*  let t0 = Sys.time () in*)
  let total_alarms = spec.Spec.pre_alarm |> flip Report.get Report.UnProven |> Report.partition in
  let num_of_total_alarms = BatMap.cardinal total_alarms in
  let current_alarm = BatMap.cardinal alarms in
  let new_alarm = BatMap.cardinal new_alarms in
  { !timer.dynamic_feature with 
    progress_time = Pervasives.min 1.0 (elapsed_time /. (float_of_int !Options.timer_deadline)); 
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
              let locs_of_query = PowLoc.add (Loc.of_allocsite a) (locs_of_alarm_exp q mem) in
              PowLoc.join locs_of_query alarm_locs
        | _ -> alarm_locs) PowLoc.empty ql
      in
      let indirect = 
        List.fold_left (fun indirect q ->
            match q.allocsite with 
              Some a when q.status = UnProven -> 
                let locs_of_query = PowLoc.add (Loc.of_allocsite a) (locs_of_alarm_exp q spec.Spec.premem) in
                PowLoc.join locs_of_query indirect
            | _ -> indirect) PowLoc.empty (try BatMap.find part total_alarms with _ -> [])
      in
      { feat with alarm = alarm_locs; indirect_alarm = indirect }
     ) new_alarms
(*  |> (fun x -> prerr_endline ("\n-- until alarm features " ^ string_of_float (Sys.time () -. t0)); x)*)
  |> Table.fold (fun node new_mem feat ->
      if (InterCfg.is_entry node) || (InterCfg.is_exit node) then 
        let old_mem = Table.find node !timer.old_inputof in
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
(*            else feat*)
          ) new_mem feat
      else feat) inputof
  |> add_large_array_set_val_field
(*  |> (fun x -> prerr_endline ("\n-- until semantic features " ^ string_of_float (Sys.time () -. t0)); x)*)

let extreme_strategy locset_fs = locset_fs
let random_strategy locset_fs = 
  BatSet.fold (fun x -> if Random.bool () then BatSet.add x else id) locset_fs BatSet.empty

let load_classifier global = 
(*  let filename = Filename.basename global.file.Cil.fileName in*)
  let path = "/home/khheo/project/TimerExperiment/" in
  let py = Lymp.init ~exec:"python2" path in
  let py_module = Lymp.get_module py "sparrow" in
  let classifier = Lymp.Pyref (Lymp.get_ref py_module "load" [Lymp.Pystr !Options.timer_clf]) in
  (py_module, classifier)

let predict py_module clf x feature static_feature = 
  let vec = feature_vector x feature static_feature in
(*  prerr_string (Loc.to_string x);
  List.iter (fun x -> prerr_float x; prerr_string ", ") vec;*)
  let vec = Lymp.Pylist (List.map (fun x -> Lymp.Pyfloat x) vec) in
  let b = Lymp.get_bool py_module "predict_one" [clf; vec] in
(*  prerr_endline (" : " ^ string_of_bool b);*)
  b
 
let predict_proba py_module clf x feature static_feature = 
  let vec = feature_vector x feature static_feature in
(*  prerr_string (Loc.to_string x);
  List.iter (fun x -> prerr_float x; prerr_string ", ") vec;*)
  let vec = Lymp.Pylist (List.map (fun x -> Lymp.Pyfloat x) vec) in
  let b = Lymp.get_float py_module "predict_proba" [clf; vec] in
(*  prerr_endline (" : " ^ string_of_bool b);*)
  b

let clf_strategy global feature static_feature = 
  let (py_module, clf) = load_classifier global in 
  Hashtbl.fold (fun k _ -> 
      if predict py_module clf k feature static_feature then PowLoc.add k
      else id) locset_hash PowLoc.empty 
(* TODO *)
let threshold_list = 
  match coarsening with 
  | Dug -> [0; 10; 50; 80; 100; 110; 120; 130]
  | Worklist -> [0; 10; 30; 60; 100; 110; 120; 130]
let rec threshold i = 
  !Options.timer_deadline * (try List.nth threshold_list i with _ -> 10000000) / 100

let threshold_list_loc = [0; 10; 50; 80; 100]

let rank_strategy global spec feature static_feature = 
  let num_locset = PowLoc.cardinal spec.Spec.locset in
  let top = 
    match coarsening with 
    | Dug -> 
        (try List.nth threshold_list_loc !timer.time_stamp with _ -> 100) * num_locset / 100
          - (try List.nth threshold_list_loc (!timer.time_stamp -1) with _ -> 100) * num_locset / 100
    | Worklist -> 
        (try List.nth threshold_list !timer.time_stamp with _ -> 100) * num_locset / 100 
  in
  let ranking =
    if !Options.timer_oracle_rank then
      let filename = Filename.basename global.file.Cil.fileName in
      let oracle = try MarshalManager.input ~dir:!Options.timer_dir (filename^".oracle") with _ -> prerr_endline "Can't find the oracle"; BatMap.empty in
(*      BatMap.iter (fun (idx, k) b ->
        prerr_endline ("("^string_of_int idx ^", "^k^") -> "^string_of_float b)) oracle;
*)      Hashtbl.fold (fun k _ l ->
        let score = 
          (try BatMap.find (!timer.threshold, Loc.to_string k) oracle with _ -> 2.0)
        in
        (k, score)::l) locset_hash []
      |> List.sort (fun (_, x) (_, y) -> if x > y then -1 else if x = y then 0 else 1)
    else if !Options.timer_static_rank then
      let locset = Hashtbl.fold (fun k _ l -> k::l) locset_hash [] in
      let weights = Str.split (Str.regexp "[ \t]+") (!Options.pfs_wv) in
      PartialFlowSensitivity.assign_weight locset static_feature weights
      |> List.sort (fun (_, x) (_, y) -> if x < y then -1 else if x = y then 0 else 1)
    else
      let (py_module, clf) = load_classifier global in 
      Hashtbl.fold (fun k _ l -> 
          (k, predict_proba py_module clf k feature static_feature)::l) locset_hash []
      |> List.sort (fun (_, x) (_, y) -> if x > y then -1 else if x = y then 0 else 1)
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

(*
let my_strategy global feature static_feature = 
  let (py_module, clf) = load_classifier global in 
  prerr_endline "== Predict ==";
  let (locs, features) = Hashtbl.fold (fun k _ (locs, features) -> 
      (k::locs, (Lymp.Pylist (feature_vector k feature static_feature |> List.map (fun x -> Lymp.Pyfloat x)))::features))
    locset_hash ([], [])
  in
  let results = Lymp.get_list py_module "predict" [clf; Lymp.Pylist features] in
  List.fold_left2 (fun locs loc result -> 
      match result with Lymp.Pybool true -> PowLoc.add loc locs | _ -> locs) PowLoc.empty locs results
*)

let last_time = ref 0.0
let last_coverage = ref 0
let last_alarm = ref 0
let remaining = ref 0.0
let widen_start = ref 0.0
let num_of_coarsen = ref 0
let limit_of_coarsen = 10
let coarsening_level = ref 0

type mode = NoCoarsen | Finish | Coarsen

let trigger_old : Spec.t -> DUGraph.t -> Worklist.t -> mode
= fun spec dug worklist ->
  if !widen_start = 0.0 then (widen_start := Sys.time (); NoCoarsen)
  else if (Sys.time () -. !widen_start) > 
          ((float_of_int !Options.timer_deadline) -. !widen_start) 
          *. (float_of_int !num_of_coarsen) /. (float_of_int limit_of_coarsen) then 
  begin
    if !num_of_coarsen = limit_of_coarsen then Finish
    else (num_of_coarsen := !num_of_coarsen + 1; Coarsen)
  end
  else NoCoarsen

let trigger : float -> float list -> Spec.t -> DUGraph.t -> Worklist.t -> mode
= fun elapsed trigger_list spec dug worklist ->
  if !widen_start = 0.0 then (widen_start := Sys.time (); NoCoarsen)
  else if elapsed > (List.nth trigger_list !num_of_coarsen) then
    if !num_of_coarsen = (List.length trigger_list) - 1 then Finish
    else 
      let _ = num_of_coarsen := !num_of_coarsen + 1 in
      Coarsen
  else NoCoarsen
let compare_query a b = 
  if Pervasives.compare a.loc.file b.loc.file = 0 then 
    if Pervasives.compare a.loc.line b.loc.line = 0 then 
      Pervasives.compare (AlarmExp.to_string a.exp) (AlarmExp.to_string b.exp)
    else Pervasives.compare a.loc.line b.loc.line
  else Pervasives.compare a.loc.file b.loc.file


module AlarmSet = BatSet.Make(struct type t = Report.query let compare = compare_query end)

let old_alarms = ref AlarmSet.empty

let get_new_alarms alarms = 
  let new_alarms = List.filter (fun q -> not (AlarmSet.mem q !old_alarms)) alarms in
  List.iter (fun q ->
      old_alarms := AlarmSet.add q !old_alarms; ()) new_alarms;
  new_alarms

let diff_alarms alarms1 alarms2 = 
  let alarms2_set = List.fold_left (fun set q -> AlarmSet.add q set) AlarmSet.empty alarms2 in
  List.filter (fun q -> not (AlarmSet.mem q alarms2_set)) alarms1

let timer_dump global dug inputof feature new_alarms time = 
  let filename = Filename.basename global.file.Cil.fileName in
  let surfix = string_of_int (!Options.timer_unit) ^ "." 
             ^ string_of_int (!Options.timer_alpha) ^ "." 
             ^ string_of_int (!Options.timer_deadline) ^ "."
             ^ string_of_int time
  in
  let dir = !Options.timer_dir in
  MarshalManager.output ~dir (filename ^ ".feature." ^ surfix) feature;
  MarshalManager.output ~dir (filename ^ ".inputof." ^ surfix) inputof;
  MarshalManager.output ~dir (filename ^ ".dug." ^ surfix) dug;
  MarshalManager.output ~dir (filename ^ ".alarm." ^ surfix) new_alarms

let initialize spec global dug = 
  widen_start := Sys.time ();
(*  let inputof = Table.bot in*)
  Mem.iter (fun k v -> Hashtbl.add premem_hash k v) spec.Spec.premem;
(*  prerr_endline "Pre mem";*)
(*  prerr_endline (Mem.to_string spec.Spec.premem);*)
(*  Mem.iter (fun k v ->
      prerr_endline ((Loc.to_string k) ^ " -> " ^ (Val.to_string v))) spec.Spec.premem;*)
(*  let alarms = (BatOption.get spec.Spec.inspect_alarm) global spec inputof |> flip Report.get Report.UnProven in
  let new_alarms = get_new_alarms alarms in*)
(*  let alarms_part = Report.partition alarms in*)
(*  let new_alarms_part = Report.partition new_alarms in*)
(*  let dynamic_feature1 = add_precise_pre spec.Spec.premem empty_feature in
  let dynamic_feature2 = extract_feature spec 0.0 alarms_part new_alarms_part inputof in
  let dynamic_feature = { dynamic_feature2 with precise_pre = dynamic_feature1.precise_pre } in*)
  timer := { 
    !timer with threshold = threshold !timer.time_stamp; (*!Options.timer_unit;*) 
    static_feature = PartialFlowSensitivity.extract_feature global spec.Spec.locset_fs;
(*    dynamic_feature;*)
  };
  let filename = Filename.basename global.file.Cil.fileName in
  let dir = !Options.timer_dir in
  MarshalManager.output ~dir (filename ^ ".static_feature") !timer.static_feature;
  PowLoc.iter (fun k -> (*if Hashtbl.mem premem_hash k then*) Hashtbl.add locset_hash k k) spec.Spec.locset_fs
(*  (if !Options.timer_dump then timer_dump global inputof dynamic_feature [] 0);*)
(*  SparseAnalysis.nb_nodes := DUGraph.nb_node dug;*)


(*  static_rank := PartialFlowSensitivity.rank global spec.Spec.locset_fs*)

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
              (try Hashtbl.find premem_hash l with _ -> Val.bot)
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
    Hashtbl.filteri_inplace (fun k _ -> not (PowLoc.mem k locset_coarsen)) locset_hash;
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
          (try Hashtbl.find premem_hash l with _ -> Val.bot)
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

let target_edge icfg (src, _, dst) =
  (InterCfg.cmdof icfg src <> IntraCfg.Cmd.Cskip)
  || not (InterCfg.is_callnode src icfg) || not (InterCfg.is_callnode dst icfg)
  || not (InterCfg.is_returnnode src icfg) || not (InterCfg.is_returnnode dst icfg)
  || not (InterCfg.is_entry src) || not (InterCfg.is_entry dst)
  || not (InterCfg.is_exit src) || not (InterCfg.is_exit dst)

let intra_edge icfg src dst =
  not ((InterCfg.is_callnode src icfg) && (InterCfg.is_entry dst))
  || not ((InterCfg.is_exit src) && (InterCfg.is_returnnode dst icfg))

let dependency_of_query global dug access q mem degree =
  let rec loop degree works visited results = 
(*    if degree < 1 then results
    else*)
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
        |> (fun works -> loop (degree - 1) works visited results)
  in
  loop degree [(q.node, locs_of_alarm_exp q mem)] PowNode.bot PowLoc.bot

let dependency_of_query_set global dug access qset feature static_feature inputof_prev inputof_idx degree = 
  AlarmSet.fold (fun q ->
    let mem_idx = Table.find q.node inputof_idx in
    let mem_prev = Table.find q.node inputof_prev in
    let set = dependency_of_query global dug access q mem_prev degree in
    (if !Options.timer_debug then
    let _ = prdbg_endline ("query: "^(Report.string_of_query q)) in
    prdbg_endline ("node: "^(Node.to_string q.node));
    prdbg_endline ("cmd: "^(InterCfg.cmdof global.icfg q.node |> IntraCfg.Cmd.to_string));
(*    let _ = prdbg_endline ("idx mem: "^(Mem.to_string mem_idx)) in
    let _ = prdbg_endline ("prev mem: "^(Mem.to_string mem_prev)) in
*)    let _ = prdbg_endline ("dep: "^(PowLoc.to_string set)) in
    PowLoc.iter (fun x -> 
      (if Mem.mem x mem_prev (*&& Random.int 10 = 0*) then
       begin
         prdbg_endline ("feat: "^(string_of_raw_feature x feature static_feature));
         prdbg_endline ("FS val : "^(Val.to_string (Mem.find x mem_prev)));
         prdbg_endline ("FI val : "^(try Val.to_string (Mem.find x global.mem) with _ -> "Notfound"))
       end)) set
      else ());
    set
(*    PowLoc.filter (fun x -> Mem.mem x mem_prev) set*)
    |> PowLoc.join) qset PowLoc.bot

module Data = Set.Make(Loc)

let extract_data_normal spec global access oc filename surfix lst alarm_fs alarm_fi alarms_list static_feature =
  output_string oc ("# Iteration\n");
  let dir = !Options.timer_dir in
  List.fold_left (fun (pos_data, neg_data) i ->
    try 
      let idx = threshold i in
      let prev = threshold (i-1) in
      let next = threshold (i+1) in
      let alarm_idx = MarshalManager.input ~dir (filename ^ ".alarm."^ surfix ^ "." ^ string_of_int idx) |> AlarmSet.of_list in
      let alarm_prev = MarshalManager.input ~dir (filename ^ ".alarm."^ surfix ^ "." ^ string_of_int prev) |> AlarmSet.of_list in
      let alarm_next = try MarshalManager.input ~dir (filename ^ ".alarm."^ surfix ^ "." ^ string_of_int next) |> AlarmSet.of_list with _ -> AlarmSet.empty in
      let inputof_prev = MarshalManager.input ~dir (filename ^ ".inputof." ^ surfix ^ "." ^ string_of_int prev) in
      let inputof_idx = MarshalManager.input ~dir (filename ^ ".inputof." ^ surfix ^ "." ^ string_of_int idx) in
      let dug = MarshalManager.input ~dir (filename ^ ".dug." ^ surfix ^ "." ^ string_of_int prev) in
      let feature_prev = MarshalManager.input ~dir (filename ^ ".feature."^ surfix ^ "." ^ string_of_int prev) in
      if next <= !Options.timer_deadline then
        let _ = output_string oc ("# Idx : " ^(string_of_int idx) ^ "\n") in
        output_string oc ("# Update w to raise alarms in A_{i} - bar{A} at i + 1. "^(string_of_int next)^" -> " ^ (string_of_int prev)^"\n");
        (* locs not related to FI-alarms *)
        prdbg_endline ("extract type 1 data of Idx " ^ string_of_int idx);
        let locs_of_fi_alarms = dependency_of_query_set global dug access alarm_fi feature_prev static_feature inputof_prev inputof_idx 1 in
        let pos_locs = PowLoc.diff spec.Spec.locset locs_of_fi_alarms in
        prerr_endline "type 1 data";
        prerr_endline (PowLoc.to_string pos_locs);
        PowLoc.iter (fun x ->
          output_string oc (string_of_raw_feature x feature_prev static_feature^ " : 1\n")) pos_locs;
        (* 2. Update w to coarsen variables that are related to the FS alarms earlier *)
        prdbg_endline ("extract type 2 data of Idx " ^ string_of_int idx);
        output_string oc ("# Update w to coarsen variables that are related to the FS alarms earlier."^(string_of_int next)^" -> " ^ (string_of_int prev)^"\n");
        let inter = AlarmSet.inter alarm_fs (AlarmSet.diff alarm_next alarm_idx) in
        (* locs related to FS-alarms *)
        let locs_of_fs_alarms = dependency_of_query_set global dug access inter feature_prev static_feature inputof_prev inputof_idx 1 in
        let pos_locs = PowLoc.join pos_locs locs_of_fs_alarms in
        PowLoc.iter (fun x ->
          output_string oc (string_of_raw_feature x feature_prev static_feature^ " : 1\n")) pos_locs;
        (* 3. Update w to coarsen variable *)
        output_string oc ("# push back "^(string_of_int idx)^" -> " ^ (string_of_int next)^"\n");
        output_string oc ("# number of alarm prev: "^(string_of_int (AlarmSet.cardinal alarm_prev))^"\n");
        output_string oc ("# number of alarm idx: "^(string_of_int (AlarmSet.cardinal alarm_idx))^"\n");
        prdbg_endline ("extract type 3 data of Idx " ^ string_of_int idx);
        let diff = AlarmSet.diff (AlarmSet.diff alarm_idx alarm_prev) alarm_fs in
        let locs_of_alarms = dependency_of_query_set global dug access diff feature_prev static_feature inputof_prev inputof_idx  1 in
        let neg_locs = locs_of_alarms in
        PowLoc.iter (fun x ->
          output_string oc (string_of_raw_feature x feature_prev static_feature^ " : 0\n")) neg_locs;
        let conflict = PowLoc.inter pos_locs neg_locs in
        output_string oc ("# Summary at "^(string_of_int idx)^"\n");
        output_string oc ("# positive : "^(string_of_int (PowLoc.cardinal pos_locs))^"\n");
        output_string oc ("# negative : "^(string_of_int (PowLoc.cardinal neg_locs))^"\n");
        output_string oc ("# conflict : "^(string_of_int (PowLoc.cardinal conflict))^"\n");
        let pos_data = PowLoc.fold (fun x pos_data -> 
(*            if PowLoc.mem x conflict then pos_data
            else*) (i, x, feature_prev)::pos_data) pos_locs pos_data in
        let neg_data = PowLoc.fold (fun x neg_data -> 
(*            if PowLoc.mem x conflict then neg_data
            else*) (i, x, feature_prev)::neg_data) neg_locs neg_data in
        (pos_data, neg_data)
      else 
        (* 4. *)
        let _ = output_string oc "# pull. If t > deadline then Update w to raise alarm in A_{i} at i - 1\n" in
        output_string oc ("# "^(string_of_int next)^" -> " ^ (string_of_int idx)^"\n");
        prdbg_endline ("extract type 4 data");
        let inter = AlarmSet.diff alarm_next alarm_idx in
        let dep_locs = dependency_of_query_set global dug access inter feature_prev static_feature inputof_prev inputof_idx  1 in
        let pos_data = PowLoc.fold (fun x pos_data -> 
            output_string oc (string_of_raw_feature x feature_prev static_feature ^ " : 1\n");
            (i, x, feature_prev)::pos_data) dep_locs pos_data 
        in
        (pos_data, neg_data)
    with _ -> (pos_data, neg_data)
  ) ([], []) lst

let extract_data spec global access initial  = 
  let filename = Filename.basename global.file.Cil.fileName in
  let surfix = string_of_int (!Options.timer_unit) ^ "." 
             ^ string_of_int (!Options.timer_alpha) ^ "." 
             ^ string_of_int (!Options.timer_deadline)
  in
  let dir = !Options.timer_dir in
  let oc = open_out_gen [Open_creat; Open_append; Open_text] 0o640 (!Options.timer_dir ^ "/" ^ filename ^ ".tr_data." ^ surfix ^ ".dat.raw") in
  let alarm_fs = MarshalManager.input (filename ^ ".alarm") |> flip Report.get Report.UnProven |> AlarmSet.of_list in
  let alarm_fi = spec.Spec.pre_alarm |> flip Report.get Report.UnProven |> AlarmSet.of_list in
  let alarms_list = List.fold_left (fun l i -> 
                    try 
                      let a = MarshalManager.input ~dir (filename ^ ".alarm."^ surfix ^ "." ^ (string_of_int (threshold i))) |> AlarmSet.of_list in
                      a::l
                    with _ -> l) [] (BatList.range 1 `To 6)
  in
  let alarm_final = List.hd alarms_list in
  let lst = BatList.range 1 `To 100 in
  let static_feature = MarshalManager.input ~dir (filename ^ ".static_feature") in
  let (pos_data, neg_data) = 
      extract_data_normal spec global access oc filename surfix lst alarm_fs alarm_fi alarms_list static_feature
  in
  close_out oc;
  let oc = open_out_gen [Open_creat; Open_append; Open_text] 0o640 (!Options.timer_dir ^ "/" ^ filename ^ ".tr_data." ^ surfix ^ ".dat") in
  output_string oc "# Iteration\n";
  List.iter (fun (_, x, feature) -> 
(*      if PowLoc.mem x conflict then () else *)
    output_string oc (string_of_raw_feature x feature static_feature ^ " : 1\n")) pos_data;
  List.iter (fun (_, x, feature) -> 
(*      if PowLoc.mem x conflict then () else *)
    output_string oc (string_of_raw_feature x feature static_feature ^ " : 0\n")) neg_data;
  let oracle = List.fold_left (fun oracle (idx, x, feature) -> 
    let prev = threshold (idx - 1) in
    BatMap.add (prev, Loc.to_string x) 1.0 oracle) BatMap.empty pos_data in
  let oracle = List.fold_left (fun oracle (idx, x, feature) -> 
    let prev = threshold (idx - 1) in
    BatMap.add (prev, Loc.to_string x) 0.0 oracle) oracle neg_data in
  close_out oc;
  MarshalManager.output ~dir (filename^".oracle") oracle;

  let score = List.fold_left (fun score i ->
      try
      let idx = threshold i in
      let prev = threshold (i-1) in
      let alarm_idx = MarshalManager.input ~dir (filename ^ ".alarm."^ surfix ^ "." ^ string_of_int idx) |> AlarmSet.of_list in
      let alarm_prev = if i-1 = 0 then AlarmSet.empty else MarshalManager.input ~dir (filename ^ ".alarm."^ surfix ^ "." ^ string_of_int prev) |> AlarmSet.of_list in
      let new_alarm = AlarmSet.diff alarm_idx alarm_prev in
      let inter = AlarmSet.inter alarm_fs new_alarm in
      if idx <= !Options.timer_deadline then 
        (* score 1: for FS-alarms (d - t) / d *)
        let score1 = ((float_of_int (!Options.timer_deadline - idx))
                  /. float_of_int !Options.timer_deadline)
                  *. (float_of_int (AlarmSet.cardinal inter))
                  /. (float_of_int (AlarmSet.cardinal alarm_final))
        in
        (* score 2: for non-FS-alarms t / d *)
        let score2 = (float_of_int idx)
                  /. (float_of_int !Options.timer_deadline)
                  *. float_of_int (AlarmSet.cardinal (AlarmSet.diff new_alarm inter))
                  /. (float_of_int (AlarmSet.cardinal alarm_final))
        in
        prerr_endline ("idx : " ^ string_of_int idx);
        prerr_endline ("# alarms in FS-alarm before deadline: " ^ string_of_int (AlarmSet.cardinal inter));
        prerr_endline ("# alarms not in FS-alarm before deadline: " ^ string_of_int (AlarmSet.cardinal (AlarmSet.diff new_alarm inter)));
        score +. score1 +. score2
      else 
      begin
        prerr_endline ("idx : " ^ string_of_int idx);
        prerr_endline ("# alarms in FS-alarm after deadline: " ^ string_of_int (AlarmSet.cardinal inter));
        prerr_endline ("# alarms not in FS-alarm after deadline: " ^ string_of_int (AlarmSet.cardinal (AlarmSet.diff new_alarm inter)));
        let discount = ((float_of_int (idx - !Options.timer_deadline))
                    /. float_of_int !Options.timer_deadline)
                    *. (float_of_int (AlarmSet.cardinal new_alarm))
                    /. (float_of_int (AlarmSet.cardinal alarm_final))
        in
        score -. discount
      end
      with _ -> score) 0.0 lst
  in 
  prerr_endline ("Score of proxy: " ^ string_of_float score);
  exit 0

let coarsening_fs : Spec.t -> Global.t -> Access.t -> DUGraph.t -> Worklist.t -> Table.t 
  -> Spec.t * DUGraph.t * Worklist.t * Table.t
= fun spec global access dug worklist inputof ->
  (if !widen_start = 0.0 then initialize spec global dug);   (* initialize *)
  let t0 = Sys.time () in
  let elapsed = t0 -. !widen_start in
  if elapsed > (float_of_int !timer.threshold) then
    let _ = prerr_endline ("\n== Timer: Coarsening #"^(string_of_int !timer.time_stamp)^" starts at " ^ (string_of_float elapsed)) in
    let num_of_locset_fs = PowLoc.cardinal spec.Spec.locset_fs in
    let num_of_locset = Hashtbl.length locset_hash in
    if num_of_locset_fs = 0 then 
      (spec, dug, worklist, inputof)
    else 
      let _ = Profiler.reset () in
      let alarms = (BatOption.get spec.Spec.inspect_alarm) global spec inputof |> flip Report.get Report.UnProven in
      let new_alarms = get_new_alarms alarms in
      let alarms_part = Report.partition alarms in
      let new_alarms_part = Report.partition new_alarms in
      let dynamic_feature = extract_feature spec elapsed alarms_part new_alarms_part inputof in
      (if !Options.timer_dump then timer_dump global dug inputof dynamic_feature alarms !timer.threshold); 
      prerr_endline ("\n== Timer: feature extraction took " ^ string_of_float (Sys.time () -. t0));
      let t1 = Sys.time () in
      (* fixted portion *)
      let locset_coarsen = 
        match strategy with
        | Rank -> rank_strategy global spec dynamic_feature !timer.static_feature
        | Clf -> clf_strategy global dynamic_feature !timer.static_feature
      in
      prerr_endline ("\n== Timer: Predict took " ^ string_of_float (Sys.time () -. t1));
      let num_of_works = Worklist.cardinal worklist in
      let t2 = Sys.time () in
      let (spec,dug,worklist,inputof) = 
        match coarsening with
        | Dug -> coarsening_dug global access locset_coarsen dug worklist inputof spec
        | Worklist -> 
            let (dug,worklist,inputof) = coarsening_worklist access locset_coarsen dug worklist inputof spec in
            (spec,dug,worklist,inputof)
      in
      prerr_endline ("\n== Timer: Coarsening dug took " ^ string_of_float (Sys.time () -. t2));
      prerr_endline ("Unproven Query          : " ^ string_of_int (BatMap.cardinal new_alarms_part));
      prerr_endline ("Unproven Query (acc)    : " ^ string_of_int (BatMap.cardinal alarms_part));
      prerr_endline ("Coarsening Target       : " ^ string_of_int (PowLoc.cardinal locset_coarsen) ^ " / " ^ string_of_int num_of_locset);
(*      prerr_endline ("Coarsening Target (acc) : " ^ string_of_int (Hashtbl.length locset_fi_hash) ^ " / " ^ string_of_int num_of_locset);*)
      prerr_endline ("Analyzed Node           : " ^ string_of_int (PowNode.cardinal !SparseAnalysis.reach_node) ^ " / " ^ string_of_int !SparseAnalysis.nb_nodes);
      prerr_endline ("#Abs Locs on Dug        : " ^ string_of_int (DUGraph.nb_loc dug));
      prerr_endline ("#Node on Dug            : " ^ string_of_int (DUGraph.nb_node dug));
      prerr_endline ("#Worklist               : " ^ (string_of_int num_of_works) ^ " -> "^(string_of_int (Worklist.cardinal worklist)));
      prdbg_endline ("Coarsened Locs : \n\t"^PowLoc.to_string locset_coarsen);
      Report.display_alarms ("Alarms at "^string_of_int !timer.threshold) new_alarms_part;
      prerr_endline ("== Timer: Coarsening took " ^ string_of_float (Sys.time () -. t0));
      prerr_endline ("== Timer: Coarsening completes at " ^ string_of_float (Sys.time () -. !widen_start));
      Profiler.report stdout;
      timer := { !timer with 
        threshold = threshold (!timer.time_stamp + 1);
        time_stamp = !timer.time_stamp + 1;
        dynamic_feature;
        old_inputof = inputof;
        alarm_history = BatMap.add !timer.threshold alarms !timer.alarm_history;
      };
      (spec,dug,worklist,inputof) 
  else (spec, dug, worklist, inputof)

let finalize spec global dug inputof =
  let alarms = (BatOption.get spec.Spec.inspect_alarm) global spec inputof |> flip Report.get Report.UnProven in
(*   let new_alarms_part = Report.partition alarms in *)
(*   Report.display_alarms ("Alarms at "^string_of_int !timer.threshold) new_alarms_part; *)
  timer_dump global dug inputof empty_feature alarms !timer.threshold

let cost () = 
  BatMap.foldi (fun t alarms cost -> 
      if t < !Options.timer_deadline then cost
      else cost + (Report.partition alarms |> BatMap.cardinal)) !timer.alarm_history 0
