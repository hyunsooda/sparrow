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
module Hashtbl = BatHashtbl.Make(struct type t = int let equal = ( = ) let hash = Hashtbl.hash end)
module LocHashtbl = BatHashtbl.Make(Loc)

module Pfs = PartialFlowSensitivity

module PowLocBit =
struct
  include BatBitSet
  let add x t =
    set t x;
    t

  let mem x t = mem t x

  let encode encoding locset =
    PowLoc.fold (fun x ->
        try
          add (LocHashtbl.find encoding x)
        with _ ->
          id
    ) locset (empty ())

  let encode_join encoding locset codeset =
    let set = encode encoding locset in
    unite set codeset;
    set
end


(* 24 features *)
type feature = {
  encoding : int LocHashtbl.t;
(*   progress_time  : float; *)
  progress_alarm : float;
  delta_alarm    : float;
  fi_var         : float;
  (* dynamic semantic features *)
  alarm                     : PowLocBit.t;
  alarm_fi                  : PowLocBit.t;  (* TODO *)
  indirect_alarm            : PowLocBit.t;
  eq_fi                     : PowLocBit.t;
  zero_itv                  : PowLocBit.t;
  constant_itv              : PowLocBit.t;
  neg_itv                   : PowLocBit.t;
  top_itv                   : PowLocBit.t;
  left_open_itv             : PowLocBit.t;
  right_open_itv            : PowLocBit.t;
  zero_offset               : PowLocBit.t;
  constant_offset           : PowLocBit.t;
  constant_size             : PowLocBit.t;
  finite_offset             : PowLocBit.t;
  finite_size               : PowLocBit.t;
  neg_offset                : PowLocBit.t;
  left_open_offset          : PowLocBit.t;
  right_open_offset         : PowLocBit.t;
  left_open_size            : PowLocBit.t;
  right_open_size           : PowLocBit.t;
  neg_size                  : PowLocBit.t;
  zero_size                 : PowLocBit.t;
  large_ptr_set             : PowLocBit.t;
  large_ptr_set_val         : PowLocBit.t;
  large_ptr_set_val_widen   : PowLocBit.t;
  singleton_array_set       : PowLocBit.t;
  large_array_set           : PowLocBit.t;
  large_array_set_val       : PowLocBit.t;
  large_array_set_val_widen : PowLocBit.t;
  large_array_set_val_field : PowLocBit.t;
  unstable                  : PowLocBit.t;
  non_bot                       : PowLocBit.t;
  (* syntactic features *)
  temp_var                  : PowLocBit.t;
}

let empty_feature = {
  encoding = LocHashtbl.create 100000;
(*   progress_time = 0.0; *)
  progress_alarm = 0.0;
  delta_alarm = 0.0;
  fi_var = 0.0;
  (* features *)
  alarm                     = PowLocBit.empty ();
  alarm_fi                  = PowLocBit.empty ();
  indirect_alarm            = PowLocBit.empty ();
  eq_fi                     = PowLocBit.empty ();
  zero_itv                   = PowLocBit.empty ();
  constant_itv                   = PowLocBit.empty ();
  neg_itv                   = PowLocBit.empty ();
  top_itv                   = PowLocBit.empty ();
  left_open_itv             = PowLocBit.empty ();
  right_open_itv            = PowLocBit.empty ();
  zero_offset = PowLocBit.empty ();
  constant_offset = PowLocBit.empty ();
  constant_size = PowLocBit.empty ();
  finite_offset = PowLocBit.empty ();
  finite_size = PowLocBit.empty ();
  neg_offset                = PowLocBit.empty ();
  left_open_offset          = PowLocBit.empty ();
  right_open_offset         = PowLocBit.empty ();
  left_open_size            = PowLocBit.empty ();
  right_open_size           = PowLocBit.empty ();
  neg_size                  = PowLocBit.empty ();
  zero_size                 = PowLocBit.empty ();
  large_ptr_set             = PowLocBit.empty ();
  large_ptr_set_val         = PowLocBit.empty ();
  large_ptr_set_val_widen   = PowLocBit.empty ();
  singleton_array_set           = PowLocBit.empty ();
  large_array_set           = PowLocBit.empty ();
  large_array_set_val       = PowLocBit.empty ();
  large_array_set_val_widen = PowLocBit.empty ();
  large_array_set_val_field = PowLocBit.empty ();
  unstable                  = PowLocBit.empty ();
  (* syntacitc *)
  temp_var                  = PowLocBit.empty ();
  non_bot                   = PowLocBit.empty ();
}

let print_feature feat =
(*   "\nprogress_time  : " ^ string_of_float feat.progress_time ^ "\n" *)
  "progress_alarm : " ^ string_of_float feat.progress_alarm ^ "\n"
  ^ "delta_alarm    : " ^ string_of_float feat.delta_alarm ^ "\n"
  ^ "fi_variable    : " ^ string_of_float feat.fi_var ^ "\n"
  |> prerr_endline

let b2s = function true -> "1.0" | false -> "0.0"
let b2f = function true -> 1.0 | false -> 0.0

let extract_static_feature x static_feature =
  [
   b2f (PowLoc.mem x static_feature.Pfs.gvars);
   b2f (PowLoc.mem x static_feature.Pfs.lvars);
   b2f (PowLoc.mem x static_feature.Pfs.lvars_in_G);
   b2f (PowLoc.mem x static_feature.Pfs.fields);
   b2f (PowLoc.mem x static_feature.Pfs.ptr_type);
   b2f (PowLoc.mem x static_feature.Pfs.allocsites);
   b2f (PowLoc.mem x static_feature.Pfs.static_array);
   b2f (PowLoc.mem x static_feature.Pfs.ext_allocsites);
   b2f (PowLoc.mem x static_feature.Pfs.single_defs);
   b2f (PowLoc.mem x static_feature.Pfs.assign_const); (* 10 *)
   b2f (PowLoc.mem x static_feature.Pfs.assign_sizeof);
   b2f (PowLoc.mem x static_feature.Pfs.prune_simple);
   b2f (PowLoc.mem x static_feature.Pfs.prune_by_const);
   b2f (PowLoc.mem x static_feature.Pfs.prune_by_var);
   b2f (PowLoc.mem x static_feature.Pfs.prune_by_not);
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_alloc);
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_alloc2);
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_alloc_clos);
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_realloc);
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_realloc2); (* 20 *)
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_realloc_clos);
   b2f (PowLoc.mem x static_feature.Pfs.pass_to_buf);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_alloc);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_alloc2);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_alloc_clos);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_realloc);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_realloc2);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_realloc_clos);
   b2f (PowLoc.mem x static_feature.Pfs.inc_itself_by_one);
   b2f (PowLoc.mem x static_feature.Pfs.inc_itself_by_var); (* 30 *)
   b2f (PowLoc.mem x static_feature.Pfs.incptr_itself_by_one);
   b2f (PowLoc.mem x static_feature.Pfs.inc);
   b2f (PowLoc.mem x static_feature.Pfs.dec);
   b2f (PowLoc.mem x static_feature.Pfs.dec_itself);
   b2f (PowLoc.mem x static_feature.Pfs.dec_itself_by_const);
   b2f (PowLoc.mem x static_feature.Pfs.mul_itself_by_const);
   b2f (PowLoc.mem x static_feature.Pfs.mul_itself_by_var);
   b2f (PowLoc.mem x static_feature.Pfs.used_as_array_index);
   b2f (PowLoc.mem x static_feature.Pfs.used_as_array_buf);
   b2f (PowLoc.mem x static_feature.Pfs.mod_in_rec_fun); (* 40 *)
   b2f (PowLoc.mem x static_feature.Pfs.read_in_rec_fun);
   b2f (PowLoc.mem x static_feature.Pfs.return_from_ext_fun);
   b2f (PowLoc.mem x static_feature.Pfs.mod_inside_loops);
   b2f (PowLoc.mem x static_feature.Pfs.used_inside_loops);
   b2f (PowLoc.mem x static_feature.Pfs.constant_itv_pre);
   b2f (PowLoc.mem x static_feature.Pfs.finite_itv_pre);
   b2f (PowLoc.mem x static_feature.Pfs.zero_offset_pre);
   b2f (PowLoc.mem x static_feature.Pfs.constant_offset_pre);
   b2f (PowLoc.mem x static_feature.Pfs.constant_size_pre);
   b2f (PowLoc.mem x static_feature.Pfs.finite_offset_pre); (* 50 *)
   b2f (PowLoc.mem x static_feature.Pfs.top_offset_pre);
   b2f (PowLoc.mem x static_feature.Pfs.finite_size_pre);
   b2f (PowLoc.mem x static_feature.Pfs.natural_size_pre);
   b2f (PowLoc.mem x static_feature.Pfs.positive_size_pre);
   b2f (PowLoc.mem x static_feature.Pfs.singleton_ptr_set_pre);
   b2f (PowLoc.mem x static_feature.Pfs.singleton_array_set_pre);
   b2f (PowLoc.mem x static_feature.Pfs.large_array_set_pre);
   b2f (PowLoc.mem x static_feature.Pfs.singleton_array_set_val_pre);
 ]

let encode_static_feature locset static_feature =
  let hashtbl = LocHashtbl.create 100000 in
  PowLoc.iter (fun k ->
      LocHashtbl.add hashtbl k (extract_static_feature k static_feature)) locset;
  hashtbl

let feature_vector x feat static_feature =
  let static_feature = LocHashtbl.find static_feature x in
  let x = LocHashtbl.find feat.encoding x in
  static_feature @ [
   b2f (PowLocBit.mem x feat.alarm);
   b2f (PowLocBit.mem x feat.alarm_fi); (* 60 *)
   b2f (PowLocBit.mem x feat.indirect_alarm);
   b2f (PowLocBit.mem x feat.eq_fi);
   b2f (PowLocBit.mem x feat.zero_itv);
   b2f (PowLocBit.mem x feat.constant_itv);
   b2f (PowLocBit.mem x feat.neg_itv);
   b2f (PowLocBit.mem x feat.top_itv);
   b2f (PowLocBit.mem x feat.left_open_itv);
   b2f (PowLocBit.mem x feat.right_open_itv);
   b2f (PowLocBit.mem x feat.neg_offset);
   b2f (PowLocBit.mem x feat.left_open_offset); (* 70 *)
   b2f (PowLocBit.mem x feat.right_open_offset);
   b2f (PowLocBit.mem x feat.zero_offset);
   b2f (PowLocBit.mem x feat.constant_offset);
   b2f (PowLocBit.mem x feat.constant_size);
   b2f (PowLocBit.mem x feat.finite_offset);
   b2f (PowLocBit.mem x feat.finite_size);
   b2f (PowLocBit.mem x feat.left_open_size);
   b2f (PowLocBit.mem x feat.right_open_size);
   b2f (PowLocBit.mem x feat.neg_size);
   b2f (PowLocBit.mem x feat.zero_size); (* 80 *)
   b2f (PowLocBit.mem x feat.large_ptr_set);
   b2f (PowLocBit.mem x feat.large_ptr_set_val);
   b2f (PowLocBit.mem x feat.large_ptr_set_val_widen);
   b2f (PowLocBit.mem x feat.singleton_array_set);
   b2f (PowLocBit.mem x feat.large_array_set);
   b2f (PowLocBit.mem x feat.large_array_set_val);
   b2f (PowLocBit.mem x feat.large_array_set_val_widen);
   b2f (PowLocBit.mem x feat.large_array_set_val_field);
   b2f (PowLocBit.mem x feat.unstable); (* 89 *)
 ]

let string_of_raw_feature x feat static_feature =
  List.fold_left (fun s f -> s ^ " " ^ string_of_float f) 
    (Loc.to_string x ^ " : ") (feature_vector x feat static_feature)

let premem_hash = LocHashtbl.create 10000
let locset_hash = LocHashtbl.create 10000  (* locset \ bot-locs *)

let initialize_cache locset premem =
  PowLoc.iter (fun k -> LocHashtbl.add locset_hash k k) locset;
  Mem.iter (LocHashtbl.add premem_hash) premem;
  ignore(PowLoc.fold (fun k i ->
      LocHashtbl.add empty_feature.encoding k i;
      i + 1) locset 0);
  empty_feature

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

let add_neg_itv k i feat =
  if (Itv.meet Itv.neg i) <> Itv.bot then
    { feat with neg_itv = PowLocBit.add k feat.neg_itv }
  else feat

let add_right_open_itv k i feat =
  if Itv.open_right i then
    { feat with right_open_itv = PowLocBit.add k feat.right_open_itv }
  else 
    feat

let add_constant_itv k i feat =
  if Itv.is_const i then
    { feat with constant_itv = PowLocBit.add k feat.constant_itv }
  else 
    feat

let add_zero_itv k i feat =
  if Itv.is_zero i then
    { feat with zero_itv = PowLocBit.add k feat.zero_itv }
  else 
    feat

let extract_itv_feature k v feat =
  let i = Val.itv_of_val v in
  if Itv.is_top i then
    { feat with top_itv = PowLocBit.add k feat.top_itv;
                left_open_itv = PowLocBit.add k feat.left_open_itv;
                right_open_itv = PowLocBit.add k feat.right_open_itv;
                neg_itv = PowLocBit.add k feat.neg_itv; }
  else if Itv.open_left i then
    { feat with left_open_itv = PowLocBit.add k feat.left_open_itv;
                neg_itv = PowLocBit.add k feat.neg_itv; }
  else
    feat
    |> add_right_open_itv k i
    |> add_neg_itv k i
    |> add_constant_itv k i
    |> add_zero_itv k i

let neg_offset_cache = Hashtbl.create 1000
let left_open_offset_cache = Hashtbl.create 1000
let right_open_offset_cache = Hashtbl.create 1000

let add_neg_offset k offset feat =
  if Hashtbl.mem neg_offset_cache k then feat
  else if (Itv.meet Itv.neg offset) <> Itv.bot then 
    let _ = Hashtbl.add neg_offset_cache k k in
    { feat with neg_offset = PowLocBit.add k feat.neg_offset }
  else feat


let add_left_open_offset k offset feat =
  if Hashtbl.mem left_open_offset_cache k then feat
  else if Itv.open_left offset then 
    let _ = Hashtbl.add left_open_offset_cache k k in
    { feat with left_open_offset = PowLocBit.add k feat.left_open_offset }
  else feat

let add_right_open_offset k offset feat =
  if Hashtbl.mem right_open_offset_cache k then feat
  else if Itv.open_right offset then 
    let _ = Hashtbl.add right_open_offset_cache k k in
    { feat with right_open_offset = PowLocBit.add k feat.right_open_offset }
  else feat

let not_constant_offset_cache = Hashtbl.create 1000
let add_constant_offset k offset feat = 
  if Hashtbl.mem not_constant_offset_cache k then feat 
  else
    if Itv.is_const offset then 
      { feat with constant_offset = PowLocBit.add k feat.constant_offset }
    else if Itv.is_bot offset then feat
    else
      let _ = Hashtbl.add not_constant_offset_cache k k in
      feat

let not_finite_offset_cache = Hashtbl.create 1000
let add_finite_offset k offset feat = 
  if Hashtbl.mem not_finite_offset_cache k then feat 
  else 
    if Itv.is_finite offset then 
      { feat with finite_offset = PowLocBit.add k feat.finite_offset }
    else if Itv.is_bot offset then feat
    else
      let _ = Hashtbl.add not_finite_offset_cache k k in
      feat

let not_zero_offset_cache = Hashtbl.create 1000
let add_zero_offset k offset feat = 
  if Hashtbl.mem not_zero_offset_cache k then feat 
  else
    if Itv.is_zero offset then 
      { feat with zero_offset = PowLocBit.add k feat.zero_offset }
    else if Itv.is_bot offset then feat
    else
      let _ = Hashtbl.add not_zero_offset_cache k k in
      feat

let extract_offset_feature k v feat =
  let offset = Val.array_of_val v |> ArrayBlk.offsetof in
  feat
  |> add_neg_offset k offset
  |> add_left_open_offset k offset
  |> add_right_open_offset k offset
  |> add_constant_offset k offset
  |> add_finite_offset k offset
  |> add_zero_offset k offset

let neg_size_cache = Hashtbl.create 1000
let add_neg_size k size feat = 
  if Hashtbl.mem neg_size_cache k then feat
  else if (Itv.meet Itv.neg size) <> Itv.bot then 
    let _ = Hashtbl.add neg_size_cache k k in
    { feat with neg_size = PowLocBit.add k feat.neg_size }
  else feat

let left_open_size_cache = Hashtbl.create 1000
let add_left_open_size k size feat = 
  if Hashtbl.mem left_open_size_cache k then feat
  else if Itv.open_left size then 
    let _ = Hashtbl.add left_open_size_cache k k in
    { feat with left_open_size = PowLocBit.add k feat.left_open_size }
  else feat

let left_right_size_cache = Hashtbl.create 1000
let add_right_open_size k size feat = 
  if Hashtbl.mem left_right_size_cache k then feat
  else if Itv.open_right size then 
    let _ = Hashtbl.add left_right_size_cache k k in
    { feat with right_open_size = PowLocBit.add k feat.right_open_size }
  else feat

let zero_size_cache = Hashtbl.create 1000
let add_zero_size k size feat = 
  if Hashtbl.mem zero_size_cache k then feat
  else if (Itv.meet Itv.zero size) <> Itv.bot then 
    let _ = Hashtbl.add zero_size_cache k k in
    { feat with zero_size = PowLocBit.add k feat.zero_size }
  else feat

let not_constant_size_cache = Hashtbl.create 1000
let add_constant_size k size feat = 
  if Hashtbl.mem not_constant_size_cache k then feat 
  else 
    if Itv.is_const size then 
      { feat with constant_size = PowLocBit.add k feat.constant_size }
    else if Itv.is_bot size then feat
    else 
      let _ = Hashtbl.add not_constant_size_cache k k in
      feat

let not_finite_size_cache = Hashtbl.create 1000
let add_finite_size k size feat = 
  if Hashtbl.mem not_finite_size_cache k then feat 
  else 
    if Itv.is_finite size then 
      { feat with finite_size = PowLocBit.add k feat.finite_size }
    else if Itv.is_bot size then feat
    else
      let _ = Hashtbl.add not_finite_size_cache k k in
      feat

let extract_size_feature k v feat =
  let size = Val.array_of_val v |> ArrayBlk.sizeof in
  feat
  |> add_neg_size k size
  |> add_left_open_size k size
  |> add_right_open_size k size
  |> add_constant_size k size
  |> add_finite_size k size
  |> add_zero_size k size

let add_large_ptr_set k v feat = 
  if (Val.pow_loc_of_val v |> PowLoc.cardinal > 2) 
    || (Val.pow_proc_of_val v |> PowProc.cardinal > 2) then
    { feat with large_ptr_set = PowLocBit.add k feat.large_ptr_set } 
  else feat

let add_large_ptr_set_val k v feat =
  if (Val.pow_loc_of_val v |> PowLoc.cardinal > 2) then
    { feat with large_ptr_set_val = PowLocBit.encode_join feat.encoding (Val.pow_loc_of_val v) (feat.large_ptr_set_val) }
  else feat

let large_ptr_set_val_widen_cache = Hashtbl.create 1000
let add_large_ptr_set_val_widen x k v feat =
  if Hashtbl.mem large_ptr_set_val_widen_cache k then feat
  else if (Val.pow_loc_of_val v |> PowLoc.cardinal > 1) then
    let _ = Hashtbl.add large_ptr_set_val_widen_cache k k in
    { feat with large_ptr_set_val_widen = 
        PowLocBit.encode_join feat.encoding (LocHashtbl.find premem_hash x |> Val.pow_loc_of_val)
          (feat.large_ptr_set_val_widen) }
  else feat

let large_array_set_cache = Hashtbl.create 1000
let add_large_array_set k v feat = 
  if Hashtbl.mem large_array_set_cache k then feat
  else if (Val.array_of_val v |> ArrayBlk.cardinal > 1) then
    let _ = Hashtbl.add large_array_set_cache k k in
    { feat with large_array_set = PowLocBit.add k feat.large_array_set } 
  else feat

let not_singleton_array_set_cache = Hashtbl.create 1000
let add_singleton_array_set k v feat = 
  if Hashtbl.mem not_singleton_array_set_cache k then feat
  else if (Val.array_of_val v |> ArrayBlk.cardinal = 1) then
    { feat with singleton_array_set = PowLocBit.add k feat.singleton_array_set } 
  else if (Val.array_of_val v |> ArrayBlk.cardinal > 1) then
    let _ = Hashtbl.add not_singleton_array_set_cache k k in
    feat
  else feat

(* TODO: optimize *)
let large_array_set_val_cache = Hashtbl.create 1000
let add_large_array_set_val k v feat = 
  if Hashtbl.mem large_array_set_val_cache k && Random.bool () then feat
  else if (Val.array_of_val v |> ArrayBlk.cardinal >= 3) then
    let _ = Hashtbl.replace large_array_set_val_cache k k in
    { feat with large_array_set_val = PowLocBit.encode_join feat.encoding (Val.array_of_val v |> ArrayBlk.pow_loc_of_array) feat.large_array_set_val } 
  else feat
 
let large_array_set_val_widen_cache = Hashtbl.create 1000
let add_large_array_set_val_widen x k v feat = 
  if Hashtbl.mem large_array_set_val_widen_cache k then feat
  else if (Val.array_of_val v |> ArrayBlk.cardinal >= 3) then
    let _ = Hashtbl.add large_array_set_val_widen_cache k k in
    { feat with large_array_set_val_widen =
        PowLocBit.encode_join feat.encoding (LocHashtbl.find premem_hash x |> Val.array_of_val |> ArrayBlk.pow_loc_of_array)
          feat.large_array_set_val_widen }
  else feat

let add_large_array_set_val_field feat = 
  { feat with 
      large_array_set_val_field = 
        LocHashtbl.fold (fun k _ ->
            match k with
            | Loc.Field (l, _, _) 
              when (PowLocBit.mem (LocHashtbl.find feat.encoding l) feat.large_array_set_val_widen)
                || not (LocHashtbl.mem locset_hash l) ->
              PowLocBit.add (LocHashtbl.find feat.encoding k)
            | _ -> id)
          premem_hash feat.large_array_set_val_field }
     
let unstable v1 v2 = not (Val.le v2 v1) 
let add_unstable k old_v new_v feat = 
  if unstable old_v new_v then 
    { feat with unstable = PowLocBit.add k feat.unstable }
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
let add_eq_fi x k v feat = 
  if Hashtbl.mem eq_cache k then feat
  else if soft_eq v (LocHashtbl.find premem_hash x) then 
    let _ = Hashtbl.add eq_cache k k in
    { feat with eq_fi = PowLocBit.add k feat.eq_fi }
  else feat

let add_temp_var k v feat = 
  if (Val.itv_of_val v |> Itv.meet Itv.neg) <> Itv.bot then 
    { feat with neg_itv = PowLocBit.add k feat.neg_itv }
  else feat

let add_non_bot k v feat = 
  if Val.bot <> v then { feat with non_bot = PowLocBit.add k feat.non_bot }
  else feat

let extract spec global alarms new_alarms old_inputof inputof old_feature = 
(*  let t0 = Sys.time () in*)
  let encoding = old_feature.encoding in
  let total_alarms = spec.Spec.pre_alarm |> flip Report.get Report.UnProven |> Report.partition in
  let num_of_total_alarms = BatMap.cardinal total_alarms in
  let current_alarm = BatMap.cardinal alarms in
  let new_alarm = BatMap.cardinal new_alarms in
  { old_feature with
    (*!timer.dynamic_feature with *)
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
      { feat with alarm = PowLocBit.encode encoding alarm_locs;
                  indirect_alarm = PowLocBit.encode encoding indirect;
        (* non-monoton features *)
                  singleton_array_set = PowLocBit.empty ();
                  zero_offset = PowLocBit.empty(); constant_offset = PowLocBit.empty ();
                  constant_size = PowLocBit.empty(); finite_offset = PowLocBit.empty ();
                  finite_size = PowLocBit.empty ();
      }
     ) new_alarms
(*  |> (fun x -> prerr_endline ("\n-- until alarm features " ^ string_of_float (Sys.time () -. t0)); x)*)
  |> Table.fold (fun node new_mem feat ->
      if (InterCfg.is_entry node) || (InterCfg.is_exit node)
        || (InterCfg.is_callnode node global.icfg) || (InterCfg.is_returnnode node global.icfg)
      then 
        let old_mem = Table.find node old_inputof in
        Mem.fold (fun k v feat ->
(*            if Hashtbl.mem locset_hash k then*)
              let ki = LocHashtbl.find encoding k in
              feat
              |> (extract_itv_feature ki v)
              |> (extract_offset_feature ki v)
              |> (extract_size_feature ki v)
              |> (add_large_ptr_set ki v)
              |> (add_large_ptr_set_val ki v)
              |> (add_large_ptr_set_val_widen k ki v)
              |> (add_singleton_array_set ki v)
              |> (add_large_array_set ki v)
              |> (add_large_array_set_val ki v)
              |> (add_large_array_set_val_widen k ki v)
              |> (add_unstable ki (Mem.find k old_mem) v )
              |> (add_eq_fi k ki v)
              |> (add_non_bot ki v)
(*            else feat*)
          ) new_mem feat
      else feat) inputof
  |> add_large_array_set_val_field
(*  |> (fun x -> prerr_endline ("\n-- until semantic features " ^ string_of_float (Sys.time () -. t0)); x)*)
