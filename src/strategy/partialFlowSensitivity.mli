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
type locset = BasicDom.PowLoc.t
type feature = {
  gvars : locset; (* global variable: done. *)
  lvars : locset; (* local variable: done. *)
  lvars_in_G : locset; (* local variables of _G_ : done *)
  fields : locset; (* structure fields : done *)
  ptr_type : locset; (* TODO *)
  allocsites : locset; (* allocsites : done *)
  static_array : locset;  (* TODO *)
  ext_allocsites : locset; (* external allocsites : done *)
  single_defs : locset; (* defined at single-site: done.*)
  assign_const : locset; (* e.g. x = (c1 + c2): done. *)
  assign_sizeof : locset; (* e.g., x = sizeof(...): done *)
  prune_simple : locset; (* make_prune_simple worked: done *)
  prune_by_const : locset; (* e.g., x < c: done *)
  prune_by_var : locset; (* e.g., x < y: done *)
  prune_by_not : locset; (* e.g., !x: done *)
  pass_to_alloc : locset; (* e.g., malloc(x): done *)
  pass_to_alloc2 : locset; (* e.g., y = x; malloc(y): done *)
  pass_to_alloc_clos : locset; (* e.g., y = x; malloc(y): done *)
  pass_to_realloc : locset; (* e.g., realloc(x): done *)
  pass_to_realloc2 : locset; (* e.g., y = x; realloc(y): done *)
  pass_to_realloc_clos : locset; (* e.g., y = x; realloc(y): done *)
  pass_to_buf : locset; (* e.g., buf = x; done *)
  return_from_alloc : locset; (* x := malloc(...): done *)
  return_from_alloc2 : locset; (* y := malloc(...); x = y: done *)
  return_from_alloc_clos : locset; (* y := malloc(...); x = y: done *)
  return_from_realloc : locset; (* x := malloc(...): done *)
  return_from_realloc2 : locset; (* y := malloc(...); x = y: done *)
  return_from_realloc_clos : locset; (* y := malloc(...); x = y: done *)
  inc_itself_by_one : locset; (* e.g., x = x + 1: done *)
  inc_itself_by_var : locset; (* e.g., x = x + y *)
  incptr_itself_by_one : locset; (* e.g., x = x + 1 (x is a pointer): done *)
  inc_itself_by_const : locset; (* e.g., x = x + c (where c > 1): done *)
  incptr_itself_by_const : locset; (* e.g., x = x + c (x is a pointer) (where c > 1): done *)
  inc : locset; (* e.g., x = y + 1 : done *)
  dec : locset; (* e.g., x = y - 1 : done *)
  dec_itself : locset; (* e.g., x = x - y : done *)
  dec_itself_by_const : locset; (* e.g., x = x - c : done *) (* TODO *)
  mul_itself_by_const : locset; (* e.g., x = x * 2 : done *)
  mul_itself_by_var : locset; (* e.g., x = x * y : done *) (* TODO *)
  used_as_array_index : locset;  (* e.g., arr[x]: done *)
  used_as_array_buf : locset; (* e.g., x[i] : done *)
  mod_in_rec_fun : locset; (* modified inside recursive functions : done *)
  read_in_rec_fun : locset; (* modified inside recursive functions *) (* TODO *)
  return_from_ext_fun : locset; (* e.g., x = ext_function() : done *)
  mod_inside_loops : locset; (* while (1) { ... x:= ... } : done *)
  used_inside_loops : locset; (* while (1) { ... :=x ... } : done *)
  constant_itv_pre : locset;
  finite_itv_pre : locset;
  finite_size_pre : locset;
  finite_offset_pre : locset;
  top_offset_pre : locset;
  constant_size_pre : locset;
  constant_offset_pre : locset;
  zero_offset_pre : locset;
  natural_size_pre : locset;
  positive_size_pre : locset;
  singleton_ptr_set_pre : locset;
  singleton_array_set_pre : locset;
  large_array_set_pre : locset;
  singleton_array_set_val_pre: locset;
}

val empty_feature : feature
val extract_feature : Global.t -> BasicDom.PowLoc.t -> feature
val select : Global.t -> BasicDom.PowLoc.t -> BasicDom.PowLoc.t
val select_simple : Global.t -> BasicDom.PowLoc.t -> BasicDom.PowLoc.t
val assign_weight : BasicDom.Loc.t list -> feature -> string list -> (BasicDom.Loc.t * float) list
