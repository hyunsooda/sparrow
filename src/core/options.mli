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
(** Commandline options *)

(** {2 Intermediate Represenation } *)

val il : bool ref
val cfg : bool ref
val dug : bool ref
val optil : bool ref

(** {2 Context Sensitivity } *)

val inline : string list ref
val inline_size : int ref
val pfs : int ref
val pfs_wv : string ref

(** {2 Octagon Analysis } *)

val oct : bool ref
val pack_impact : bool ref
val pack_manual : bool ref

(** {2 Unsoundness } *)

val unsound_loop : string BatSet.t ref
val unsound_lib : string BatSet.t ref
val extract_loop_feat : bool ref
val extract_lib_feat : bool ref
val top_location : bool ref
val bugfinder :  int ref
val unsound_recursion : bool ref
val unsound_alloc : bool ref

(** {2 Main Analysis } *)

val narrow : bool ref
val scaffold : bool ref
val int_overflow : bool ref

(** {2 Alarm Report } *)

val bo : bool ref
val nd : bool ref
val dz : bool ref
val show_all_query : bool ref

(** {2 Pretty Printer & Debugging } *)

val nobar : bool ref
val profile : bool ref
val noalarm : bool ref
val debug : bool ref
val oct_debug : bool ref
val print_premem : bool ref
val verbose : int ref

(** {2 Marshaling } *)

val marshal_in : bool ref
val marshal_out : bool ref
val marshal_dir : string ref
val marshal_in_global : bool ref
val marshal_in_dug : bool ref
val marshal_in_worklist : bool ref
val marshal_out_global : bool ref
val marshal_out_dug : bool ref
val marshal_out_worklist : bool ref
val marshal_out_alarm : bool ref

(** {2 Timer (experimental) } *)

val timer_deadline : int ref
val timer_iter : int ref
val timer_unit : int ref
val timer_alpha : int ref
val timer_dump : bool ref
val timer_extract : bool ref
val timer_iteration : int ref
val timer_debug : bool ref
val timer_static_rank : bool ref
val timer_oracle_rank : bool ref
val timer_clf : string ref
val timer_dir : string ref
val print_height : bool ref
val print_time : bool ref
val optimistic : bool ref
val coarsen_trigger : string ref
val timer_wv : string ref
val predictor : bool ref
val timer_threshold_time : string ref
val timer_threshold_abs : string ref
val timer_initial_coarsening : bool ref
val timer_stat : bool ref
val timer_counter_example : bool ref

(** {2 Options lists } *)

val opts : (string * Arg.spec * string) list
