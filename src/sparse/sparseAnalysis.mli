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
(** Sparse analysis framework *)
val total_iterations : int ref
val predict_start : float ref
val reach_node : BasicDom.PowNode.t ref
val nb_nodes : int ref

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

module Make (Sem:AbsSem.S) : S
  with type Dom.t = Sem.Dom.t
  and type Dom.A.t = Sem.Dom.A.t
  and type Dom.PowA.t = Sem.Dom.PowA.t
  and type Dom.Access.t = Sem.Dom.Access.t
  and type DUGraph.t = Sem.Spec.DUGraph.t
  and type Worklist.t = Sem.Spec.Worklist.t

module MakeWithAccess (Sem:AccessSem.S) : S
  with type Dom.t = Sem.Dom.t
  and type Dom.A.t = Sem.Dom.A.t
  and type Dom.PowA.t = Sem.Dom.PowA.t
  and type Dom.Access.t = Sem.Dom.Access.t
  and type DUGraph.t = Sem.Spec.DUGraph.t
  and type Worklist.t = Sem.Spec.Worklist.t
