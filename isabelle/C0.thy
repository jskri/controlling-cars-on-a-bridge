(***************************************************************************)
(* First model of course 02: Controlling cars on a bridge                  *)
(*                                                                         *)
(* This model is only concerned with limiting the number of cars on the    *)
(* island and brige.                                                       *)
(*                                                                         *)
(* See https://web-archive.southampton.ac.uk/deploy-eprints.ecs.soton.ac.uk/112/1/sld.ch2.car.pdf *)
(*                                                                         *)
(*                      ML_out                                             *)
(*  -----------------   <-----   ----------                                *)
(* | Island + Bridge |          | MainLand |                               *)
(*  -----------------   ----->   ----------                                *)
(*                      ML_in                                              *)
(*                                                                         *)
(***************************************************************************)

theory C0
  imports Main Common
begin

(* ========================================================================== *)
(* Specification                                                              *)
(* ========================================================================== *)

(* Cars that are not on mainland, i.e. that are on bridge or island. *)
datatype state
  = State (carCount: int)

(* Two events: 1. a car enters the mainland
               2. a car exits the mainland *)
datatype event
  = ML_in
  | ML_out
  | Stutter

(* state that results from an event applying to a given state.
 * `next` is a reserved keyword, hence `nxt`. *)
fun nxt :: "event \<Rightarrow> state \<Rightarrow> state option" where
  "nxt ML_in   (State n) = (if n > 0 then Some (State (n-1)) else None)" |
  "nxt ML_out  (State n) = (if n < d then Some (State (n+1)) else None)" |
  "nxt Stutter s         = Some s"

(* A behavior is a sequence of states, where each state after the first is
   obtained through the nxt function. *)
inductive behavior :: "state list \<Rightarrow> bool" where
  init: "behavior [State 0]" |
  succ: "\<lbrakk> behavior (states @ [s]);
           nxt e s = Some s' \<rbrakk> \<Longrightarrow> behavior ((states @ [s]) @ [s'])"

(* ========================================================================== *)
(* Invariants                                                                 *)
(* ========================================================================== *)

fun type_ok :: "state \<Rightarrow> bool" where
  "type_ok (State n) = (0 \<le> n \<and> n \<le> d)"

fun deadlock_free :: "state \<Rightarrow> bool" where
  "deadlock_free (State n) = (0 < n \<or> n < d)" (* ML_in guard and ML_out guard *)


(* ========================================================================== *)
(* Proofs                                                                     *)
(* ========================================================================== *)

(* Behaviors are non-empty by construction. *)
lemma behavior_nonempty:
  assumes "behavior states"
  shows "states \<noteq> []"
  using assms by (induction rule: behavior.induct) auto

(************)
(* type_ok  *)
(************)

lemma nxt_type_ok:
  assumes "type_ok s"
      and "nxt e s = Some s'"
    shows "type_ok s'"
  using assms
  by (cases e; cases s; auto split: if_splits; linarith)

theorem spec_type_ok:
  assumes "behavior states"
    shows "type_ok (last states)"
  using assms
proof (induction rule: behavior.induct)
  case init
  then show ?case
    using d_pos by auto
next
  case (succ ss s e s')
  then show ?case
    by (metis last_snoc nxt_type_ok)
qed

(*****************)
(* deadlock_free *)
(*****************)

(* Step preservation for deadlock_free. *)
lemma nxt_deadlock_free:
  assumes "deadlock_free s"
      and "nxt e s = Some s'"
    shows "deadlock_free s'"
  using assms d_pos
  by (cases e; cases s; auto split: if_splits; linarith)

theorem spec_deadlock_free:
  assumes "behavior states"
    shows "deadlock_free (last states)"
  using assms
proof (induction rule: behavior.induct)
  case init
  then show ?case
    by (simp add: d_pos)
next
  case (succ ss s e s')
  then show ?case
    by (metis last_snoc nxt_deadlock_free)
qed

end
