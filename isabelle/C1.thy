(***************************************************************************)
(* Second model of course 02: Controlling cars on a bridge                 *)
(*                                                                         *)
(* Introducing the bridge.                                                 *)
(*                                                                         *)
(* See https://web-archive.southampton.ac.uk/deploy-eprints.ecs.soton.ac.uk/112/1/sld.ch2.car.pdf *)
(*                                                                         *)
(*               IL_in                       ML_out                        *)
(*   ---------   <-----   ----------------   <-----   ----------           *)
(*  | Island  |          | One Way Bridge |          | MainLand |          *)
(*   ---------   ----->   ----------------   ----->   ----------           *)
(*               IL_out                       ML_in                        *)
(*                                                                         *)
(***************************************************************************)

theory C1
  imports Main C0 Common
begin

(* ========================================================================== *)
(* Specification                                                              *)
(* ========================================================================== *)

(***************************************************************************)
(*                               a                                         *)
(*   ---------   <---------------------------------   ----------           *)
(*  |    b    |            One Way Bridge            |          |          *)
(*   ---------   --------------------------------->   ----------           *)
(*                               c                                         *)
(***************************************************************************)

datatype state
  = State int (* Number of cars going to the island. *)
          int (* Number of cars on the island. *)
          int (* Number of cars going to the mainland. *)

datatype event
  = ML_in
  | ML_out
  | IL_in
  | IL_out
  | Stutter

(* state that results from an event.
 * `next` is a reserved keyword, hence `nxt`. *)
fun nxt :: "event \<Rightarrow> state \<Rightarrow> state option" where
  "nxt e (State a b c) =
   (let s = State a b c in
    case e of
      ML_in    \<Rightarrow> (if c > 0             then Some (State a b (c-1))     else None) |
      ML_out   \<Rightarrow> (if a+b+c < d \<and> c = 0 then Some (State (a+1) b c)   else None) |
      IL_in    \<Rightarrow> (if a > 0             then Some (State (a-1) (b+1) c) else None) |
      IL_out   \<Rightarrow> (if a = 0 \<and> b > 0     then Some (State a (b-1) (c+1)) else None) |
      Stutter  \<Rightarrow> Some s
   )"

(* A behavior is a sequence of states, where each state after the first is
   obtained through the nxt function. *)
inductive behavior :: "state list \<Rightarrow> bool" where
  init: "behavior [State 0 0 0]" |
  succ: "\<lbrakk> behavior (states @ [s]);
           Some s' = nxt e s \<rbrakk> \<Longrightarrow>
           behavior ((states @ [s]) @ [s'])"

(* ========================================================================== *)
(* Variants & invariants                                                      *)
(* ========================================================================== *)

fun type_ok :: "state \<Rightarrow> bool" where
  "type_ok (State a b c) = (a \<ge> 0 \<and> b \<ge> 0 \<and> c \<ge> 0)"

fun one_way_bridge :: "state \<Rightarrow> bool" where
  "one_way_bridge (State a _ c) = (a = 0 \<or> c = 0)"

(* Combined invariant. *)
fun correct :: "state \<Rightarrow> bool" where
  "correct s = (type_ok s \<and> one_way_bridge s)"

(* variant: see new_events_converge *)
fun v :: "state \<Rightarrow> int" where
  "v (State a b _) = 2*a + b"

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
  then show ?case by simp
next
  case (succ ss s e s')
  then show ?case
    by (metis last_snoc nxt_type_ok)
qed

(******************)
(* one_way_bridge *)
(******************)

(* one_way_bridge is self-invariant: no type_ok hypothesis needed. *)
lemma nxt_one_way_bridge:
  assumes "one_way_bridge s"
      and "nxt e s = Some s'"
    shows "one_way_bridge s'"
  using assms
  by (cases e; cases s; auto split: if_splits; linarith)

theorem spec_one_way_bridge:
  assumes "behavior states"
    shows "one_way_bridge (last states)"
  using assms
proof (induction rule: behavior.induct)
  case init
  then show ?case by simp
next
  case (succ ss s s' e)
  have "one_way_bridge s" using succ.IH by force
  then have "one_way_bridge s'" using nxt_one_way_bridge succ.hyps(2) by presburger
  then show ?case by fastforce
qed

(***********)
(* correct *)
(***********)

theorem spec_correct:
  assumes "behavior states"
    shows "correct (last states)"
  using spec_type_ok spec_one_way_bridge assms by auto

(***************)
(* Convergence *)
(***************)

theorem new_events_converge:
  assumes "type_ok s"
      and "e = IL_in \<or> e = IL_out"
      and "nxt e s = Some s'"
    shows "v s' < v s"
  using assms
  by (cases s; cases e; auto split: if_splits; linarith)

(**************)
(* Refinement *)
(**************)

(* The refinement mapping f is a homomorphism from the C1 spec to the C0 spec.
 * The constraints of f are:
 * - initial states are sent to initial states
 * - the following diagram commutes, where s? are states and e? are events:
 *
 *           f_s e1
 *  C0:   s0 -----> s0'
 *         ^         ^
 *      f_s|         |f_s
 *  C1:   s1 -----> s1'
 *             e1
 *)

fun f_s :: "C1.state \<Rightarrow> C0.state" where
  "f_s (C1.State a b c) = C0.State (a+b+c)"

fun f_e :: "C1.event \<Rightarrow> C0.event" where
  "f_e C1.ML_in   = C0.ML_in"  |
  "f_e C1.ML_out  = C0.ML_out" |
  "f_e C1.IL_in   = C0.Stutter" |
  "f_e C1.IL_out  = C0.Stutter" |
  "f_e C1.Stutter = C0.Stutter"

(* Step refinement. Takes type_ok s rather than behavior, making this lemma
 * independent of the behavior predicate and easier to reuse. *)
lemma nxt_refine:
  assumes "C1.type_ok s"
      and "C1.nxt e s = Some s'"
    shows "C0.nxt (f_e e) (f_s s) = Some (f_s s')"
  using assms
proof (cases e)
  case ML_in
  then show ?thesis
    using assms by (cases s; auto split: if_splits; linarith)
next
  case ML_out
  then show ?thesis
    using assms by (cases s; auto split: if_splits)
next
  case IL_in
  then show ?thesis
    using assms by (cases s; auto split: if_splits; linarith)
next
  case IL_out
  then show ?thesis
    using assms by (cases s; auto split: if_splits; linarith)
next
  case Stutter
  then show ?thesis
    using assms by (cases s; auto)
qed

theorem refine:
  assumes "C1.behavior states"
    shows "C0.behavior (map f_s states)"
  using assms
proof (induction rule: C1.behavior.induct)
  case init
  then show ?case
    by (simp add: C0.behavior.init)
next
  case (succ ss s s' e)
  moreover have "C1.type_ok s"
    using spec_correct succ.hyps(1) by fastforce
  ultimately show ?case
    by (metis (mono_tags, lifting) C0.behavior.simps list.simps(8,9) map_append
        C1.nxt_refine)
qed

end
