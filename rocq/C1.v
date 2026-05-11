(**************************************************************************************************)
(* Second model of course 02: Controlling cars on a bridge                                        *)
(*                                                                                                *)
(* Introducing the bridge.                                                                        *)
(*                                                                                                *)
(* See https://web-archive.southampton.ac.uk/deploy-eprints.ecs.soton.ac.uk/112/1/sld.ch2.car.pdf *)
(*                                                                                                *)
(*               IL_in                       ML_out                                               *)
(*   ---------   <-----   ----------------   <-----   ----------                                  *)
(*  | Island  |          | One Way Bridge |          | MainLand |                                 *)
(*   ---------   ----->   ----------------   ----->   ----------                                  *)
(*               IL_out                       ML_in                                               *)
(*                                                                                                *)
(**************************************************************************************************)

From Stdlib Require Import Unicode.Utf8 Arith micromega.Lia.
From Hammer Require Import Tactics.
From CarsOnBridge Require Import Common.
From CarsOnBridge Require C0.

(* ========================================================================== *)
(* Specification                                                              *)
(* ========================================================================== *)

(*    IL_in           ML_out
        <-    one-way   <- 
island       bridge          Mainland
        ->              ->
      IL_out          ML_in
    b          <- a
               -> c

d = max cars on island and bridge
*)

Record State := mkState
  { a : ℕ (* number of cars on bridge going to the island *)
  ; b : ℕ (* number of cars on the island *)
  ; c : ℕ (* number of cars bridge going to the mainland *)
  }.

Inductive Event := ML_in | ML_out | IL_in | IL_out | Stutter.

Definition Init : State := mkState 0 0 0.

Definition Next (e : Event) (s : State) : option State :=
  let 'mkState a b c := s in
  match e with
  | ML_in   => if 0 <? c then Some (mkState a b (c-1)) else None
  | ML_out  => if (a+b <? d) && (c =? 0) then Some (mkState (a+1) b c) else None
  | IL_in   => if 0 <? a then Some (mkState (a-1) (b+1) c) else None
  | IL_out  => if (0 <? b) && (a =? 0) then Some (mkState a (b-1) (c+1)) else None
  | Stutter => Some s
  end.

(* ========================================================================== *)
(* Variants & invariants                                                      *)
(* ========================================================================== *)

Definition OneWayBridge (s : State) : Prop :=
  s.(a) = 0 ∨ s.(c) = 0.

(* variant: see NewEventsConverge *)
Definition V (s : State) : ℕ := 2*s.(a) + s.(b).


(* ========================================================================== *)
(* Proofs                                                                     *)
(* ========================================================================== *)

(*************************)
(* Variants & invariants *)
(*************************)

Theorem SpecOneWayBridge : ∀ (e : Event) (s s' : State),
  (OneWayBridge Init ∧
    (OneWayBridge s → Next e s = Some s' → OneWayBridge s')).
Proof. split; destruct e, s, s'; sauto. Qed.

Theorem NewEventsConverge : ∀ (e : Event) (s s' : State)
  (ev : e = IL_in ∨ e = IL_out),
  Next e s = Some s' →
  V s' < V s.
Proof. intros; destruct ev; sauto unfold: V. Qed.


(*************************)
(* Refinement            *)
(*************************)

(* f is an homomorphism from the C1 spec to the C0 spec.
 * The constraints of f are:
 * - initial states are sent to initial states
 * - the following diagram commutes, where s? are states and e? are events:
 *
 *           fₑ e1
 *  C0:   s0 -----> s0'
 *         ^         ^
 *       fₛ|         |fₛ
 *  C1:   s1 -----> s1'
 *             e1
 *)

(* fₛ is the state component of f. *)
Definition fₛ (s1 : C1.State) : C0.State :=
  let 'C1.mkState a b c := s1 in
  C0.mkState (a + b + c).

(* fₑ is the event component of f. *)
Definition fₑ (e1 : C1.Event) : C0.Event :=
  match e1 with
  | C1.ML_in => C0.ML_in
  | C1.ML_out => C0.ML_out
  | C1.IL_in | C1.IL_out | C1.Stutter => C0.Stutter
  end.

Lemma RefineInit : fₛ C1.Init = C0.Init.
Proof. sauto. Qed.

(* Prove
E : s1 = C1.mkState a b c
Cond : cond = true
-------------------------
(if cond then Some (a + b + c) else None) = Some (fₛ s1)
*)
Ltac if_some Cond E :=
  try rewrite Cond; f_equal; rewrite E; simpl; f_equal; lia.

Lemma RefineML_in : ∀ (s1 s1' : C1.State)
  (nx1 : C1.Next C1.ML_in s1 = Some s1'),
  C0.Next (fₑ C1.ML_in) (fₛ s1) = Some (fₛ s1').
Proof.
  intros; destruct s1 as [a b c]. (* [a b c] needed to shadow State projs *)
  enough (H : 0 < c ∧ s1' = C1.mkState a b (c-1)). {
    destruct H as [? H2]; simpl.
    assert (L : 0 <? a + b + c = true) by now apply Nat.ltb_lt; lia.
    if_some L H2.
  }
  sauto.
Qed.

Lemma RefineML_out : ∀ (s1 s1' : C1.State)
  (nx1 : C1.Next C1.ML_out s1 = Some s1'),
  C0.Next (fₑ C1.ML_out) (fₛ s1) = Some (fₛ s1').
Proof.
  intros; destruct s1 as [a b c].
  enough (H : (a+b < d ∧ c = 0) ∧ s1' = C1.mkState (a+1) b c). {
    destruct H as [? H2]; simpl.
    assert (L : a + b + c <? d = true) by now apply Nat.ltb_lt; lia.
    if_some L H2.
  }
  sauto.
Qed.

Lemma RefineIL_in : ∀ (s1 s1' : C1.State)
  (nx1 : C1.Next C1.IL_in s1 = Some s1'),
  C0.Next (fₑ C1.IL_in) (fₛ s1) = Some (fₛ s1').
Proof.
  intros; destruct s1 as [a b c].
  enough (0 < a ∧ s1' = C1.mkState (a-1) (b+1) c). {
    destruct H as [? H2]; simpl.
    assert (L : 0 <? a = true) by now apply Nat.ltb_lt; lia.
    if_some L H2.
  }
  sauto.
Qed.

Lemma RefineIL_out : ∀ (s1 s1' : C1.State)
  (nx1 : C1.Next C1.IL_out s1 = Some s1'),
  C0.Next (fₑ C1.IL_out) (fₛ s1) = Some (fₛ s1').
Proof.
  intros; destruct s1 as [a b c].
  enough ((0 < b ∧ a = 0) ∧ s1' = C1.mkState a (b-1) (c+1)). {
    destruct H as [H1 H2]; simpl.
    assert (L : (0 <? b) && (a =? 0) = true)
      by now destruct H1; apply Bool.andb_true_iff; sauto.
    if_some L H2.
  }
  sauto.
Qed.

Lemma RefineStutter : ∀ (s1 s1' : C1.State)
  (nx1 : C1.Next C1.Stutter s1 = Some s1'),
  C0.Next (fₑ C1.Stutter) (fₛ s1) = Some (fₛ s1').
Proof. sauto. Qed.

Theorem Refine : ∀ (s0 s0' : C0.State) (s1 s1' s1'' : C1.State) (e1 : C1.Event),
    fₛ C1.Init = C0.Init
  ∧ (C1.Next e1 s1 = Some s1' → C0.Next (fₑ e1) (fₛ s1) = Some (fₛ s1')).
Proof.
  destruct e1; auto using RefineInit, RefineML_in, RefineML_out,
    RefineIL_in, RefineIL_out, RefineStutter.
Qed.