(**************************************************************************************************)
(* Third model of course 02: Controlling cars on a bridge                                         *)
(*                                                                                                *)
(* Introducing traffic lights.                                                                    *)
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
From CarsOnBridge Require C1.

(* ========================================================================== *)
(* Specification                                                              *)
(* ========================================================================== *)

(***************************************************************************)
(*                               a               ml_tl                     *)
(*   ---------   <---------------------------------   ----------           *)
(*  |    b    |            One Way Bridge            |          |          *)
(*   ---------   --------------------------------->   ----------           *)
(*            il_tl              c                                         *)
(***************************************************************************)

Inductive Color := Green | Red.

Scheme Equality for Color.
(* auto-generates Color_beq : Color → Color → bool *)
(* and            Color_eq_dec : ∀ x y : Color, {x=y} + {x≠y} *)

Record State := mkState
  { a : ℕ          (* number of cars on bridge going to the island *)
  ; b : ℕ          (* number of cars on the island *)
  ; c : ℕ          (* number of cars bridge going to the mainland *)
  ; ml_tl : Color  (* mainland's traffic light color *)
  ; il_tl : Color  (* island's traffic light color *)
  ; ml_pass : bool (* true if at least one car passed since ml_tl turned green *)
  ; il_pass : bool (* true if at least one car passed since il_tl turned green *)
  }.

Inductive Event := ML_in | ML_out | IL_in | IL_out | ML_tl_green | IL_tl_green | Stutter.

Definition Init : State := mkState 0 0 0 Red Red true true.

Definition NextML_tl_green (s : State) : option State :=
  let 'mkState a b c ml_tl il_tl ml_pass il_pass := s in  
  if (Color_beq ml_tl Red) && (a+b <? d) && (c =? 0) && il_pass then
    Some {| ml_tl := Green
         ;  il_tl := Red
         ;  ml_pass := false
         ;  a := a; b := b; c := c; il_pass := il_pass
         |}
  else
    None.

Definition NextIL_tl_green (s : State) : option State :=
  let 'mkState a b c ml_tl il_tl ml_pass il_pass := s in  
  if (Color_beq il_tl Red) && (a =? 0) && (0 <? b) && ml_pass then
    Some {| ml_tl := Red
         ;  il_tl := Green
         ;  il_pass := false
         ;  a := a; b := b; c := c; ml_pass := ml_pass
         |}
  else
    None.

Definition NextML_out (s : State) : option State :=
  let 'mkState a b c ml_tl il_tl ml_pass il_pass := s in
  if Color_beq ml_tl Green then
    Some {| a := a+1
         ;  ml_tl := if (a+1+b <? d) then Green else Red
         ;  il_tl := Red
         ;  ml_pass := true
         ;  b := b; c := c; il_pass := il_pass
         |}
  else
    None.

Definition NextIL_out (s : State) : option State :=
  let 'mkState a b c ml_tl il_tl ml_pass il_pass := s in
  if Color_beq il_tl Green then
    Some {| b := b-1
         ;  c := c+1
         ;  ml_tl := Red
         ;  il_tl := if (0 <? b-1) then Green else Red
         ;  il_pass := true
         ;  a := a; ml_pass := ml_pass
         |}
  else
    None.

(* Forgetful mapping from C2 states to C1 states.
 * This is the refinement mapping fₛ, see below. *)
Definition toS1 (s : State) : C1.State :=
  C1.mkState s.(a) s.(b) s.(c).

(* C2 state based on `s1` and completed with `s`. *)
Definition toS (s : State) (s1 : C1.State) : State :=
  {| a := s1.(C1.a); b := s1.(C1.b); c := s1.(C1.c);
     ml_tl := s.(ml_tl); il_tl := s.(il_tl); ml_pass := s.(ml_pass); il_pass := s.(il_pass) |}.

Definition Next (e : Event) (s : State) : option State :=
  match e with
  | ML_in       => option_map (toS s) (C1.Next C1.ML_in (toS1 s)) (* same as C1 *)
  | ML_out      => NextML_out s
  | IL_in       => option_map (toS s) (C1.Next C1.IL_in (toS1 s)) (* same as C1 *)
  | IL_out      => NextIL_out s
  | ML_tl_green => NextML_tl_green s
  | IL_tl_green => NextIL_tl_green s
  | Stutter     => Some s
  end.


(* ========================================================================== *)
(* Invariants                                                                 *)
(* ========================================================================== *)

Definition MlTlSafe (s : State) : Prop :=
  s.(ml_tl) = Green →
  s.(a) + s.(b) < d ∧ s.(c) = 0.

Definition IlTlSafe (s : State) : Prop :=
  s.(il_tl) = Green →
  s.(a) = 0 ∧ s.(b) > 0.

Definition AtLeastOneTrafficLightIsRed (s : State) : Prop :=
  s.(ml_tl) = Red ∨ s.(il_tl) = Red.

Definition MlTlPass (s : State) : Prop :=
  s.(ml_tl) = Red →
  s.(ml_pass) = true.

Definition IlTlPass (s : State) : Prop :=
  s.(il_tl) = Red →
  s.(il_pass) = true.

Definition Correct (s : State) : Prop :=
    MlTlSafe s
  ∧ IlTlSafe s
  ∧ C1.OneWayBridge (toS1 s)
  ∧ AtLeastOneTrafficLightIsRed s
  ∧ MlTlPass s
  ∧ IlTlPass s.


(* ========================================================================== *)
(* Proofs                                                                     *)
(* ========================================================================== *)

Section CorrectInvariant.
  Variables s s' : State.

  Lemma InitCorrect : Correct Init.
  Proof. hfcrush. Qed.

  (* Split a goal of the form A ∧ B ∧ ... into n subgoals (A, B, ...).
   * Differs from `repeat split` by not recursively splitting top-level
   * conjuncts (A, B, ...) if they are themselves conjunctions.
   *)
  Ltac split_top :=
    match goal with
    | |- _ ∧ _ => split; [| split_top]
    | |- _     => idtac
    end.

  (* top-level definition because reused in refinement proof *)
  Lemma ML_outState : Next ML_out s = Some s' →
      s.(ml_tl) = Green
    ∧ s' = {| a := s.(a)+1
           ;  ml_tl := if (s.(a)+1+s.(b) <? d) then Green else Red
           ;  il_tl := Red
           ;  ml_pass := true
           ;  b := s.(b); c := s.(c); il_pass := s.(il_pass)
           |}.
  Proof. intros; destruct s; sauto. Qed.

  Lemma ML_outCorrect : ∀ (Hc : Correct s) (Hn : Next ML_out s = Some s'), Correct s'.
  Proof.
    intros; apply ML_outState in Hn; unfold Correct; split_top;
      sauto unfold: MlTlSafe, IlTlSafe.
  Qed.

  Lemma ML_inCorrect : Correct s → Next ML_in s = Some s' → Correct s'.
  Proof. sauto unfold: MlTlSafe. Qed.

  Lemma IL_inCorrect : Correct s → Next IL_in s = Some s' → Correct s'.
  Proof.
    assert (L : Next IL_in s = Some s' →
        0 < s.(a)
      ∧ s' = {| a := s.(a)-1
             ;  b := s.(b)+1
             ;  c := s.(c); ml_tl := s.(ml_tl);  il_tl := s.(il_tl); ml_pass := s.(ml_pass); il_pass := s.(il_pass)
             |}) by now sauto.
    intros; sauto use: L unfold: MlTlSafe, IlTlSafe.
  Qed.

  Lemma IL_outState : Next IL_out s = Some s' →
      s.(il_tl) = Green
    ∧ s' = {| b := s.(b)-1
           ;  c := s.(c)+1
           ;  ml_tl := Red
           ;  il_tl := if (0 <? s.(b)-1) then Green else Red
           ;  il_pass := true
           ;  a := s.(a); ml_pass := s.(ml_pass)
           |}.
  Proof. intros; destruct s; sauto. Qed.

  Lemma IL_outCorrect : ∀ (Hc : Correct s) (Hn : Next IL_out s = Some s'), Correct s'.
  Proof.
    intros; apply IL_outState in Hn; unfold Correct; split_top;
      sauto unfold: MlTlSafe, IlTlSafe.
  Qed.

  Lemma ML_tl_greenCorrect : Correct s → Next ML_tl_green s = Some s' → Correct s'.
  Proof.
    assert (L : Next ML_tl_green s = Some s' →
        s.(ml_tl) = Red ∧ (s.(a) + s.(b) < d) ∧ s.(c) = 0 ∧ s.(il_pass) = true
      ∧ s' = {| ml_tl := Green
             ;  il_tl := Red
             ;  ml_pass := false
             ;  a := s.(a); b := s.(b); c := s.(c); il_pass := s.(il_pass)
             |}) by now intros; destruct s; sauto.
    intros; unfold Correct; split_top; sauto use: L unfold: MlTlSafe, IlTlSafe, MlTlPass.
  Qed.

  Lemma IL_tl_greenCorrect : Correct s → Next IL_tl_green s = Some s' → Correct s'.
  Proof.
    assert (L : Next IL_tl_green s = Some s' →
        s.(il_tl) = Red ∧ (s.(a) = 0) ∧ (0 < s.(b)) ∧ s.(ml_pass) = true
      ∧ s' = {| ml_tl := Red
             ;  il_tl := Green
             ;  il_pass := false
             ;  a := s.(a); b := s.(b); c := s.(c); ml_pass := s.(ml_pass)
             |}) by now intros; destruct s; sauto.
    intros; unfold Correct; split_top; sauto use: L unfold: MlTlSafe, IlTlSafe, IlTlPass.
  Qed.

  Lemma StutterCorrect : Correct s → Next Stutter s = Some s' → Correct s'.
  Proof. intros. sauto. Qed.

  Theorem SpecCorrect : ∀ (e : Event),
      Correct Init
    ∧ (Correct s → Next e s = Some s' → Correct s').
  Proof.
    split.
    - apply InitCorrect.
    - destruct e; apply ML_inCorrect || apply ML_outCorrect || apply IL_inCorrect || apply IL_outCorrect
        || apply ML_tl_greenCorrect || apply IL_tl_greenCorrect || apply StutterCorrect.
  Qed.
End CorrectInvariant.


Section Refinement.
  (* In this section, we explicitly qualify C2 definitions for readability purpose. *)
  Variables s1 s1' : C1.State.
  Variables s2 s2' s2'' : C2.State.

  (* f is an homomorphism from the C2 spec to the C1 spec.
  * The constraints of f are:
  * - initial states are sent to initial states
  * - the following diagram commutes, where s? are states and e? are events:
  *
  *           fₑ e2
  *  C1:   s1 -----> s1'
  *         ^         ^
  *       fₛ|         |fₛ
  *  C2:   s2 -----> s2'
  *             e2
  *)

  (* fₛ is the state component of f. *)
  Definition fₛ : C2.State → C1.State := toS1.

  (* fₑ is the event component of f. *)
  Definition fₑ (e2 : C2.Event) : C1.Event :=
    match e2 with
    | C2.ML_in       => C1.ML_in
    | C2.ML_out      => C1.ML_out
    | C2.IL_in       => C1.IL_in
    | C2.IL_out      => C1.IL_out
    | C2.ML_tl_green => C1.Stutter
    | C2.IL_tl_green => C1.Stutter
    | C2.Stutter     => C1.Stutter
    end.

  Lemma RefineInit : fₛ C2.Init = C1.Init.
  Proof. sauto. Qed.

  Lemma RefineML_in :
    ∀ (nx2 : C2.Next C2.ML_in s2 = Some s2'),
      C1.Next (fₑ C2.ML_in) (fₛ s2) = Some (fₛ s2').
  Proof. sauto. Qed.

  Lemma RefineML_out :
    ∀ (Hc : C2.Correct s2) (nx2 : C2.Next C2.ML_out s2 = Some s2'),
      C1.Next (fₑ C2.ML_out) (fₛ s2) = Some (fₛ s2').
  Proof.
    intros; apply ML_outState in nx2; sauto use: ML_outCorrect
      unfold: MlTlSafe, IlTlSafe, NextML_out.
  Qed.

  Lemma RefineIL_in :
    ∀ (nx2 : C2.Next C2.IL_in s2 = Some s2'),
      C1.Next (fₑ C2.IL_in) (fₛ s2) = Some (fₛ s2').
  Proof. sauto. Qed.

  Lemma RefineIL_out :
    ∀ (Hc : C2.Correct s2)
      (Hn : C2.Next C2.IL_out s2 = Some s2'),
      C1.Next (fₑ C2.IL_out) (fₛ s2) = Some (fₛ s2').
  Proof.
    intros; apply IL_outState in Hn; sauto use: IL_outCorrect
      unfold: MlTlSafe, IlTlSafe, NextIL_out.
  Qed.

  Lemma RefineML_tl_green :
    ∀ (nx2 : C2.Next C2.ML_tl_green s2 = Some s2'),
      C1.Next (fₑ C2.ML_tl_green) (fₛ s2) = Some (fₛ s2').
  Proof. sauto. Qed.

  Lemma RefineIL_tl_green :
    ∀ (nx2 : C2.Next C2.IL_tl_green s2 = Some s2'),
      C1.Next (fₑ C2.IL_tl_green) (fₛ s2) = Some (fₛ s2').
  Proof. sauto. Qed.

  Lemma RefineStutter :
    ∀ (nx2 : C2.Next C2.Stutter s2 = Some s2'),
      C1.Next (fₑ C2.Stutter) (fₛ s2) = Some (fₛ s2').
  Proof. sauto. Qed.

  Theorem Refine : ∀ (e2 : C2.Event),
      fₛ C2.Init = C1.Init
    ∧ (Correct s2 → C2.Next e2 s2 = Some s2' → C1.Next (fₑ e2) (fₛ s2) = Some (fₛ s2')).
  Proof.
    split.
    - auto using RefineInit.
    - destruct e2; auto using RefineML_in, RefineML_out, RefineIL_in,
        RefineIL_out, RefineML_tl_green, RefineIL_tl_green, RefineStutter.
  Qed.
End Refinement.