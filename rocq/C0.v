(**************************************************************************************************)
(* First model of course 02: Controlling cars on a bridge                                         *)
(*                                                                                                *)
(* This model is only concerned with limiting the number of cars on the                           *)
(* island and brige.                                                                              *)
(*                                                                                                *)
(* See https://web-archive.southampton.ac.uk/deploy-eprints.ecs.soton.ac.uk/112/1/sld.ch2.car.pdf *)
(*                                                                                                *)
(*                      ML_out                                                                    *)
(*  -----------------   <-----   ----------                                                       *)
(* | Island + Bridge |          | MainLand |                                                      *)
(*  -----------------   ----->   ----------                                                       *)
(*                      ML_in                                                                     *)
(*                                                                                                *)
(**************************************************************************************************)

From Stdlib Require Import Unicode.Utf8 Arith.
From Hammer Require Import Tactics.
From CarsOnBridge Require Import Common.

(* ========================================================================== *)
(* Specification                                                              *)
(* ========================================================================== *)

(*       ML_out
island    <- 
and             Mainland
bridge    ->
          ML_in

d = max cars on island + bridge
*)

(* record a bit overkill here but for uniformity with further models *)
Record State := mkState
  { n : ℕ (* number of cars on island + brige. *)
  }.

Inductive Event := ML_in | ML_out | Stutter.

Definition Init : State := mkState 0.

Definition Next (e : Event) (s : State) : option State :=
  match e with
  | ML_in   => if 0 <? s.(n) then Some (mkState (s.(n) - 1)) else None
  | ML_out  => if s.(n) <? d then Some (mkState (s.(n) + 1)) else None
  | Stutter => Some s
  end.


(* ========================================================================== *)
(* Invariants                                                                 *)
(* ========================================================================== *)

Definition Correct (s : State) : Prop :=
  s.(n) ≤ d.

Definition DeadlockFree (s : State) : Prop :=
    0 < s.(n)  (* ML_in guard *)
  ∨ s.(n) < d. (* ML_out guard *)


(* ========================================================================== *)
(* Proofs                                                                     *)
(* ========================================================================== *)

Section Invariants.
  Variables (e : Event) (s s' : State).

  Theorem SpecCorrect :
      Correct Init
    ∧ (Correct s → Next e s = Some s' → Correct s').
  Proof. split; destruct e; sauto unfold: Correct. Qed.

  Theorem SpecDeadlockFree :
      DeadlockFree Init
    ∧ (DeadlockFree s → Next e s = Some s' → DeadlockFree s').
  Proof. split; destruct e; sauto unfold: DeadlockFree use: Ax2. Qed.
End Invariants.