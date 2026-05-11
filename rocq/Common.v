From Stdlib Require Import Arith.

Notation ℕ := nat.
Notation "x && y" := (andb x y).

Parameter d : ℕ.
Axiom Ax2 : d > 0.
