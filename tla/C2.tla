-------------------------------- MODULE C2 --------------------------------
(***************************************************************************)
(* Third model of course 02: Controlling cars on a bridge                  *)
(*                                                                         *)
(* Introducing traffic lights.                                             *)
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
EXTENDS Common, TLAPS

(***************************************************************************)
(*                               a               ml_tl                     *)
(*   ---------   <---------------------------------   ----------           *)
(*  |    b    |            One Way Bridge            |          |          *)
(*   ---------   --------------------------------->   ----------           *)
(*            il_tl              c                                         *)
(***************************************************************************)

VARIABLES a,       (* Number of cars going to the island. *)
          b,       (* Number of cars on the island. *)
          c,       (* Number of cars going to the mainland. *)
          ml_tl,   (* Mainland's traffic light. *)
          il_tl,   (* Island's traffic light. *)
          ml_pass, (* True if at least one car passed since ml tl turned green. *)
          il_pass  (* True if at least one car passed since il tl turned green. *)

(* ml_pass and il_pass avoid that traffic lights turn red alternatively without
 * any car has passed. *)
m1_vars == <<a, b, c>>
m2_vars == <<ml_tl, il_tl, ml_pass, il_pass>>
vars == <<m1_vars, m2_vars>>

Color == {"green", "red"}

C1 == INSTANCE C1 (* naming OK: modules and instances have different namespaces *)
-----------------------------------------------------------------------------
TypeOK ==
  /\ C1!TypeOK
  /\ ml_tl \in Color
  /\ il_tl \in Color
  /\ ml_pass \in BOOLEAN
  /\ il_pass \in BOOLEAN

(* Green implies the guard of C1!ML_out. *)
MlTlSafe ==
  ml_tl = "green" => ( /\ a + b < d
                       /\ c = 0 )

(* Green implies the guard of C1!IL_out. *)
IlTlSafe ==
  il_tl = "green" => ( /\ a = 0
                       /\ b > 0 )

(* Can be derived from C1!OneWayBridge, MlTlSafe and IlTlSafe. *)
AtLeastOneTrafficLightIsRed ==
  \/ ml_tl = "red"
  \/ il_tl = "red"

MlTlPass ==
  ml_tl = "red" => ml_pass

IlTlPass ==
  il_tl = "red" => il_pass
-----------------------------------------------------------------------------
Init ==
  /\ C1!Init
  /\ ml_tl = "red"
  /\ il_tl = "red"
  /\ ml_pass = TRUE
  /\ il_pass = TRUE

(* Mainland's traffic light turns green. *)
ML_tl_green ==
  /\ ml_tl = "red"
  /\ a + b < d
  /\ c = 0
  /\ il_pass
  /\ ml_tl' = "green"
  /\ il_tl' = "red"
  /\ ml_pass' = FALSE
  /\ UNCHANGED <<m1_vars, il_pass>>

IL_tl_green ==
  /\ il_tl = "red"
  /\ a = 0
  /\ b > 0
  /\ ml_pass
  /\ ml_tl' = "red"
  /\ il_tl' = "green"
  /\ il_pass' = FALSE
  /\ UNCHANGED <<m1_vars, ml_pass>>

ML_in ==
  /\ C1!ML_in
  /\ UNCHANGED m2_vars

(* The mainland's traffic light turns red if the maximum number of cars
 * is reached. *)
ML_out ==
  /\ ml_tl = "green"
  /\ a' = a + 1
  /\ ml_tl' = IF a' + b < d THEN "green" ELSE "red"
  /\ il_tl' = "red"
  /\ ml_pass' = TRUE
  /\ UNCHANGED <<b, c, il_pass>>

IL_in ==
  /\ C1!IL_in
  /\ UNCHANGED m2_vars

(* The island's traffic light turns red if there is no more car on the
 * island. *)
IL_out ==
  /\ il_tl = "green"
  /\ b' = b - 1
  /\ c' = c + 1
  /\ ml_tl' = "red"
  /\ il_tl' = IF b' > 0 THEN "green" ELSE "red"
  /\ il_pass' = TRUE
  /\ UNCHANGED <<a, ml_pass>>

Next ==
  \/ ML_in
  \/ ML_out
  \/ IL_in
  \/ IL_out
  \/ ML_tl_green
  \/ IL_tl_green

Spec ==
  /\ Init
  /\ [][Next]_vars
-----------------------------------------------------------------------------
Correct ==
  /\ TypeOK
  /\ MlTlSafe
  /\ IlTlSafe
  /\ C1!OneWayBridge
  /\ AtLeastOneTrafficLightIsRed
  /\ MlTlPass
  /\ IlTlPass

THEOREM SpecCorrect == Spec => []Correct
<1>1. Init => Correct
  BY DEF Init, C1!Init, Correct,
    TypeOK, C1!TypeOK, MlTlSafe, IlTlSafe, C1!OneWayBridge,
    AtLeastOneTrafficLightIsRed, MlTlPass, IlTlPass, Color
<1>2. Correct /\ [Next]_vars => Correct'
  <2> SUFFICES ASSUME Correct,[Next]_vars
               PROVE  Correct' OBVIOUS
  <2> USE DEF Correct, TypeOK, C1!TypeOK, MlTlSafe, IlTlSafe, C1!OneWayBridge,
    AtLeastOneTrafficLightIsRed, MlTlPass, IlTlPass,
    Next, vars, m1_vars, m2_vars,
    ML_in, C1!ML_in, ML_out, IL_in, C1!IL_in, IL_out,
    ML_tl_green, IL_tl_green, Color
  <2>1. CASE ML_in BY <2>1
  <2>2. CASE ML_out BY <2>2
  <2>3. CASE IL_in BY <2>3
  <2>4. CASE IL_out BY <2>4
  <2>5. CASE ML_tl_green BY <2>5, Zenon
  <2>6. CASE IL_tl_green BY <2>6, Zenon
  <2>7. CASE UNCHANGED vars BY <2>7
  <2>8. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Refinement == Spec => C1!Spec
<1>1. Init => C1!Init
  BY DEF Init
<1>2. Correct /\ [Next]_vars => [C1!Next]_m1_vars
  BY DEF Correct, TypeOK, C1!TypeOK, MlTlSafe, IlTlSafe, C1!OneWayBridge,
    AtLeastOneTrafficLightIsRed, MlTlPass, IlTlPass,
    Next, vars, m1_vars, m2_vars,
    C1!Next, C1!ML_in, C1!ML_out, C1!IL_in, C1!IL_out,
    ML_in, ML_out, IL_in, IL_out,
    ML_tl_green, IL_tl_green, Color
<1>3. QED
  BY <1>1, <1>2, SpecCorrect, PTL DEF Spec, C1!Spec, C1!vars, m1_vars
=============================================================================
