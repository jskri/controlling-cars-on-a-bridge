--------------------------- MODULE CarsOnBridge1 ---------------------------
(***************************************************************************)
(* Second model of course 02: Controlling cars on a bridge                 *)
(*                                                                         *)
(* Introducing the bridge.                                                 *)
(*                                                                         *)
(* See https://www.event-b.org/A_ch2.pdf                                   *)
(*                                                                         *)
(*               IL_in                       ML_out                        *)
(*   ---------   <-----   ----------------   <-----   ----------           *)
(*  | Island  |          | One Way Bridge |          | MainLand |          *)
(*   ---------   ----->   ----------------   ----->   ----------           *)
(*               IL_out                       ML_in                        *)
(*                                                                         *)
(***************************************************************************)
EXTENDS CarsOnBridgeConstants, TLAPS

(***************************************************************************)
(*                               a                                         *)
(*   ---------   <---------------------------------   ----------           *)
(*  |    b    |            One Way Bridge            |          |          *)
(*   ---------   --------------------------------->   ----------           *)
(*                               c                                         *)
(***************************************************************************)
VARIABLES a, \* Number of cars going to the island.
          b, \* Number of cars on the island.
          c  \* Number of cars going to the mainland.
vars == <<a, b, c>>

TypeOK ==
  /\ a \in Nat
  /\ b \in Nat
  /\ c \in Nat

OneWayBridge ==
  \/ a = 0
  \/ c = 0

Init ==
  /\ a = 0
  /\ b = 0
  /\ c = 0

ML_in ==
  /\ c > 0 \* At least one incoming car on the bridge.
  /\ c' = c - 1
  /\ UNCHANGED <<a, b>>

ML_out ==
  /\ a + b + c < d \* Max cars not reached on island + bridge.
  /\ c = 0         \* No car in the mainland direction.
  /\ a' = a + 1
  /\ UNCHANGED <<b, c>>

\* No car count check here because it is done when leaving mainland.
IL_in ==
  /\ a > 0 \* At least one incoming car on the bridge.
  /\ a' = a - 1
  /\ b' = b + 1
  /\ UNCHANGED c

IL_out ==
  /\ a = 0 \* No incoming car on the bridge.
  /\ b > 0
  /\ b' = b - 1
  /\ c' = c + 1
  /\ UNCHANGED a

Next ==
  \/ ML_in
  \/ ML_out
  \/ IL_in
  \/ IL_out

Spec ==
  /\ Init
  /\ [][Next]_vars
-----------------------------------------------------------------------------
THEOREM SpecTypeOK == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, ML_in, ML_out, IL_in, IL_out, vars
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM SpecOneWayBridge == Spec => []OneWayBridge
<1>1. Init => OneWayBridge
  BY DEF Init, OneWayBridge
<1>2. OneWayBridge /\ [Next]_vars => OneWayBridge'
  BY DEF OneWayBridge, Next, ML_in, ML_out, IL_in, IL_out, vars
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec
-----------------------------------------------------------------------------
n == a + b + c
M0 == INSTANCE CarsOnBridge0

Correct == TypeOK /\ OneWayBridge

THEOREM SpecCorrect == Spec => []Correct
BY SpecTypeOK, SpecOneWayBridge DEF Correct

THEOREM Refinement == Spec => M0!Spec
<1>1. Init => M0!Init
  BY DEF Init, M0!Init, n
<1>2. Correct /\ [Next]_vars => [M0!Next]_n
  (* This proof could be compacted but is arguably clearer here. *)
  <2> SUFFICES ASSUME Correct, [Next]_vars
               PROVE  [M0!Next]_n OBVIOUS
  <2> USE DEF Correct, TypeOK
  <2>1. ML_in => M0!ML_in
    BY DEF ML_in, M0!Next, n, M0!ML_in
  <2>2. ML_out => M0!ML_out
    BY DEF ML_out, M0!Next, n, M0!ML_out
  <2>3. IL_in => UNCHANGED n
    BY DEF IL_in, n
  <2>4. IL_out => UNCHANGED n
    BY DEF IL_out, n
  <2>5. UNCHANGED vars => UNCHANGED n
    BY DEF vars, n
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, M0!Next
<1>3. QED
  BY <1>1, <1>2, SpecCorrect, PTL DEF Spec, M0!Spec
=============================================================================