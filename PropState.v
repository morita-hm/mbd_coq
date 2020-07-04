(* Prop 型でステートマシンを記述する例 *)
From Coq Require Import ssreflect.

Inductive sub_status_S1 :=
| S1_1
| S1_2.

Inductive status :=
| DEFAULT
| S0
| S1 : sub_status_S1 -> status.

Variables ps cs : status.
Variables in1 in2 flag out1 out2 ON OFF : Type.

Axiom entry_S0 :
  ps = DEFAULT ->
  cs = S0 ->
  out1 = OFF /\ out2 = OFF.

Axiom flag_on : in1 = ON /\ in2 = ON -> flag = ON.
Axiom flag_off : ~(in1 = ON /\ in2 = OFF) -> flag = OFF.

Axiom trans_S0_S1 :
  ps = S0 ->
  flag = ON ->
  cs = S1 S1_1.

Axiom during_S0 :
  ps = S0 ->
  flag = OFF ->
  cs = S0 /\ out1 = OFF /\ out2 = OFF.


Axiom entry_S1 :
  ps <> S1 S1_1 ->
  cs = S1 S1_1 ->
  out1 = ON /\ out2 = ON.


Goal ps = S0 -> in1 = ON -> in2 = ON -> out1 = ON /\ out2 = ON.
Proof.
  move=> Hs0 H1 H2.
  apply/entry_S1.
  - by rewrite Hs0.
  - apply/trans_S0_S1.
    + done.
    + apply/flag_on.
      split.
      * done.
      * done.
Qed.

