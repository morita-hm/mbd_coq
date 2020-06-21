
From Coq Require Import ssreflect.
Require Import Bool.

Definition truthtable c1 c2 c3 :=
  match c1, c2, c3 with
  | true, true, true => true
  | _, _, _ => false
  end.

Goal forall (c1 c2 c3 : bool), truthtable c1 c2 c3 = c1 && c2 && c3.
  case.
  - case.
    + case.
      * done.
      * done.
    + case.
      * done.
      * done.
  - case.
    + case.
      * done.
      * done.
    + case.
      * done.
      * done.
Qed.        
