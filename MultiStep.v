
Require Import Arith.
Require Import List.

Fixpoint rcons {X : Type} (s : list X) (x : X) :=
  match s with
  | nil => x :: nil
  | y :: ys => y :: (rcons ys x)
  end.


Fixpoint timechart_elem {A : Type} (x0 : nat*A) (s : list (nat*A)) (t : nat) :=
  match s with
  | nil =>
    let (t', a) := x0 in (t, a)
  | x :: xs =>
    let (t', a) := x in
    if t <? t' then let (t0, a0) := x0 in (t,a0) else timechart_elem x xs t
  end.


Fixpoint timechart {A : Type} (x0 : nat*A) (s : list (nat*A)) (t : nat) :=
  match t with
  | S t' => rcons (timechart x0 s t') (timechart_elem x0 s t) 
  | O => timechart_elem x0 s O :: nil
  end.

