
Require Import ZArith.
Require Import Omega.
Require Import Bool.
From Coq Require Import ssreflect.


Open Scope Z_scope.

Goal forall (x y : Z),
    x + y = 2 -> 2 * x + y = 5 -> x = 3.  
Proof.
  move=> x y H1 H2.
  omega.
Qed.  

Definition Step (b : bool) := if b then 5 else 0.

Goal forall b, b = true -> Step b = 5.
Proof.
  move=> b Ht.
  by rewrite /Step Ht.
Qed.

Definition OverThresholdLe (m x : Z) := m <=? x.
Definition OverThresholdLt (m x : Z) := m <? x.
Definition InnerRange (m1 m2 x : Z) := (m1 <=? x) && (x <=? m2).

Goal forall x, 5 <= x -> OverThresholdLe 5 x = true.
Proof.
  move=> x Ht.
  rewrite /OverThresholdLe.
    by apply/Z.leb_le.
Qed.

Goal forall x, 5 <= x <-> OverThresholdLe 5 x = true.
Proof.
  rewrite /OverThresholdLe.
  split.
  - move=> Hle.
    move/Z.leb_le in Hle.
      by [].
  - move=> Hleb.      
      by apply/Z.leb_le.
Qed.

Goal forall x, x < 5 -> OverThresholdLe 5 x = false.
Proof.
  move=> x Ht.
  rewrite /OverThresholdLe.
    by apply/Z.leb_gt.
Qed.


Goal forall x, 5 < x -> OverThresholdLt 5 x = true.
Proof.
  move=> x Ht.
  rewrite /OverThresholdLt.
    by apply/Z.ltb_lt.
Qed.

Goal forall x, x <= 5 -> OverThresholdLt 5 x = false.
Proof.
  move=> x Ht.
  rewrite /OverThresholdLt.
    by apply/Z.ltb_ge.
Qed.


Goal forall x, 1 <= x <= 5 <-> InnerRange 1 5 x = true.
Proof.
  rewrite /InnerRange.
  split.
  - case.
    move=> H1 H5.
    move/Z.leb_le in H1.
    move/Z.leb_le in H5.
      by rewrite H1 H5.
  - move=> H15.
    move/andb_true_iff in H15.
    case: H15 => H1 H5.
    move/Z.leb_le in H1.
    move/Z.leb_le in H5.
    split.
    + done.
    + done.
Qed.

Goal forall x, x < 1 \/ 5 < x <-> InnerRange 1 5 x = false.
Proof.
  rewrite /InnerRange.
  split.
  - case => H1.
    + apply/andb_false_iff.
      left.
        by apply/Z.leb_gt.
    + apply/andb_false_iff.
      right.
        by apply/Z.leb_gt.
  - move=> H15.
    move/andb_false_iff in H15.
    case: H15.
    + move=> H1.
      move/Z.leb_gt in H1.
        by left.
    + move=> H5.
      move/Z.leb_gt in H5.
        by right.
Qed.


