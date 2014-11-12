Set Implicit Arguments.
Require Import Arith.

Definition plus'(l r:nat) : nat :=
  nat_rec (fun _ => nat) r (fun _ => fun x => S x) l.

Definition pred_partial: forall (n : nat), n <> 0 ->  nat.
  intros n; case n.
  intros h; elim h; reflexivity.
  intros p h'; exact p.
Defined.

Theorem le_2_n_not_zero: forall (n : nat), 2 <= n ->  (n <> 0).
  intros n Hle; elim Hle; intros; discriminate.
Qed.

Scheme le_ind_max := Induction for le Sort Prop.

Theorem le_2_n_pred:
  forall (n : nat) (h : 2 <= n),  (pred_partial (le_2_n_not_zero h) <> 0).
  apply le_ind_max.
  intuition.
  simpl in *.
  inversion H.
  intuition.
  simpl in *.
  subst.
  inversion l.
Qed.


