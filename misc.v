Require Import
  Arith
  Omega
  Recdef.

Definition sig_extract: forall (A:Set) (P:A -> Prop), sig P -> A.
  intros.
  destruct H.
  auto.
Defined.

Theorem minus_plus_equal n m : ~ n < m -> n - m + m = n.
  omega.
Defined.

Function nat_n_rect
  (step : {n : nat | n > 0})
    (n : nat)
      (P : nat -> Type)
        (p2 : (forall m, m < (sig_extract _ _ step) -> P m))
          (p3 : (forall n, P n -> P (n + (sig_extract _ _ step)))) 
            { wf lt n } :
              P n :=
  match lt_dec n (sig_extract _ _ step) with
  | left p => p2 _ p
  | right p => 
      (fun x : (n - (sig_extract _ _ step) + (sig_extract _ _ step) = n) =>
        eq_rect
          (n - (sig_extract _ _ step) + (sig_extract _ _ step))
          P
          (p3 (n - (sig_extract _ _ step))(nat_n_rect step (n - (sig_extract _ _ step)) P p2 p3))
          n
          x)
      (minus_plus_equal n (sig_extract _ _ step) p)
  end.
  destruct step.
  unfold sig_extract.
  intros.
  omega.
  unfold well_founded.
  induction a.
  split; intros p H; inversion H.
  split.
  intros y H0.
  case (le_lt_or_eq _ _ H0).
  intro; apply Acc_inv with a; auto with arith.
  intro e; injection e; intro e1; rewrite e1; assumption.
Defined.
