Set Implicit Arguments.

Require Import Program Arith Omega Recdef.

Theorem minus_plus_equal n m : ~ n < m -> n - m + m = n.
  omega.
Defined.

Function nat_n_rect
  (step : {n : nat | n > 0})
    (n : nat)
      (P : nat -> Type)
        (p2 : (forall m, m < (` step) -> P m))
          (p3 : (forall n, P n -> P (n + (` step)))) 
            { wf lt n } :
              P n :=
  match lt_dec n (` step) with
  | left p => p2 _ p
  | right p => 
      (fun x : (n - (` step) + (` step) = n) =>
        eq_rect
          (n - (` step) + (` step))
          P
          (p3 (n - (` step))(nat_n_rect step (n - (` step)) P p2 p3))
          n
          x)
      (minus_plus_equal p)
  end.
  destruct step.
  unfold proj1_sig.
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
