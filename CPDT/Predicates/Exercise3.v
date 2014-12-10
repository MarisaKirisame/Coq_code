Require Import Arith Omega.

Inductive mult n : nat -> Prop := 
| zero : mult n 0
| succ : forall m, mult n m -> mult n (n + m).

Definition mult_6_10 n := (mult 6 n) \/ (mult 10 n).

Theorem mult_exists : forall n m, mult n m -> exists l, n * l = m.
  induction 1.
  eauto.
  destruct IHmult.
  exists (S x).
  rewrite mult_succ_r.
  subst.
  omega.
Qed.

Goal ~(mult_6_10 13).
  unfold not.
  intros.
  destruct H;
  apply mult_exists in H;
  destruct H;
  omega.
Qed.

Goal forall n, mult_6_10 n -> ~(exists m, n = 2 * m + 1).
  unfold not.
  intros.
  destruct H0.
  destruct H;
  apply mult_exists in H;
  destruct H;
  subst;
  omega.
Qed.