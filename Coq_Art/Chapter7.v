Require Import Arith Omega.

Definition divides (n m:nat) := exists p:nat, p*n = m.

Ltac first_step :=  
  unfold divides;
  intros.

Lemma divides_O : forall n:nat, divides n 0.
  first_step.
  exists 0.
  ring.
Qed.

Lemma divides_plus : forall n m:nat, divides n m -> divides n (n+m).
  first_step.
  destruct H.
  exists (S x).
  rewrite mult_succ_l.
  omega.
Qed.

Lemma not_divides_plus : forall n m:nat, ~ divides n m -> ~ divides n (n+m).
  first_step.
  unfold not in *.
  intros.
  apply H.
  destruct H0.
  exists(x - 1).
  rewrite mult_minus_distr_r.
  omega.
Qed.

Lemma not_divides_lt : forall n m:nat, 0<m ->  m<n -> ~ divides n m.
  first_step.
  unfold not.
  intros.
  destruct H1.
  rewrite <- H1 in *.
  destruct x.
  omega.
  clear H H1.
  absurd(S x * n < n).
  apply le_not_lt.
  rewrite mult_succ_l.
  apply le_plus_r.
  assumption.
Qed.

Lemma not_lt_2_divides : forall n m:nat, n <> 1 -> n < 2 -> 0 < m -> ~ divides n m.
  first_step.
  unfold not.
  intros.
  destruct H2.
  destruct n.
  omega.
  destruct n.
  auto.
  absurd(S (S n) < 2).
  omega.
  auto.
Qed.

Lemma le_plus_minus : forall n m:nat, le n m -> m = n+(m-n).
  intros.
  omega.
Qed.

Lemma lt_lt_or_eq : forall n m:nat, n < S m ->  n < m \/ n = m.
  intros.
  omega. 
Qed.

Goal forall n p:nat, n <= p -> p < S n -> n = p.
  intros.
  omega.
Qed.