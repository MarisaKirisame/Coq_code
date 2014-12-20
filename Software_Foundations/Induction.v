Require Import Omega.
Load Basics.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
  destruct b, c;
  trivial.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
  intros.
  induction n.
  trivial.
  simpl.
  trivial.
Qed.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
  intros.
  induction n.
  trivial.
  simpl.
  rewrite IHn.
  trivial.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
  intros.
  induction n.
  trivial.
  simpl.
  rewrite IHn.
  apply plus_n_Sm.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
  intros.
  induction n.
  trivial.
  simpl.
  rewrite IHn.
  trivial.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
  induction n.
  trivial.
  simpl in *.
  rewrite IHn.
  f_equal.
  apply plus_n_Sm.
Qed.

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
  intros.
  assert(n + (m + p) = n + m + p).
  apply plus_assoc.
  rewrite H.
  assert(m + (n + p) = m + n + p).
  apply plus_assoc.
  rewrite H0.
  rewrite plus_comm.
  symmetry.
  rewrite plus_comm.
  f_equal.
  rewrite plus_comm.
  trivial.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
  intros.
  induction n.
  induction m.
  trivial.
  simpl.
  trivial.
  simpl.
  rewrite <- IHn.
  clear IHn.
  induction m.
  trivial.
  simpl in *.
  f_equal.
  rewrite IHm.
  apply plus_swap.
Qed.

Theorem negb_eq_negb : forall b c, negb b = negb c -> b = c.
  intros.
  destruct b, c;
  trivial;
  discriminate.
Qed.

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
  induction n.
  trivial.
  simpl in *.
  remember(evenb n).
  apply negb_eq_negb.
  destruct b;
  rewrite <- IHn;
  trivial.
Qed.

Theorem ble_nat_refl : forall n : nat,
  true = ble_nat n n.
  induction n;
  trivial.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
  induction n;
  trivial.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
  eauto with *.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat, 
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
  intros.
  induction p;
  trivial.
Qed.

Theorem S_nbeq_0 : forall n : nat,
  beq_nat (S n) 0 = false.
  induction n;
  trivial.
Qed.

Theorem mult_1_l : forall n : nat, 1 * n = n.
  induction n.
  trivial.
  simpl.
  clear IHn.
  induction n.
  trivial.
  f_equal.
  trivial.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb
      (negb b)
      (negb c)) = true.
  destruct b, c;
  trivial.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
  induction p.
  repeat rewrite mult_0_r.
  trivial.
  rewrite mult_comm.
  simpl.
  assert(p * (n + m) = (n + m) * p).
  apply mult_comm.
  rewrite H.
  rewrite IHp.
  assert(n * S p = S p * n).
  apply mult_comm.
  rewrite H0.
  assert(m * S p = S p * m).
  apply mult_comm.
  rewrite H1.
  simpl.
  repeat rewrite <- plus_assoc.
  f_equal.
  symmetry.
  rewrite plus_comm.
  rewrite <- plus_assoc.
  f_equal.
  rewrite plus_comm.
  f_equal;
  apply mult_comm.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
  induction n.
  trivial.
  simpl.
  intros.
  rewrite IHn.
  rewrite mult_plus_distr_r.
  trivial.
Qed.

Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
  induction n;
  trivial.
Qed.

Theorem plus_swap' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
  intros.
  replace(n + (m + p)) with (n + m + p).
  replace(m + (n + p)) with (m + n + p).
  rewrite plus_comm.
  symmetry.
  rewrite plus_comm.
  f_equal.
  rewrite plus_comm.
  trivial.
  rewrite plus_assoc.
  trivial.
  rewrite plus_assoc.
  trivial.
Qed.

Exercise: 5 stars, advanced (binary_inverse)
This exercise is a continuation of the previous exercise about binary numbers. You will need your definitions and theorems from the previous exercise to complete this one.
(a) First, write a function to convert natural numbers to binary numbers.
Then prove that starting with any natural number, converting to binary,
then converting back yields the same natural number you started with.
(b) You might naturally think that we should also prove the opposite direction:
that starting with a binary number, converting to a natural,
and then back to binary yields the same number we started with.
However, it is not true! Explain what the problem is.
(c) Define a function normalize from binary numbers to binary numbers
such that for any binary number b, converting to a natural and
then back to binary yields (normalize b). Prove it.
Again, feel free to change your earlier definitions if this helps here.
