Require Import Arith Recdef Omega.

Set Implicit Arguments.

Definition nandb (b1:bool) (b2:bool) : bool := negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
  trivial.
Qed.

Example test_nandb2: (nandb false false) = true.
  trivial.
Qed.

Example test_nandb3: (nandb false true) = true.
  trivial.
Qed.

Example test_nandb4: (nandb true true) = false.
  trivial.
Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) := andb (andb b1 b2) b3.

Example test_andb31: (andb3 true true true) = true.
  trivial.
Qed.

Example test_andb32: (andb3 false true true) = false.
  trivial.
Qed.

Example test_andb33: (andb3 true false true) = false.
  trivial.
Qed.

Example test_andb34: (andb3 true true false) = false.
  trivial.
Qed.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => mult (factorial n') n
  end.

Example test_factorial1: (factorial 3) = 6.
  trivial.
Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
  trivial.
Qed.

Fixpoint blt_nat (n m : nat) : bool :=
  match n, m with
  | O, O => false
  | O, S _ => true
  | S _, O => false
  | S n', S m' => blt_nat n' m'
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
  trivial.
Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
  trivial.
Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
  trivial.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
  auto.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
  auto.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
  intros.
  simpl in *.
  destruct n;
  trivial.
Qed.

Theorem identity_fn_applied_twice : 
  forall(f : bool -> bool), (forall(x : bool), f x = x) ->
    forall(b : bool), f (f b) = b.
  intros.
  remember (H b).
  rewrite e.
  trivial.
Qed.

Theorem andb_eq_orb : 
  forall(b c : bool), (andb b c = orb b c) -> b = c.
  intros.
  destruct b;
  auto.
Qed.

Inductive bnat : Set :=
| BZero
| BEven : bnat -> bnat
| BOdd : bnat -> bnat.

Fixpoint BInc b :=
  match b with
  | BZero => BOdd BZero
  | BEven b' => BOdd b'
  | BOdd b' => BEven (BInc b')
  end.

Fixpoint BPlus b n :=
  match n with
  | O => b
  | S m => BInc (BPlus b m)
  end.

Fixpoint bnat_to_nat b :=
  match b with
  | BZero => O
  | BEven b' => 2 * (bnat_to_nat b')
  | BOdd b' => 2 * (bnat_to_nat b') + 1
  end.

Fixpoint nat_to_bnat b :=
  match b with
  | O => BZero
  | S n => BInc (nat_to_bnat n)
  end.

Theorem BInc_correct : forall b, bnat_to_nat (BInc b) = S (bnat_to_nat b).
  intros.
  induction b;
  simpl in *;
  omega.
Qed.

Fixpoint Normalize b :=
  match b with
  | BZero => BZero
  | BOdd n => BOdd (Normalize n)
  | BEven n => 
    match Normalize n with
    | BZero => BZero
    | m => BEven m
    end
  end.

Theorem BPlus_correct :
  forall b m, bnat_to_nat (BPlus b m) = (bnat_to_nat b) + m.
  intros.
  induction m;
  simpl in *.
  trivial.
  rewrite BInc_correct.
  omega.
Qed.

Theorem eq_BPlus : forall n, nat_to_bnat n = BPlus BZero n.
  induction n.
  trivial.
  simpl in *.
  f_equal.
  trivial.
Qed.

Goal forall n, bnat_to_nat (nat_to_bnat n) = n.
  induction n.
  trivial.
  simpl in *.
  remember(nat_to_bnat n).
  destruct b;
  subst;
  simpl in *.
  trivial.
  omega.
  repeat rewrite plus_0_r in *.
  replace(bnat_to_nat (BInc b)) with (S (bnat_to_nat b)).
  omega.
  symmetry.
  apply BInc_correct.
Qed.

Theorem Normalize_correct : forall b,
  bnat_to_nat (Normalize b) = bnat_to_nat b.
  induction b.
  trivial.
  simpl in *.
  replace
    (bnat_to_nat b + (bnat_to_nat b + 0)) with
    (bnat_to_nat b + bnat_to_nat b).
  remember(Normalize b).
  destruct b0;
  simpl in *;
  omega.
  auto.
  simpl in *.
  auto.
Qed.

Theorem Normalize_BOdd_Greater :
  forall b b', Normalize b = BOdd b' -> bnat_to_nat b > 0.
  induction b;
  intros.
  discriminate.
  simpl in *.
  destruct(Normalize b).
  discriminate.
  discriminate.
  discriminate.
  simpl in *.
  omega.
Qed.

Theorem Normalize_BEven_Greater :
  forall b b', Normalize b = BEven b' -> bnat_to_nat b > 0.
  induction b;
  try discriminate.
  intros.
  simpl in *.
  remember(Normalize b).
  destruct b0.
  admit.
  inversion H.
  subst.
  assert(bnat_to_nat b > 0).
  eauto.
  omega.
  inversion H.
  subst.
  assert(bnat_to_nat b > 0).
  eapply Normalize_BOdd_Greater.
  eauto.
  omega.
Qed.

Goal forall b, nat_to_bnat (bnat_to_nat b) = Normalize b.
  intros.
  induction b;
  trivial;
  simpl in *;
  try rewrite plus_0_r in *.
  remember(Normalize b).
  destruct b0.
  induction b;
  trivial;
  simpl in *.
  remember(Normalize b).
  destruct b0.
  rewrite <- Normalize_correct.
  rewrite <- Heqb1.
  trivial.
  discriminate.
  discriminate.
  discriminate.
  remember(@Normalize_BEven_Greater b b0).
  clear Heqg.
  remember (bnat_to_nat b).
  destruct n.
  discriminate.
  simpl in *.
  rewrite plus_comm.
  simpl in *.
  rewrite <- IHb.
  clear Heqn.
  clear IHb.
  clear g.
  induction n.
  trivial.
  simpl in *.
  rewrite plus_comm.
  simpl in *.
  rewrite IHn.
  trivial.
  remember(Normalize b).
  destruct b1.
  discriminate.
  discriminate.
  inversion Heqb0.
  subst.
  rewrite <- IHb.
  destruct(bnat_to_nat b).
  discriminate.
  clear IHb.
  induction n.
  trivial.
  simpl in *.
  rewrite plus_comm in *.
  simpl in *.
  rewrite IHn.
  trivial.
  rewrite <- IHb.
  clear IHb.
  induction(bnat_to_nat b).
  trivial.
  simpl in *.
  replace (n + S n + 1) with (S n + n + 1).
  simpl in *.
  rewrite IHn.
  trivial.
  omega.
Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.