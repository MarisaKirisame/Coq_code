Require Import Arith Recdef Omega Program.

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

Inductive Normalized : bnat -> Prop :=
| Normalized_BZero : Normalized BZero
| Normalized_BEven : forall n, n <> BZero -> Normalized n -> Normalized (BEven n)
| Normalized_BOdd : forall n, Normalized n -> Normalized (BOdd n).

Goal ~Normalized (BEven BZero).
  intuition.
  dependent induction H.
  tauto.
Qed.

Theorem Normalize_Normalized : forall n, Normalized (Normalize n).
  induction n;
  simpl in *;
  try solve [constructor].
  inversion IHn;
  constructor;
  try discriminate;
  try rewrite H;
  trivial.
  constructor.
  trivial.
Qed.

Theorem double_normalize b : Normalize (Normalize b) = Normalize b.
  induction b;
  intros;
  trivial;
  simpl in *;
  destruct (Normalize b);
  trivial;
  simpl in *;
  destruct (Normalize b0);
  try discriminate;
  f_equal;
  trivial.
Qed.

Theorem BPlus_correct :
  forall b m, bnat_to_nat (BPlus b m) = (bnat_to_nat b) + m.
  intros.
  induction m;
  simpl in *.
  trivial.
  rewrite BInc_correct.
  omega.
Qed.

Theorem nat_to_bnat_n_BPlus_BZero_n : forall n, nat_to_bnat n = BPlus BZero n.
  induction n.
  trivial.
  simpl in *.
  f_equal.
  trivial.
Qed.

Theorem nat_to_bnat_BPlus l r : nat_to_bnat (l + r) = BPlus (nat_to_bnat l) r.
  induction r;
  intros.
  simpl in *.
  auto.
  rewrite Nat.add_succ_r.
  simpl in *.
  f_equal.
  trivial.
Qed.

Theorem bnat_to_nat_correct n : bnat_to_nat (nat_to_bnat n) = n.
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
  rewrite Nat.add_0_r in *.
  destruct (Normalize b) eqn:Heq;
  simpl in *;
  omega.
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
  destruct(Normalize b) eqn:Heq.
  discriminate.
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

Theorem bnat_to_nat_normalize b : bnat_to_nat b = 0 -> Normalize b = BZero.
  intros.
  induction b.
  trivial.
  simpl in *.
  rewrite plus_0_r in *.
  assert(bnat_to_nat b = 0).
  omega.
  intuition.
  rewrite H1.
  trivial.
  simpl in *.
  omega.
Qed.

Theorem normalize_bnat_to_nat b : Normalize b = BZero -> bnat_to_nat b = 0.
  intros.
  induction b;
  trivial;
  simpl in *;
  destruct Normalize;
  intuition;
  discriminate.
Qed.

Theorem BOdd_BInc b : BOdd b = BInc (BEven b).
  trivial.
Qed.

Theorem nat_to_bnat_BEven b : b > 0 -> nat_to_bnat (b + b) = BEven (nat_to_bnat b).
  induction b;
  simpl in *;
  intros.
  omega.
  destruct b.
  trivial.
  simpl in *.
  rewrite Nat.add_succ_r.
  simpl in *.
  rewrite IHb.
  trivial.
  omega.
Qed.

Theorem nat_to_bnat_BOdd b : nat_to_bnat (S b + b) = BOdd (nat_to_bnat b).
  simpl in *.
  destruct b.
  trivial.
  rewrite nat_to_bnat_BEven.
  trivial.
  omega.
Qed.

Theorem nat_to_bnat_normalized n : Normalized (nat_to_bnat n).
  induction n;
  simpl in *.
  constructor.
  induction IHn;
  simpl in *;
  constructor.
  constructor.
  trivial.
  destruct n0;
  discriminate.
  trivial.
Qed.

Theorem BEven_BInc_BInc_BInc_BEven n : BEven (BInc n) = BInc (BInc (BEven n)).
  trivial.
Qed.

Theorem BPlus_BInc_BInc_BPlus : forall n b, BPlus (BInc b) n = BInc (BPlus b n).
  induction n.
  trivial.
  intros.
  simpl in *.
  f_equal.
  trivial.
Qed.

Theorem nat_to_bnat_correct_helper b : Normalized b -> nat_to_bnat (bnat_to_nat b) = b.
  induction 1;
  trivial;
  simpl in *;
  rewrite plus_0_r;
  repeat (rewrite nat_to_bnat_BPlus;simpl in *);
  [|
    assert(n = BZero \/ n <> BZero);
    [
      destruct n;
      try tauto;
      right;
      discriminate|
    ];
    destruct H0;
    try subst;
    trivial;
    rewrite BOdd_BInc;
    f_equal;
    rename H into H1;
    rename H0 into H;
    rename H1 into H0
  ];
  (rewrite <- IHNormalized;
  clear IHNormalized;
  assert(bnat_to_nat n > 0);
  [
    induction H0;
    simpl in *;
    intuition|
  ];
  induction (bnat_to_nat n);
  try omega;
  assert(n0 > 0 \/ n0 = 0);
  try omega;
  destruct H2;
  subst;
  trivial;
  simpl in *;
  rewrite BEven_BInc_BInc_BInc_BEven;
  rewrite BInc_correct;
  rewrite bnat_to_nat_correct in *;
  rewrite <- IHn0;
  trivial;
  simpl in *;
  rewrite BPlus_BInc_BInc_BPlus;
  trivial).
Qed.

Theorem nat_to_bnat_correct b : nat_to_bnat (bnat_to_nat b) = Normalize b.
  rewrite <- (bnat_to_nat_correct (bnat_to_nat b)).
  rewrite <- nat_to_bnat_correct_helper.
  rewrite nat_to_bnat_correct_helper.
  rewrite Normalize_correct.
  trivial.
  apply nat_to_bnat_normalized.
  apply Normalize_Normalized.
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