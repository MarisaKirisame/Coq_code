Require Import List.

Load Poly.

Set Implicit Arguments.

Fixpoint evenb b := 
  match b with
  | O => true
  | S O => false
  | S (S n) => evenb n
  end.

Theorem silly_ex : 
  (forall n, evenb n = true -> oddb (S n) = true) ->
    evenb 3 = true -> oddb 4 = true.
  trivial.
Qed.

Theorem rev_exercise1 : forall(l l' : list nat), l = rev l' -> l' = rev l.
  intros.
  subst.
  rewrite rev_involutive.
  trivial.
Qed.

Example trans_eq_exercise : forall(n m o p : nat),
  m = o - 2 -> (n + p) = m -> (n + p) = o - 2.
  intros.
  apply trans_eq with m;
  trivial.
Qed.

Example sillyex1 : forall(X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j -> y :: l = x :: j -> x = y.
  intros.
  inversion H.
  subst.
  inversion H0.
  trivial.
Qed.

Example sillyex2 : forall(X : Type) (x y z : X) (l j : list X),
  x :: y :: l = nil -> y :: l = z :: j -> x = z.
  intros.
  inversion H.
Qed.

Theorem beq_nat_0_l : forall n,
  beq_nat 0 n = true -> n = 0.
  intros.
  induction n.
  trivial.
  discriminate.
Qed.

Theorem beq_nat_0_r : forall n,
  beq_nat n 0 = true -> n = 0.
  intros.
  induction n.
  trivial.
  discriminate.
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m -> n = m.
  intros n.
  induction n as [| n'].
  intros.
  simpl in *.
  induction m.
  trivial.
  discriminate.
  intros.
  destruct m.
  discriminate.
  f_equal.
  apply IHn'.
  simpl in *.
  inversion H.
  rewrite plus_comm in H1.
  symmetry in H1.
  rewrite plus_comm in H1.
  inversion H1.
  trivial.
Qed.

Theorem beq_nat_true : forall n m,
  beq_nat n m = true -> n = m.
  induction n, m.
  trivial.
  discriminate.
  discriminate.
  auto.
Qed.

Fixpoint index X (n:nat) (l:list X) : option X :=
  match l with
  | nil => None 
  | a :: l' => match beq_nat n O with 
               | true => Some a
               | false => index (pred n) l' 
               end
  end.

Theorem index_after_last: forall(X : Type)(l : list X)(n : nat),
  length l = n -> index n l = None.
  induction l.
  trivial.
  intros.
  subst.
  simpl in *.
  auto.
Qed.

Theorem length_snoc''' : 
  forall(X : Type)(l : list X)(n : nat)(v : X) ,
    length l = n -> length (snoc X l v) = S n.
  induction l.
  intros.
  subst.
  trivial.
  intros.
  subst.
  simpl in *.
  auto.
Qed.

Theorem app_length_cons : 
  forall(X : Type)(l1 l2 : list X)(x : X) (n : nat),
    length (l1 ++ (x :: l2)) = n -> S (length (l1 ++ l2)) = n.
  induction l1.
  trivial.
  intros.
  subst.
  simpl in *.
  eauto.
Qed.

Theorem app_length_twice : forall(X:Type)(l:list X),
  length (l ++ l) = length l + length l.
  destruct l.
  trivial.
  simpl in *.
  f_equal.
  remember l.
  rewrite Heql0 at 2.
  rewrite Heql0 at 3.
  clear Heql0.
  induction l0.
  trivial.
  simpl in *.
  auto.
Qed.

Theorem double_induction: forall(P : nat -> nat -> Prop), 
  P 0 0 ->
    (forall m, P m 0 -> P (S m) 0) ->
      (forall n, P 0 n -> P 0 (S n)) ->
        (forall m n, P m n -> P (S m) (S n)) ->
          forall m n, P m n.
  induction m.
  induction n.
  trivial.
  auto.
  induction n.
  auto.
  auto.
Qed.

Theorem override_shadow : forall(X:Type) x1 x2 k1 k2 (f : nat -> X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
  intros.
  unfold override.
  destruct(beq_nat k1 k2).
  trivial.
  trivial.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
    combine l1 l2 = l.
  induction l.
  intros.
  simpl in *.
  inversion H.
  trivial.
  intros.
  simpl in *.
  destruct a.
  inversion H.
  destruct l1, l2;
  try discriminate.
  inversion H1.
  inversion H4.
  subst.
  simpl in *.
  f_equal.
  apply IHl.
  destruct(split l).
  trivial.
Qed.

Theorem bool_fn_applied_thrice : 
  forall(f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
  intros.
  destruct (f true) eqn:Ht;
  destruct (f false) eqn:Hf;
  destruct b;
  repeat(rewrite Ht || rewrite Hf);
  trivial.
Qed.

Theorem override_same : forall(X:Type) x1 k1 k2 (f : nat -> X),
  f k1 = x1 -> 
    (override f k1 x1) k2 = f k2.
  intros.
  unfold override.
  destruct(beq_nat k1 k2) eqn : Heq.
  apply beq_nat_true in Heq.
  subst.
  trivial.
  trivial.
Qed.

Theorem beq_nat_ineq : forall n m, n <> m -> false = beq_nat m n.
  intros n m.
  refine(
    double_induction
      (fun l r => l <> r -> false = beq_nat r l)
      _
      _
      _
      _
      n
      m).
  tauto.
  trivial.
  trivial.
  auto.
Qed.

Theorem beq_nat_sym : forall(n m : nat),
  beq_nat n m = beq_nat m n.
  intros.
  destruct(beq_nat n m) eqn : Heq.
  apply beq_nat_true in Heq.
  subst.
  apply beq_nat_refl.
  apply beq_nat_false in Heq.
  apply beq_nat_ineq.
  trivial.
Qed.

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
    beq_nat m p = true ->
      beq_nat n p = true.
  intros.
  apply beq_nat_true in H.
  subst.
  trivial.
Qed.

Definition split_combine_statement : 
  forall x y l1 l2, length l1 = length l2 ->
    split (@combine x y l1 l2) = (l1,l2).
  induction l1.
  intros.
  destruct l2.
  trivial.
  discriminate.
  intros.
  simpl in *.
  destruct l2.
  discriminate.
  simpl in *.
  f_equal.
  f_equal.
  rewrite IHl1.
  trivial.
  auto.
  f_equal.
  rewrite IHl1.
  trivial.
  auto.
Qed.

Theorem override_permute : forall(X:Type)x1 x2 k1 k2 k3 (f : nat -> X),
  beq_nat k2 k1 = false -> 
    (override (override f k2 x2) k1 x1) k3 =
    (override (override f k1 x1) k2 x2) k3.
  unfold override.
  intros.
  destruct(beq_nat k1 k3) eqn:H13.
  apply beq_nat_true in H13.
  subst.
  rewrite H.
  trivial.
  trivial.
Qed.

Theorem filter_exercise : 
  forall(X : Type) (test : X -> bool)(x : X) (l lf : list X),
    filter test l = x :: lf ->
      test x = true.
  induction l.
  discriminate.
  intros.
  simpl in *.
  destruct(test a) eqn:Ha.
  inversion H.
  subst.
  trivial.
  eauto.
Qed.

Fixpoint forallb {x} test (l : list x) : bool :=
  match l with
  | nil => true
  | l_head :: l_tail => andb (test l_head) (forallb test l_tail)
  end.

Fixpoint existsb {x} test (l : list x) : bool :=
  match l with
  | nil => false
  | l_head :: l_tail => orb (test l_head) (existsb test l_tail)
  end.

Definition existsb' {x} test (l : list x) : bool := 
  negb (forallb (fun e => negb (test e)) l).

Goal forall T test l, @existsb T test l  = @existsb' T test l.
  unfold existsb'.
  induction l.
  trivial.
  simpl in *.
  destruct(test a).
  trivial.
  simpl in *.
  trivial.
Qed.