Require Import List.

Inductive last(A : Set) : list A -> A -> Prop :=
  single : forall a : A, last A (a :: nil) a
| compound : forall (l : list A)(a b : A), last A l a -> last A (b :: l) a.

Fixpoint last_fun(A : Set)(l : list A) : option A :=
  match l with
  | nil => None
  | a :: nil => Some a
  | a :: b => last_fun A b
  end.

Goal forall(A : Set)(l : list A)(a : A), last A l a -> last_fun A l = Some a.
  intros.
  elim H.
  reflexivity.
  intros.
  rewrite <- H1.
  simpl.
  destruct l0.
  inversion H1.
  reflexivity.
Qed.

Inductive permutation(A : Set) : list A -> list A -> Prop :=
  transpose : 
    forall (l r : A)(lis : list A),
      permutation A (l :: r :: lis) (r :: l :: lis)
| trans : forall a b c, permutation A a b -> permutation A b c -> permutation A a c
| id : forall a, permutation A a a.

Require Import Relations.

Theorem equiv_perm : forall A : Set, equiv _ (permutation A).
  intros.
  repeat split.
  unfold reflexive.
  constructor.
  unfold transitive.
  intros.
  apply (trans A x y z);assumption.
  unfold symmetric.
  intros.
  elim H.
  intros.
  constructor.
  intros.
  econstructor.
  eassumption.
  assumption.
  constructor.
Qed.

Require Import JMeq.
Require Import Arith.

Lemma plus_assoc_JM : 
  forall n p q:nat,
    JMeq (n+(p+q)) (n+p+q).
  intros.
  rewrite plus_assoc.
  constructor.
Qed.

Inductive even : nat -> Prop :=
| O_even : even 0
| plus_2_even : forall n:nat, even n -> even (S (S n)).

Hint Resolve O_even plus_2_even.

Fixpoint mult2 (n:nat) : nat :=
  match n with
  | O => 0
  | S p => S (S (mult2 p))
  end.

Goal forall n, even (n * 2).
  intros.
  induction n.
  auto.
  rewrite mult_succ_l.
  rewrite plus_comm.
  simpl.
  auto.
Qed.

Goal forall n, even n -> exists x, x * 2 = n.
  intros.
  induction H.
  exists 0.
  auto.
  destruct IHeven.
  exists (S x).
  rewrite mult_succ_l.
  rewrite plus_comm.
  simpl.
  auto with arith.
Qed.

Lemma even_plus : forall n m, even n -> even m -> even (n + m).
  intros.
  induction H.
  auto.
  simpl.
  auto.
Qed.

Goal forall n, even n -> even (n * n).
  intros.
  induction H.
  auto.
  repeat rewrite mult_succ_l.
  repeat rewrite mult_succ_r.
  repeat apply even_plus;auto.
Qed.

Theorem lt_le : forall n p:nat, n < p -> n <= p.
  intros n p H.
  apply (le_ind (S n)).
  repeat constructor.
  intros.
  constructor.
  assumption.
  assumption. 
Qed.

Definition my_le (n p:nat) :=
  forall P:nat->Prop,
    P n ->
      (forall q:nat, P q -> P (S q)) ->
        P p.

Lemma my_le_n : forall n:nat, my_le n n.
  unfold my_le.
  intros.
  assumption.
Qed.

Lemma my_le_S : forall n p:nat, my_le n p -> my_le n (S p).
  unfold my_le.
  intros.
  apply H.
  auto.
  intros.
  auto.
Qed.

Lemma my_le_inv : forall n p:nat, my_le n p -> n=p \/ my_le (S n) p.
  unfold my_le.
  intros.
  apply H.
  left.
  auto.
  intros.
  destruct H0.
  right.
  intros.
  rewrite <- H0.
  auto.
  right.
  intros.
  apply H2.
  apply H0;
  auto.
Qed.

Lemma my_le_inv2 :
  forall n p:nat, my_le (S n) p ->
    exists q, p=(S q) /\ my_le n q.
  unfold my_le.
  intros.
  apply H.
  exists n.
  split;
  auto.
  intros.
  destruct H0.
  destruct H0.
  exists (S x).
  split.
  auto with arith.
  intros.
  apply H3.
  apply H1;
  auto.
Qed.

Lemma my_le_n_O : forall n:nat, my_le n 0 -> n = 0.
  intros.
  destruct n.
  auto.
  ecase my_le_inv2.
  eassumption.
  intros.
  destruct H0.
  discriminate H0.
Qed.

Lemma my_le_le : forall n p:nat, my_le n p -> le n p.
  intros.
  apply H;
  auto.
Qed.

Lemma le_my_le : forall n p:nat, le n p -> my_le n p.
  unfold my_le.
  intros.
  induction H;
  auto.
Qed.

