Require Import List Arith Recdef Setoid Relations Omega.

Set Implicit Arguments.

Fixpoint Insertion(n : nat)(l : list nat) := 
  match l with
  | nil => n :: nil
  | l_head :: l_tail => 
      match lt_dec n l_head with
      | left _ => n :: l_head ::l_tail
      | right _ => l_head :: Insertion n l_tail
      end
  end.

Fixpoint InsertionSort(l : list nat) : list nat :=
  match l with
  | nil => nil
  | l_head :: l_tail => Insertion l_head (InsertionSort l_tail)
  end.

Theorem InsertionLength : forall n l, length(Insertion n l) = S (length l).
  intro.
  induction l.
  trivial.
  simpl in *.
  destruct (lt_dec n a).
  trivial.
  intuition.
  simpl in *.
  auto.
Qed.

Theorem InsertionSortSameLength : forall l, length (InsertionSort l) = length l.
  intros.
  induction l.
  trivial.
  simpl in *.
  rewrite InsertionLength.
  auto.
Qed.

Fixpoint occ(n : nat)(l : list nat) : nat :=
  match l with
  | nil => O
  | l_head :: l_tail => (if beq_nat n l_head then 1 else 0) + (occ n l_tail)
  end.

Definition Permutation(l l':list nat) := 
  forall n : nat, occ n l = occ n l'.

Theorem Permutation_Equiv : Equivalence Permutation.
  unfold Permutation.
  intuition.
  unfold Transitive.
  intuition.
  rewrite <- H0.
  trivial.
Qed.

Theorem occ_Nil : forall l,(forall n, occ n l = 0) -> l = nil.
  induction l.
  trivial.
  intuition.
  remember(H a).
  simpl in *.
  absurd((if beq_nat a a then 1 else 0) + occ a l = 0).
  rewrite <- beq_nat_refl.
  subst.
  auto.
  trivial.
Qed.

Theorem occ_same : forall n l r,
  Permutation l r ->
    S (occ n l) = occ n (Insertion n r).
  unfold Permutation.
  destruct l.
  intuition.
  simpl in *.
  assert(r = nil).
  apply occ_Nil.
  auto.
  subst.
  simpl in *.
  rewrite <- beq_nat_refl.
  trivial.
  intuition.
  simpl in *.
  rewrite H.
  clear H.
  clear n0.
  clear l.
  induction r.
  simpl in *.
  rewrite <- beq_nat_refl.
  trivial.
  simpl in *.
  remember(beq_nat n a).
  destruct b.
  simpl in *.
  assert(n = a).
  apply beq_nat_true.
  auto.
  remember(lt_dec n a).
  destruct s.
  subst.
  omega.
  subst.
  simpl in *.
  rewrite <- Heqb.
  auto.
  simpl.
  remember(lt_dec n a).
  destruct s.
  intuition.
  simpl in *.
  rewrite <- beq_nat_refl.
  simpl in *.
  f_equal.
  rewrite <- Heqb.
  trivial.
  intuition.
  simpl in *.
  rewrite <- Heqb.
  trivial.
Qed.

Theorem occ_diff : forall n m l r,
  Permutation l r ->
    beq_nat n m = false ->
      occ n l = occ n (Insertion m r).
  unfold Permutation.
  induction l.
  intuition.
  simpl in *.
  assert(r = nil).
  apply occ_Nil.
  eauto.
  subst.
  simpl in *.
  rewrite H0.
  trivial.
  induction r.
  intuition.
  assert(a :: l = nil).
  apply occ_Nil.
  trivial.
  absurd(a :: l = nil).
  auto with *.
  trivial.
  intuition.
  simpl in *.
  remember(lt_dec m a0).
  destruct s.
  intuition.
  simpl in *.
  rewrite H0.
  eauto.
  simpl in *.
  assert(occ n (Insertion m r) = occ n r).
  clear IHl.
  clear IHr.
  clear H.
  clear Heqs.
  clear n0.
  clear a0.
  clear l.
  clear a.
  induction r.
  intuition.
  simpl in *.
  rewrite H0.
  trivial.
  simpl in *.
  remember(lt_dec m a).
  destruct s.
  intuition.
  simpl in *.
  rewrite H0.
  omega.
  intuition.
  simpl in *.
  auto.
  rewrite H1.
  apply H.
Qed.

Theorem InsertionSortPermutation : forall l, Permutation (InsertionSort l) l.
  unfold Permutation.
  induction l.
  simpl in *.
  constructor.
  simpl in *.
  intuition.
  remember(beq_nat n a).
  destruct b.
  simpl in *.
  admit.
  simpl in *.
  symmetry.
  apply occ_diff.
  unfold Permutation.
  auto.
  auto.
Qed.

Inductive sorted : list nat -> Prop :=
| sorted0 : sorted nil
| sorted1 : forall n, sorted (n :: nil)
| sorted2 :
    forall n1 n2 l,
      n1 <= n2 ->
        sorted (n2 :: l) -> sorted (n1 :: n2 :: l).

Theorem InsertionSortNil : forall l, InsertionSort l = nil -> l = nil.
  intros.
  destruct l.
  trivial.
  simpl in *.
  remember(InsertionSort l).
  destruct l0.
  simpl in *.
  inversion H.
  simpl in *.
  destruct (lt_dec n n0).
  inversion H.
  inversion H.
Qed.

Theorem SortedCons : forall e l, sorted (e :: l) -> sorted l.
  intros.
  induction l.
  constructor.
  inversion H.
  trivial.
Qed.

Theorem InsertionSorted : forall e l, sorted l -> sorted (Insertion e l).
  intros.
  induction l.
  simpl in *.
  constructor.
  simpl in *.
  case(lt_dec e a).
  intros.
  constructor.
  omega.
  trivial.
  intros.
  inversion H.
  subst.
  simpl in *.
  constructor.
  omega.
  constructor.
  subst.
  simpl in *.
  remember(lt_dec e n2).
  destruct s.
  constructor.
  omega.
  constructor.
  omega.
  trivial.
  constructor.
  trivial.
  tauto.
Qed.

Theorem InsertionSortSorted : forall l, sorted (InsertionSort l).
  induction l.
  simpl in *.
  constructor.
  simpl in *.
  apply InsertionSorted.
  trivial.
Qed.