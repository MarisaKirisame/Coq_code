Require Import List Arith Recdef Setoid Relations Omega Permutation Sorted.

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

Goal forall (A : Type) (l : list A), Permutation nil l -> l = nil.
  intros.
  eapply (Permutation_ind (fun l' r' => r' = nil -> l' = nil)).
  trivial.
  intros.
  inversion H2.
  intros.
  inversion H0.
  tauto.
  instantiate( 1 := nil ).
  auto with *.
  trivial.
Qed.

Theorem InsertionPermutationSelf : forall n l, Permutation (n :: l) (Insertion n l).
  intros.
  induction l.
  trivial.
  simpl in *.
  case (lt_dec n a).
  trivial.
  intros.
  assert(Permutation (n :: a :: l) (a :: n :: l)).
  constructor.
  apply(perm_trans H).
  auto.
Qed.

Theorem InsertionPermutation : forall n l r, Permutation l r -> Permutation (n :: l) (Insertion n r).
  induction 1.
  trivial.
  simpl in *.
  case(lt_dec n x).
  auto.
  intros.
  assert (Permutation (n :: x :: l) (x :: n :: l)) as T.
  constructor.
  apply(perm_trans T).
  auto.
  simpl in *.
  case(lt_dec n x),(lt_dec n y).
  constructor.
  constructor.
  constructor.
  constructor.
  assert (Permutation (n :: y :: x :: l) (n :: x :: y :: l)) as T.
  constructor.
  constructor.
  apply(perm_trans T).
  constructor.
  assert(Permutation (n :: y :: x :: l) (x :: y :: n :: l)) as T.
  assert(Permutation (n :: y :: x :: l) (x :: n :: y :: l)) as T.
  assert(Permutation (n :: y :: x :: l) (n :: x :: y :: l)) as T.
  constructor.
  constructor.
  apply(perm_trans T).
  constructor.
  apply(perm_trans T).
  constructor.
  constructor.
  apply(perm_trans T).
  constructor.
  constructor.
  apply InsertionPermutationSelf.
  assert (Permutation (n :: l) (n :: l')) as T.
  auto.
  apply(perm_trans T).
  trivial.
Qed.

Theorem InsertionSortPermutation : forall l, Permutation l (InsertionSort l).
  induction l.
  trivial.
  inversion IHl.
  trivial.
  subst.
  simpl in *.
  apply InsertionPermutation.
  trivial.
  subst.
  simpl in *.
  apply InsertionPermutation.
  trivial.
  subst.
  simpl in *.
  apply InsertionPermutation.
  trivial.
Qed.

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

Theorem SortedCons : forall e l, Sorted le (e :: l) -> Sorted le l.
  intros.
  induction l.
  constructor.
  inversion H.
  trivial.
Qed.

Theorem InsertionSorted : forall e l, Sorted le l -> Sorted le (Insertion e l).
  intros.
  induction l.
  simpl in *.
  auto.
  simpl in *.
  remember (lt_dec e a).
  destruct s.
  auto with *.
  constructor.
  apply IHl.
  eapply SortedCons.
  eauto.
  induction l.
  simpl in *.
  constructor.
  omega.
  simpl in *.
  remember (lt_dec e a0).
  destruct s.
  auto with *.
  constructor.
  inversion H.
  subst.
  inversion H3.
  trivial.
Qed.

Theorem InsertionSortSorted : forall l, Sorted le (InsertionSort l).
  induction l.
  simpl in *.
  trivial.
  simpl in *.
  apply InsertionSorted.
  trivial.
Qed.