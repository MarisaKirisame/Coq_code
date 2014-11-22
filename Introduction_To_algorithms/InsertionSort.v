Require Import List Arith Recdef Setoid Relations Omega Permutation.

Set Implicit Arguments.

Fixpoint occ(n : nat)(l : list nat) : nat :=
  match l with
  | nil => O
  | l_head :: l_tail => (if beq_nat n l_head then 1 else 0) + (occ n l_tail)
  end.

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

Inductive sorted : list nat -> Prop :=
| sorted0 : sorted nil
| sorted1 : forall n, sorted (n :: nil)
| sorted2 :
    forall n1 n2 l,
      n1 <= n2 ->
        sorted (n2 :: l) -> sorted (n1 :: n2 :: l).

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

Theorem InsertionPermutation : forall l r n, Permutation l r -> Permutation (n :: l) (Insertion n r).
  intros.
Admitted.

Theorem InsertionSortPermutation : forall l, Permutation (InsertionSort l) l.
  induction l.
  trivial.
  simpl in *.
  inversion IHl.
  trivial.
  subst.
  simpl in *.
  remember(lt_dec a x).
  destruct s.
  auto.
  symmetry.
  assert(Permutation (a :: x :: l') (x :: a :: l')).
  constructor.
  apply (perm_trans H1).
  constructor.
  eapply InsertionPermutation.
  auto with *.
  subst.
  simpl in *.
  remember(lt_dec a x).
  remember(lt_dec a y).
  destruct s, s0.
  constructor.
  constructor.
  assert(Permutation (y :: a :: x :: l0) (a :: y :: x :: l0)).
  constructor.
  apply (perm_trans H).
  constructor.
  constructor.
  constructor.
  constructor.
  symmetry.
  assert(Permutation (a :: x :: y :: l0) (y :: x :: a :: l0)).
  assert(Permutation (a :: x :: y :: l0) (x :: a :: y :: l0)).
  constructor.
  apply (perm_trans H).
  assert(Permutation (x :: a :: y :: l0) (x :: y :: a :: l0)).
  constructor.
  constructor.
  apply (perm_trans H1).
  constructor.
  apply (perm_trans H).
  constructor.
  constructor.
  eapply InsertionPermutation.
  trivial.
  subst.
  symmetry.
  eapply InsertionPermutation.
  symmetry.
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

