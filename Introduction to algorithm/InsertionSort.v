Require Import List Arith Recdef.

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
