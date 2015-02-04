Require Import List Permutation Program Omega.

Load tactic.

Set Implicit Arguments.

Fixpoint count_true (T : Type) (l : list T) (P : T -> bool) :=
  match l with
  | nil => 0
  | l_head :: l_tail => (if P l_head then 1 else 0) + count_true l_tail P
  end.

Definition count_false (T : Type) (l : list T) (P : T -> bool) :=
  count_true l (fun x => negb (P x)).

Theorem conunt_length_eq : forall T (l : list T) p, count_true l p + count_false l p = length l.
  intros.
  induction l.
  trivial.
  unfold count_false in *.
  simpl in *.
  destruct (p a);
  simpl in *;
  omega.
Qed.

Theorem count_split_eq : 
  forall T (l r : list T) p, count_true (l ++ r) p = count_true l p + count_true r p.
  intros.
  induction l;
  intros.
  trivial.
  simpl in *.
  destruct (p a);
  simpl in *;
  auto.
Qed.

Theorem permutation_count_eq : 
  forall T (l r : list T) p, Permutation l r -> count_true l p = count_true r p.
  intros.
  induction H;
  simpl in *;
  auto;
  omega.
Qed.