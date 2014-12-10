Inductive inf_tree : Set :=
| node : (nat -> inf_tree) -> inf_tree
| leaf : nat -> inf_tree.

Fixpoint Increment t :=
  match t with
  | leaf n => leaf (S n)
  | node f => node (fun x => Increment (f x))
  end.

Fixpoint LeapFrog i nt :=
  match nt with
  | leaf n => n
  | node f => LeapFrog (S i) (f i)
  end.

Goal forall nt i, S (LeapFrog i nt) = LeapFrog i (Increment nt).
  induction nt.
  intros.
  simpl in *.
  trivial.
  trivial.
Qed.