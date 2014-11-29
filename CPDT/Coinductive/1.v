Require Import Bool Setoid.

Set Implicit Arguments.

CoInductive inf_tree A := 
| node : A -> inf_tree A -> inf_tree A -> inf_tree A.

CoFixpoint everywhere A (a : A) : inf_tree A :=
  node a (everywhere a) (everywhere a).

CoFixpoint map A l r (f : A -> A -> A):=
  match l, r with
  | node a ll lr, node b rl rr => node (f a b) (map ll rl f) (map lr rr f)
  end.

CoFixpoint false_tree : inf_tree bool := node false false_tree false_tree.

CoFixpoint true_false : inf_tree bool :=
  node true (node false true_false true_false) (node false true_false true_false).

CoInductive eq_tree A :  inf_tree A -> inf_tree A -> Prop :=
| teq : forall a ll lr rl rr, 
    eq_tree ll rl ->
      eq_tree lr rr ->
        eq_tree (node a ll lr) (node a rl rr).

Definition frob A (s : inf_tree A) : inf_tree A :=
  match s with
    | node a l r => node a l r
  end.

Theorem frob_eq : forall A (s : inf_tree A), s = frob s.
  intros.
  destruct s.
  trivial.
Qed.

Goal eq_tree (map true_false false_tree orb) true_false.
  cofix.
  rewrite (frob_eq true_false).
  rewrite (frob_eq true_false).
  rewrite (frob_eq (map (frob (frob true_false)) false_tree orb)).
  simpl in *.
  constructor;
  rewrite (frob_eq (map (node false true_false true_false) false_tree orb));
  simpl in *;
  split;
  trivial.
Qed.


