Require Import Bool.

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
| teq : forall la ll lr ra rl rr, 
  la = ra ->
    eq_tree ll rl ->
      eq_tree lr rr ->
        eq_tree (node la ll lr) (node ra rl rr).

Goal eq_tree (map true_false false_tree orb) true_false.
  cofix.
Admitted.


