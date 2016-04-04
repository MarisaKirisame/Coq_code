Require Import Program Omega.
Set Implicit Arguments.

Class iso A B :=
  {
    f : A -> B;
    g : B -> A;
    fg : forall x, f (g x) = x;
    gf : forall x, g (f x) = x
  }.

Instance iso_id A : iso A A :=
  {
  }.
  all: intuition.
Defined.
Hint Resolve iso_id.

Instance iso_sym A B (I : iso A B) : iso B A :=
  {
  }.
  all: destruct I; intuition.
Defined.

Instance iso_trans A B C (L : iso A B) (R : iso B C) : iso A C :=
  {
  }.
  all: destruct L, R; intuition; congruence.
Defined.

Goal nat <> bool.
  intuition.
  assert(iso nat bool) by (rewrite H; auto).
  destruct X.
  pose proof (fg0 true); specialize (fg0 false).
  specialize(gf0 (S ((g0 true) + (g0 false)))).
  destruct (f0 (S _)); do 2 destruct g0;
    simpl in *; try rewrite H1 in *; discriminate || omega.
Qed.