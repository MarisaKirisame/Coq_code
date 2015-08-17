Require Export Program Omega.
Set Implicit Arguments.
Definition iso A B := exists (f : A -> B) (g : B -> A), 
  (forall l, f (g l) = l) /\ forall r, g (f r) = r.
Theorem iso_id A : iso A A.
  exists (@id A) (@id A);intuition.
Qed.
Hint Resolve iso_id.
Goal nat <> bool.
  intuition.
  assert(iso nat bool) by (rewrite H;auto).
  destruct H0.
  destruct H0.
  intuition.
  clear H.
  pose proof (H1 true);specialize (H1 false).
  specialize(H2 (S ((x0 true) + (x0 false)))).
  destruct (x (S _));do 2 destruct x0;simpl in *;try rewrite H1 in *;try discriminate||omega.
Qed.