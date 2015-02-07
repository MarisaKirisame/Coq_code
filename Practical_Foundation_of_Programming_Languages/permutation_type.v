Require Import Omega List Program Permutation.
Require Import eq_dec bring_to_front tactic Setoid.

Set Implicit Arguments.

Inductive permutation_type {A : Type} : list A -> list A -> Type :=
| perm_type_nil : permutation_type [] []
| perm_type_skip : forall (x : A) (l l' : list A),
    permutation_type l l' -> permutation_type (x :: l) (x :: l')
| perm_type_swap : forall (x y : A) (l : list A),
    permutation_type (y :: x :: l) (x :: y :: l)
| perm_type_trans : forall l l' l'' : list A,
    permutation_type l l' -> permutation_type l' l'' -> permutation_type l l''.

Definition permutation_type_reflexive : forall T (l : list T), permutation_type l l.
  induction l.
  constructor.
  constructor.
  trivial.
Defined.

Theorem permutation_type_Permutation :
  forall T (l : list T) r (P : permutation_type l r),
    eq_dec T -> Permutation l r.
  intros.
  induction P.
  trivial.
  auto.
  constructor.
  econstructor.
  exact IHP1.
  trivial.
Defined.

Theorem permutation_type_symmetric : 
  forall T (l r : list T), permutation_type l r -> permutation_type r l.
  induction 1;
  repeat constructor.
  trivial.
  econstructor.
  exact IHX2.
  trivial.
Defined.

Theorem permutation_type_cons_app : forall T (t : T) l l0 l1,
  permutation_type l (l0 ++ l1) ->
    permutation_type (t :: l) (l0 ++ t :: l1).
  intros.
  dependent induction X;
  destruct l0;
  try invc x;
  simpl in *;
  subst;
  repeat constructor.
  trivial.
  assert (permutation_type (t :: t0 :: l) (t0 :: t :: l)).
  constructor.
  eapply perm_type_trans.
  exact X0.
  constructor.
  auto.
  destruct l0.
  simpl in *.
  subst.
  assert (permutation_type (t :: y :: t0 :: l) (t :: t0 :: y :: l)).
  repeat constructor.
  eapply perm_type_trans.
  exact X.
  constructor.
  simpl in *.
  invc H1.
  assert (permutation_type (t :: t1 :: t0 :: l0 ++ l1) (t1 :: t :: t0 :: l0 ++ l1)).
  constructor.
  assert (permutation_type (t0 :: t1 :: l0 ++ t :: l1) (t1 :: t0 :: l0 ++ t :: l1)).
  constructor.
  eapply perm_type_trans.
  exact X.
  apply permutation_type_symmetric.
  eapply perm_type_trans.
  exact X0.
  constructor.
  assert (permutation_type (t :: t0 :: l0 ++ l1) (t0 :: t :: l0 ++ l1)).
  constructor.
  apply permutation_type_symmetric.
  eapply perm_type_trans.
  exact X1.
  constructor.
  clear X X0 X1.
  induction l0.
  simpl in *.
  apply permutation_type_reflexive.
  simpl in *.
  assert (permutation_type (t :: a :: l0 ++ l1) (a :: t :: l0 ++ l1)).
  constructor.
  eapply perm_type_trans.
  exact X.
  constructor.
  trivial.
  eapply perm_type_trans.
  exact X1.
  trivial.
  assert (permutation_type (t :: l) (t :: l')).
  constructor.
  trivial.
  eapply perm_type_trans.
  exact X.
  trivial.
Defined.

Definition Permutation_permutation_type_inner : 
  forall T (l : list T) r (P : Permutation l r) n,
    eq_dec T -> length l <= n -> permutation_type l r.
  intros.
  generalize dependent r.
  generalize dependent l.
  induction n;
  intros.
  destruct l.
  apply Permutation_nil in P.
  subst.
  constructor.
  simpl in *.
  omega.
  destruct l.
  apply Permutation_nil in P.
  subst.
  constructor.
  simpl in *.
  assert (length l <= n).
  omega.
  clear H.
  destruct (bring_to_front X t r).
  apply (Permutation_in t P).
  simpl in *.
  tauto.
  intuition.
  destruct x.
  subst.
  simpl in *.
  destruct l0.
  simpl in *.
  assert(permutation_type l l1).
  apply IHn.
  trivial.
  apply Permutation_cons_inv in P.
  trivial.
  constructor.
  trivial.
  simpl in *.
  invc H2.
  assert (Permutation (t :: l) (t :: l0 ++ l1)).
  apply Permutation_cons_app_inv in P.
  auto.
  apply Permutation_cons_inv in H.
  assert (permutation_type l (l0 ++ l1)).
  auto.
  apply permutation_type_cons_app.
  trivial.
Defined.

Theorem Permutation_permutation_type : forall T (l : list T) r (P : Permutation l r),
  eq_dec T -> permutation_type l r.
  intros.
  eapply Permutation_permutation_type_inner;
  trivial.
Defined.