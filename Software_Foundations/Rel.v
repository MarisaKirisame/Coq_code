Require Import Relations Omega.

Set Implicit Arguments.

Theorem lt_trans' :
  transitive _ lt.
  unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o];
  auto.
Qed.

Theorem lt_trans'' :
  transitive _ lt.
  unfold lt.
  unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  inversion Hmo.
  inversion Hmo.
  subst.
  auto.
  subst.
  auto.
Qed.

Theorem le_S_n_m_le_n_n : forall m n, S n <= m -> n <= m.
  induction m;
  intros;
  inversion H;
  subst;
  auto.
Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
  intros.
  inversion H;
  subst;
  trivial.
  apply le_S_n_m_le_n_n.
  trivial.
Qed.

Theorem le_Sn_n : forall n, ~ S n <= n.
  intros.
  unfold not.
  induction n.
  intros.
  inversion H.
  intros.
  apply IHn.
  inversion H.
  trivial.
  subst.
  apply le_S_n_m_le_n_n.
  trivial.
Qed.

Theorem le_not_symmetric :
  ~ (symmetric _ le).
  unfold symmetric.
  unfold not.
  intros.
  assert(0 <= 1).
  auto.
  apply H in H0.
  inversion H0.
Qed.

Theorem le_antisymmetric :
  antisymmetric _ le.
  unfold antisymmetric.
  induction x;
  destruct y;
  intros;
  trivial.
  inversion H0.
  inversion H.
  f_equal.
  apply IHx;
  apply le_S_n;
  trivial.
Qed.

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
  induction n;
  induction m;
  induction p;
  intros;
  trivial;
  try(inversion H;fail).
  apply le_0_n.
  inversion H0;
  subst.
  inversion H.
  inversion H2.
  inversion H2.
  inversion H0;
  subst.
  inversion H;
  subst.
  trivial.
  auto.
  auto.
Qed.

Inductive refl_step_closure {X:Type} (R: relation X) : relation X :=
| rsc_refl : forall(x : X), refl_step_closure R x x
| rsc_step : forall(x y z : X),
    R x y ->
      refl_step_closure R y z ->
        refl_step_closure R x z.

Theorem rsc_trans :
  forall(X:Type) (R: relation X) (x y z : X),
    refl_step_closure R x y ->
      refl_step_closure R y z ->
        refl_step_closure R x z.
  repeat induction 1;
  try (constructor;fail);
  repeat
    (try apply IHrefl_step_closure;
    econstructor;
    eauto;
    trivial).
Qed.

Theorem rtc_rsc_coincide :
         forall(X:Type) (R: relation X) (x y : X),
  clos_refl_trans _ R x y <-> refl_step_closure R x y.
  split;
  induction 1;
  try (constructor;fail);
  try (
    econstructor;
    eauto;
    constructor).
  inversion H;
  inversion H0;
  subst;
  eapply rsc_trans;
  eauto.
  auto with *.
  apply (rt_trans _ _ _ y).
  auto with *.
  trivial.
Qed.