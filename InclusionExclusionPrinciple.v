Require Export Finite_sets Classical_sets Finite_sets_facts Arith Classical Omega Program.

Set Implicit Arguments.

Theorem Intersection_Empty_set_r U (S : Ensemble U) : 
  Intersection _ S (Empty_set U) = Empty_set U.
  apply Extensionality_Ensembles.
  intuition.
Qed.

Theorem Intersection_Empty_set_l U (S : Ensemble U) : 
  Intersection _ (Empty_set U) S = Empty_set U.
  apply Extensionality_Ensembles.
  intuition.
Qed.

Theorem Union_Empty_set_r U (S : Ensemble U) : 
  Union _ S (Empty_set U) = S.
  apply Extensionality_Ensembles.
  intuition.
Qed.

Theorem Union_Empty_set_l U (S : Ensemble U) : 
  Union _ (Empty_set U) S = S.
  apply Extensionality_Ensembles.
  intuition.
Qed.

Theorem In_Intersection_In_l U (L R : Ensemble U) x :
  In _ (Intersection _ L R) x -> In _ L x.
  destruct 1.
  trivial.
Qed.

Theorem In_Intersection_In_r U (L R : Ensemble U) x :
  In _ (Intersection _ L R) x -> In _ R x.
  destruct 1.
  trivial.
Qed.

Theorem not_In_Subtract U (L : Ensemble U) x :
  ~ (In _ (Subtract _ L x) x).
  intuition.
  destruct H.
  auto with *.
Qed.

Theorem Inclusion_Exclusion_Principle U (L R : Ensemble U) n l m r :
  cardinal _ (Union _ L R) n -> 
    cardinal _ L l -> cardinal _ R r -> cardinal _ (Intersection _ L R) m -> n = l + r - m.
  intros.
  generalize dependent n.
  generalize dependent m.
  generalize dependent r.
  generalize dependent R.
  generalize dependent L.
  induction l;
  intros.
  apply cardinalO_empty in H0.
  simpl in *.
  subst.
  rewrite Intersection_Empty_set_l in H2.
  apply cardinal_Empty in H2.
  subst.
  rewrite Union_Empty_set_l in H.
  replace r with n in *.
  auto with *.
  eapply cardinal_unicity;
  eauto.
  destruct (cardinal_invert _ L (S l)).
  trivial.
  destruct H3.
  destruct H3.
  destruct H4.
  subst.
  destruct (classic (In _ R x0)).
  destruct m.
  apply cardinalO_empty in H2.
  apply Extension in H2.
  unfold Same_set in H2.
  destruct H2.
  unfold Included in *.
  specialize (H2 x0).
  assert(In U (Intersection U (Add U x x0) R) x0).
  constructor.
  right.
  constructor.
  trivial.
  intuition.
  destruct H8.
  assert(cardinal U (Intersection U x R) m).
  pose (card_soustr_1 U (Intersection U (Add U x x0) R) (S m) H2 x0).
  assert (In U (Intersection U (Add U x x0) R) x0).
  constructor.
  auto with *.
  trivial.
  simpl in *.
  intuition.
  replace (Intersection U x R) with (Subtract U (Intersection U (Add U x x0) R) x0).
  trivial.
  apply Extensionality_Ensembles.
  constructor;
  unfold Included;
  intros.
  destruct(classic (x0 = x1)).
  subst.
  apply not_In_Subtract in H8.
  tauto.
  do 3 destruct H8.
  auto with *.
  tauto.
  destruct (classic (x0 = x1)).
  subst.
  apply In_Intersection_In_l in H8.
  tauto.
  constructor.
  constructor.
  constructor.
  eapply In_Intersection_In_l.
  eauto.
  eapply In_Intersection_In_r.
  eauto.
  auto with *.
  specialize(IHl x H5 R r H1 m H6 n).
  simpl in *.
  apply IHl.
  replace (Union U x R) with (Union U (Add U x x0) R).
  trivial.
  apply Extensionality_Ensembles.
  constructor.
  unfold Included.
  intros.
  destruct(classic (x0 = x1)).
  subst.
  right.
  trivial.
  destruct H7.
  destruct H7.
  left.
  trivial.
  auto with *.
  right.
  trivial.
  unfold Included.
  intros.
  destruct(classic (x0 = x1)).
  subst.
  left.
  right.
  auto with *.
  destruct H7;
  auto with *.
  replace (Intersection U (Add U x x0) R) with (Intersection U x R) in *.
  destruct n.
  apply cardinalO_empty in H.
  apply Extension in H.
  unfold Same_set in H.
  destruct H.
  unfold Included in *.
  specialize(H x0).
  assert(In U (Union U (Add U x x0) R) x0).
  constructor.
  apply Add_intro2.
  intuition.
  destruct H8.
  specialize(IHl x H5 R r H1 m H2 n).
  assert(cardinal U (Union U x R) n).
  pose (card_soustr_1 U (Union U (Add U x x0) R) (S n) H x0).
  simpl in *.
  assert(In U (Union U (Add U x x0) R) x0).
  auto with *.
  intuition.
  replace (Union U x R) with (Subtract U (Union U (Add U x x0) R) x0).
  trivial.
  apply Extensionality_Ensembles.
  constructor;
  unfold Included;
  intros;
  destruct (classic (x0 = x1));
  subst.
  destruct H8.
  auto with *.
  destruct H8.
  destruct H8.
  destruct H8.
  left.
  trivial.
  tauto.
  right.
  trivial.
  destruct H8;
  tauto.
  constructor.
  destruct H8;
  auto with *.
  auto with *.
  intuition.
  subst.
  assert(r >= m).
  unfold ge.
  eapply incl_card_le;
  eauto.
  apply Intersection_decreases_r.
  omega.
  apply Extensionality_Ensembles.
  unfold Same_set.
  intuition;
  constructor.
  apply In_Intersection_In_l in H6.
  constructor.
  trivial.
  apply In_Intersection_In_r in H6.
  trivial.
  destruct (classic (x0 = x1)).
  subst.
  apply In_Intersection_In_r in H6.
  tauto.
  apply In_Intersection_In_l in H6.
  destruct H6.
  trivial.
  destruct H6.
  tauto.
  apply In_Intersection_In_r in H6.
  trivial.
Qed.

Print Assumptions Inclusion_Exclusion_Principle.