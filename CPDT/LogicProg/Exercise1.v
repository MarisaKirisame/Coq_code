Require Import Setoid.

Section Group.

  Variable T : Type.
  Variable F : T -> T -> T.
  Variable e : T.
  Variable i : T -> T.
  Infix "*" := F.
  Axiom Associativity : forall a b c, (a * b) * c = a * (b * c).
  Axiom Identity_r : forall a, a * e = a.
  Axiom Inverse_r : forall a, a * i a = e.
  Hint Resolve Associativity Identity_r Inverse_r.
  Hint Rewrite <- Associativity Identity_r Inverse_r.
  Hint Rewrite Associativity Identity_r Inverse_r.

  Theorem IdentityCharacterize : forall a, a * a = a -> a = e.
    intros.
    rewrite <- (Inverse_r a).
    rewrite <- H at 2.
    rewrite Associativity.
    rewrite Inverse_r.
    rewrite Identity_r.
    trivial.
  Qed.

  Theorem Inverse_l : forall a, i a * a = e.
    intros.
    rewrite <- (Identity_r a) at 2.
    rewrite <- (Inverse_r (i a)) at 1.
    rewrite <- (Associativity a).
    rewrite Inverse_r.
    rewrite <- Associativity.
    rewrite Identity_r.
    trivial.
  Qed.

  Theorem Identity_l : forall a, e * a = a.
    intros.
    rewrite <- (Inverse_r a).
    rewrite Associativity.
    rewrite Inverse_l.
    trivial.
    Qed.

  Theorem DoubleInverse : forall a, i (i a) = a.
    intros.
    rewrite <- Identity_l.
    rewrite <- (Inverse_l (i a)).
    rewrite <- Identity_r at 1.
    rewrite Associativity.
    f_equal.
    symmetry.
    apply Inverse_l.
  Qed.

  Theorem InverseDistributivity : forall a b, i (a * b) = i b * i a.
    intros.
    rewrite <- Identity_l.
    rewrite <- (Inverse_l (a * b)).
    rewrite <- (Identity_r (i (a * b))) at 1.
    rewrite Associativity.
    f_equal.
    rewrite Associativity.
    rewrite <- (Associativity b).
    rewrite Inverse_r.
    rewrite Identity_l.
    auto.
  Qed.

  Theorem F_both_side_r : forall a b c, a = b -> a * c = b * c.
    intros.
    subst.
    trivial.
  Qed.

  Theorem F_both_side_l : forall a b c, a = b -> c * a = c * b.
    intros.
    subst.
    trivial.
  Qed.

  Theorem Cancellation_l : forall a b x, x * a = x * b -> a = b.
    intros.
    eapply F_both_side_l in H.
    repeat rewrite <- Associativity in H.
    erewrite Inverse_l in H.
    repeat rewrite Identity_l in H.
    trivial.
  Qed.

  Theorem Cancellation_r : forall a b x, a * x = b * x -> a = b.
    intros.
    eapply F_both_side_r in H.
    repeat rewrite Associativity in H.
    erewrite Inverse_r in H.
    repeat rewrite Identity_r in H.
    trivial.
  Qed.

  Theorem IdentityInverse : i e = e.
    rewrite <- (Inverse_l e) at 1.
    rewrite InverseDistributivity.
    trivial.
  Qed.

  Theorem Identity_l_unique : forall a p, p * a = a -> p = e.
    intros.
    eapply Cancellation_r.
    rewrite Identity_l.
    eauto.
  Qed.

  Theorem Inverse_r_unique : forall a b, a * b = e -> b = i a.
    intros.
    apply (Cancellation_l _ _ a).
    rewrite H.
    eauto.
  Qed.

  Theorem Inverse_l_unique : forall a b, a * b = e -> a = i b.
    intros.
    apply (Cancellation_r _ _ b).
    rewrite H.
    rewrite Inverse_l.
    trivial.
  Qed.

End Group. 