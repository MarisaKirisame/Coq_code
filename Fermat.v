Require Export Arith Classical.
Definition Fermat n := forall a b c, a ^ n + b ^ n <> c ^ n.
Theorem FermatMNN n m : ~Fermat (m * n) -> ~Fermat n.
  simpl; unfold Fermat in *; intuition.
  apply H; intros.
  specialize (H0 (a ^ m) (b ^ m) (c ^ m)).
  rewrite <- !Nat.pow_mul_r in *.
  simpl in *; intuition.
Qed.
Theorem FermatM n m : Fermat n -> Fermat (m * n).
  pose proof(FermatMNN n m).
  intros; destruct (classic (Fermat (m * n))); intuition.
Qed.