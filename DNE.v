Require Export Classical Recdef Arith Omega.
Section DNE.
  Variable
    (T : Type) (Sat : T -> Prop)(Dec : forall a, { Sat a } + { ~ Sat a })
      (Gen : nat -> T)(Com : forall a, exists n, Gen n = a)(DN : ~~exists n, (Sat (Gen n))).
  Theorem exists_ceiling : exists n, (Sat (Gen n)).
    destruct (classic (exists a, Sat a)).
    destruct H.
    destruct (Com x);subst;eauto.
    exfalso.
    apply DN.
    destruct 1;eauto.
  Qed.
  Theorem WF : well_founded (fun (l r : nat) => l = S r /\ (forall n, n < r -> ~ Sat (Gen n))).
    unfold well_founded;intros.
    destruct exists_ceiling.
    assert(exists n, n + a > x) by (exists (S x); omega).
    destruct H0.
    generalize dependent a.
    induction x0.
    intros;simpl in *.
    constructor;intuition;subst;exfalso;eauto.
    intros.
    constructor;intuition.
  Qed.
  Definition ConstructiveDNE' (n : nat)(H : forall m, m < n -> ~ Sat (Gen m)) : { a | Sat a }.
    revert H.
    refine (Fix WF (fun _ => _) _ n).
    intuition.
    destruct (Dec (Gen x));eauto.
    eapply X;intuition.
    eapply H;eauto.
    destruct (le_dec x m);omega||(assert(x = m) by omega;subst;tauto).
  Defined.
  Definition ConstructiveDNE : { a | Sat a }.
    destruct (Dec (Gen 0));eauto.
    eapply (ConstructiveDNE' 0);intros.
    destruct m;omega.
  Defined.
End DNE.

