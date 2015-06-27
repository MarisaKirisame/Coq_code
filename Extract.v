Require Export Classical Recdef Arith Omega.
Section Extract.
  Variable
    (T : Type) (Sat : T -> Prop)(Dec : forall a, { Sat a } + { ~ Sat a })
      (Gen : nat -> T)(Com : forall a, exists n, Gen n = a)(Ex : exists n, (Sat (Gen n))).
  Theorem WF : well_founded (fun (l r : nat) => l = S r /\ (forall n, n < r -> ~ Sat (Gen n))).
    unfold well_founded;intros.
    destruct Ex.
    assert(exists n, n + a > x) by (exists (S x); omega).
    destruct H0.
    generalize dependent a.
    induction x0.
    intros;simpl in *.
    constructor;intuition;subst;exfalso;eauto.
    intros.
    constructor;intuition.
  Qed.
  Definition Extract' (n : nat)(H : forall m, m < n -> ~ Sat (Gen m)) : { a | Sat a }.
    revert H.
    refine (Fix WF (fun _ => _) _ n).
    intuition.
    destruct (Dec (Gen x));eauto.
    eapply X;intuition.
    eapply H;eauto.
    destruct (le_dec x m);omega||(assert(x = m) by omega;subst;tauto).
  Defined.
  Definition Extract : { a | Sat a }.
    destruct (Dec (Gen 0));eauto.
    eapply (Extract' 0);intros.
    destruct m;omega.
  Defined.
  Definition exists_sig := Extract.
End Extract.