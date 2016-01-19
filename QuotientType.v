Require Import Program Arith Omega CoqCore.Tactic.
Set Implicit Arguments.
Set Universe Polymorphism.

Definition quotient A EQ := forall B (f : A -> B) (H : forall l r, EQ l r -> f l = f r), B.
Definition mk_quotient A EQ (a : A) : @quotient A EQ := fun _ f _ => f a.
Definition EQ_eq A EQ (l r : A) : EQ l r -> mk_quotient EQ l = mk_quotient EQ r :=
  ltac:(intros; unfold mk_quotient; repeat ext; auto).
Definition quotient_elim_eq A B C (l : @quotient A B) lf lfp rf rfp :
  lf = rf -> l C lf lfp = l C rf rfp.
  intros; subst; f_equal; apply proof_irrelevance.
Qed.

Definition PFE l r := l mod 5 = r mod 5.
Definition MF := quotient PFE.
Definition mk_MF (n : nat) : MF := mk_quotient PFE n.

Definition of_nat_lt_eq n lv lp rv rp :
  lv = rv -> @Fin.of_nat_lt lv n lp = @Fin.of_nat_lt rv n rp.
  intros; subst; f_equal; apply proof_irrelevance.
Qed.

Program Definition toFin (l : MF) : Fin.t 5 := 
  l (Fin.t 5) (fun n => @Fin.of_nat_lt (n mod 5) _ _) _.
Next Obligation.
  repeat match_destruct; omega.
Defined.
Next Obligation.
  apply of_nat_lt_eq.
  compute in *; trivial.
Defined.

Program Definition MFPlus (l r : MF) : MF := 
  l MF (fun ln => r MF (fun rn => mk_MF (ln + rn)) _) 
    (fun _ _ _ => quotient_elim_eq _ _ _ _).
Next Obligation.
  unfold mk_MF, mk_quotient, PFE in *; repeat ext.
  apply H2.
  rewrite (Nat.add_mod ln l0), (Nat.add_mod ln r0); f_equal; omega.
Qed.
Next Obligation.
  ext; apply EQ_eq; unfold PFE in *.
  rewrite (Nat.add_mod H), (Nat.add_mod H0); f_equal; omega.
Qed.

Program Definition MFMult (l r : MF) : MF := 
  l MF (fun ln => r MF (fun rn => mk_MF (ln * rn)) _) 
    (fun _ _ _ => quotient_elim_eq _ _ _ _).
Next Obligation.
  unfold mk_MF, mk_quotient, PFE in *; repeat ext.
  apply H2.
  rewrite (Nat.mul_mod ln l0), (Nat.mul_mod ln r0); do 2 f_equal; omega.
Qed.
Next Obligation.
  ext; apply EQ_eq; unfold PFE in *.
  rewrite (Nat.mul_mod H), (Nat.mul_mod H0); do 2 f_equal; omega.
Qed.

Program Definition Evil (l : MF) : nat := l nat id _.
Next Obligation.
Admitted.

Eval compute in toFin (MFPlus (mk_MF 4) (mk_MF 7)).
Eval compute in Evil (MFPlus (mk_MF 4) (mk_MF 7)).