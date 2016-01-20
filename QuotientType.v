Require Import Program Arith Omega CoqCore.Tactic.
Set Implicit Arguments.
Set Universe Polymorphism.

Definition quotient A EQ := forall B (f : A -> B) (H : forall l r, EQ l r -> f l = f r), B.
Definition mk_quotient A EQ (a : A) : @quotient A EQ := fun _ f _ => f a.
Definition EQ_eq A EQ (l r : A) : EQ l r -> mk_quotient EQ l = mk_quotient EQ r :=
  ltac:(intros; unfold mk_quotient; repeat ext; auto).
Definition quotient_elim_eq A B C (q : @quotient A B) lf lfp rf rfp :
  lf = rf -> q C lf lfp = q C rf rfp.
  intros; subst; f_equal; apply proof_irrelevance.
Qed.

Definition MFE l r := l mod 5 = r mod 5.
Definition MFR := quotient MFE.
Definition mk_MFR (n : nat) : MFR := mk_quotient MFE n.

Definition of_nat_lt_eq n lv lp rv rp :
  lv = rv -> @Fin.of_nat_lt lv n lp = @Fin.of_nat_lt rv n rp.
  intros; subst; f_equal; apply proof_irrelevance.
Qed.

Program Definition toFin (l : MFR) : Fin.t 5 := 
  l (Fin.t 5) (fun n => @Fin.of_nat_lt (n mod 5) _ _) _.
Next Obligation.
  repeat match_destruct; omega.
Defined.
Next Obligation.
  apply of_nat_lt_eq.
  compute in *; trivial.
Defined.

Program Definition MFRPlus (l r : MFR) : MFR := 
  l MFR (fun ln => r MFR (fun rn => mk_MFR (ln + rn)) _) 
    (fun _ _ _ => quotient_elim_eq _ _ _ _).
Next Obligation.
  unfold mk_MFR, mk_quotient, MFE in *; repeat ext.
  apply H2.
  rewrite (Nat.add_mod ln l0), (Nat.add_mod ln r0); f_equal; omega.
Qed.
Next Obligation.
  ext; apply EQ_eq; unfold MFE in *.
  rewrite (Nat.add_mod H), (Nat.add_mod H0); f_equal; omega.
Qed.

Program Definition MFRMult (l r : MFR) : MFR := 
  l MFR (fun ln => r MFR (fun rn => mk_MFR (ln * rn)) _) 
    (fun _ _ _ => quotient_elim_eq _ _ _ _).
Next Obligation.
  unfold mk_MFR, mk_quotient, MFE in *; repeat ext.
  apply H2.
  rewrite (Nat.mul_mod ln l0), (Nat.mul_mod ln r0); do 2 f_equal; omega.
Qed.
Next Obligation.
  ext; apply EQ_eq; unfold MFE in *.
  rewrite (Nat.mul_mod H), (Nat.mul_mod H0); do 2 f_equal; omega.
Qed.

Goal mk_MFR 2 = mk_MFR 7.
  unfold mk_MFR, mk_quotient; repeat ext.
  apply H1; unfold MFE; trivial.
Qed.