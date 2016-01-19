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
Program Definition MFPlus (l r : MF) : MF := 
  l MF (fun ln => r MF (fun rn => mk_MF (ln + rn)) _) 
    (fun _ _ _ => quotient_elim_eq _ _ _ _).
Next Obligation.
  unfold mk_MF, mk_quotient, PFE in *; repeat ext.
  apply H2.
  rewrite (Nat.add_mod ln l0), (Nat.add_mod ln r0); f_equal; omega.
Defined.
Next Obligation.
  ext; apply EQ_eq; unfold PFE in *.
  rewrite (Nat.add_mod H), (Nat.add_mod H0); f_equal; omega.
Defined.