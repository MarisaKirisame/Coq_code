Require Fin Vector.
Require Import Program Arith Omega CoqCore.Tactic.
Set Implicit Arguments.

Definition Vector_get { A } { n } (v : Vector.t A n) (f : Fin.t n) : A.
  induction v.
  + invcs f.
  + invcs f; [|apply IHv]; ii.
Defined.

Definition Vector_drop { A } { n } (v : Vector.t A n) (f : Fin.t n) : Vector.t A (pred n).
  induction v.
  + invcs f.
  + invcs f; [|destruct n; try solve [invcs H0]; constructor]; ii.
Defined.

Program Definition Fin_split l r (f : Fin.t (l + r)) : 
  { res : Fin.t l | ` (Fin.to_nat res) = ` (Fin.to_nat f) } + 
  { res : Fin.t r | ` (Fin.to_nat res) = ` (Fin.to_nat f) - l } :=
  match lt_dec (Fin.to_nat f) l with
  | in_left => inl (@Fin.of_nat_lt (Fin.to_nat f) l _)
  | in_right => inr (@Fin.of_nat_lt (Fin.to_nat f - l) r _)
  end.
Solve All Obligations with program_simpl; destruct Fin.to_nat; simpl in *; omega.
Solve All Obligations with program_simpl; rewrite Fin.to_nat_of_nat; trivial.

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