Require Export List Program CoqCore.Tactic Omega ClassicalFacts.
Set Implicit Arguments.
Axiom PE : prop_extensionality.
Variable T : Type.
Variable P : T -> Prop.
Variable Dec : forall t, { P t } + { ~P t }.
Variable Machine : Type.
Variable Step : Machine -> Machine + T.
Fixpoint iterate { T } n F (x : T) :=
  match n with
  | 0 => x
  | S n' => iterate n' F (F x)
  end.
Definition f_iterate T n f : forall x : T, iterate (S n) f x = f (iterate n f x).
  induction n; simpl in *; trivial.
Qed.
Definition StepN n m : Machine + T := 
  iterate n (fun x => match x with inl m' => Step m' | _ => x end) (inl m).
Definition StepNS n m M : 
  StepN n m = inl M -> StepN (S n) m = Step M.
  unfold StepN; rewrite f_iterate.
  intros H; rewrite H; trivial.
Qed.
Variable AllMachine : nat -> Machine.
Definition AMSN n m := StepN n (AllMachine m).
Definition HasSolution n m := exists t, inr t = AMSN n m /\ P t.
Variable SolutionExists : exists n m, HasSolution n m.
Definition SmallestSolution n m : Prop := 
  HasSolution n m /\ forall l r, HasSolution l r -> m + n <= l + r.
Variable SmallestSolutionExists : exists n m, SmallestSolution n m.
Fixpoint split_sum L R (l : list (L + R)) : list L * list R :=
  match l with
  | [] => ([],[])
  | inl h :: t => let (l', r') := split_sum t in (h :: l', r')
  | inr h :: t => let (l', r') := split_sum t in (l', h :: r')
  end.

Definition Exists_dec_cons (A : Type) (P : A -> Prop) (l : list A) :
  (forall x : A, {P x} + {~ P x}) -> {x | P x /\ In x l} + {~Exists P l}.
  induction l; intuition idtac.
  right; intros; inversion H.
  destruct a0; intuition eauto with *.
  destruct (X a); [intuition eauto with *|].
  right; intros; inversion H; eauto.
Defined.
Definition AMSNSL l r m : 
  AMSN (S l) r = inl m -> exists m', AMSN l r = inl m' /\ Step m' = inl m.
  intros; unfold AMSN in *.
  revert m H; generalize (AllMachine r); clear r.
  induction l; intros; unfold StepN in *.
  simpl in *; eauto.
  rewrite !f_iterate in *.
  repeat match_destruct; try congruence.
  specialize (IHl m m2); rewrite !f_iterate, !H0 in *; ii.
  destruct H2; ii.
  invcs H3; eauto.
Qed.
Definition AMSNSR l r t : 
  AMSN (S l) r = inr t -> 
  AMSN l r = inr t \/ exists m', AMSN l r = inl m' /\ Step m' = inr t.
  intros; unfold AMSN in *; unfold StepN in *; rewrite !f_iterate in *.
  repeat match_destruct; try congruence; eauto.
Qed.
Search(well_founded).
Program Fixpoint UniversalSearchAux 
  (n : {n | forall l r, SmallestSolution l r -> n <= l + r})
  (m : list Machine) 
  {wf (fun l r => r < l /\ forall n m, SmallestSolution n m -> l <= n + m) n } : 
  (forall l r, 
    l + r = n -> 
    match AMSN l r with
    | inl M => In M m
    | inr t => ~P t
    end) ->
  { t | P t } :=
  fun H =>
  let map_step := split_sum (map Step m) in
  match Exists_dec_cons P (snd map_step) Dec with
  | inleft X => X
  | inright X => @UniversalSearchAux (S n) (AllMachine (S n) :: (fst map_step)) _ _
  end.
Obligation Tactic := repeat (ii; subst).
Definition split_sum_In_fst L R (l : list (L + R)) t : 
  In (inl t) l <-> In t (fst (split_sum l)).
  split; induction l; intros; simpl in *; trivial; ii; subst; simpl in *;
  destruct split_sum eqn:?; simpl in *; ii.
  destruct a; simpl in *; ii; subst; ii.
Defined.
Definition split_sum_In_snd L R (l : list (L + R)) t : 
  In (inr t) l <-> In t (snd (split_sum l)).
  split; induction l; intros; simpl in *; trivial; ii; subst; simpl in *;
  destruct split_sum eqn:?; simpl in *; ii.
  destruct a; simpl in *; ii; subst; ii.
Defined.
Next Obligation.
  destruct n; simpl in *.
  specialize (l0 l r); ii.
  destruct (Nat.eq_dec (l + r) x); subst; try omega.
  exfalso; specialize(H l r eq_refl); unfold HasSolution in *.
  unfold SmallestSolution, HasSolution in *; ii.
  destruct H2; match_destruct; ii; congruence.
Defined.

Next Obligation.
  compute[proj1_sig]; try omega.
  destruct n; simpl in *.
  pose proof (l n0 m0); ii.
  destruct (Nat.eq_dec (n0 + m0) x); subst; try omega.
  exfalso; specialize(H n0 m0 eq_refl); unfold HasSolution in *.
  unfold SmallestSolution, HasSolution in *; ii.
  destruct H1; match_destruct; ii; congruence.
Defined.

Next Obligation.
  destruct l, n; simpl in *; subst; ii.
  invcs H0; specialize(H l r eq_refl); match_destruct.
  Apply AMSNSL; destruct H0; ii; rewrite H1 in *.
  right; apply split_sum_In_fst; rewrite <- H2; apply in_map; ii.
  Apply AMSNSR; ii.
  rewrite H2 in *; ii.
  destruct H2; ii; rewrite H2 in *.
  apply X; apply Exists_exists; econstructor; ii; eauto.
  apply split_sum_In_snd; rewrite <- H3; apply in_map; ii.
Defined.
Definition StepSmallestSolution n := exists l r, SmallestSolution l r /\ n = l + r.
Next Obligation.
  apply measure_wf; destruct SmallestSolutionExists as [? []].
  match goal with |- well_founded ?P => replace P with (fun l r : nat => r < l <= (x + x0)) end.
  apply Nat.gt_wf.
  repeat ext; apply PE; unfold SmallestSolution in *; ii.
  specialize(H3 n m H6); omega.
  eapply H5; eauto.
Defined.
Program Definition UniversalSearch : { t | P t } := UniversalSearchAux 0 [AllMachine 0] _.
Next Obligation.
  omega.
Defined.
Next Obligation.
  simpl in *.
  destruct l, r; try omega.
  unfold AMSN; simpl in *; tauto.
Defined.