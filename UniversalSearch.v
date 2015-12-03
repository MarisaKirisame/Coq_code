Require Export Omega ClassicalFacts CoqCore.Tactic CoqCore.MoreFunction CoqCore.MoreList Recdef.
Set Implicit Arguments.
Section UniversalSearch.
  Variable T : Type.
  Variable P : T -> Prop.
  Variable Dec : forall t, { P t } + { ~P t }.
  Variable Machine : Type.
  Variable Step : Machine -> Machine + T.
  Definition StepN n m : Machine + T := 
    iterate n (fun x => match x with inl m' => Step m' | _ => x end) (inl m).
  Definition StepNS n m M : 
    StepN n m = inl M -> StepN (S n) m = Step M.
    unfold StepN; rewrite f_iterate.
    intros H; rewrite H; trivial.
  Qed.
  Variable AllMachine : nat -> Machine.
  Definition AMSN n m := StepN n (AllMachine m).
  Definition IsSolution n m := exists t, inr t = AMSN n m /\ P t.
  Variable HasSolution : exists n m, IsSolution n m.

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
  Definition R l r := l = S r /\ forall n m, IsSolution n m -> l <= n + m.
  Definition WFR : well_founded R.
    destruct HasSolution as [? []]; clear HasSolution.
    unfold well_founded; intros.
    assert({n | n = x + x0 - a}) by eauto; destruct H0.
    revert H e; revert a.
    induction x1; intros.
    destruct(lt_dec (x + x0) a).
    constructor; intros; exfalso; unfold R in *; ii; subst.
    specialize(H2 _ _ H); omega.
    assert(a = x + x0) by omega; subst.
    constructor; intros; exfalso; unfold R in *; ii; subst.
    specialize(H2 _ _ H); omega.
    constructor; intros; unfold R in *; ii; subst.
    apply IHx1; auto; omega.
  Qed.
  Definition UniversalSearchAux (n : nat) (m : list Machine) : 
    (forall l r, 
      l + r = n -> 
      match AMSN l r with
      | inl M => In M m
      | inr t => ~P t
      end) ->
    (forall l r, IsSolution l r -> n <= l + r) ->
    { t | P t }.
    revert m; refine (Wf.Fix WFR (fun _ => _) _ n).
    intros; unfold R in *.
    pose (map_step := split_sum (map Step m)).
    destruct (Exists_dec_cons P (snd map_step) Dec) as [[]|]; ii; eauto.
    eapply X; ii; eauto;
    try(
      specialize(H0 _ _ H1);
      match goal with |- _ <= ?l + ?r => 
        destruct (Nat.eq_dec x (l + r)); subst; omega || exfalso
      end;
      unfold IsSolution in *; destruct H1; ii;
      specialize(H _ _ eq_refl); repeat match_destruct; congruence).
    instantiate(m := AllMachine (S x) :: (fst map_step)).
    destruct l; simpl in *; subst; ii.
    invcs H1; specialize (H l r eq_refl).
    destruct (AMSN (S l) r) eqn:?.
    Apply AMSNSL; destruct Heqs; ii; right.
    compute[map_step]; apply split_sum_In_fst; rewrite <- H3, H2 in *; apply in_map; ii.
    Apply AMSNSR; ii.
    rewrite H2 in *; ii.
    destruct H2; ii.
    rewrite H3 in *.
    apply n0.
    apply Exists_exists; econstructor; ii; eauto.
    compute[map_step]; apply split_sum_In_snd; rewrite <- H4; apply in_map; ii.
  Defined.

  Program Definition UniversalSearch : { t | P t } := @UniversalSearchAux 0 [AllMachine 0] _ _.
  Next Obligation.
    simpl in *.
    destruct l, r; try omega.
    unfold AMSN; simpl in *; tauto.
  Defined.
  Solve All Obligations with program_simpl; omega.
End UniversalSearch.
Recursive Extraction UniversalSearch.