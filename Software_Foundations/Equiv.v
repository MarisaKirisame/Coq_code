Load ImpCEvalFun.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state) sta,
    ceval c1 sta st st' <-> ceval c2 sta st st'.

Theorem skip_right: forall  c,
  cequiv
    (c;; SKIP)
    c.
  unfold cequiv.
  intros.
  intuition;
  invc_stop;
  trivial.
  destruct sta;
  eauto.
Qed.

Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
  intros.
  split;
  intuition;
  invc_stop;
  eauto with *.
Qed.

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
  intros.
  split;
  intros;
  invc_stop;
  simpl in *;
  destruct (beval st b) eqn:Heq;
  try solve
  [
    eapply E_IfFalse;
    simpl in *;
    try rewrite Heq;
    trivial
  ];
  try solve
  [
    apply E_IfTrue;
    simpl in *;
    try rewrite Heq;
    trivial
  ];
  discriminate.
Qed.

Ltac FEX :=
  apply functional_extensionality;
  unfold update;
  intros;
  destruct eq_id_dec;
  subst;
  trivial.

Theorem identity_assignment : forall (X:id),
  cequiv
    (X ::= AId X)
    SKIP.
  unfold cequiv.
  intuition.
  invc H.
  simpl in *.
  replace (update st X0 (st X0)) with st.
  trivial.
  FEX.
  invc H.
  replace st' with (update st' X0 (st' X0)) at 2.
  auto.
  FEX.
Qed.

Theorem assign_aequiv : forall X e,
  aequiv (AId X) e ->
    cequiv SKIP (X ::= e).
  intros.
  unfold aequiv in *.
  unfold cequiv.
  intuition;
  simpl in *.
  invc H0.
  replace st' with (update st' X0 (st' X0)) at 2.
  auto.
  FEX.
  invc H0.
  replace (update st X0 (aeval st e)) with st.
  trivial.
  FEX.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (c1;;c2) (c1';;c2').
  unfold cequiv.
  intuition;
  invc_stop;
  (constructor||econstructor);
  (apply H||apply H0);
  eauto.
Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
  unfold bequiv.
  unfold cequiv.
  intuition;
  invc_stop;
    (apply E_IfTrue;
    [eauto;fail|])
  ||
    (apply E_IfFalse;
    [eauto|]);
  apply H0||apply H1;
  trivial.
Qed.

Inductive var_not_used_in_aexp (X:id) : aexp -> Prop :=
| VNUNum: forall n, var_not_used_in_aexp X (ANum n)
| VNUId: forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
| VNUPlus: forall a1 a2,
    var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
        var_not_used_in_aexp X (APlus a1 a2)
| VNUMinus: forall a1 a2,
    var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
        var_not_used_in_aexp X (AMinus a1 a2)
| VNUMult: forall a1 a2,
    var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
        var_not_used_in_aexp X (AMult a1 a2).

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
    aeval (update st i ni) a = aeval st a.
  intros.
  generalize dependent H.
  unfold update.
  induction a;
  intros;
  simpl in *;
  invc H;
  trivial;
  auto.
  destruct eq_id_dec;
  subst;
  tauto.
Qed.

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i' => if eq_id_dec i i' then u else AId i'
  | APlus a1 a2 => APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 => AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2 => AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Definition update_equiv_property : forall n st i1 a1,
  var_not_used_in_aexp i1 a1 ->
    aeval st a1 = aeval (update st i1 n) a1.
  induction 1;
  trivial;
  simpl in *;
  unfold update;
  try destruct eq_id_dec;
  subst;
  auto;
  tauto.
Qed.

Ltac UPD :=
  unfold update;
  destruct eq_id_dec;
  subst;
  trivial;
  try discriminate;
  try tauto;
  simpl in *.

Theorem update_equiv : forall i1 a1 n st,
  var_not_used_in_aexp i1 a1 -> 
    aeval (update st i1 n) a1 = aeval st a1.
  intros.
  induction H;
  trivial;
  simpl in *;
  intuition.
  UPD.
Qed.

Theorem aexpr_subst_equiv : forall i1 a1 a2 st,
  var_not_used_in_aexp i1 a1 ->
    aeval (update st i1 (aeval st a1)) (subst_aexp i1 a1 a2) =
    aeval (update st i1 (aeval st a1)) a2.
  destruct a1;
  intros;
  simpl in *;
  invc H;
  induction a2;
  simpl in *;
  auto;
  try solve [repeat UPD];
  simpl in *;
  destruct eq_id_dec;
  subst;
  simpl in *;
  trivial;
  unfold update at 3;
  destruct eq_id_dec;
  subst;
  f_equal;
  try apply update_equiv;
  trivial;
  tauto.
Qed.

Definition subst_equiv_property : forall i1 i2 a1 a2,
  var_not_used_in_aexp i1 a1 ->
    cequiv
      (i1 ::= a1;; i2 ::= a2)
      (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).
  intros.
  unfold cequiv.
  intuition;
  invc_stop;
  econstructor;
  auto;
  repeat(
    replace (aeval st a1 + 0) with (aeval st a1);
    trivial);
  constructor;
  try apply aexpr_subst_equiv;
  try symmetry;
  try apply aexpr_subst_equiv;
  trivial.
Qed.

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
  unfold cequiv.
  intuition.
  specialize (H empty_state empty_state SContinue).
  intuition.
  assert(ceval SKIP SContinue empty_state empty_state).
  trivial.
  intuition.
  clear H H1.
  remember (WHILE BTrue DO SKIP END).
  dependent induction H2;
  invc Heqc;
  try discriminate;
  simpl in *;
  invc_stop.
  tauto.
Qed.