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