Load Imp.

Notation "'LETOPT' x <== e1 'IN' e2" :=
  (match e1 with
  | Some x => e2
  | None => None
  end)
  (right associativity, at level 60).

Fixpoint ceval_step (st : state)(c : com) (i : nat) : option (state * status) :=
  match i with
  | O => None
  | S i' =>
    match c with
    | SKIP =>
        Some (st, SContinue)
    | l ::= a1 =>
        Some ((update st l (aeval st a1)), SContinue)
    | c1 ;; c2 =>
        LETOPT st' <== ceval_step st c1 i' IN
          match (snd st') with
          | SContinue => ceval_step (fst st') c2 i'
          | SBreak => Some ((fst st'), SBreak)
          end 
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step st c1 i'
            else ceval_step st c2 i'
    | WHILE b1 DO c1 END =>
      if (beval st b1)
        then LETOPT st' <== ceval_step st c1 i' IN
          match (snd st') with
          | SContinue => ceval_step (fst st') c i'
          | SBreak => Some ((fst st'), SContinue)
          end
        else Some (st, SContinue)
    | BREAK => Some (st, SBreak)
    end
  end.

Definition PEven_X_Z := 
  WHILE (BLe (ANum 2) (AId X)) DO
    X ::= (AMinus (AId X) (ANum 2))
  END;;
  Z ::= (AId X).

Eval compute in 
  match ceval_step (update empty_state X 10) PEven_X_Z 10
  with
  | None => None
  | Some (st, _) => Some (st Z)
  end.

Hint Constructors ceval.

Theorem ceval_step__ceval: forall c st st',
  (exists i, ceval_step st c i = Some st') ->
    ceval c (snd st') st (fst st').
  intros.
  invc H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction x;
  try discriminate.
  intros.
  destruct c;
  simpl in *;
  invc H0;
  simpl in *;
  try solve [repeat constructor];
  try destruct (beval st b) eqn:Heqb;
  destruct st';
  simpl in *;
  try apply IHx in H1;
  try solve [invc H1;auto];
  simpl in *;
  auto;
  match goal with
  | [ H : LETOPT _ <== ?d IN _ = _ |- _ ] => destruct d eqn:Heqc
  end;
  try discriminate;
  destruct p;
  simpl in *;
  destruct s2;
  apply IHx in Heqc;
  simpl in *;
  try match goal with
  | [ H : Some _ = Some _ |- _ ] => invc H1
  end;
  auto;
  apply IHx in H1;
  simpl in *;
  eauto;
  destruct s0;
  eauto;
  invc H1.
Qed.

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
    ceval_step st c i1 = Some st' ->
      ceval_step st c i2 = Some st'.
  induction i1;
  simpl in *.
  discriminate.
  destruct i2;
  intros.
  omega.
  destruct c;
  destruct st';
  trivial;
  simpl in *;
  try destruct (beval st b) eqn:Heqb;
  auto with *;
  match goal with
  | [ H : LETOPT _ <== ceval_step ?l ?r i1 IN _ = _ |- _ ] => 
    destruct (ceval_step l r i1) eqn:Heqc1;
    destruct (ceval_step l r i2) eqn:Heqc2
  end;
  try discriminate;
  destruct p;
  try destruct p0;
  simpl in *;
  eapply (IHi1 i2) in Heqc1;
  try omega;
  rewrite Heqc1 in *;
  invc Heqc2;
  destruct s4;
  auto with *.
Qed.

Theorem ceval__ceval_step: forall c st st' sta,
  ceval c sta st st' ->
    exists i, ceval_step st c i = Some (st', sta).
  intros c st st' sta Hce.
  induction Hce;
  subst;
  try destruct IHHce1, IHHce2;
  try destruct IHHce;
  try solve
  [
    exists 1;
    trivial
  ];
  try exists (S (x + x0));
  try exists (S x);
  try exists 1;
  simpl in *;
  try rewrite H;
  try rewrite H0;
  trivial;
  repeat match goal with
  | [H : ceval_step _ _ _ = _ |- _] => 
    progress (apply (ceval_step_more (i2 := x + x0)) in H; try omega)
  end;
  [
    destruct (ceval_step st c1 (x + x0)) eqn:Heq|
    destruct (ceval_step st c (x + x0)) eqn:Heq
  ];
  try discriminate;
  destruct p;
  simpl in *;
  match goal with
  | [H : Some _ = Some _ |- _] => invc H
  end;
  trivial.
Qed.

Theorem ceval_and_ceval_step_coincide: forall c st st' sta,
      ceval c sta st st'
  <-> exists i, ceval_step st c i = Some (st', sta).
  intros c st st'.
  split.
  apply ceval__ceval_step.
  apply ceval_step__ceval.
Qed.
