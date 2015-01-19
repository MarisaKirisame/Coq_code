Load Equiv.

Definition Assertion := state -> Prop.

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st' sta, ceval c sta st st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
  unfold hoare_triple.
  trivial.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
  unfold hoare_triple.
  intuition.
  eauto with *.
Qed.

Goal {{fun _ => True}} X ::= (ANum 5) {{fun st => st X = 5}}.
  unfold hoare_triple.
  intros.
  invc_stop.
  trivial.
Qed.

Goal {{fun st => st X = 2}} X ::= (APlus (AId X) (ANum 1)) {{fun st => st X = 3}}.
  unfold hoare_triple.
  intros.
  invc_stop.
  simpl in *.
  unfold update.
  destruct eq_id_dec.
  omega.
  tauto.
Qed.

Goal {{fun _ => True}} X ::= (ANum 5);; Y ::= (ANum 0) {{fun st => st X = 5}}.
  unfold hoare_triple.
  intros.
  invc_stop.
  trivial.
Qed.

Goal {{fun st => st X = 2 /\ st X = 3}} X ::= (ANum 5) {{fun st => st X = 0}}.
  unfold hoare_triple.
  intros.
  omega.
Qed.

Goal {{fun _ => False}} SKIP {{fun _ => True}}.
  split.
Qed.

Goal {{fun _ => True}} WHILE BTrue DO SKIP END {{fun _ => False}}.
  unfold hoare_triple.
  intros.
  dependent induction H;
  invc_stop;
  simpl in *.
  tauto.
Qed.

Goal
  {{fun st => st X = 0}}
  WHILE (BEq (AId X) (ANum 0)) DO X ::= (APlus (AId X) (ANum 1)) END
  {{fun st => st X = 1}}.
  unfold hoare_triple.
  intros.
  invc H;
  simpl in *;
  rewrite H0 in *;
  try discriminate;
  invc_stop.
  invc H8;
  invc_stop;
  simpl in *;
  unfold update in *;
  destruct eq_id_dec;
  rewrite H0 in *;
  try omega;
  try tauto;
  discriminate.
Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a, {{ Q [X |-> a] }} X ::= a {{ Q }}.
  unfold hoare_triple.
  intros.
  invc H.
  trivial.
Qed.

Goal
  {{ (fun st => st X <= 5) [X |-> (APlus (AId X) (ANum 1))] }}
  X ::= (APlus (AId X) (ANum 1))
  {{ (fun st => st X <= 5) }}.
  apply hoare_asgn.
Qed.

Goal ~forall a, {{ fun _ => True }} X ::= a {{ fun st => st X = aeval st a }}.
  intuition.
  assert(exists s, ceval (X ::= APlus (AId X) (ANum 1)) SContinue empty_state s).
  eauto.
  invc H0.
  specialize (H (APlus (AId X)(ANum 1)) empty_state x SContinue).
  simpl in *.
  intuition.
Qed.