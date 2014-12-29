Load Poly.

Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
  intros.
  tauto.
Qed.

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
  intros.
  tauto.
Qed.

Theorem iff_refl : forall P : Prop, 
  P <-> P.
  intros.
  tauto.
Qed.

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
  intros.
  tauto.
Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
  intros.
  tauto.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
  intros.
  tauto.
Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
  intros.
  destruct b.
  simpl in *.
  subst.
  auto.
  simpl in *.
  auto.
Qed.

Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
  intros.
  destruct b.
  simpl in *.
  auto.
  simpl in *.
  subst.
  auto.
Qed.

Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
  intros.
  destruct b, c;
  simpl in *;
  auto;
  discriminate.
Qed.

Goal forall P : Prop, P -> ~~P.
  intros.
  auto.
Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
  intros.
  auto.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
  intros.
  tauto.
Qed.

Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P: Prop,
  ~~P -> P.
Definition excluded_middle := forall P: Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q: Prop,
  ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q: Prop,
  (P->Q) -> (~P \/ Q).

Goal peirce -> classic.
  unfold peirce.
  unfold classic.
  intros.
  apply (H _ (~P)).
  intros.
  tauto.
Qed.

Goal classic -> excluded_middle.
  unfold classic.
  unfold excluded_middle.
  intros.
  apply H.
  unfold not.
  auto.
Qed.

Goal excluded_middle -> de_morgan_not_and_not.
  unfold excluded_middle.
  unfold de_morgan_not_and_not.
  intros.
  destruct (H (P \/ Q)).
  trivial.
  unfold not in *.
  absurd(P \/ Q -> False).
  tauto.
  trivial.
Qed.

Goal de_morgan_not_and_not -> implies_to_or.
  unfold de_morgan_not_and_not.
  unfold implies_to_or.
  intros.
  apply H.
  unfold not.
  intros.
  destruct H1.
  apply H1.
  intros.
  apply H2.
  auto.
Qed.

Goal implies_to_or -> peirce.
  unfold implies_to_or.
  unfold peirce.
  intros.
  assert(~P \/ P).
  auto.
  destruct H1.
  tauto.
  trivial.
Qed.

Theorem excluded_middle_irrefutable: forall(P:Prop), ~~ (P \/ ~ P).
  unfold not.
  intros.
  auto.
Qed.

Theorem false_beq_nat : forall n m : nat,
  n <> m ->
  beq_nat n m = false.
  induction n.
  intros.
  simpl in *.
  destruct m.
  tauto.
  trivial.
  intros.
  destruct m.
  simpl in *.
  trivial.
  apply IHn.
  auto.
Qed.

Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
  induction n;
  destruct m.
  intros.
  simpl in *.
  discriminate.
  intros.
  simpl in *.
  trivial.
  intros.
  simpl in *.
  discriminate.
  intros.
  simpl in *.
  auto.
Qed.