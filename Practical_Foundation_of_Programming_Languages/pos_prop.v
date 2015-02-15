Require Import Program pos remove.

Set Implicit Arguments.

Definition pos_before_pos T (t : T) lt (P P' : pos t lt) : Prop := 
  pos_nat P < pos_nat P'.
Definition pos_after_pos T (t : T) lt (P P' : pos t lt) : Prop :=
  pos_nat P > pos_nat P'.

Theorem pos_neq_pos_before_or_after_pos : forall T (t : T) lt
  (P P' : pos t lt),
  ((pos_before_pos P P') \/ (pos_after_pos P P')) <-> P <> P'.
  intuition;
  subst;
  unfold pos_before_pos in *;
  unfold pos_after_pos in *;
  try apply pos_neq_pos_nat in H;
  omega.
Qed.

Theorem pos_before_pos_after T (t : T) l r (p : pos t (l ++ t :: r)) : 
  pos_before p = l -> pos_after p = r.
  intros.
  induction l.
  simpl in *.
  dependent induction p.
  trivial.
  discriminate.
  simpl in *.
  dependent induction p.
  discriminate.
  clear IHp.
  specialize (IHl p).
  unfold pos_before in *.
  unfold pos_after in *.
  simpl in *.
  inversion H.
  tauto.
Qed.