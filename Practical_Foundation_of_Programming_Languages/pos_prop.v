Require Import List Program Omega Arith.
Require Import tactic count eq_dec pos remove.

Set Implicit Arguments.

Definition pos_before_pos T (t : T) lt (P P' : pos t lt) : Prop := 
  pos_nat P < pos_nat P'.
Definition pos_after_pos T (t : T) lt (P P' : pos t lt) : Prop :=
  pos_nat P > pos_nat P'.

Theorem pos_before_pos_or_pos_after_pos_pos_neq : forall T (t : T) lt
  (P P' : pos t lt),
  ((pos_before_pos P P') \/ (pos_after_pos P P')) -> P <> P'.
  intuition;
  subst;
  unfold pos_before_pos in *;
  unfold pos_after_pos in *;
  omega.
Qed.

Theorem pos_neq_pos_before_pos_or_pos_after_pos : forall T (t : T) lt
  (P P' : pos t lt),
  P <> P' -> ((pos_before_pos P P') + (pos_after_pos P P')).
  intuition.
  unfold pos_before_pos in *.
  unfold pos_after_pos in *.
  apply pos_neq_pos_nat in H.
  destruct (Compare_dec.le_lt_dec (pos_nat P) (pos_nat P'));
  auto with *.
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

Theorem pos_before_pos_pos_after_pos : forall T (t : T) l (p p' : pos t l),
  pos_before_pos p p' -> pos_after_pos p' p.
  unfold pos_before_pos, pos_after_pos.
  intros.
  omega.
Qed.

Theorem pos_after_pos_pos_before_pos : forall T (t : T) l (p p' : pos t l),
  pos_after_pos p' p -> pos_before_pos p p'.
  unfold pos_before_pos, pos_after_pos.
  intros.
  omega.
Qed.

Theorem pos_before_pos_lt : forall T (dec : eq_dec T) t l (p p' : pos t l),
  pos_before_pos p p' -> 
    count_occ dec (pos_before p) t < count_occ dec (pos_before p') t.
  intros.
  unfold pos_before_pos in *.
  dependent induction l.
  eauto with *.
  dependent induction p;
  dependent induction p';
  try clear IHp;
  try clear IHp';
  simpl in *;
  try dedec dec;
  subst;
  try omega;
  try tauto;
  eauto with *.
Qed.

Theorem pos_after_pos_gt : forall T (dec : eq_dec T) t l (p p' : pos t l),
  pos_after_pos p p' -> 
    count_occ dec (pos_before p) t > count_occ dec (pos_before p') t.
  intros.
  apply pos_after_pos_pos_before_pos in H.
  eapply pos_before_pos_lt in H.
  eauto.
Qed.