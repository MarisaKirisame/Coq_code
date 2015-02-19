Require Import Program List Permutation Omega.
Require Import tactic permutation_type eq_dec count.

Set Implicit Arguments.

Inductive pos T : T -> list T -> Type :=
| pos_fst : forall t l, pos t (t :: l)
| pos_skip : forall t e l, pos t l -> pos t (e :: l).

Definition pos_lt_contain T (t : T) (p : pos t nil) : False.
  remember [].
  generalize dependent Heql.
  induction p;
  discriminate.
Defined.

Hint Resolve pos_lt_contain.

Fixpoint pos_nat T (t : T) l (p : pos t l) :=
  match p with
  | pos_fst _ _ => 0
  | pos_skip _ _ _ p' => S (pos_nat p')
  end.

Definition pos_before T (t : T) l (p : pos t l) := firstn (pos_nat p) l.
Definition pos_after T (t : T) l (p : pos t l) := skipn (S (pos_nat p)) l.

Theorem pos_before_pos_after : forall T (t : T) lt (p : pos t lt),
  pos_before p ++ t :: pos_after p = lt.
  induction p.
  trivial.
  simpl in *.
  f_equal.
  trivial.
Qed.

Definition eq_pos_dec : forall T (t : T) ls, eq_dec T -> eq_dec (pos t ls).
  intros.
  unfold eq_dec.
  induction ls.
  eauto.
  intros.
  dependent induction l;
  dependent induction r;
  try tauto;
  try (right;
       discriminate).
  clear IHl IHr.
  destruct (IHls l1 r).
  subst.
  tauto.
  right.
  intuition.
  invc H.
  apply Eqdep_dec.inj_pair2_eq_dec in H1.
  auto with *.
  trivial.
Defined.

Definition pos_In : forall T (t : T) lt, pos t lt -> In t lt.
  induction 1;
  simpl in *;
  tauto.
Qed.

Definition In_pos : forall T (t : T) (dec : eq_dec T)
  lt, In t lt -> { p : pos t lt | count_occ dec (pos_before p) t = 0 }.
  induction lt;
  intros;
  simpl in *.
  tauto.
  destruct (dec a t).
  subst.
  exists (pos_fst t lt).
  trivial.
  assert (In t lt).
  tauto.
  intuition.
  destruct X.
  exists (pos_skip a x).
  simpl in *.
  dedec dec;
  tauto.
Defined.

Definition pos_app : forall T (t : T) l r (p : pos t (l ++ r)),
  { pl : pos t l | pos_before pl = pos_before p } + 
  { pr : pos t r | l ++ pos_before pr = pos_before p }.
  dependent induction p.
  destruct l.
  simpl in *.
  destruct r.
  discriminate.
  invc x0.
  subst.
  eauto.
  simpl in *.
  invc x0.
  subst.
  left.
  exists (pos_fst t0 l).
  trivial.
  destruct l.
  simpl in *.
  subst.
  subst.
  eauto.
  simpl in *.
  invc x0.
  subst.
  specialize (IHp l r p).
  intuition.
  destruct a.
  left.
  exists (pos_skip t0 x).
  unfold pos_before in *.
  simpl in *.
  f_equal.
  trivial.
  destruct b.
  right.
  exists x.
  unfold pos_before in *.
  simpl in *.
  f_equal.
  trivial.
Defined.

Definition pos_eq_pos_nat :
  forall T (t : T) l (p p' : pos t l), p = p' -> pos_nat p = pos_nat p'.
  intros.
  subst.
  trivial.
Defined.

Definition pos_neq_pos_nat :
  forall T (t : T) l (p p' : pos t l), p <> p' -> pos_nat p <> pos_nat p'.
  intros.
  induction l.
  eauto.
  dependent induction p;
  dependent induction p'.
  tauto.
  discriminate.
  discriminate.
  clear IHp IHp'.
  simpl in *.
  assert (pos_nat p <> pos_nat p').
  apply IHl.
  intuition.
  subst.
  tauto.
  auto.
Defined.

Definition pos_nat_eq_pos :
  forall T (t : T) l (p p' : pos t l), pos_nat p = pos_nat p' -> p = p'.
  intros.
  induction l.
  eauto with *.
  dependent induction p;
  dependent induction p'.
  trivial.
  discriminate.
  discriminate.
  clear IHp IHp'.
  simpl in *.
  f_equal.
  auto.
Defined.

Definition pos_nat_neq_pos :
  forall T (dec : eq_dec T) (t : T) l (p p' : pos t l),
    pos_nat p <> pos_nat p' -> p <> p'.
  intros.
  induction l.
  eauto with *.
  dependent induction p;
  dependent induction p'.
  simpl in *.
  tauto.
  discriminate.
  discriminate.
  clear IHp IHp'.
  simpl in *.
  assert (p <> p').
  auto.
  intuition.
  inversion H1.
  apply Eqdep_dec.inj_pair2_eq_dec in H3.
  apply Eqdep_dec.inj_pair2_eq_dec in H3.
  tauto.
  intros.
  auto with *.
  trivial.
Defined.

Definition pos_extend_right T (l r : list T) t (p : pos t l) : 
  { p' : pos t (l ++ r) | pos_before p' = pos_before p }.
  induction l.
  eauto with *.
  dependent induction p.
  simpl in *.
  exists (pos_fst a (l ++ r)).
  trivial.
  specialize (IHl p).
  destruct IHl.
  simpl in *.
  exists (pos_skip a x).
  unfold pos_before in *.
  simpl in *.
  f_equal.
  trivial.
Defined.

Definition pos_extend_left T (l r : list T) t (p : pos t r) : 
  { p' : pos t (l ++ r) | pos_before p' = l ++ pos_before p }.
  induction l.
  simpl in *.
  eauto.
  destruct IHl.
  simpl in *.
  exists (pos_skip a x).
  unfold pos_before in *.
  simpl in *.
  f_equal.
  trivial.
Defined.

Theorem pos_before_length : forall T (t : T) lt (P : pos t lt),
  pos_nat P = length (pos_before P).
  dependent induction P.
  trivial.
  simpl in *.
  auto.
Qed.

Theorem pos_before_eq : forall T t (lt : list T) (P : pos t lt) t' lt'
  (P' : pos t' lt'), 
  pos_before P = pos_before P' -> pos_nat P = pos_nat P'.
  intros.
  repeat rewrite pos_before_length.
  f_equal.
  trivial.
Qed.

Theorem pos_before_l_app : forall T l t (lt : list T)
  (P : pos t lt) t' lt' (P' : pos t' lt'), 
  pos_before P = l ++ pos_before P' -> pos_nat P = length l + pos_nat P'.
  intros.
  repeat rewrite pos_before_length.
  rewrite H.
  rewrite app_length.
  trivial.
Qed.

Theorem pos_before_r_app : forall T l t (lt : list T)
  (P : pos t lt) t' lt' (P' : pos t' lt'), 
  pos_before P = pos_before P' ++ l -> pos_nat P = pos_nat P' + length l.
  intros.
  repeat rewrite pos_before_length.
  rewrite H.
  rewrite app_length.
  trivial.
Qed.

Definition pos_contract_left T (l r : list T) (t : T) (P : pos t (l ++ r)) :
  pos_nat P < length l -> { p : pos t l | pos_before p = pos_before P }.
  induction l;
  intros;
  simpl in *.
  omega.
  dependent induction P.
  exists (pos_fst a l).
  trivial.
  clear IHP.
  simpl in *.
  assert (pos_nat P < length l).
  omega.
  specialize (IHl P H0).
  destruct IHl.
  exists (pos_skip a x).
  unfold pos_before in *.
  simpl in *.
  f_equal.
  trivial.
Defined.

Definition pos_contract_right T (l r : list T) (t : T) (P : pos t (l ++ r)) :
  pos_nat P >= length l ->
    { p : pos t r | l ++ pos_before p = pos_before P }.
  induction l;
  intros;
  simpl in *.
  eauto.
  dependent induction P;
  simpl in *.
  omega.
  clear IHP.
  assert (pos_nat P >= length l).
  omega.
  specialize (IHl P H0).
  destruct IHl.
  exists x.
  unfold pos_before in *.
  simpl in *.
  f_equal.
  trivial.
Defined.

Theorem count_occ_before_count_occ_after T dec (t : T) l r
  (P : pos t (l ++ t :: r)) :
    count_occ dec l t = count_occ dec (pos_before P) t -> 
      count_occ dec r t = count_occ dec (pos_after P) t.
  intros.
  induction l;
  dependent induction P;
  simpl in *;
  repeat dedec dec;
  trivial;
  try discriminate;
  try tauto;
  subst;
  eauto.
Qed.

Theorem pos_skip_neq : forall T (e : T) t l (p p' : pos t l),
  pos_skip e p <> pos_skip e p' -> p <> p'.
  intros.
  intuition.
  subst.
  tauto.
Qed.