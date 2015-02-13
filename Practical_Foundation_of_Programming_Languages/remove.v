Require Import Plus Permutation Program List.
Require Import bring_to_front count tactic pos permutation_type eq_dec.

Set Implicit Arguments.

Definition remove_fst T (dec : eq_dec T) (t : T) l : In t l -> 
  { l' : (list T * list T) | 
      l = (fst l') ++ [t] ++ (snd l') /\ count_occ dec (fst l') t = 0 }.
  induction l.
  simpl in *.
  tauto.
  intros.
  destruct (dec t a).
  subst.
  exists (@nil T, l).
  simpl in *.
  tauto.
  assert (In t l).
  destruct H.
  subst.
  tauto.
  trivial.
  clear H.
  intuition.
  destruct X.
  destruct x.
  simpl in *.
  intuition.
  subst.
  exists ((a :: l0), l1).
  simpl in *.
  intuition.
  destruct (dec a t).
  subst.
  tauto.
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

Hint Rewrite count_count_occ.

Theorem count_occ_app : forall T dec (t : T) l r,
  count_occ dec (l ++ r) t = count_occ dec l t + count_occ dec r t.
  intros.
  repeat rewrite count_count_occ.
  apply count_app.
Qed.

Theorem count_occ_lt_In : forall T dec (t : T) l, In t l <-> count_occ dec l t > 0.
  intuition;
  induction l;
  simpl in *;
  try destruct (dec a t);
  subst;
  (omega||tauto).
Qed.

Definition count_occ_lt_pos_find T (dec : eq_dec T)
  t (l r : list T) (p : pos t l) : count_occ dec (pos_before p) t < count_occ dec r t -> 
  { p' : pos t r | count_occ dec (pos_before p') t = count_occ dec (pos_before p) t }.
  intros.
  generalize dependent r.
  generalize dependent l.
  induction l.
  eauto with *.
  intros.
  dependent induction p;
  simpl in *.
  apply count_occ_lt_In in H.
  destruct (In_pos _ dec _ H).
  eauto.
  clear IHp.
  dedec dec;
  subst.
  dependent induction r;
  simpl in *.
  omega.
  dedec dec;
  subst.
  assert (count_occ dec (firstn (pos_nat p) l) t < count_occ dec r t).
  omega.
  specialize (IHl p r).
  intuition.
  destruct X.
  exists (pos_skip t x).
  simpl in *.
  dedec dec;
  auto;
  tauto.
  intuition.
  destruct X.
  exists (pos_skip a x).
  simpl in *.
  dedec dec;
  subst;
  tauto.
  eauto.
Defined.

Definition permutation_type_find_pos T (t : T) dec (l l' : list T) (P : pos t l) :
  permutation_type l l' ->
    { p : pos t l' | count_occ dec (pos_before p) t = count_occ dec (pos_before P) t }.
  induction 1.
  eauto.
  depde P.
  simpl in *.
  exists (pos_fst x l').
  trivial.
  specialize (IHX p).
  destruct IHX.
  simpl in *.
  exists (pos_skip x x0).
  repeat (
    dedec dec;
    subst;
    auto;
    try tauto;
    simpl in *).
  depde P.
  simpl in *.
  destruct (dec x y).
  subst.
  exists (pos_fst y (y :: l)).
  trivial.
  simpl in *.
  exists (pos_skip x (pos_fst y l)).
  simpl in *.
  dedec dec;
  tauto.
  depde p.
  simpl in *.
  dedec dec;
  subst.
  exists (pos_skip x (pos_fst x l)).
  simpl in *.
  dedec dec;
  tauto.
  exists (pos_fst x (y :: l)).
  trivial.
  simpl in *.
  exists (pos_skip x (pos_skip y p0)).
  repeat (dedec dec; subst; simpl in *;trivial;try tauto).
  specialize (IHX1 P).
  destruct IHX1.
  specialize (IHX2 x).
  destruct IHX2.
  exists x0.
  omega.
Defined.

Definition remove_fst_join T (dec : eq_dec T) (t : T) l (P : In t l) :=
  fst (` (remove_fst dec t _ P)) ++ snd (` (remove_fst dec t _ P)).

Definition remove_pos T (t : T) l (p : pos t l) : 
  { l' : (list T * list T) | 
      l = (fst l') ++ [t] ++ (snd l') /\
      forall dec, count_occ dec (fst l') t = count_occ dec (pos_before p) t }.
  induction l.
  eauto with *.
  depde p.
  simpl in *.
  exists (@nil T, l).
  simpl in *.
  tauto.
  simpl in *.
  specialize (IHl p0).
  destruct IHl.
  destruct x.
  simpl in *.
  intuition.
  subst.
  exists (a :: l0, l1).
  simpl in *.
  intuition.
  destruct (dec a t);
  auto.
Defined.

Definition remove_fst_join_neq_find_pos T dec
  (l : list T) (t t' : T) (P : pos t l) (P' : pos t' l) :
    t <> t' -> 
      { p : pos t' (remove_fst_join dec _ _ (pos_In P)) | 
          count_occ dec (pos_before P') t' = count_occ dec (pos_before p) t' }.
  induction l.
  eauto with *.
  intros.
  dependent induction P.
  simpl in *.
  unfold remove_fst_join.
  destruct remove_fst.
  simpl in *.
  destruct x.
  simpl in *.
  intuition.
  destruct l0.
  simpl in *.
  invc H0.
  dependent induction P'.
  tauto.
  clear IHP'.
  simpl in *.
  dedec dec.
  tauto.
  exists P'.
  trivial.
  simpl in *.
  invc H0.
  dedec dec.
  discriminate.
  tauto.
  clear IHP.
  dependent induction P'.
  simpl in *.
  unfold remove_fst_join.
  destruct remove_fst.
  simpl in *.
  destruct x.
  simpl in *.
  intuition.
  destruct l0;
  invc H0.
  tauto.
  simpl in *.
  exists (pos_fst t0 (l0 ++ l1)).
  trivial.
  clear IHP'.
  simpl in *.
  dedec dec.
  subst.
  unfold remove_fst_join.
  destruct remove_fst.
  simpl in *.
  destruct x.
  simpl in *.
  intuition.
  destruct l0;
  simpl in *;
  invc H0.
  tauto.
  dedec dec.
  discriminate.
  destruct (pos_app _ _ P').
  destruct s.
  destruct (pos_extend_right l1 x).
  exists (pos_skip t1 x0).
  simpl in *.
  destruct (dec t1 t1).
  unfold pos_before in *.
  rewrite e0.
  rewrite e.
  trivial.
  tauto.
  destruct s.
  dependent induction x.
  tauto.
  clear IHx.
  destruct (pos_extend_left (t0 :: l0) x).
  simpl in *.
  exists x0.
  rewrite e0.
  unfold pos_before in *.
  simpl in *.
  destruct (dec t0 t0).
  rewrite <- e.
  replace (t :: firstn (pos_nat x) l1) with ([t] ++ firstn (pos_nat x) l1).
  repeat rewrite count_occ_app.
  simpl in *.
  destruct (dec t t0).
  tauto.
  trivial.
  trivial.
  tauto.
  unfold remove_fst_join.
  destruct remove_fst.
  simpl in *.
  destruct x.
  simpl in *.
  intuition.
  destruct l0;
  simpl in *;
  invc H0.
  exists P'.
  trivial.
  dedec dec.
  discriminate.
  specialize (IHl P P').
  intuition.
  destruct X.
  unfold remove_fst_join in *.
  destruct remove_fst.
  destruct x0.
  simpl in *.
  intuition.
  assert (l0 = l).
  clear e x P P'.
  generalize dependent l0.
  induction l;
  intros.
  destruct l0;
  invc H0.
  trivial.
  simpl in *.
  dedec dec.
  discriminate.
  tauto.
  simpl in *.
  destruct (dec a t).
  discriminate.
  intuition.
  destruct l0;
  invc H0.
  tauto.
  f_equal.
  apply H3.
  simpl in *.
  dedec dec.
  discriminate.
  trivial.
  trivial.
  subst.
  apply app_inv_head in H0.
  invc H0.
  exists (pos_skip t1 x).
  simpl in *.
  dedec dec.
  tauto.
  unfold pos_before in *.
  rewrite e.
  trivial.
Defined.

Theorem perm_swap_trans : forall T (l : list T) r tl tr,
  Permutation l r -> Permutation (tl :: tr :: l) (tr :: tl :: r).
  intros.
  eapply (@perm_trans _ _ (tl :: tr :: r)).
  auto.
  constructor.
Qed.

Theorem count_occ_In : forall T dec (t : T) l, count_occ dec l t >= 1 -> In t l.
  induction l;
  intros;
  simpl in *.
  omega.
  destruct (dec a t);
  subst;
  simpl in *;
  tauto.
Qed.

Theorem In_count_occ : forall T dec (t : T) l, In t l -> count_occ dec l t >= 1.
  induction l;
  intros;
  simpl in *.
  tauto.
  dedec dec.
  omega.
  assert (In t l).
  tauto.
  tauto.
Qed.

Definition pos_before_pos T (t : T) lt (P P' : pos t lt) : Prop := pos_nat P < pos_nat P'.
Definition pos_after_pos T (t : T) lt (P P' : pos t lt) : Prop := pos_nat P > pos_nat P'.

Theorem pos_neq_pos_before_or_after_pos : forall T (t : T) lt (P P' : pos t lt),
  ((pos_before_pos P P') \/ (pos_after_pos P P')) <-> P <> P'.
  intuition;
  subst;
  unfold pos_before_pos in *;
  unfold pos_after_pos in *;
  try apply pos_neq_pos_nat in H;
  omega.
Qed.

Theorem pos_before_length : forall T (t : T) lt (P : pos t lt),
  pos_nat P = length (pos_before P).
  dependent induction P.
  trivial.
  simpl in *.
  auto.
Qed.

Theorem pos_before_eq : forall T t (lt : list T) (P : pos t lt) t' lt' (P' : pos t' lt'), 
  pos_before P = pos_before P' -> pos_nat P = pos_nat P'.
  intros.
  repeat rewrite pos_before_length.
  f_equal.
  trivial.
Qed.

Theorem pos_before_l_app : forall T l t (lt : list T) (P : pos t lt) t' lt' (P' : pos t' lt'), 
  pos_before P = l ++ pos_before P' -> pos_nat P = length l + pos_nat P'.
  intros.
  repeat rewrite pos_before_length.
  rewrite H.
  rewrite app_length.
  trivial.
Qed.

Theorem pos_before_r_app : forall T l t (lt : list T) (P : pos t lt) t' lt' (P' : pos t' lt'), 
  pos_before P = pos_before P' ++ l -> pos_nat P = pos_nat P' + length l.
  intros.
  repeat rewrite pos_before_length.
  rewrite H.
  rewrite app_length.
  trivial.
Qed.

Definition remove_fst_join_eq_find_pos T (dec : eq_dec T)
  (l : list T) (t : T) (P : pos t l) (I : In t (pos_before P)) :
    { p : pos t (remove_fst_join dec _ _ (pos_In P)) | 
          pos_before p = remove_fst_join dec _ _ I }.
  dependent induction P;
  simpl in *.
  tauto.
  destruct (dec e t);
  subst;
  unfold remove_fst_join;
  repeat destruct remove_fst;
  destruct x, x0;
  simpl in *;
  intuition;
  destruct l0;
  simpl in *;
  invc H;
  unfold pos_before in *;
  simpl in *;
  destruct l2;
  simpl in *;
  invc H1;
  eauto;
  dedec dec;
  try discriminate;
  try tauto.
  assert (In t (firstn (pos_nat P) (l0 ++ t :: l1))).
  tauto.
  specialize (IHP H).
  destruct IHP.
  unfold remove_fst_join in *.
  repeat destruct remove_fst.
  destruct x0, x1.
  simpl in *.
  intuition.
  assert (l0 = l).
  clear e x P H H5 I H4.
  generalize dependent l0.
  induction l;
  destruct l0;
  intros;
  simpl in *;
  trivial;
  invc H0;
  repeat dedec dec;
  try invc H1;
  try discriminate;
  try tauto.
  f_equal.
  apply IHl;
  trivial.
  subst.
  apply app_inv_head in H1.
  invc H1.
  clear I.
  assert (l2 ++ t :: l3 = l5 ++ t :: l6).
  rewrite <- H4.
  trivial.
  assert (l5 = l2).
  clear H5 H4 P x e H.
  generalize dependent l5.
  induction l2;
  destruct l5;
  intros;
  trivial;
  simpl in *;
  invc H0;
  repeat dedec dec;
  try invc H1;
  try discriminate;
  try tauto.
  f_equal.
  apply IHl2;
  trivial.
  subst.
  apply app_inv_head in H1.
  invc H1.
  exists (pos_skip t1 x).
  simpl in *.
  f_equal.
  trivial.
Defined.

Definition remove_pos_join T (t : T) l (p : pos t l) := let (l,r) := ` (remove_pos p) in l ++ r.

Definition remove_pos_join_neq_find_pos T (dec : eq_dec T)
  (l : list T) (t t' : T) (P : pos t l) (P' : pos t' l) :
    t <> t' -> 
      { p : pos t' (remove_pos_join P) | 
          count_occ dec (pos_before P') t' = count_occ dec (pos_before p) t' }.
  induction l.
  eauto with *.
  intros.
  dependent induction P;
  dependent induction P'.
  tauto.
  clear IHP'.
  unfold remove_pos_join.
  destruct remove_pos.
  destruct x.
  simpl in *.
  intuition.
  destruct l0;
  invc H0.
  admit.
  specialize (H1 dec).
  simpl in *.
  repeat dedec dec;
  try discriminate;
  tauto.
  clear IHP.
  unfold remove_pos_join.
  destruct remove_pos.
  destruct x.
  simpl in *.
  intuition.
  destruct l0;
  invc H0.
  tauto.
  specialize (H1 dec).
  simpl in *.
  destruct (dec t0 t).
  subst.
  tauto.
  exists (pos_fst t0 (l0 ++ l1)).
  trivial.
  clear IHP IHP'.
  specialize (IHl P P').
  simpl in *.
  intuition.
  destruct X.
  unfold remove_pos_join in *.
  repeat destruct remove_pos.
  destruct x0, x1.
  simpl in *.
  intuition.
  specialize (H1 dec).
  specialize (H3 dec).
  subst.
  destruct l2;
  invc H2;
  try discriminate;
  try tauto;
  repeat (
    dedec dec;
    subst;
    simpl in *);
  try discriminate;
  try tauto;
  (assert (l2 = l0);
  [
    symmetry;
    apply (count_occ_app_head t dec _ l1 _ l3);
    trivial;
    unfold pos_before in *;
    omega|
  ]);
  subst;
  apply app_inv_head in H5;
  invc H5;
  [
    exists (pos_skip t0 x)|
    exists (pos_skip t x)|
    exists (pos_skip t1 x)
  ];
  simpl in *;
  dedec dec;
  trivial;
  auto;
  tauto.
Defined.

Definition remove_pos_join_pos_before_pos_find_pos T (dec : eq_dec T)
  (t : T) (l : list T) (P P' : pos t l) :
    pos_before_pos P' P ->
      { p : pos t (remove_pos_join P) | 
          pos_before p = pos_before P' }.
  induction l;
  intros.
  eauto with *.
  unfold remove_pos_join.
  destruct remove_pos.
  destruct x.
  simpl in *.
  intuition.
  specialize (H1 dec).
  destruct l0;
  invc H0;
  simpl in *.
  unfold pos_before_pos in *.
  unfold pos_before in *.
  dependent induction P;
  simpl in *.
  omega.
  dedec dec.
  discriminate.
  tauto.
  dedec dec.
  subst.
  unfold pos_before_pos in *.
  dependent induction P;
  dependent induction P';
  simpl in *;
  try omega;
  clear IHP;
  try clear IHP';
  dedec dec;
  try tauto;
  unfold pos_before in *;
  simpl in *.
  exists (pos_fst t (l0 ++ l1)).
  trivial.
  invc H1.
  specialize (IHl P P').
  assert (pos_nat P' < pos_nat P).
  omega.
  intuition.
  destruct X.
  unfold remove_pos_join in *.
  destruct remove_pos.
  destruct x0.
  simpl in *.
  intuition.
  specialize (H3 dec).
  unfold pos_before in *.
  assert (l0 = l).
  apply (count_occ_app_head t dec _ l1 _ l2);
  trivial.
  omega.
  subst.
  apply app_inv_head in H1.
  invc H1.
  exists (pos_skip t x).
  simpl in *.
  f_equal.
  trivial.
  dependent induction P;
  dependent induction P';
  try tauto.
  clear IHP IHP'.
  simpl in *.
  dedec dec.
  tauto.
  unfold pos_before_pos in *.
  specialize (IHl P P').
  simpl in *.
  assert (pos_nat P' < pos_nat P).
  omega.
  intuition.
  destruct X.
  unfold remove_pos_join in *.
  destruct remove_pos.
  destruct x0.
  simpl in *.
  intuition.
  assert (l0 = l).
  apply (count_occ_app_head t dec _ l1 _ l2);
  trivial.
  specialize (H3 dec).
  unfold pos_before in *.
  omega.
  subst.
  apply app_inv_head in H2.
  invc H2.
  exists (pos_skip t0 x).
  unfold pos_before in *.
  simpl in *.
  f_equal.
  trivial.
Defined.

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
  pos_nat P >= length l -> { p : pos t r | l ++ pos_before p = pos_before P }.
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

Theorem count_occ_before_count_occ_after T dec (t : T) l r (P : pos t (l ++ t :: r)) :
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

Hint Rewrite count_occ_app_head.

Definition remove_pos_join_pos_after_pos_find_pos T (dec : eq_dec T)
  (t : T) (l : list T) (P P' : pos t l) :
    pos_after_pos P' P ->
      { p : pos t (remove_pos_join P) | 
          pos_after p = pos_after P' }.
  induction l;
  intros.
  eauto with *.
  unfold remove_pos_join.
  destruct remove_pos.
  destruct x.
  simpl in *.
  intuition.
  specialize (H1 dec).
  unfold pos_after_pos in *.
  destruct l0;
  invc H0;
  simpl in *;
  dependent induction P;
  dependent induction P';
  simpl in *;
  try dedec dec;
  subst;
  try tauto;
  try omega;
  try clear IHP;
  try clear IHP';
  try solve [exists P'; trivial];
  specialize (IHl P P');
  assert (pos_nat P' > pos_nat P);
  try omega;
  clear H;
  intuition;
  destruct X;
  unfold remove_pos_join in *;
  destruct remove_pos;
  destruct x0;
  simpl in *;
  intuition;
  specialize (H2 dec);
  (assert (l0 = l);
  [
    unfold pos_before in *;
    invc H1;
    rewrite <- H4 in H2;
    eapply count_occ_app_head;
    eauto|
  ]);
  subst;
  apply app_inv_head in H;
  invc H;
  unfold pos_after in *.
  exists (pos_skip t x).
  trivial.
  exists (pos_skip t0 x).
  trivial.
Defined.

Definition remove_pos_join_neq_pos_eq T dec (t t' : T) (neq : t <> t')
  l (p : pos t l) (p_before : pos t' l) (p_after : pos t' (remove_pos_join p)) :=
    p_after = ` (remove_pos_join_neq_find_pos dec p p_before neq).

Definition remove_pos_join_pos_before_pos_eq T dec (t : T) l 
  (p p_before : pos t l) (p_after : pos t (remove_pos_join p)) 
    (pb : pos_before_pos p_before p) :=
      p_after = ` (remove_pos_join_pos_before_pos_find_pos dec pb).

Definition remove_pos_join_pos_after_pos_eq T dec (t : T) l 
  (p p_before : pos t l) (p_after : pos t (remove_pos_join p)) 
    (pb : pos_after_pos p_before p) :=
      p_after = ` (remove_pos_join_pos_after_pos_find_pos dec pb).