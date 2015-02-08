Require Import Permutation Program List.
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
  dependent induction p.
  simpl in *.
  induction r;
  simpl in *.
  omega.
  destruct (dec a0 a).
  subst.
  exists (pos_fst a r).
  trivial.
  intuition.
  destruct X.
  exists (pos_skip a0 x).
  simpl in *.
  destruct (dec a0 a).
  subst.
  tauto.
  trivial.
  clear IHp.
  simpl in *.
  destruct (dec a t).
  subst.
  unfold pos_before in *.
  specialize (IHl p).
  assert (count_occ dec r t > 0).
  omega.
  apply count_occ_lt_In in H0.
  destruct (remove_fst dec t r H0).
  destruct x.
  simpl in *.
  intuition.
  subst.
  repeat (replace (t :: l1) with ([t] ++ l1) in *;trivial).
  repeat rewrite count_occ_app in *.
  rewrite H2 in *.
  simpl in *.
  destruct (dec t t).
  simpl in *.
  assert(count_occ dec (firstn (pos_nat p) l) t < count_occ dec l1 t).
  omega.
  clear e H.
  specialize (IHl l1).
  intuition.
  destruct X.
  induction l0.
  simpl in *.
  exists (pos_skip t x).
  simpl in *.
  destruct (dec t t).
  auto.
  tauto.
  simpl in *.
  destruct (dec a t).
  discriminate.
  intuition.
  assert (In t (l0 ++ t :: l1)).
  apply in_or_app.
  simpl in *.
  tauto.
  intuition.
  destruct X0.
  exists (pos_skip a x0).
  simpl in *.
  destruct (dec a t).
  tauto.
  trivial.
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
  destruct (dec x t).
  subst.
  simpl in *.
  destruct (dec t t).
  auto.
  tauto.
  simpl in *.
  destruct (dec x t).
  subst.
  tauto.
  trivial.
  depde P.
  destruct (dec x y).
  subst.
  exists (pos_fst y (y :: l)).
  trivial.
  simpl in *.
  exists (pos_skip x (pos_fst y l)).
  simpl in *.
  destruct (dec x y).
  subst.
  tauto.
  trivial.
  depde p.
  simpl in *.
  destruct (dec y x).
  subst.
  exists (pos_skip x (pos_fst x l)).
  simpl in *.
  destruct (dec x x).
  trivial.
  tauto.
  exists (pos_fst x (y :: l)).
  trivial.
  simpl in *.
  exists (pos_skip x (pos_skip y p0)).
  destruct (dec x t);
  destruct (dec y t);
  subst;
  simpl in *;
  destruct (dec t t);
  try destruct (dec y t);
  try destruct (dec x t);
  trivial;
  tauto.
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

Definition remove_fst_join_find_pos T dec (l : list T) (t t' : T) (P : pos t l) (P' : pos t' l) :
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
  destruct (dec a t).
  tauto.
  exists P'.
  trivial.
  simpl in *.
  invc H0.
  destruct (dec t t).
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
  destruct (dec a t0).
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
  destruct (dec t1 t).
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
  destruct (dec t1 t).
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
  destruct (dec t t).
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
  destruct (dec a t).
  discriminate.
  trivial.
  trivial.
  subst.
  apply app_inv_head in H0.
  invc H0.
  exists (pos_skip t1 x).
  simpl in *.
  destruct (dec t1 t0).
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