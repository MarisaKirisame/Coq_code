Require Import Program List.
Require Import count tactic pos permutation_type eq_dec.

Set Implicit Arguments.

Definition split_list T (dec : eq_dec T) (t : T) l : In t l -> 
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
  destruct p.
  simpl in *.
  inversion e.
  subst.
  exists (pos_fst (a :: l ++ r) eq_refl).
  trivial.
  simpl in *.
  specialize (IHl p).
  destruct IHl.
  exists (pos_skip (a :: l ++ r) x).
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
  exists (pos_skip ((a :: l) ++ r) x).
  simpl in *.
  unfold pos_before in *.
  simpl in *.
  f_equal.
  trivial.
Defined.

Hint Rewrite count_count_occ.

Theorem count_occ_split : forall T dec (t : T) l r,
  count_occ dec (l ++ r) t = count_occ dec l t + count_occ dec r t.
  intros.
  repeat rewrite count_count_occ.
  apply count_split.
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
  destruct (dec t a).
  subst.
  destruct p.
  simpl in *.
  clear e.
  clear IHl.
  induction r;
  simpl in *.
  omega.
  destruct (dec a0 a).
  subst.
  exists (@pos_fst _ a (a :: r) eq_refl).
  trivial.
  intuition.
  destruct H0.
  exists (pos_skip (a0 :: r) x).
  simpl in *.
  destruct (dec a0 a).
  tauto.
  trivial.
  simpl in *.
  destruct (dec a a).
  clear e.
  specialize (IHl p r).
  assert (count_occ dec (pos_before p) a < count_occ dec r a).
  auto with *.
  intuition.
  destruct H1.
  induction r;
  simpl in *.
  omega.
  destruct (dec a0 a).
  subst.
  unfold pos_before in *.
  
Defined.

Definition permutation_type_find_pos T (t : T) dec (l l' : list T) (P : pos t l) :
  permutation_type l l' ->
    { p : pos t l' | count_occ dec (pos_before p) t = count_occ dec (pos_before P) t }.
  induction 1.
  eauto.
  destruct P.
  simpl in *.
  invc e.
  exists (@pos_fst _ x (x :: l') eq_refl).
  trivial.
  simpl in *.
  destruct (dec x x).
  specialize (IHX P).
  destruct IHX.
  exists (pos_skip (x :: l') x0).
  simpl in *.
  destruct (dec x t).
  auto.
  tauto.
  tauto.
  destruct P.
  simpl in *.
  invc e.
  destruct (dec x y).
  subst.
  exists (@pos_fst _ y (y :: y :: l) eq_refl).
  trivial.
  exists (pos_skip (x :: y :: l) (@pos_fst _ y (y :: l) eq_refl)).
  simpl in *.
  destruct (dec x y).
  subst.
  tauto.
  trivial.
  simpl in *.
  destruct P.
  simpl in *.
  invc e.
  destruct (dec y x).
  subst.
  exists (pos_skip (x :: x :: l) (@pos_fst _ x (x :: l) eq_refl)).
  simpl in *.
  destruct (dec x x).
  trivial.
  tauto.
  exists (@pos_fst _ x (x :: y :: l) eq_refl).
  trivial.
  simpl in *.
  exists (pos_skip (x :: y :: l) (pos_skip (y :: l) P)).
  simpl in *.
  destruct (dec y t);
  destruct (dec x t);
  subst;
  trivial.
  specialize (IHX1 P).
  destruct IHX1.
  specialize (IHX2 x).
  destruct IHX2.
  exists x0.
  omega.
Defined.

Definition remove T (t : T) (l : list T) (P : pos t l) :
  { ret : (list T) * (list T) | fst ret ++ t :: snd ret = l }.
  induction l.
  apply pos_lt_contain in P.
  tauto.
  destruct P.
  simpl in *.
  invc e.
  exists (@nil T, l).
  trivial.
  simpl in *.
  intuition.
  destruct X.
  destruct x.
  subst.
  simpl in *.
  exists (a :: l0, l1).
  trivial.
Defined.

Definition remove_join T (t : T) l (P : pos t l) := fst (` (remove P)) ++ snd (` (remove P)).

Definition remove_join_find_pos T dec (t t' : T) (l : list T) (P : pos t l) (P' : pos t' l) :
  t <> t' -> 
    { p : pos t' (remove_join P) | 
        count_occ dec (pos_before P') t' = count_occ dec (pos_before p) t' }.
  intros.
  induction l.
  eauto with *.
  destruct P.
  inversion e.
  subst.
  destruct P'.
  inversion e0.
  subst.
  tauto.
  simpl in *.
  destruct (dec a t').
  tauto.
  unfold remove_join in *.
  destruct remove.
  destruct x.
  simpl in *.
  destruct l0;
  simpl in *;
  invc e0.
  admit (**).
  admit (**).
  simpl in *.
  destruct P'.
  simpl in *.
  invc e.
  unfold remove_join in *.
  destruct remove.
  destruct x.
  simpl in *.
  destruct l0;
  simpl in *;
  invc e.
  tauto.
  admit (**).
  simpl in *.
  specialize (IHl P P').
  destruct IHl.
  unfold remove_join in *.
  repeat destruct remove.
  destruct x0, x1.
  subst.
  simpl in *.
  destruct l2;
  invc e1;
  simpl in *.
  destruct (dec a t').
  tauto.
  exists P'.
  trivial.
  destruct (dec a t').
  subst.
Defined.

Definition find_front_pos_inner T (dec : eq_dec T) (l r : list T) n t
  : n = length l -> Permutation (t :: l) r -> pos t r.
  generalize dependent l.
  generalize dependent r.
  induction n.
  intros.
  destruct l.
  simpl in *.
  apply Permutation_length_1_inv in H0.
  subst.
  constructor.
  trivial.
  discriminate.
  intros.
  destruct l.
  discriminate.
  invc H.
  destruct r.
  apply Permutation_length in H0.
  discriminate.
  destruct (dec t t1).
  subst.
  constructor.
  trivial.
  apply pos_skip.
  simpl in *.
  assert (In t r).
  eapply (Permutation_in t) in H0.
  destruct H0.
  subst.
  tauto.
  trivial.
  simpl in *.
  tauto.
  destruct (bring_to_front dec t r H).
  intuition.
  destruct x.
  discriminate.
  invc H2.
  assert(length l = length x).
  apply Permutation_length in H0.
  apply Permutation_length in H1.
  simpl in *.
  omega.
  eauto with *.
Defined.

Definition find_front_pos T (dec : eq_dec T) (l r : list T) t
  : Permutation (t :: l) r -> pos t r.
  eapply find_front_pos_inner;
  trivial.
Defined.

Theorem perm_swap_trans : forall T (l : list T) r tl tr,
  Permutation l r -> Permutation (tl :: tr :: l) (tr :: tl :: r).
  intros.
  eapply (@perm_trans _ _ (tl :: tr :: r)).
  auto.
  constructor.
Qed.

Theorem count_occ_In : forall T dec (t : T) l, count_occ dec l t > 1 -> In t l.
  induction l;
  intros;
  simpl in *.
  omega.
  destruct (dec a t);
  subst;
  simpl in *;
  tauto.
Qed.

Definition pos_remove_eq :
  forall T (t : T) l (p p' : pos t l), p <> p' -> pos_nat p <> pos_nat p'.
  intros.
  induction l.
  admit.
  destruct p, p';
  simpl in *;
  try discriminate.
  inversion e.
  subst.
  intuition.
  apply H.
  f_equal.
  admit.
  intuition.
  invc H0.
  specialize (IHl p p').
  assert(p <> p').
  intuition.
  subst.
  tauto.
  tauto.
Defined.

