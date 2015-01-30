Require Import Program List Permutation Omega.

Load tactic.
Load permutation_type.
Load eq_dec.

Set Implicit Arguments.

Inductive pos T (t : T) (lt : list T) : Type :=
| pos_fst : Some t = hd_error lt -> pos t lt
| pos_skip : pos t (tail lt) -> pos t lt.

Fixpoint pos_rect' (P : forall T (t : T) (lt : list T), pos t lt -> Type)
  (PF : forall T (t : T) (lt : list T) (p : Some t = hd_error lt), P T t lt (pos_fst lt p))
    (PS : forall T (t : T) (lt : list T) (p : pos t (tail lt)), P T t (tail lt) p -> 
      P T t lt (pos_skip lt p))
    T (t : T) (lt : list T) (p : pos t lt)
  : P T t lt p.
  destruct p.
  trivial.
  apply PS.
  apply pos_rect';
  trivial.
Defined.

Definition pos_lt_contain T (t : T) (p : pos t nil) : False.
  remember [].
  generalize dependent Heql.
  refine (pos_rect' (fun _ _ _ _ => _ -> _) _ _ p);
  intros;
  subst;
  try tauto;
  discriminate.
Defined.

Fixpoint pos_nat T (t : T) l (p : pos t l) :=
  match p with
  | pos_fst _ => 0
  | pos_skip p' => S (pos_nat p')
  end.

Definition pos_before T (t : T) l (p : pos t l) := firstn (pos_nat p) l.
Definition pos_after T (t : T) l (p : pos t l) := skipn (S (pos_nat p)) l.

Theorem pos_before_pos_after : forall T (t : T) lt (p : pos t lt),
  pos_before p ++ [t] ++ pos_after p = lt.
  induction p.
  destruct lt.
  discriminate.
  inversion e.
  subst.
  trivial.
  destruct lt.
  simpl in *.
  assert (False).
  clear IHp.
  apply pos_lt_contain in p.
  trivial.
  tauto.
  simpl in *.
  f_equal.
  trivial.
Qed.

Definition eq_pos_dec : forall T (t : T) ls, eq_dec (pos t ls).
  intros.
  unfold eq_dec.
  induction ls.
  intros.
  assert(False).
  eapply pos_lt_contain.
  eauto.
  tauto.
  intros.
  destruct l, r;
  simpl in *;
  try inversion e;
  subst;
  try(
    left;
    f_equal;
    apply proof_irrelevance);
  try(
    right;
    discriminate).
  destruct (IHls l r).
  subst.
  tauto.
  right.
  intuition.
  inversion H.
  subst.
  tauto.
Defined.

Definition pos_In : forall T (t : T) lt, pos t lt -> In t lt.
  induction 1.
  destruct lt.
  discriminate.
  invc e.
  simpl in *.
  tauto.
  destruct lt.
  trivial.
  simpl in *.
  tauto.
Qed.

Definition In_pos : forall T (t : T) (dec : eq_dec T)
  lt, In t lt -> pos t lt.
  induction lt.
  intros.
  simpl in *.
  tauto.
  intros.
  simpl in *.
  destruct (dec a t).
  subst.
  constructor.
  trivial.
  assert(In t lt).
  destruct H.
  tauto.
  trivial.
  apply pos_skip.
  simpl in *.
  tauto.
Defined.

Definition remove T (t : T) (l : list T) (P : pos t l) :
  { l' : list T | Permutation (t :: l') l }.
  induction l.
  apply pos_lt_contain in P.
  tauto.
  destruct P.
  simpl in *.
  inversion e.
  subst.
  exists l.
  trivial.
  simpl in *.
  intuition.
  destruct X.
  exists (a :: x).
  assert(Permutation (a :: t :: x) (a :: l)).
  auto.
  eapply perm_trans in H.
  eauto.
  constructor.
Defined.

Definition find_pos T (t : T) (l l' : list T) (P : pos t l) : permutation_type l l' -> pos t l'.
  induction 1.
  trivial.
  destruct P.
  simpl in *.
  inversion e.
  subst.
  constructor.
  trivial.
  simpl in *.
  intuition.
  apply pos_skip.
  trivial.
  inversion P.
  simpl in *.
  inversion H.
  subst.
  apply pos_skip.
  simpl in *.
  constructor.
  trivial.
  simpl in *.
  inversion H.
  inversion H0.
  subst.
  simpl in *.
  constructor.
  trivial.
  simpl in *.
  apply pos_skip.
  apply pos_skip.
  trivial.
  tauto.
Defined.

Definition bring_to_front { T } 
  (dec : eq_dec T) e : 
    forall l : list T, In e l -> { lr | Permutation l lr /\ hd_error lr = value e }.
  induction l.
  simpl in *.
  tauto.
  intros.
  destruct (dec e a).
  subst.
  exists (a :: l).
  auto.
  assert(In e l).
  simpl in *.
  intuition.
  clear H.
  intuition.
  invc X.
  intuition.
  destruct x.
  discriminate.
  simpl in *.
  invc H2.
  exists (e :: a :: x).
  split.
  assert (Permutation (a :: l) (a :: e :: x)).
  auto.
  eapply perm_trans.
  exact H.
  constructor.
  trivial.
Defined.

Definition update_pos T (t t' : T) (l : list T) (P : pos t l) (P' : pos t' l) :
  t <> t' -> pos t' (` (remove P)).
  induction l.
  apply pos_lt_contain in P'.
  tauto.
  intros.
  destruct P, P';
  try inversion e;
  try inversion e0;
  subst.
  tauto.
  simpl in P'.
  simpl in e.
  destruct (remove (pos_fst (a :: l) e)).
  simpl in *.
  apply Permutation_cons_inv in p.
  admit.
  simpl in *.
  destruct (remove P).
  simpl in *.
  constructor.
  trivial.
  simpl in *.
  remember (IHl P P' H).
  clear Heqp.
  destruct (remove P).
  simpl in *.
  apply pos_skip.
  trivial.
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

Definition Permutation_permutation_type_inner : forall T (l : list T) r (P : Permutation l r) n,
  eq_dec T -> length l <= n -> permutation_type l r.
  intros.
  generalize dependent r.
  generalize dependent l.
  induction n;
  intros.
  destruct l.
  apply Permutation_nil in P.
  subst.
  constructor.
  simpl in *.
  omega.
  destruct l.
  apply Permutation_nil in P.
  subst.
  constructor.
  simpl in *.
  assert (length l <= n).
  omega.
  clear H.
  destruct (bring_to_front X t r).
  apply (Permutation_in t P).
  simpl in *.
  tauto.
  intuition.
  destruct x.
  discriminate.
  simpl in *.
  invc H1.
  assert(permutation_type l x).
  apply IHn.
  trivial.
  assert (Permutation (t :: l) (t :: x)).
  eapply perm_trans.
  exact P.
  trivial.
  apply Permutation_cons_inv in H1.
  trivial.
  destruct r.
  symmetry in P.
  apply Permutation_nil in P.
  discriminate.
  destruct (X t t0).
  subst.
  constructor.
  eapply IHn.
  trivial.
  apply Permutation_cons_inv in P.
  trivial.
  destruct (bring_to_front X t0 l).
  assert (In t0 (t :: l)).
  eapply Permutation_in.
  symmetry.
  exact P.
  simpl in *.
  tauto.
  destruct H1.
  subst.
  tauto.
  trivial.
  intuition.
  destruct x0.
  discriminate.
  invc H2.
  destruct (bring_to_front X t r).
  assert (In t (t0 :: r)).
  eapply Permutation_in.
  symmetry.
  exact H.
  simpl in *.
  tauto.
  destruct H2.
  subst.
  tauto.
  trivial.
  intuition.
  destruct x1.
  discriminate.
  invc H3.
  assert (Permutation (t :: t0 :: x0) (t0 :: t :: x1)).
  apply (@perm_trans _ _ (t :: l)).
  auto with *.
  apply (@perm_trans _ _ (t0 :: r)).
  trivial.
  auto.
  assert (permutation_type x0 x1).
  apply IHn.
  apply Permutation_length in H1.
  simpl in *.
  omega.
  trivial.
  eapply (@perm_trans _ (t0 :: t :: x0)) in H3.
  repeat apply Permutation_cons_inv in H3.
  trivial.
  constructor.
  assert (permutation_type (t :: l) (t :: t0 :: x0)).
  constructor.
  auto.
  eapply perm_type_trans.
  exact X2.
  assert (permutation_type (t0 :: t :: x1) (t0 :: r)).
  constructor.
  apply IHn.
  simpl in *.
  apply Permutation_length in H2.
  apply Permutation_length in P.
  simpl in *.
  omega.
  auto with *.
  eapply perm_type_trans.
  Focus 2.
  exact X3.
  assert (permutation_type (t :: t0 :: x0) (t0 :: t :: x0)).
  constructor.
  eapply perm_type_trans.
  exact X4.
  constructor.
  constructor.
  trivial.
Defined.

Theorem Permutation_permutation_type : forall T (l : list T) r (P : Permutation l r),
  eq_dec T -> permutation_type l r.
  intros.
  eapply Permutation_permutation_type_inner;
  trivial.
Defined.

Definition split_list T (dec : eq_dec T) (t : T) l : In t l -> 
  { l' : (list T * list T) | l = (fst l') ++ [t] ++ (snd l') /\ count_occ dec (fst l') t = 0 }.
  induction l.
  simpl in *.
  tauto.
  intros.
  destruct (dec t a).
  subst.
  admit.
  assert (In t l).
  destruct H.
  subst.
  tauto.
  trivial.
  clear H.
  intuition.
  destruct X.
  simpl in *.
  intuition.
  subst.
  destruct x.
  simpl in *.
  exists ((a :: l), l0).
  simpl in *.
  intuition.
  destruct (dec a t).
  subst.
  tauto.
  trivial.
Defined.

Definition pos_find_inner T (dec : eq_dec T)
  t (l r : list T) (p : pos t l) : count_occ dec (pos_before p) t < count_occ dec r t -> 
  { p' : pos t r | count_occ dec (pos_before p') t = count_occ dec (pos_before p) t }.
  intros.
  generalize dependent r.
  generalize dependent l.
  induction l.
  intros.
  assert(False).
  clear H.
  apply pos_lt_contain in p.
  trivial.
  tauto.
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
  subst.
  tauto.
  trivial.
  simpl in *.
  destruct (dec a a).
  clear e.
  unfold pos_before in *.
  admit (*split *r* into two part, with the first part containing one *a**).
  tauto.
  destruct p.
  inversion e.
  subst.
  tauto.
  simpl in *.
  destruct (dec a t).
  subst.
  tauto.
  clear n0.
  unfold pos_before in *.
  apply IHl.
  trivial.
Defined.

Definition Permutation_pos_find T (dec : eq_dec T)
  t (l r : list T) (p : pos t l) (P : Permutation l r) : pos t r.
  eapply Permutation_pos_find_inner;
  eauto.
Defined.