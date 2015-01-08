Require Import Arith List Program Permutation.

Load "Prop.v".

Set Implicit Arguments.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
  intuition.
  destruct H0.
  auto.
Qed.

Definition excluded_middle := forall P : Prop, P \/  ~P.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
  unfold excluded_middle.
  intuition.
  remember(H (P x)).
  destruct o.
  trivial.
  absurd(P x -> False).
  eauto.
  trivial.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
  intros.
  intuition;
  try(destruct H;
  intuition;
  eauto;
  fail);
  destruct H0;
  eauto.
Qed.

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Goal forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
  intros.
  unfold override.
  destruct (eq_nat_dec k1 k2);
  trivial.
Qed.

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
| all_nil : all P nil
| all_con : forall e l, P e -> all P l -> all P (e :: l).

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Goal forall X t l, @forallb X t l = true -> all (fun x => t x = true) l.
  intros.
  induction l;
  simpl in *.
  constructor.
  destruct (t a) eqn:Heq;
  simpl in *.
  constructor.
  trivial.
  tauto.
  discriminate.
Qed.

Goal forall X t l, @forallb X t l = false -> ~all (fun x => t x = true) l.
  intros.
  induction l;
  simpl in *.
  discriminate.
  destruct (t a) eqn:Heq;
  simpl in *.
  intuition.
  inversion H0.
  subst.
  tauto.
  intuition.
  inversion H0.
  subst.
  apply IHl.
  eauto with *.
  trivial.
Qed.

Inductive iom { T } : list T -> list T -> list T -> Prop :=
| iom_nil : iom nil nil nil
| iom_l_cons : forall e l r m, iom l r m -> iom (e :: l) r (e :: m)
| iom_r_cons : forall e l r m, iom l r m -> iom l (e :: r) (e :: m).

Goal forall T test l1 l2 l3,
  @all T (fun e => test e = true) l1 -> 
    all (fun e => test e = false) l2 -> 
      iom l1 l2 l3 ->
        l1 = filter test l3.
  induction l1;
  induction l2;
  induction l3;
  trivial;
  intros;
  simpl in *;
  try(inversion H1;fail);
  intuition;
  inversion H1;
  subst.
  inversion H0;
  subst.
  rewrite H6.
  auto.
  inversion H;
  subst.
  rewrite H5.
  f_equal.
  eauto.
  inversion H.
  subst.
  rewrite H5.
  f_equal.
  eauto.
  inversion H0.
  subst.
  rewrite H6.
  auto.
Qed.

Theorem sub_e_l_sub_l : forall T e l r, @sub T (e :: l) r -> sub l r.
  induction l.
  intros.
  apply sub_l_nil.
  intros.
  induction r.
  inversion H.
  inversion H;
  subst.
  intuition.
  constructor.
  trivial.
  constructor.
  trivial.
Qed.

Goal forall T test l r,
  all (fun e => test e = true) r -> @sub T r l -> length r <= length (filter test l).
  induction l.
  intros.
  simpl in *.
  inversion H0.
  trivial.
  intros.
  simpl in *.
  destruct(test a) eqn:Heq;
  simpl in *.
  inversion H0;
  subst.
  auto.
  simpl in *.
  assert(length l0 <= (length (filter test l))).
  apply IHl.
  inversion H.
  trivial.
  trivial.
  omega.
  apply IHl.
  trivial.
  inversion H0;
  subst.
  trivial.
  inversion H;
  subst.
  eauto with *.
Qed.

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
| ai_here : forall l, appears_in a (a::l)
| ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Lemma appears_in_app : forall (X:Type)(x:X)(xs ys : list X),
  appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
  induction xs.
  intros.
  simpl in *.
  tauto.
  intros.
  simpl in *.
  inversion H;
  subst.
  constructor.
  constructor.
  remember (IHxs ys).
  clear Heqo.
  intuition.
  left.
  constructor.
  trivial.
Qed.

Lemma app_appears_in : forall (X:Type)(x:X)(xs ys : list X),
  appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
  induction xs;
  intros.
  simpl in *.
  intuition.
  inversion H0.
  destruct H.
  simpl in *.
  inversion H;
  subst.
  constructor.
  constructor.
  apply IHxs.
  tauto.
  simpl in *.
  constructor.
  auto.
Qed.

Definition disjoint T x y :=
  (forall e, @appears_in T e x -> ~appears_in e y) /\
    (forall e, appears_in e y -> ~appears_in e x).

Inductive no_repeats { X } : list X -> Prop :=
| no_nil : no_repeats nil
| no_cons : forall l (e : X), disjoint [e] l -> no_repeats l -> no_repeats (e :: l).

Theorem disjoint_l_nil : forall T l, @disjoint T l nil.
  intros.
  split;
  intros;
  intuition.
  inversion H0.
  inversion H.
Qed.

Theorem disjoint_reflexive : forall T l r, @disjoint T l r -> disjoint r l.
  induction l;
  intros.
  apply disjoint_l_nil.
  inversion_clear H.
  intuition.
  split;
  trivial.
Qed.

Goal forall T l1 l2,
  @no_repeats T l1 -> 
    no_repeats l2 -> 
      disjoint l1 l2 -> 
        no_repeats (l1 ++ l2).
  induction l1.
  intros.
  simpl in *.
  trivial.
  intros.
  simpl in *.
  constructor.
  admit.
  apply IHl1.
  inversion H.
  trivial.
  trivial.
  inversion H1.
  intuition.
  split;
  intros;
  intuition;
  eapply H3;
  eauto;
  constructor;
  trivial.
Qed.

Inductive nostutter { X } : list X -> Prop :=
| nostutter_nil : nostutter nil
| nostutter_once : forall e, nostutter [e]
| nostutter_cons : forall a e l, a <> e -> nostutter (e :: l) -> nostutter (a :: e :: l).

Example test_nostutter_1 : nostutter [3;1;4;1;5;6].
  repeat constructor;
  discriminate.
Qed.

Example test_nostutter_2 : @nostutter nat [].
  constructor.
Qed.

Example test_nostutter_3 : nostutter [5].
  constructor.
Qed.

Example test_nostutter_4 : ~(nostutter [3;1;1;4]).
  intuition.
  inversion_clear H.
  inversion_clear H1.
  tauto.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
| repeat_twice : forall x, repeats[x;x]
| repeat_skip : forall l r x, repeats (l ++ r) -> repeats(l ++ [x] ++ r).

Theorem disjoint_no_cons : forall T (e : T) l, ~disjoint [e] (e :: l).
  intros.
  intuition.
  inversion_clear H.
  apply(H1 e);
  intuition;
  constructor.
Qed.

Theorem disjoint_inequal : forall T (le re : T) l, disjoint [le] (re :: l) -> le <> re.
  intros.
  intuition.
  subst.
  apply disjoint_no_cons in H.
  trivial.
Qed.

Theorem repeats_cons : forall T (e : T) l, repeats l -> repeats (e :: l).
  induction 1.
  replace [e; x; x] with ([] ++ [e] ++ [x; x]);
  trivial.
  apply repeat_skip;
  simpl in *;
  constructor.
  replace (e :: l ++ [x] ++ r) with ((e :: l) ++ [x] ++ r);
  try apply repeat_skip;
  trivial.
Qed.

Definition bring_to_front { T } 
  (dec : forall l r : T, { l = r } + { l <> r }) e : 
    forall l : list T, appears_in e l -> { lr | Permutation l lr /\ hd_error lr = value e }.
  intros.
  induction l.
  assert (False).
  inversion H.
  tauto.
  destruct (dec e a).
  subst.
  exists (a :: l).
  simpl in *.
  auto.
  assert (appears_in e l).
  inversion H.
  tauto.
  trivial.
  intuition.
  destruct X.
  intuition.
  exists (x ++ [a]).
  intuition.
  apply (@perm_trans _ _ (l ++ [a])).
  apply Permutation_cons_append.
  apply Permutation_app_tail.
  trivial.
  destruct x.
  discriminate.
  trivial.
Defined.

Theorem not_forall : 
  excluded_middle -> 
    forall X (F : _ -> Prop), ~(forall x : X, F x) ->
      exists x, ~F x.
  intros.
  destruct (H (exists x : X, ~F x)).
  trivial.
  assert (False).
  apply H0.
  intros.
  destruct (H (F x)).
  trivial.
  assert (False).
  apply H1.
  eauto.
  tauto.
  tauto.
Qed.

Theorem appears_repeat : forall T (e : T) l, appears_in e l -> repeats (e :: l).
  induction l.
  intros.
  inversion H.
  intros.
  inversion H.
  subst.
  clear IHl H.
  induction l.
  constructor.
  replace (a :: a :: a0 :: l) with ([a; a] ++ [a0] ++ l).
  apply repeat_skip.
  trivial.
  trivial.
  subst.
  intuition.
  replace (e :: a :: l) with ([e] ++ [a] ++ l).
  apply repeat_skip.
  trivial.
  trivial.
Qed.

Theorem Permutation_appears : 
  forall X (x : X) l r,
    appears_in x l -> 
      Permutation l r -> 
        appears_in x r.
  induction 2.
  trivial.
  inversion H;
  subst;
  constructor.
  tauto.
  inversion H;
  subst;
  try (repeat constructor;trivial;fail).
  inversion H1;
  subst;
  try (repeat constructor;trivial;fail).
  tauto.
Qed.

Definition appears_dec : forall (X : Type)
  (H : (forall l r : X, { l = r } + { l <> r })),
    forall (x : X) l,
      { appears_in x l } + { ~appears_in x l }.
  induction l.
  right.
  inversion 1.
  destruct IHl.
  left.
  constructor.
  trivial.
  destruct (H x a).
  subst.
  left.
  constructor.
  right.
  inversion 1;
  subst;
  tauto.
Qed.

Theorem pigeonhole_principle: forall (X : Type)
  (H : (forall l r : X, { l = r } + { l <> r })), 
    forall (l1 l2 : list X),
      (forall x, appears_in x l1 -> appears_in x l2) -> 
        length l2 < length l1 -> 
          repeats l1.
  induction l1;
  intros;
  simpl in *;
  try omega.
  destruct (appears_dec H a l1).
  apply appears_repeat.
  trivial.
  assert (appears_in a l2).
  apply H0.
  constructor.
  intros.
  destruct (@bring_to_front X H a l2 H2).
  destruct a0.
  assert (forall x0 : X, appears_in x0 (a :: l1) -> appears_in x0 x).
  intros.
  apply (@Permutation_appears _ _ l2).
  apply H0.
  trivial.
  trivial.
  clear H0.
  assert(length x < S (length l1)).
  apply Permutation_length in H3.
  omega.
  clear H1.
  assert(appears_in a x).
  apply (@Permutation_appears _ _ l2).
  trivial.
  trivial.
  clear H2 H3 l2.
  destruct x.
  discriminate.
  simpl in *.
  destruct (H a x).
  subst.
  clear H1.
  assert(repeats l1).
  apply (IHl1 x0);
  intros.
  assert(appears_in x1 (x :: l1)).
  constructor;
  trivial.
  specialize (H5 x1);
  intuition.
  destruct (H x1 x);
  subst.
  tauto.
  inversion H3;
  subst;
  trivial;
  tauto.
  omega.
  apply repeats_cons.
  trivial.
  inversion H4;
  subst;
  tauto.
Qed.