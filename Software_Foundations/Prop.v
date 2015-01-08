Require Import Omega Arith List Recdef Program.

Set Implicit Arguments.

Fixpoint evenb n :=
  match n with
  | O => true
  | S O => false
  | S (S n) => evenb n
  end.

Definition even (n:nat) : Prop :=
  evenb n = true.

Inductive ev : nat -> Prop :=
| ev_0 : ev O
| ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem double_even : forall n,
  ev (n + n).
  induction n.
  constructor.
  simpl.
  rewrite plus_comm.
  simpl.
  constructor.
  trivial.
Qed.

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
   induction 1.
   trivial.
   intros.
   intuition.
   constructor.
   trivial.
Qed.

Inductive beautiful : nat -> Prop :=
| b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Hint Constructors beautiful ev.

Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
  intros.
  simpl.
  replace(n + (n + 0)) with (n + n).
  apply (@b_sum n);
  trivial.
  auto.
Qed. 

Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
  induction m.
  simpl in *.
  constructor.
  intros.
  simpl in *.
  intuition.
Qed.

Inductive gorgeous : nat -> Prop :=
| g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (S (S (S n)))
| g_plus5 : forall n, gorgeous n -> gorgeous (S (S (S (S (S n))))).

Hint Constructors gorgeous.

Theorem gorgeous_plus13: forall n,
  gorgeous n -> gorgeous (13+n).
  intros.
  simpl in *.
  auto.
Qed.

Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
  induction 1.
  trivial.
  intros.
  simpl in *.
  auto.
  intros.
  simpl in *.
  auto.
Qed.

Hint Resolve gorgeous_sum.

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
  induction 1;
  trivial;
  auto.
Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
  induction 1;
  trivial;
  simpl in *;
  auto.
Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
  inversion 1.
  inversion H1.
  trivial.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
  inversion 1.
  inversion H1.
  inversion H3.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  intros.
  induction H0.
  trivial.
  simpl in *.
  inversion H.
  tauto.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
  intros.
  assert(ev (n + n + (m + p))).
  admit.
  apply (@ ev_ev__ev (n + n)) in H1.
  trivial.
  apply double_even.
Qed.

Inductive pal { t } : list t -> Prop :=
| pal_nil : pal nil
| pal_one : forall y, pal (y :: nil)
| pal_con : forall y l, pal l -> pal (y :: l ++ (y :: nil)).

Theorem last_last : forall T l (t : T) n, (last (l ++ (t :: nil)) n = t).
  intros.
  induction l.
  trivial.
  simpl in *.
  rewrite <- IHl at 2.
  destruct (l ++ t :: nil) eqn: H.
  simpl in *.
  destruct l;
  discriminate.
  trivial.
Qed.

Definition extract_last { T } (l : list T) : { n | l = fst n ++ snd n :: nil } + (l = nil).
  induction l.
  tauto.
  left.
  destruct IHl.
  destruct s.
  subst.
  destruct x.
  simpl in *.
  exists (a :: l, t).
  trivial.
  subst.
  exists (@nil T, a).
  trivial.
Defined.

Fixpoint double_list_rect_inner (A : Type) (P : list A -> Type) (f : P nil)
  (f0 : forall a : A, P (a :: nil))
    (f1 : forall (a b : A) (l : list A), P l -> P (a :: l ++ b :: nil))
      (l : list A)
        (list_length : nat)(E : length l = list_length) 
          { struct list_length } : P l.
  destruct l.
  trivial.
  destruct list_length.
  discriminate.
  trivial.
  simpl in *.
  inversion E.
  destruct (extract_last l).
  destruct s.
  destruct x.
  simpl in *.
  subst l.
  apply f1.
  destruct l0.
  trivial.
  destruct list_length.
  discriminate.
  apply double_list_rect_inner with (list_length := list_length).
  trivial.
  trivial.
  trivial.
  assert(length (l0 ++ [a0]) = S (length l0)).
  clear E.
  clear H0.
  induction l0;
  simpl in *;
  auto.
  simpl in *.
  omega.
  subst.
  trivial.
Defined.

Definition double_list_rect (A : Type) (P : list A -> Type) (f : P nil)
  (f0 : forall a : A, P (a :: nil))
    (f1 : forall (a b : A) (l : list A), P l -> P (a :: l ++ b :: nil))
      (l : list A) : P l.
  eapply double_list_rect_inner;
  trivial.
Defined.

Goal forall t l, @rev t l = l -> pal l.
  intros t l.
  refine(double_list_rect (fun l0 => rev l0 = l0 -> pal l0) _ _ _ l);
  intros;
  try (constructor;fail).
  simpl in *.
  rewrite rev_unit in *.
  simpl in *.
  inversion H0.
  subst.
  constructor.
  apply app_inv_tail in H3.
  rewrite H3.
  auto.
Qed.

Goal forall t l, pal l -> @rev t l = l.
  induction 1.
  trivial.
  trivial.
  simpl in *.
  rewrite rev_unit.
  simpl in *.
  f_equal.
  f_equal.
  trivial.
Qed.

Inductive sub { T } : list T -> list T -> Prop :=
| sub_nil : sub [] []
| sub_skip : forall l r e, sub l r -> sub l (e :: r)
| sub_con : forall l r e, sub l r -> sub (e :: l) (e :: r).

Goal forall T l, @sub T l l.
  induction l.
  constructor.
  apply sub_con.
  trivial.
Qed.

Theorem sub_app : forall T l1 l2 l3, @sub T l1 l2 -> sub l1 (l2 ++ l3).
  induction 1.
  simpl in *.
  induction l3.
  constructor.
  constructor.
  trivial.
  simpl in *.
  constructor.
  trivial.
  apply sub_con.
  trivial.
Qed.

Theorem sub_l_nil : forall T l, @sub T [] l.
  induction l.
  constructor.
  constructor.
  trivial.
Qed.

Theorem sub_trans : forall T l1 l2 l3, @sub T l1 l2 -> sub l2 l3 -> sub l1 l3.
  induction l1.
  intros.
  apply sub_l_nil.
  induction l2.
  inversion 1.
  induction l3.
  inversion 2.
  intros.
  inversion H0;
  subst;
  intuition.
  induction H2.
  constructor.
  constructor.
  intuition.
  constructor.
  constructor.
  trivial.
  constructor.
  apply sub_con.
  trivial.
  inversion H.
  subst.
  constructor.
  auto.
  subst.
  apply sub_con.
  eauto.
Qed.

Inductive R : nat -> list nat -> Prop :=
| c1 : R 0 []
| c2 : forall n l, R n l -> R (S n) (n :: l)
| c3 : forall n l, R (S n) l -> R n l.

Goal R 2 [1;0].
  repeat constructor.
Qed.

Goal R 1 [1;2;1;0].
  repeat constructor.
Qed.

Inductive total : nat -> nat -> Prop := total_all : forall n m, total n m.
Inductive empty : nat -> nat -> Prop :=.

Goal forall m n o, m <= n -> n <= o -> m <= o.
  induction m;
  induction n;
  induction o;
  intros;
  trivial;
  inversion H0;
  subst;
  trivial;
  auto.
Qed.

Goal forall n, 0 <= n.
  induction n.
  trivial.
  auto.
Qed.

Goal forall n m, n <= m -> S n <= S m.
  intros.
  induction H.
  trivial.
  auto.
Qed.

Goal forall n m, S n <= S m -> n <= m.
  induction n.
  intros.
  clear H.
  induction m.
  trivial.
  auto.
  induction m.
  intros.
  inversion H;
  subst.
  inversion H1.
  intros.
  inversion H.
  trivial.
  subst.
  inversion H1;
  subst;
  auto.
Qed.

Goal forall a b, a <= a + b.
  induction a.
  intros.
  simpl in *.
  induction b.
  trivial.
  auto.
  intros.
  replace (S a + b) with (S b + a).
  apply le_n_S.
  rewrite plus_comm.
  trivial.
  ring.
Qed.

Goal forall n1 n2 m, n1 + n2 < m -> n1 < m /\ n2 < m.
  induction n1.
  intros.
  simpl in *.
  split;
  trivial.
  destruct m.
  inversion H.
  clear n2 H.
  induction m;
  auto.
  induction n2.
  intros.
  rewrite plus_comm in H.
  simpl in *.
  split.
  trivial.
  destruct m.
  inversion H.
  clear n1 IHn1 H.
  induction m;
  auto.
  induction m.
  intros.
  simpl in *.
  inversion H.
  intros.
  simpl in *.
  split.
  apply IHn2.
  rewrite plus_comm in *.
  apply lt_S_n.
  simpl in *.
  auto.
  apply IHn1.
  apply lt_S_n.
  auto.
Qed.

Goal forall n m, n < m -> n < S m.
  induction n;
  induction m;
  intros;
  auto.
Qed.

Goal forall n m, leb n m = true -> n <= m.
  induction n;
  induction m.
  trivial.
  intros.
  simpl in *.
  auto.
  discriminate.
  intros.
  simpl in *.
  auto with *.
Qed.

Goal forall n m, n <= m -> leb n m = true.
  induction n;
  induction m;
  trivial.
  inversion 1.
  intros.
  simpl in *.
  destruct m;
  auto with *.
Qed.

Goal forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
  intros.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply leb_correct.
  eapply le_trans with m;
  trivial.
Qed.

Goal forall n m, leb n m = false -> ~(n <= m).
  induction n;
  induction m;
  intros;
  simpl in *;
  try discriminate;
  intuition.
  destruct m;
  eauto with *.
Qed.

Module R.

  Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 : forall m n o, R m n o -> R (S m) n (S o)
  | c3 : forall m n o, R m n o -> R m (S n) (S o)
  | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
  | c5 : forall m n o, R m n o -> R n m o.

  Goal R 1 1 2.
    constructor.
    constructor.
    constructor.
  Qed.

  Goal forall x y z, R x y z -> x + y = z.
    induction 1;
    subst;
    trivial;
    try ring;
    omega.
  Qed.

End R.

Definition combine_odd_even (Podd Peven : nat -> Prop) n : Prop :=
  if NPeano.even n then Peven n else Podd n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (NPeano.even n = false -> Podd n) ->
      (NPeano.even n = true -> Peven n) ->
        combine_odd_even Podd Peven n.
  intros.
  unfold combine_odd_even.
  destruct(NPeano.even n);
  tauto.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
      NPeano.even n = false ->
        Podd n.
  intros.
  unfold combine_odd_even in *.
  rewrite H0 in *.
  trivial.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
      NPeano.even n = true ->
        Peven n.
  intros.
  unfold combine_odd_even in *.
  rewrite H0 in *.
  trivial.
Qed.

Fixpoint true_upto_n__true_everywhere (n : nat) (P : nat -> Prop) { struct n } :=
  match n with
  | O => forall n, P n
  | S N => (P n) -> true_upto_n__true_everywhere N P
  end.

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
  simpl in *.
  trivial.
Qed.