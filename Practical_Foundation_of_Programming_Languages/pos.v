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
  pos_before p ++ [t] ++ pos_after p = lt.
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
  lt, In t lt -> pos t lt.
  induction lt;
  intros;
  simpl in *.
  tauto.
  destruct (dec a t).
  subst.
  constructor.
  assert (In t lt).
  tauto.
  intuition.
  constructor.
  trivial.
Defined.

