Require Import List Permutation Program Omega.
Require Import tactic eq_dec.

Set Implicit Arguments.

Fixpoint count_true (T : Type) (P : T -> bool) (l : list T) :=
  match l with
  | nil => 0
  | l_head :: l_tail => (if P l_head then 1 else 0) + count_true P l_tail
  end.

Definition count_false (T : Type) (P : T -> bool) (l : list T) :=
  count_true (fun x => negb (P x)) l.

Theorem count_length : forall T p (l : list T), count_true p l + count_false p l = length l.
  intros.
  induction l.
  trivial.
  unfold count_false in *.
  simpl in *.
  destruct (p a);
  simpl in *;
  omega.
Qed.

Theorem count_app : forall T p (l r : list T),
  count_true p (l ++ r) = count_true p l + count_true p r.
  intros.
  induction l;
  intros.
  trivial.
  simpl in *.
  destruct (p a);
  simpl in *;
  auto.
Qed.

Theorem Permutation_count : forall T p (l r : list T),
  Permutation l r -> count_true p l = count_true p r.
  intros.
  induction H;
  simpl in *;
  auto;
  omega.
Qed.

Theorem count_le_length : forall T p (l : list T),
  count_true p l <= length l.
  induction l.
  trivial.
  simpl in *.
  destruct (p a);
  omega.
Qed.

Theorem count_Forall : forall T (dec : T -> bool) (l : list T),
  Forall (fun e => dec e = true) l <-> count_true dec l = length l.
  intuition;
  induction l;
  trivial.
  simpl in *.
  invc H.
  rewrite H2.
  simpl in *.
  auto.
  simpl in *.
  destruct (dec a) eqn:Heqd.
  simpl in *.
  invc H.
  auto.
  simpl in *.
  remember (count_le_length dec l).
  omega.
Qed.

Theorem count_Exists : forall T (dec : T -> bool) (l : list T),
  Exists (fun e => dec e = true) l <-> count_true dec l >= 1.
  intuition;
  induction l;
  invc H;
  simpl in *;
  intuition;
  try rewrite H1;
  try omega;
  destruct (dec a) eqn:Heqdec;
  simpl in *;
  auto with *.
Qed.

Theorem count_filter : forall T p (l : list T),
  count_true p l = length (filter p l).
  induction l.
  trivial.
  simpl in *.
  destruct (p a);
  simpl;
  auto.
Qed.

Theorem count_count_occ : forall T t (dec : eq_dec T) l, 
  count_occ dec l t =
  count_true (fun e => if dec e t then true else false) l.
  induction l.
  trivial.
  simpl in *.
  destruct (dec a t).
  subst.
  simpl in *.
  auto.
  trivial.
Qed.
Hint Rewrite count_count_occ.

Theorem count_occ_app_head : forall T t dec (lh lt rh rt : list T),
  lh ++ t :: lt = rh ++ t :: rt -> 
    count_occ dec lh t = count_occ dec rh t ->
      lh = rh.
  induction lh;
  intros;
  destruct rh;
  invc H;
  simpl in *;
  repeat dedec dec;
  trivial;
  try discriminate;
  try tauto;
  f_equal;
  eauto.
Qed.
Hint Rewrite count_occ_app_head.

Theorem count_occ_app_tail : forall T t dec (lh lt rh rt : list T),
  lh ++ t :: lt = rh ++ t :: rt -> 
    count_occ dec lh t = count_occ dec rh t ->
      lt = rt.
  intros.
  rewrite (count_occ_app_head t dec lh lt rh rt) in H;
  trivial.
  apply app_inv_head in H.
  invc H.
  trivial.
Qed.

Theorem count_occ_app : forall T dec (t : T) l r,
  count_occ dec (l ++ r) t = count_occ dec l t + count_occ dec r t.
  intros.
  repeat rewrite count_count_occ.
  apply count_app.
Qed.

Theorem count_occ_lt_In : forall T dec (t : T) l,
  In t l <-> count_occ dec l t > 0.
  intuition;
  induction l;
  simpl in *;
  try destruct (dec a t);
  subst;
  (omega||tauto).
Qed.

Theorem count_occ_In : forall T dec (t : T) l,
  count_occ dec l t >= 1 -> In t l.
  induction l;
  intros;
  simpl in *.
  omega.
  destruct (dec a t);
  subst;
  simpl in *;
  tauto.
Qed.

Theorem In_count_occ : forall T dec (t : T) l, 
  In t l -> count_occ dec l t >= 1.
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