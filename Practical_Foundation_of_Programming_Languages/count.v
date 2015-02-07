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

Theorem conunt_length : forall T p (l : list T), count_true p l + count_false p l = length l.
  intros.
  induction l.
  trivial.
  unfold count_false in *.
  simpl in *.
  destruct (p a);
  simpl in *;
  omega.
Qed.

Theorem count_app : 
  forall T p (l r : list T), count_true p (l ++ r) = count_true p l + count_true p r.
  intros.
  induction l;
  intros.
  trivial.
  simpl in *.
  destruct (p a);
  simpl in *;
  auto.
Qed.

Theorem Permutation_count : 
  forall T p (l r : list T), Permutation l r -> count_true p l = count_true p r.
  intros.
  induction H;
  simpl in *;
  auto;
  omega.
Qed.

Theorem count_le_length : forall T p (l : list T), count_true p l <= length l.
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

Theorem count_filter : forall T p (l : list T), count_true p l = length (filter p l).
  induction l.
  trivial.
  simpl in *.
  destruct (p a);
  simpl;
  auto.
Qed.

Theorem count_count_occ : forall T t (dec : eq_dec T) l, 
  count_occ dec l t = count_true (fun e => if dec e t then true else false) l.
  induction l.
  trivial.
  simpl in *.
  destruct (dec a t).
  subst.
  simpl in *.
  auto.
  trivial.
Qed.