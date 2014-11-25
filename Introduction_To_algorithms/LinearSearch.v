Require Import List Mergesort Setoid Permutation Sorted Orders Omega.

Set Implicit Arguments.

Fixpoint LinearSearch (A : Type)(l : list A)(f : A -> bool) : option nat := 
  match l with
  | nil => None
  | l_head :: l_tail =>
      match f l_head with
      | true => Some O
      | false => 
          match LinearSearch l_tail f with
          | None => None
          | Some n => Some (S n)
          end
      end
  end.

Theorem SearchNoneFalse : forall A (l : list A) f, 
  LinearSearch l f = None -> 
    (forall n d, f d = false -> f (nth n l d) = false).
  intros A l f H.
  induction l.
  simpl in *.
  destruct n.
  trivial.
  trivial.
  simpl in *.
  intros.
  remember (f a) as b.
  destruct b.
  inversion H.
  destruct n.
  auto.
  apply IHl.
  remember (LinearSearch l f) as R.
  destruct R.
  inversion H.
  trivial.
  trivial.
Qed.

Theorem FalseSearchNone : forall A (l : list A) f d,
  f d = false ->
  (forall n, f (nth n l d) = false) ->
    LinearSearch l f = None.
  intros.
  induction l.
  trivial.
  simpl.
  assert(LinearSearch l f = None) as HR.
  apply IHl.
  intros.
  remember (H0 (S n)).
  trivial.
  rewrite HR in *.
  remember(H0 0).
  simpl in *.
  rewrite e.
  trivial.
Qed.

Theorem TrueSearchSome : forall A d f (l : list A) m,
  f d = false -> 
    f (nth m l d) = true ->
      (forall n, n < m -> f (nth n l d) = false) ->
        LinearSearch l f = Some m.
  induction l.
  intros.
  simpl in *.
  destruct m;
  rewrite H in H0;
  inversion H0.
  intros.
  simpl in *.
  destruct m.
  rewrite H0 in *.
  trivial.
  assert(f a = false).
  remember(H1 0).
  simpl in *.
  auto with *.
  rewrite H2 in *.
  assert(LinearSearch l f = Some m).
  apply IHl.
  trivial.
  trivial.
  intros.
  remember(H1 (S n)).
  simpl in *.
  apply e.
  subst.
  auto with *.
  rewrite H3.
  trivial.
Qed.

Theorem SomeTrueSearch : forall A d f (l : list A) m,
  LinearSearch l f = Some m ->
    f d = false -> 
      f (nth m l d) = true ->
        (forall n, n < m -> f (nth n l d) = false).
  induction l.
  simpl in *.
  destruct n;
  trivial.
  intros.
  simpl in *.
  destruct m.
  omega.
  remember (f a) as b.
  destruct b.
  inversion H.
  destruct n.
  auto.
  remember (LinearSearch l f) as L.
  destruct L.
  assert(m = n0).
  inversion H.
  trivial.
  subst.
  eapply IHl.
  trivial.
  trivial.
  trivial.
  omega.
  inversion H.
Qed.