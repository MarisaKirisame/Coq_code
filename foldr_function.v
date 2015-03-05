Set Implicit Arguments.

Require Import Program List FunctionalExtensionality.

Fixpoint foldl a b (f : a -> b -> a) (l : a) (r : list b) : a :=
  match r with
  | [] => l
  | r_head :: r_tail => foldl f (f l r_head) r_tail
  end.

Fixpoint foldr a b (f : a -> b -> b) (l : b) (r : list a) : b :=
  match r with
  | [] => l
  | r_head :: r_tail => f r_head (foldr f l r_tail)
  end.

Definition foldr_id a (l : list a) : list a :=
  foldr cons [] l.

Goal forall a, @foldr_id a = id.
  intros.
  apply functional_extensionality.
  unfold id.
  induction x.
  trivial.
  unfold foldr_id in *.
  simpl in *.
  f_equal.
  trivial.
Qed.

Definition foldr_map a b (f : a -> b) (l : list a) : list b :=
  foldr (fun x ys => f x :: ys) [] l.

Goal forall a b, @foldr_map a b = @map a b.
  intros.
  apply functional_extensionality.
  intros.
  apply functional_extensionality.
  induction x0.
  trivial.
  unfold foldr_map in *.
  simpl in *.
  f_equal.
  trivial.
Qed.

Definition foldr_filter a (f : a -> bool) (l : list a) :=
  foldr (fun x ys => if f x then x :: ys else ys) [] l.

Goal forall a, @foldr_filter a = @filter a.
  intros.
  apply functional_extensionality.
  intros.
  apply functional_extensionality.
  induction x0.
  trivial.
  simpl in *.
  unfold foldr_filter.
  simpl in *.
  destruct(x a0).
  f_equal.
  trivial.
  trivial.
Qed.

Definition foldr_foldl a b (f : a -> b -> a) (l : a) (r : list b) : a :=
  foldr (fun x g a => g (f a x)) id r l.

Goal forall a b, @foldr_foldl a b = @foldl a b.
  intros.
  apply functional_extensionality.
  intros.
  apply functional_extensionality.
  intros.
  apply functional_extensionality.
  intros.
  generalize dependent x0.
  induction x1.
  trivial.
  simpl in *.
  intros.
  eauto.
Qed.