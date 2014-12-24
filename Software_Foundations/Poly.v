Require Import List Arith.

Set Implicit Argument.

Inductive baz : Type :=
| bazx : baz -> baz
| bazy : baz -> bool -> baz.

Goal baz -> False.
  induction 1;
  trivial.
Qed.

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S m => n :: (repeat n m)
  end.

Theorem nil_app : forall X:Type, forall l:list X,
  app nil l = l.
  trivial.
Qed.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil => v :: nil
  | cons h t => h :: (snoc X t v)
  end.

Theorem rev_snoc :
  forall X (v : X) (s : list X),
  rev (snoc X s v) = v :: (rev s).
  intros.
  induction s.
  trivial.
  simpl in *.
  rewrite IHs.
  trivial.
Qed.

Theorem rev_unit :
  forall (A : Type) (l : list A) (a : A), rev (l ++ a :: nil) = a :: rev l.
  induction l.
  trivial.
  intros.
  simpl in *.
  rewrite IHl.
  trivial.
Qed.

Theorem rev_involutive : forall l : list nat,
  rev (rev l) = l.
  induction l.
  trivial.
  simpl in *.
  rewrite rev_unit.
  f_equal.
  trivial.
Qed.

Theorem snoc_with_append :
  forall X (l1 l2 : list X) v,
  snoc X (l1 ++ l2) v = l1 ++ (snoc X l2 v).
  induction l1.
  trivial.
  intros.
  simpl in *.
  f_equal.
  trivial.
Qed.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | nil => pair nil nil
  | pair a b :: l' => pair (a :: fst (split l')) (b :: snd (split l'))
  end.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Theorem uncurry_curry : forall(X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
  trivial.
Qed.

Theorem curry_uncurry : forall(X Y Z : Type) f p,
  prod_uncurry (@prod_curry X Y Z f) p = f p.
  tauto.
Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter 
    (fun n => 
      andb
        (NPeano.ltb 7 n)
        ((fix even (n : nat) : bool := 
          match n with
          | O => true
          | S O => false
          | S (S m) => even m
          end) n))
    l.

Definition partition {X : Type} (test : X -> bool) (l : list X)
  : list X * list X :=
  match l with
  | nil => (nil, nil)
  | l_head :: l_tail => 
    if (test l_head)
    then (l_head :: fst (partition test l_tail), snd (partition test l_tail))
    else (fst (partition test l_tail), l_head ::snd (partition test l_tail))
  end.

Fixpoint oddb n :=
  match n with
  | O => false
  | S O => true
  | S (S m) => oddb m
  end.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
  induction l.
  trivial.
  simpl in *.
  rewrite map_app.
  simpl in *.
  f_equal.
  trivial.
Qed.

Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) := fold (fun l r => l ++ r) (map f l) nil.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat -> X:=
  fun (k' : nat) => if beq_nat k k' then x else f k'.

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
  trivial.
Qed.

Theorem override_neq : forall(X:Type) x1 x2 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
  intros.
  subst.
  unfold override.
  rewrite H0.
  trivial.
Qed.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
  intros.
  induction l.
  trivial.
  simpl in *.
  unfold fold_length.
  simpl in *.
  auto.
Qed.

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun l r => f l :: r) l nil.

Goal forall a b (f : a -> b) (l : list a), map f l = (fold_map f l).
  induction l.
  trivial.
  simpl in *.
  unfold fold_map.
  simpl in *.
  f_equal.
  trivial.
Qed.