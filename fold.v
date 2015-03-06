Set Implicit Arguments.

Require Import Program List FunctionalExtensionality Recdef Omega.

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

Fixpoint concat a (l : list (list a)) : list a :=
  match l with
  | [] => []
  | l_head :: l_tail => l_head ++ (concat l_tail)
  end.

Definition foldr_concat a (l : list (list a)) : list a :=
  foldr (fun l r => l ++ r) [] l.

Goal forall a, @foldr_concat a = @concat a.
  intros.
  apply functional_extensionality.
  induction x.
  trivial.
  unfold foldr_concat in *.
  simpl in *.
  f_equal.
  trivial.
Qed.

Fixpoint takeWhile a (P : a -> bool) (l : list a) : list a :=
  match l with
  | [] => []
  | l_head :: l_tail =>
      if P l_head then l_head :: takeWhile P l_tail else []
  end.

Definition foldr_takeWhile a (P : a -> bool) (l : list a) : list a :=
  foldr (fun l r => if P l then l :: r else []) [] l.

Goal forall a, @foldr_takeWhile a = @takeWhile a.
  intros.
  apply functional_extensionality.
  intros.
  apply functional_extensionality.
  induction x0.
  trivial.
  unfold foldr_takeWhile in *.
  simpl in *.
  destruct (x a0).
  f_equal.
  trivial.
  trivial.
Qed.

Fixpoint dropWhile a (P : a -> bool) (l : list a) : list a :=
  match l with
  | [] => []
  | l_head :: l_tail =>
      if P l_head then dropWhile P l_tail else l
  end.

Print foldl.

Definition foldl_dropWhile a (P : a -> bool) (l : list a) : list a := 
  match
    (foldl 
      (fun l r => 
        match l with
        | inl _ => if P r then l else inr [r]
        | inr li => inr (li ++ [r])
      end)
      (@inl unit (list a) tt)
      l) with
  | inl _ => []
  | inr li => li
  end.

Goal forall a, @foldl_dropWhile a = @dropWhile a.
  intros.
  apply functional_extensionality.
  intros.
  apply functional_extensionality.
  induction x0.
  trivial.
  simpl in *.
  unfold foldl_dropWhile in *.
  simpl in *.
  destruct (x a0).
  trivial.
  clear IHx0.
  replace (a0 :: x0) with ([a0] ++ x0).
  generalize dependent [a0].
  clear a0.
  induction x0.
  induction l.
  simpl in *.
  trivial.
  simpl in *.
  f_equal.
  trivial.
  intros.
  simpl in *.
  rewrite IHx0.
  rewrite <- app_assoc.
  trivial.
  trivial.
Qed.

Fixpoint groupBy_inner a n (P : a -> a -> bool) (l : list a) :
  list (list a) :=
  match n with
  | O => []
  | S n' => 
      match l with
      | [] => []
      | l_head :: l_tail => 
          (l_head :: takeWhile (fun e => P l_head e) l_tail) ::
          groupBy_inner n' P (dropWhile (fun e => P l_head e) l_tail)
      end
  end.

Definition groupBy a (P : a -> a -> bool) l := groupBy_inner (length l) P l.

Definition foldl_groupBy a (P : a -> a -> bool) (l : list a) : 
  list (list a) :=
  match 
    foldl
      (fun (l : (list a) * (list (list a))) (r : a) => 
        match l with
        | ([],lr) => ([r], lr)
        | (ll_head::ll_tail,lr) => let ll := ll_head::ll_tail in
            if (P ll_head r) then (ll++[r], lr) else ([r],lr ++ [ll])
        end)
      (pair [] [])
      l with
  | ([], r) => r
  | (l, r) => r ++ [l]
  end.

Theorem app_single_l : forall a (e : a) l, e :: l = [e] ++ l.
  trivial.
Qed.

Theorem takeWhile_dropWhile a P (l : list a) :
  l = takeWhile P l ++ dropWhile P l.
  induction l.
  trivial.
  simpl in *.
  destruct (P a0).
  simpl in *.
  f_equal.
  trivial.
  trivial.
Qed.

Theorem foldl_groupBy_lextract a (x : a -> a -> bool) a0 a1 x0 : 
  (let (l, r) :=
    foldl
      (fun (l : list a * list (list a)) (r : a) =>
        let (l0, lr) := l in
        match l0 with
        | [] => ([r], lr)
        | ll_head :: ll_tail =>
            if x ll_head r
            then (ll_head :: ll_tail ++ [r], lr)
            else ([r], lr ++ [ll_head :: ll_tail])
        end)
    (a1, a0)
    x0 in
    match l with
    | [] => r
    | _ :: _ => r ++ [l]
    end) =
  a0 ++ 
  (let (l, r) :=
    foldl
      (fun (l : list a * list (list a)) (r : a) =>
        let (l0, lr) := l in
        match l0 with
        | [] => ([r], lr)
        | ll_head :: ll_tail =>
            if x ll_head r
            then (ll_head :: ll_tail ++ [r], lr)
            else ([r], lr ++ [ll_head :: ll_tail])
        end)
    (a1, [])
    x0 in
    match l with
    | [] => r
    | _ :: _ => r ++ [l]
    end).
  generalize dependent a1.
  generalize dependent a0.
  induction x0.
  simpl in *.
  destruct a1;
  auto with *.
  simpl in *.
  intros.
  destruct a2.
  trivial.
  destruct (x a2 a0).
  trivial.
  rewrite IHx0.
  rewrite <- app_assoc.
  simpl in *.
  f_equal.
  rewrite (IHx0 [a2 :: a3] [a0]).
  trivial.
Qed.

Theorem foldl_groupBy_rextract a a0 a1 (x : a -> a -> bool) x0 :
  (let (l, r) :=
    foldl
      (fun (l : list a * list (list a)) (r : a) =>
        let (l0, lr) := l in
        match l0 with
        | [] => ([r], lr)
        | ll_head :: ll_tail =>
            if x ll_head r
            then (ll_head :: ll_tail ++ [r], lr)
            else ([r], lr ++ [ll_head :: ll_tail])
        end)
      ([a0] ++ a1, [])
      (takeWhile (fun e : a => x a0 e) x0 ++
      dropWhile (fun e : a => x a0 e) x0) in
  match l with
  | [] => r
  | _ :: _ => r ++ [l]
  end) =
  (a0 :: a1 ++ takeWhile (fun e : a => x a0 e) x0) ::
  (let (l, r) :=
    foldl
      (fun (l : list a * list (list a)) (r : a) =>
        let (l0, lr) := l in
          match l0 with
          | [] => ([r], lr)
          | ll_head :: ll_tail =>
              if x ll_head r
              then (ll_head :: ll_tail ++ [r], lr)
              else ([r], lr ++ [ll_head :: ll_tail])
          end)
      ([], []) 
      (dropWhile (fun e : a => x a0 e) x0) in
  match l with
  | [] => r
  | _ :: _ => r ++ [l]
  end).
  generalize dependent a1.
  induction x0;
  intros;
  simpl in *.
  f_equal.
  f_equal.
  auto with *.
  destruct (x a0 a1) eqn:B.
  simpl in *.
  rewrite B.
  rewrite IHx0.
  f_equal.
  f_equal.
  rewrite <- app_assoc.
  trivial.
  simpl in *.
  rewrite B.
  rewrite foldl_groupBy_lextract.
  simpl in *.
  f_equal.
  f_equal.
  auto with *.
Qed.

Goal forall a, @foldl_groupBy a = @groupBy a.
  intros.
  apply functional_extensionality.
  intros.
  apply functional_extensionality.
  unfold groupBy.
  assert(
    forall n x0,
      n >= length x0 ->
        foldl_groupBy x x0 = groupBy_inner n x x0).
  induction n;
  intros.
  simpl in *.
  destruct x0.
  trivial.
  simpl in *.
  omega.
  destruct x0.
  trivial.
  simpl in *.
  rewrite <- IHn.
  clear IHn H.
  rewrite (takeWhile_dropWhile (fun e : a => x a0 e) x0) at 1.
  unfold foldl_groupBy.
  simpl in *.
  induction x0.
  trivial.
  simpl in *.
  destruct (x a0 a1) eqn:B;
  simpl in *.
  unfold foldl_groupBy.
  simpl in *.
  rewrite B in *.
  replace ([a0;a1]) with ([a0] ++ [a1]).
  rewrite foldl_groupBy_rextract.
  trivial.
  trivial.
  unfold foldl_groupBy.
  simpl in *.
  rewrite B in *.
  rewrite foldl_groupBy_lextract.
  trivial.
  induction x0.
  simpl in *.
  omega.
  simpl in *.
  destruct (x a0 a1).
  auto with *.
  simpl in *.
  omega.
  intros.
  auto.
Qed.

Fixpoint any a (P : a -> bool) l : bool :=
  match l with
  | nil => false
  | l_head :: l_tail => orb (P l_head) (any P l_tail)
  end.

Definition foldr_any a (P : a -> bool) (l : list a) : bool := 
  foldr (fun l r => orb (P l) r) false l.

Goal forall a, @foldr_any a = @any a.
  intros.
  apply functional_extensionality.
  intros.
  apply functional_extensionality.
  intros.
  induction x0.
  trivial.
  unfold foldr_any in *.
  simpl in *.
  f_equal.
  trivial.
Qed.