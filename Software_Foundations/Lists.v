Require Import List Arith.

Set Implicit Arguments.

Definition swap_pair a b (p : a * b) :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing_stuck : forall a b (p : a * b),
  p = (fst p, snd p).
  intros.
  destruct p.
  trivial.
Qed.

Theorem snd_fst_is_swap : forall a b (p : a * b),
  (snd p, fst p) = swap_pair p.
  intros.
  destruct p.
  trivial.
Qed.

Theorem fst_swap_is_snd : forall a b (p : a * b),
  fst (swap_pair p) = snd p.
  tauto.
Qed.

Definition nonzeros (l: list nat) : list nat := 
  filter (fun n => match n with O => false | _ => true end) l.

Fixpoint oddmembers (l:list nat) : list nat :=
  filter (fix odd n := match n with O => false | S n' => negb (odd n') end) l.

Fixpoint countoddmembers l := length (oddmembers l).

Fixpoint alternate (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | l1_head :: l1_tail, l2_head :: l2_tail =>
    l1_head :: l2_head :: alternate l1_tail l2_tail
  end.

Fixpoint count (v:nat) (s:list nat) : nat :=
  length
    (filter 
      (fun n => match eq_nat_dec v n with left _ => true | _ => false end)
      s).

Definition member (v:nat) (s:list nat) : bool := 
  match count v s with
  | O => false
  | _ => true
  end.

Fixpoint remove_all (v:nat) (s:list nat) := 
  filter (fun n => match eq_nat_dec v n with left _ => false | _ => true end) s.

Fixpoint remove_one (v:nat)(s:list nat) : list nat :=
  match s with
  | nil => nil
  | s_head :: s_tail => 
    match eq_nat_dec s_head v with
    | left _ => s_tail
    | _ => s_head :: remove_one v s_tail
    end
  end.

Fixpoint subset (s1 s2:list nat) : bool :=
  match s1 with
  | nil => true
  | s1_head :: s1_tail => 
    andb (member s1_head s2) (subset s1_tail (remove_one s1_head s2))
  end.

Theorem filter_nil_nil : forall a n, filter n nil = @nil a.
  trivial.
Qed.

Goal forall n l1 l2, count n l1 + count n l2 = count n (l1 ++ l2).
  induction l1.
  intros.
  simpl in *.
  replace (count n nil) with 0.
  trivial.
  clear l2.
  destruct n;
  trivial.
  intros.
  unfold count in *.
  simpl in *.
  remember n as n';
  destruct n';
  rewrite Heqn' in *;
  simpl in *;
  remember (eq_nat_dec n a) as s;
  destruct s;
  repeat subst;
  simpl in *;
  auto.
Qed.

Theorem app_nil_end : forall l : list nat,
  l ++ nil = l.
  induction l.
  trivial.
  simpl.
  f_equal.
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

Theorem app_assoc : 
  forall l1 l2 l3 : list nat, l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
  induction l1.
  trivial.
  intros.
  simpl.
  f_equal.
  trivial.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : list nat,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  intros.
  repeat rewrite app_assoc.
  trivial.
Qed.

Fixpoint snoc (l:list nat) (v:nat) := 
  match l with
  | nil => v :: nil
  | h :: t => h :: (snoc t v)
  end.

Theorem snoc_append : forall (l:list nat) (n:nat),
  snoc l n = l ++ n :: nil.
  intros.
  induction l.
  trivial.
  simpl in *.
  f_equal.
  trivial.
Qed.

Theorem distr_rev : forall l1 l2 : list nat,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
  intros.
  induction l1.
  simpl in *.
  symmetry.
  apply app_nil_end.
  simpl in *.
  rewrite IHl1.
  rewrite app_assoc.
  trivial.
Qed.

Lemma nonzeros_app : forall l1 l2,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  induction l1.
  trivial.
  destruct a.
  intros.
  simpl in *.
  trivial.
  intros.
  simpl in *.
  f_equal.
  trivial.
Qed.

Fixpoint beq_natlist (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | l1_head :: l1_tail, l2_head :: l2_tail => 
    andb (beq_nat l1_head l2_head) (beq_natlist l1_tail l2_tail)
  end.

Theorem beq_natlist_refl : forall l,
  true = beq_natlist l l.
  induction l.
  trivial.
  simpl in *.
  induction a.
  trivial.
  trivial.
Qed.

Theorem count_member_nonzero : forall s,
  1 <= (count 1 (1 :: s)).
  induction s.
  trivial.
  simpl in *.
  auto with *.
Qed.

Theorem remove_decreases_count : forall s,
  (count 0 (remove_one 0 s)) <= (count 0 s).
  induction s.
  auto.
  destruct a.
  auto with *.
  trivial.
Qed.

Goal forall l1 l2, @rev nat l1 = rev l2 -> l1 = l2.
  intros.
  rewrite <- (rev_involutive l1).
  rewrite <- (rev_involutive l2).
  f_equal.
  trivial.
Qed.

Definition hd_opt (l : list nat) : option nat :=
  match l with
  | nil => None
  | e :: _ => Some e
  end.

Definition option_elim (d : nat) (o : option nat) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Theorem option_elim_hd : forall l (default:nat),
  hd default l = option_elim default (hd_opt l).
  induction l.
  trivial.
  trivial.
Qed.

Theorem beq_nat_eq : forall k, beq_nat k k = true.
  induction k.
  trivial.
  trivial.
Qed.

Module Dictionary.

  Inductive dictionary : Type :=
  | empty : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

  Definition insert (key value : nat) (d : dictionary) : dictionary :=
    (record key value d).

  Fixpoint find (key : nat) (d : dictionary) : option nat :=
    match d with
    | empty => None
    | record k v d' => 
        if (beq_nat key k)
        then (Some v)
        else (find key d')
    end.

  Theorem dictionary_invariant1' : forall (d : dictionary) (k v: nat),
    (find k (insert k v d)) = Some v.
    intros.
    simpl in *.
    rewrite beq_nat_eq.
    trivial.
  Qed.

  Theorem dictionary_invariant2' : forall(d : dictionary) (m n o: nat),
    beq_nat m n = false -> find m d = find m (insert n o d).
    intros.
    simpl in *.
    rewrite H.
    trivial.
  Qed.

End Dictionary.