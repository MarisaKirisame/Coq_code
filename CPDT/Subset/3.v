Require Import Bool List Arith Omega.

Set Implicit Arguments.

Definition var := nat.

Inductive literal :=
| positive : forall v : var, literal
| negative : forall v : var, literal.

Definition get_var (l : literal) : var :=
  match l with
  | positive v => v
  | negative v => v
  end.

Definition disjunction := list literal.

Definition CNF := list disjunction.

Definition literal_bool_denote truth l :=
  match l with
  | positive v => truth v
  | negative v => negb (truth v)
  end.

Fixpoint disjunction_bool_denote truth d : bool :=
  match d with
  | nil => false
  | d_head :: d_tail => 
      orb
        (literal_bool_denote truth d_head)
        (disjunction_bool_denote truth d_tail)
  end.

Fixpoint CNF_bool_denote truth f : bool :=
  match f with
  | nil => true
  | f_head :: f_tail =>
      andb 
        (disjunction_bool_denote truth f_head)
        (CNF_bool_denote truth f_tail)
  end.

Definition literal_assign (b : bool) (v : var) (l : literal) : literal + bool :=
  match l with
  | positive l' =>
      match eq_nat_dec l' v with
      | left _ => inr b
      | _ => inl l
      end
  | negative l' => 
      match eq_nat_dec l' v with
      | left _ => inr (negb b)
      | _ => inl l
      end
  end.

Fixpoint disjunction_assign
  (b : bool) (v : var) (l : disjunction) : disjunction + bool :=
  match l with
  | nil => inr false
  | l_head :: l_tail =>
      match literal_assign b v l_head, disjunction_assign b v l_tail with
      | inr true, _ => inr true
      | inr false, l => l
      | _, inr true => inr true
      | inl l, inr false => inl (l :: nil)
      | inl l, inl r => inl (l :: r)
      end
  end.

Fixpoint CNF_assign
  (b : bool) (v : var) (l : CNF) : CNF + bool :=
  match l with
  | nil => inr true
  | l_head :: l_tail =>
      match disjunction_assign b v l_head, CNF_assign b v l_tail with
      | inr true, l => l
      | inr false, _ => inr false
      | _, inr false => inr false
      | inl l, inr true => inl (l :: nil)
      | inl l, inl r => inl (l :: r)
      end
  end.

Theorem literal_assign_preserve : forall v truth f, 
  literal_bool_denote truth f = 
    match literal_assign (truth v) v f with
    | inl f' => literal_bool_denote truth f'
    | inr b => b
    end.
  intros.
  destruct f;
  remember (eq_nat_dec v0 v);
  destruct s;
  subst;
  simpl in *;
  try rewrite <- Heqs;
  trivial.
Qed.

Theorem disjunction_assign_preserve : forall v truth f, 
  disjunction_bool_denote truth f = 
    match disjunction_assign (truth v) v f with
    | inl f' => disjunction_bool_denote truth f'
    | inr b => b
    end.
  induction f;
  trivial;
  simpl in *;
  rewrite IHf.
  rewrite (literal_assign_preserve v).
  remember (disjunction_assign (truth v) v f) as s;
  remember (literal_assign (truth v) v a) as s0;
  destruct s, s0;
  trivial;
  destruct b;
  auto with *;
  destruct b0;
  trivial.
Qed.

Theorem CNF_assign_preserve : forall v truth f, 
  CNF_bool_denote truth f = 
    match CNF_assign (truth v) v f with
    | inl f' => CNF_bool_denote truth f'
    | inr b => b
    end.
  induction f;
  trivial.
  simpl in *.
  rewrite IHf.
  rewrite (disjunction_assign_preserve v).
  remember (CNF_assign (truth v) v f) as s;
  remember (disjunction_assign (truth v) v a) as s0;
  destruct s, s0;
  simpl in *;
  trivial.
  destruct b;
  trivial.
  subst;
  remember (CNF_bool_denote truth f) as s;
  destruct s;
  trivial;
  ring.
  destruct b0;
  trivial.
Qed.

Lemma band_true_split : forall a b, a && b = true <-> a = true /\ b = true.
  auto with *.
Defined.

Lemma band_false_split : forall a b, a && b = false <-> a = false \/ b = false.
  destruct a, b;
  tauto.
Defined.

Fixpoint literal_total_length (l : literal) := 1.

Definition disjunction_total_length := @length literal.

Fixpoint CNF_total_length (f : CNF) :=
  match f with
  | nil => 0
  | f_head :: f_tail => disjunction_total_length f_head + CNF_total_length f_tail
  end.

Definition literal_bool_total_length (l : literal + bool) :=
  match l with
  | inl l => literal_total_length l
  | _ => 0
  end.

Definition disjunction_bool_total_length (c : disjunction + bool) :=
  match c with
  | inl f => disjunction_total_length f
  | _ => 0
  end.

Definition CNF_bool_total_length (c : CNF + bool) :=
  match c with
  | inl f => CNF_total_length f
  | _ => 0
  end.

Definition CNF_sat truth f := CNF_bool_denote truth f = true.

Definition CNF_bool_sat t (r : CNF + bool) :=
  match r with
  | inl f => CNF_sat t f
  | inr b => b = true
  end.

Inductive literal_has : literal -> var -> Prop :=
| has_positive : forall v, literal_has (positive v) v
| has_negative : forall v, literal_has (negative v) v.

Inductive disjunction_has : disjunction -> var -> Prop :=
| disjunction_has_fst : 
    forall l v n, literal_has l v -> disjunction_has (l :: n) v
| disjunction_has_cons : 
    forall l v c, 
      disjunction_has l v -> 
        disjunction_has (c :: l) v.

Inductive CNF_has : CNF -> var -> Prop :=
| CNF_has_fst : 
    forall l v n, disjunction_has l v -> CNF_has (l :: n) v
| CNF_has_cons : 
    forall l v c, 
      CNF_has l v -> 
        CNF_has (c :: l) v.

Function CNF_bool_and_rect
  (P : CNF + bool -> Type)
    (t : P (inr true))
      (f : P (inr false))
        (ta : forall v cnf, P (CNF_assign true v cnf))
        (fa : forall v cnf, P (CNF_assign false v cnf))
        (F : False)
          (l : CNF + bool) :
            P l :=
  (fun tr =>
    match tr return P tr with
    | inr true => t
    | inr false => f
    | inl y => False_rect (P (inl y)) F
    end) l.

Theorem literal_assign_lt : forall b l v, 
  literal_has l v -> 
    literal_bool_total_length (literal_assign b v l) < literal_total_length l.
  intros;
  inversion H;
  subst;
  simpl in *;
  case eq_nat_dec;
  auto;
  tauto.
Qed.

Theorem disjunction_assign_le : forall b v l,
  disjunction_bool_total_length (disjunction_assign b v l) <=
    (disjunction_total_length l).
  induction l;
  auto.
  simpl in *;
  remember (literal_assign b v a);
  destruct s;
  try remember (disjunction_assign b v l) as s;
  destruct s;
  simpl in *;
  try omega;
  destruct b0;
  simpl in *;
  auto with *.
Qed.

Theorem literal_has_eq : forall a b, literal_has a b <-> get_var a = b.
  intros.
  split;
  intros.
  inversion H;
  trivial.
  subst.
  destruct a;
  constructor.
Qed.

Theorem iff_not : forall a b : Prop, (a <-> b) -> (~a <-> ~b).
  tauto.
Qed.

Theorem literal_assign_inl : 
  forall v b c d, literal_assign b v c = inl d -> get_var c <> v.
  destruct c;
  simpl in *;
  remember (eq_nat_dec v0 v);
  destruct s;
  trivial;
  discriminate.
Qed.

Theorem disjunction_assign_lt : forall b l v,
  disjunction_has l v ->
    disjunction_bool_total_length (disjunction_assign b v l) < 
    disjunction_total_length l.
  intros.
  induction l.
  inversion H.
  simpl in *.
  remember (literal_assign b v a).
  destruct s.
  remember (disjunction_assign b v l).
  destruct s.
  simpl in *.
  assert ((disjunction_total_length d) < (disjunction_total_length l)).
  apply IHl.
  symmetry in Heqs.
  apply literal_assign_inl in Heqs.
  apply (iff_not (literal_has_eq a v)) in Heqs.
  inversion H.
  subst.
  tauto.
  trivial.
  omega.
  destruct b0.
  auto with *.
  simpl in *.
  assert (0 < disjunction_total_length l).
  symmetry in Heqs.
  apply literal_assign_inl in Heqs.
  apply (iff_not (literal_has_eq a v)) in Heqs.
  inversion H.
  subst.
  tauto.
  subst.
  tauto.
  omega.
  destruct b0.
  auto with *.
  assert
    (disjunction_bool_total_length (disjunction_assign b v l) <=
      (disjunction_total_length l)).
  apply disjunction_assign_le.
  omega.
Qed.

Theorem CNF_assign_le : forall b l v,
  CNF_bool_total_length (CNF_assign b v l) <= CNF_total_length l.
  intros.
  induction l;
  trivial.
  simpl in *.
  remember(disjunction_assign b v a) as s;
  destruct s.
  assert(disjunction_bool_total_length (inl d) <= disjunction_total_length a).
  rewrite Heqs.
  apply disjunction_assign_le.
  remember(CNF_assign b v l) as s;
  destruct s;
  simpl in *.
  omega.
  destruct b0;
  simpl in *;
  omega.
  destruct b0;
  auto with *.
Qed.

Theorem CNF_assign_lt : forall b l v,
  CNF_has l v ->
    CNF_bool_total_length (CNF_assign b v l) < 
    CNF_total_length l.
  intros.
  induction l.
  inversion H.
  simpl in *.
  remember (disjunction_assign b v a).
  destruct s.
  remember (CNF_assign b v l).
  destruct s.
  simpl in *.
  inversion H.
  subst.
  assert(disjunction_total_length d < disjunction_total_length a).
  admit.
  assert(CNF_total_length c <= CNF_total_length l).
  admit.
  omega.
  subst.
  assert (disjunction_total_length d <= disjunction_total_length a).
  admit.
  assert(CNF_total_length c < CNF_total_length l).
  admit.
  omega.
  inversion H.
  subst.
  assert(disjunction_total_length d < disjunction_total_length a).
  admit.
  destruct b0;
  simpl in *;
  omega.
  subst.
  assert(0 < CNF_total_length l).
  admit.
  destruct b0;
  simpl in *.
  assert(disjunction_total_length d <= disjunction_total_length a).
  admit.
  omega.
  omega.
  assert(0 < disjunction_total_length a).
  admit.
  destruct b0.
  assert(CNF_bool_total_length (CNF_assign b v l) <= CNF_total_length l).
  admit.
  omega.
  simpl in *.
  omega.
Qed.

Definition CNF_bool_DPLL (f : CNF + bool) : 
  { t | CNF_bool_sat t f } +  { forall t, CNF_bool_sat t f }.
Admitted.

Definition DPLL (f : CNF) := CNF_bool_DPLL (inl f).
