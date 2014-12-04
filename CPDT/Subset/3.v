Require Import Bool List Arith.

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

Fixpoint CNF_total_length (f : CNF) :=
  match f with
  | nil => 0
  | f_head :: f_tail => length f_head + CNF_total_length f_tail
  end.

Definition sat truth f := CNF_bool_denote truth f = true.

Definition sat_raw t (r : CNF + bool) :=
  match r with
  | inl f => sat t f
  | inr b => b = true
  end.

Inductive literal_has : literal -> var -> Prop :=
| has_positive : forall v, literal_has (positive v) v
| has_negative : forall v, literal_has (negative v) v.

Inductive disjunction_has : disjunction -> var -> Prop :=
| disjunction_has_refl : 
    forall l v, literal_has l v -> disjunction_has (l :: nil) v
| disjunction_has_cons : 
    forall l v c, 
      disjunction_has l v -> 
        disjunction_has (c :: l) v.

Inductive CNF_has

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

Definition DPLL_raw (f : CNF + bool) : 
  { t | sat_raw t f } +  { forall t, ~sat_raw t f }.
  unfold sat_raw.
  unfold sat.
  destruct f.
  destruct c.
  clear DPLL_raw;
  simpl in *;
  left;
  exists (fun _ => true);
  trivial.
  destruct d.
  clear DPLL_raw;
  auto with *.
  remember (get_var l) as v.
  remember (DPLL_raw (CNF_assign true v c)) as r1.
  remember (DPLL_raw (CNF_assign false v c)) as r2.
  destruct r1, r2.
  destruct s.
  destruct s0.
  simpl in *.
  
Defined.
Admitted.

Definition DPLL (f : CNF) := DPLL_raw (inl f).
