Require Import Bool List Arith Omega Recdef.

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

Definition literal_denote truth l :=
  match l with
  | positive v => truth v
  | negative v => negb (truth v)
  end.

Fixpoint disjunction_denote truth d : bool :=
  match d with
  | nil => false
  | d_head :: d_tail => 
      orb
        (literal_denote truth d_head)
        (disjunction_denote truth d_tail)
  end.

Fixpoint cnf_denote truth f : bool :=
  match f with
  | nil => true
  | f_head :: f_tail =>
      andb 
        (disjunction_denote truth f_head)
        (cnf_denote truth f_tail)
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
  literal_denote truth f = 
    match literal_assign (truth v) v f with
    | inl f' => literal_denote truth f'
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
  disjunction_denote truth f = 
    match disjunction_assign (truth v) v f with
    | inl f' => disjunction_denote truth f'
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
  cnf_denote truth f = 
    match CNF_assign (truth v) v f with
    | inl f' => cnf_denote truth f'
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
  remember (cnf_denote truth f) as s;
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

Definition CNF_sat truth f := cnf_denote truth f = true.

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

Theorem literal_assign_inr : 
  forall v b c d, literal_assign b v c = inr d -> get_var c = v.
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
  assert(disjunction_bool_total_length (inl d) < disjunction_total_length a).
  rewrite Heqs.
  apply disjunction_assign_lt.
  trivial.
  assert(CNF_bool_total_length (inl c) <= CNF_total_length l).
  rewrite Heqs0.
  apply CNF_assign_le.
  simpl in *.
  omega.
  subst.
  assert (disjunction_bool_total_length (inl d) <= disjunction_total_length a).
  rewrite Heqs.
  apply disjunction_assign_le.
  assert(CNF_total_length c < CNF_total_length l).
  tauto.
  simpl in *.
  omega.
  inversion H.
  subst.
  assert(disjunction_bool_total_length (inl d) < disjunction_total_length a).
  rewrite Heqs.
  apply disjunction_assign_lt.
  trivial.
  destruct b0;
  simpl in *;
  omega.
  subst.
  assert(CNF_bool_total_length (inr b0) < CNF_total_length l).
  tauto.
  destruct b0;
  simpl in *.
  assert(disjunction_bool_total_length (inl d) <= disjunction_total_length a).
  rewrite Heqs.
  apply disjunction_assign_le.
  simpl in *.
  omega.
  omega.
  destruct a.
  simpl in *.
  inversion Heqs.
  subst.
  simpl in *.
  inversion H;
  subst.
  inversion H3.
  assert (CNF_bool_total_length (CNF_assign b v l) < CNF_total_length l).
  tauto.
  omega.
  destruct b0;
  simpl in *.
  assert(CNF_bool_total_length (CNF_assign b v l) <= CNF_total_length l).
  apply CNF_assign_le.
  omega.
  omega.
Qed.

Definition first_var (c : CNF) : 
  { v : var | CNF_has c v } + { CNF_total_length c = 0 }.
  induction c.
  tauto.
  destruct IHc.
  destruct s.
  left.
  exists x.
  apply CNF_has_cons.
  trivial.
  destruct a.
  right.
  trivial.
  left.
  exists (get_var l).
  constructor.
  constructor.
  destruct l;
  simpl in *;
  constructor.
Defined.

Function CNF_bool_and_rect
  (P : CNF + bool -> Type)
    (t : P (inr true))
      (f : P (inr false))
        (a0 : forall cnf, CNF_total_length cnf = 0 -> P (inl cnf))
          (PC : forall v cnf, 
            CNF_has cnf v -> 
              P (CNF_assign true v cnf) -> 
                P (CNF_assign false v cnf) -> P
                  (inl cnf))
                    (l : CNF + bool) { measure CNF_bool_total_length l } :
            P l :=
  (fun tr =>
    match tr return P tr with
    | inr true => t
    | inr false => f
    | inl y => 
      match first_var y with
      | inleft (exist l p) => 
          PC
            l
              y
                p
                  (CNF_bool_and_rect P t f a0 PC (CNF_assign true l y))
                    (CNF_bool_and_rect P t f a0 PC (CNF_assign false l y))
      | inright p => a0 y p
      end
    end) l.
  intros.
  subst.
  simpl in *.
  apply CNF_assign_lt.
  trivial.
  intros.
  subst.
  simpl in *.
  apply CNF_assign_lt.
  trivial.
Defined.

Definition CNF_bool_and_rec (a : CNF + bool -> Set) b c d e f : a f
  := CNF_bool_and_rect a b c d e f.

Definition reverse_assign b x v cnf : 
  CNF_bool_sat x (CNF_assign b v cnf) ->
    {t : var -> bool | cnf_denote t cnf = true}.
  intros.
  exists (fun v0 => 
    match eq_nat_dec v0 v with
    | left _ => b
    | right _ => x v0
    end).
  induction cnf.
  trivial.
  simpl in *.
  assert(
    disjunction_denote
      (fun v0 : nat => if eq_nat_dec v0 v then b else x v0)
      a =
    true).
  induction a.
  trivial.
  simpl in *.
  unfold CNF_sat in *;
  destruct a;
  simpl in *;
  remember(eq_nat_dec v0 v) as s;
  destruct s;
  subst;
  simpl in *;
  remember (disjunction_assign b v a0) as s;
  destruct s;
  remember (CNF_assign b v cnf) as s;
  destruct s;
  simpl in *;
  destruct b;
  trivial;
  simpl in *;
  unfold CNF_sat in *;
  simpl in *;
  try tauto;
  remember (x v0) as xv;
  destruct xv;
  trivial;
  simpl in *;
  try tauto;
  destruct b0;
  unfold CNF_bool_sat in *;
  simpl in *;
  try inversion H;
  try rewrite H;
  subst;
  simpl in *;
  try rewrite <- Heqxv in *;  
  simpl in *;
  try remember (disjunction_denote x d) as s;
  try destruct s;
  try discriminate;
  simpl in *;
  try remember (cnf_denote x c) as s;
  try destruct s;
  try discriminate;
  apply IHa;
  trivial;
  simpl in *;
  unfold CNF_sat in *;
  simpl in *;
  auto with *;
  destruct b1;
  simpl in *;
  try rewrite <- Heqxv in *;
  trivial.
  rewrite H0.
  simpl in *;
  remember(disjunction_assign b v a).
  destruct s.
  remember(CNF_assign b v cnf).
  destruct s.
  simpl in *.
  inversion H.
  rewrite H2.
  apply IHcnf.
  unfold CNF_sat.
  destruct (disjunction_denote x d).
  trivial.
  discriminate.
  simpl in *.
  destruct b0.
  tauto.
  discriminate.
  destruct b0.
  tauto.
  discriminate.
Defined.

Definition CNF_bool_DPLL (f : CNF + bool) : 
  { t | CNF_bool_sat t f } +  { forall t, ~CNF_bool_sat t f }.
  refine(
    CNF_bool_and_rec
      (fun x =>
        {t : var -> bool | CNF_bool_sat t x} +
          {(forall t : var -> bool, ~CNF_bool_sat t x)})
      _
      _
      _
      _
      f);
  simpl in *;
  intros.
  left.
  split.
  intros.
  constructor.
  trivial.
  auto with *.
  induction cnf.
  simpl in *.
  left.
  exists (fun _ => true).
  constructor.
  destruct a.
  auto with *.
  discriminate.
  unfold CNF_sat.
  destruct H0.
  destruct s.
  left.
  eapply reverse_assign.
  eauto.
  destruct H1.
  destruct s.
  left.
  eapply reverse_assign.
  eauto.
  right.
  intros.
  unfold CNF_bool_sat in *.
  unfold CNF_sat in *.
  rewrite (CNF_assign_preserve v).
  destruct (t v);
  remember(n t);
  remember(n0 t);
  remember(CNF_assign true v cnf) as s;
  remember(CNF_assign false v cnf) as s0;
  destruct s, s0;
  trivial.
Defined.

Definition DPLL (f : CNF) := CNF_bool_DPLL (inl f).