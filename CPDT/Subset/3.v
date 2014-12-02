Require Import Bool List.

Definition var := nat.

Inductive literal :=
| positive : forall v : var, literal
| negative : forall v : var, literal.

Definition disjunction := list literal.

Definition CNF := list disjunction.

Definition literal_bool_denote truth l : bool :=
  match l with
  | positive v => truth v
  | negative v => negb (truth v)
  end.

Fixpoint disjunction_bool_denote truth d : bool :=
  match d with
  | nil => true
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

Lemma band_true_split : forall a b, a && b = true -> a = true /\ b = true.
  auto with *.
Defined.

Lemma band_false_split : forall a b, a && b = false -> a = false \/ b = false.
  destruct a, b;
  tauto.
Defined.

Definition DPLL : 
  forall f : CNF , 
    { truth | CNF_bool_denote truth f = true } + 
      { forall truth, CNF_bool_denote truth f = false }.
  intros.
  induction f.
  apply inleft;
  exists (fun _ => true);
  trivial.
  inversion_clear IHf.
  inversion_clear H.
  admit.
  admit.
Defined.