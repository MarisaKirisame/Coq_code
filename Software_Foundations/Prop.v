Require Import Omega Arith List Recdef Program.

Set Implicit Arguments.

Fixpoint evenb n :=
  match n with
  | O => true
  | S O => false
  | S (S n) => evenb n
  end.

Definition even (n:nat) : Prop :=
  evenb n = true.

Inductive ev : nat -> Prop :=
| ev_0 : ev O
| ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem double_even : forall n,
  ev (n + n).
  induction n.
  constructor.
  simpl.
  rewrite plus_comm.
  simpl.
  constructor.
  trivial.
Qed.

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
   induction 1.
   trivial.
   intros.
   intuition.
   constructor.
   trivial.
Qed.

Inductive beautiful : nat -> Prop :=
| b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Hint Constructors beautiful ev.

Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
  intros.
  simpl.
  replace(n + (n + 0)) with (n + n).
  apply (@b_sum n);
  trivial.
  auto.
Qed. 

Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
  induction m.
  simpl in *.
  constructor.
  intros.
  simpl in *.
  intuition.
Qed.

Inductive gorgeous : nat -> Prop :=
| g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (S (S (S n)))
| g_plus5 : forall n, gorgeous n -> gorgeous (S (S (S (S (S n))))).

Hint Constructors gorgeous.

Theorem gorgeous_plus13: forall n,
  gorgeous n -> gorgeous (13+n).
  intros.
  simpl in *.
  auto.
Qed.

Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
  induction 1.
  trivial.
  intros.
  simpl in *.
  auto.
  intros.
  simpl in *.
  auto.
Qed.

Hint Resolve gorgeous_sum.

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
  induction 1;
  trivial;
  auto.
Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
  induction 1;
  trivial;
  simpl in *;
  auto.
Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
  inversion 1.
  inversion H1.
  trivial.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
  inversion 1.
  inversion H1.
  inversion H3.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  intros.
  induction H0.
  trivial.
  simpl in *.
  inversion H.
  tauto.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
  intros.
  assert(ev (n + n + (m + p))).
  admit.
  apply (@ ev_ev__ev (n + n)) in H1.
  trivial.
  apply double_even.
Qed.

Inductive pal { t } : list t -> Prop :=
| pal_nil : pal nil
| pal_one : forall y, pal (y :: nil)
| pal_con : forall y l, pal l -> pal (y :: l ++ (y :: nil)).

Theorem last_last : forall T l (t : T) n, (last (l ++ (t :: nil)) n = t).
  intros.
  induction l.
  trivial.
  simpl in *.
  rewrite <- IHl at 2.
  destruct (l ++ t :: nil) eqn: H.
  simpl in *.
  destruct l;
  discriminate.
  trivial.
Qed.

Definition extract_last { T } (l : list T) : { n | l = fst n ++ snd n :: nil } + (l = nil).
  induction l.
  tauto.
  left.
  destruct IHl.
  destruct s.
  subst.
  destruct x.
  simpl in *.
  exists (a :: l, t).
  trivial.
  subst.
  exists (@nil T, a).
  trivial.
Defined.

Fixpoint double_list_rect_inner (A : Type) (P : list A -> Type) (f : P nil)
  (f0 : forall a : A, P (a :: nil))
    (f1 : forall (a b : A) (l : list A), P l -> P (a :: l ++ b :: nil))
      (l : list A)
        (list_length : nat)(E : length l = list_length) 
          { struct list_length } : P l.
  destruct l.
  trivial.
  destruct list_length.
  discriminate.
  trivial.
  simpl in *.
  inversion E.
  destruct (extract_last l).
  destruct s.
  destruct x.
  simpl in *.
  subst l.
  apply f1.
  destruct l0.
  trivial.
  destruct list_length.
  discriminate.
  apply double_list_rect_inner with (list_length := list_length).
  trivial.
  trivial.
  trivial.
  assert(length (l0 ++ [a0]) = S (length l0)).
  clear E.
  clear H0.
  induction l0;
  simpl in *;
  auto.
  simpl in *.
  omega.
  subst.
  trivial.
Defined.

Definition double_list_rect (A : Type) (P : list A -> Type) (f : P nil)
  (f0 : forall a : A, P (a :: nil))
    (f1 : forall (a b : A) (l : list A), P l -> P (a :: l ++ b :: nil))
      (l : list A) : P l.
  eapply double_list_rect_inner;
  trivial.
Defined.

Goal forall t l, @rev t l = l -> pal l.
  intros t l.
  refine(double_list_rect (fun l0 => rev l0 = l0 -> pal l0) _ _ _ l);
  intros;
  try (constructor;fail).
  simpl in *.
  rewrite rev_unit in *.
  simpl in *.
  inversion H0.
  subst.
  constructor.
  apply app_inv_tail in H3.
  rewrite H3.
  auto.
Qed.

Goal forall t l, pal l -> @rev t l = l.
  induction 1.
  trivial.
  trivial.
  simpl in *.
  rewrite rev_unit.
  simpl in *.
  f_equal.
  f_equal.
  trivial.
Qed.

Inductive sub { T } : list T -> list T -> Prop :=
| sub_nil : sub [] []
| sub_skip : forall l r e, sub l r -> sub l (e :: r)
| sub_con : forall l r e, sub l r -> sub (e :: l) (e :: r).

Goal forall T l, @sub T l l.
  induction l.
  constructor.
  apply sub_con.
  trivial.
Qed.

Goal forall T l1 l2 l3, @sub T l1 l2 -> sub l1 (l2 ++ l3).
  induction 1.
  simpl in *.
  induction l3.
  constructor.
  constructor.
  trivial.
  simpl in *.
  constructor.
  trivial.
  apply sub_con.
  trivial.
Qed.

Goal forall T l1 l2 l3, @sub T l1 l2 -> sub l2 l3 -> sub l1 l3.
  
(Optional, harder) Prove that subsequence is transitive — that is, 
if l1 is a subsequence of l2 and l2 is a subsequence of l3, then l1 is a subsequence of l3.
Hint: choose your induction carefully!


Exercise: 2 stars, optional (R_provability)
Suppose we give Coq the following definition:
    Inductive R : nat → list nat → Prop :=
      | c1 : R 0 []
      | c2 : ∀n l, R n l → R (S n) (n :: l)
      | c3 : ∀n l, R (S n) l → R n l.
Which of the following propositions are provable?

    R 2 [1,0]
    R 1 [1,2,1,0]
    R 6 [3,2,1,0]

☐

Relations
A proposition parameterized by a number (such as ev or beautiful) can be thought of as
 a property — i.e., it defines a subset of nat, namely those numbers for which the proposition
 is provable. In the same way, a two-argument proposition can be thought of as a relation
 — i.e., it defines a set of pairs for which the proposition is provable.


One useful example is the "less than or equal to" relation on numbers.
The following definition should be fairly intuitive. It says that there are two ways
 to give evidence that one number is less than or equal to another: either observe that
 they are the same number, or give evidence that the first is less than or equal to
 the predecessor of the second.

Inductive le : nat → nat → Prop :=
  | le_n : ∀n, le n n
  | le_S : ∀n m, (le n m) → (le n (S m)).

Notation "m ≤ n" := (le m n).

Proofs of facts about ≤ using the constructors le_n and le_S follow the same patterns as 
proofs about properties, like ev in chapter Prop. We can apply the constructors 
to prove ≤ goals (e.g., to show that 3≤3 or 3≤6), and we can use tactics like inversion 
to extract information from ≤ hypotheses in the context (e.g., to prove that (2 ≤ 1) → 2+2=5.)
Here are some sanity checks on the definition.
(Notice that, although these are the same kind of simple "unit tests"
as we gave for the testing functions we wrote in the first few lectures, 
we must construct their proofs explicitly — simpl and reflexivity don't do the job,
because the proofs aren't just a matter of simplifying computations.)

Theorem test_le1 :
  3 ≤ 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n. Qed.

Theorem test_le2 :
  3 ≤ 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  (2 ≤ 1) → 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2. Qed.

The "strictly less than" relation n < m can now be defined in terms of le.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Here are a few more simple relations on numbers:

Inductive square_of : nat → nat → Prop :=
  sq : ∀n:nat, square_of n (n × n).

Inductive next_nat (n:nat) : nat → Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat → Prop :=
  | ne_1 : ev (S n) → next_even n (S n)
  | ne_2 : ev (S (S n)) → next_even n (S (S n)).

Exercise: 2 stars (total_relation)
Define an inductive binary relation total_relation that holds between 
every pair of natural numbers.

(* FILL IN HERE *)
☐
Exercise: 2 stars (empty_relation)
Define an inductive binary relation empty_relation (on numbers) that never holds.

(* FILL IN HERE *)
☐
Exercise: 2 stars, optional (le_exercises)
Here are a number of facts about the ≤ and < relations 
that we are going to need later in the course. The proofs make good practice exercises.

Lemma le_trans : ∀m n o, m ≤ n → n ≤ o → m ≤ o.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem O_le_n : ∀n,
  0 ≤ n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_le_m__Sn_le_Sm : ∀n m,
  n ≤ m → S n ≤ S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem Sn_le_Sm__n_le_m : ∀n m,
  S n ≤ S m → n ≤ m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem le_plus_l : ∀a b,
  a ≤ a + b.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_lt : ∀n1 n2 m,
  n1 + n2 < m →
  n1 < m ∧ n2 < m.
Proof.
 unfold lt.
 (* FILL IN HERE *) Admitted.

Theorem lt_S : ∀n m,
  n < m →
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true : ∀n m,
  ble_nat n m = true → n ≤ m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem le_ble_nat : ∀n m,
  n ≤ m →
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on m. *)
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true_trans : ∀n m o,
  ble_nat n m = true → ble_nat m o = true → ble_nat n o = true.
Proof.
  (* Hint: This theorem can be easily proved without using induction. *)
  (* FILL IN HERE *) Admitted.

Exercise: 2 stars, optional (ble_nat_false)
Theorem ble_nat_false : ∀n m,
  ble_nat n m = false → ~(n ≤ m).
Proof.
  (* FILL IN HERE *) Admitted.
☐
Exercise: 3 stars (R_provability2)
Module R.
We can define three-place relations, four-place relations, etc.,
 in just the same way as binary relations.
 For example, consider the following three-place relation on numbers:

Inductive R : nat → nat → nat → Prop :=
   | c1 : R 0 0 0
   | c2 : ∀m n o, R m n o → R (S m) n (S o)
   | c3 : ∀m n o, R m n o → R m (S n) (S o)
   | c4 : ∀m n o, R (S m) (S n) (S (S o)) → R m n o
   | c5 : ∀m n o, R m n o → R n m o.

    Which of the following propositions are provable?
        R 1 1 2
        R 2 2 6
    If we dropped constructor c5 from the definition of R, would the set of provable
 propositions change? Briefly (1 sentence) explain your answer.
    If we dropped constructor c4 from the definition of R, would the set of provable
 propositions change? Briefly (1 sentence) explain your answer.

(* FILL IN HERE *)
☐
Exercise: 3 stars, optional (R_fact)
Relation R actually encodes a familiar function. State and prove two theorems that formally
 connects the relation and the function. That is, if R m n o is true, 
what can we say about m, n, and o, and vice versa?

(* FILL IN HERE *)
☐

End R.

Programming with Propositions Revisited
As we have seen, a proposition is a statement expressing a factual claim, like
 "two plus two equals four." In Coq, propositions are written as expressions of type Prop. .

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

Both provable and unprovable claims are perfectly good propositions. 
Simply being a proposition is one thing; being provable is something else!

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

Both 2 + 2 = 4 and 2 + 2 = 5 are legal expressions of type Prop.
We've mainly seen one place that propositions can appear in Coq: in Theorem
(and Lemma and Example) declarations.

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.

But they can be used in many other ways. For example, we have also seen that we can 
give a name to a proposition using a Definition, 
just as we have given names to expressions of other sorts.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

We can later use this name in any situation where a proposition is expected — 
for example, as the claim in a Theorem declaration.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

We've seen several ways of constructing propositions.

    We can define a new proposition primitively using Inductive.
    Given two expressions e1 and e2 of the same type, we can form the proposition e1 = e2, 
which states that their values are equal.
    We can combine propositions using implication and quantification.

We have also seen parameterized propositions, such as even and beautiful.

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even.
(* ===> even : nat -> Prop *)

The type of even, i.e., nat→Prop, can be pronounced in three equivalent ways: (1)
 "even is a function from numbers to propositions," (2) "even is a family of propositions,
 indexed by a number n," or (3) "even is a property of numbers."
Propositions — including parameterized propositions — are first-class citizens in Coq.
 For example, we can define functions from numbers to propositions...

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

... and then partially apply them:

Definition teen : nat→Prop := between 13 19.

We can even pass propositions — including parameterized propositions — 
as arguments to functions:

Definition true_for_zero (P:nat→Prop) : Prop :=
  P 0.

Here are two more examples of passing parameterized propositions as arguments to a function.
The first function, true_for_all_numbers, takes a proposition P as argument and
 builds the proposition that P is true for all natural numbers.

Definition true_for_all_numbers (P:nat→Prop) : Prop :=
  ∀n, P n.

The second, preserved_by_S, takes P and builds the proposition that, 
if P is true for some natural number n', then it is also true by the successor of n' —
 i.e. that P is preserved by successor:

Definition preserved_by_S (P:nat→Prop) : Prop :=
  ∀n', P n' → P (S n').

Finally, we can put these ingredients together to define a proposition stating that
 induction is valid for natural numbers:

Definition natural_number_induction_valid : Prop :=
  ∀(P:nat→Prop),
    true_for_zero P →
    preserved_by_S P →
    true_for_all_numbers P.

Exercise: 3 stars (combine_odd_even)
Complete the definition of the combine_odd_even function below. It takes as arguments
 two properties of numbers Podd and Peven. As its result, it should return a new property P
 such that P n is equivalent to Podd n when n is odd, and equivalent to Peven n otherwise.

Definition combine_odd_even (Podd Peven : nat → Prop) : nat → Prop :=
  (* FILL IN HERE *) admit.

To test your definition, see whether you can prove the following facts:

Theorem combine_odd_even_intro :
  ∀(Podd Peven : nat → Prop) (n : nat),
    (oddb n = true → Podd n) →
    (oddb n = false → Peven n) →
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  ∀(Podd Peven : nat → Prop) (n : nat),
    combine_odd_even Podd Peven n →
    oddb n = true →
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  ∀(Podd Peven : nat → Prop) (n : nat),
    combine_odd_even Podd Peven n →
    oddb n = false →
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

☐

One more quick digression, for adventurous souls: if we can define
 parameterized propositions using Definition, then can we also define them using Fixpoint?
Of course we can! However, this kind of "recursive parameterization" 
doesn't correspond to anything very familiar from everyday mathematics. 
The following exercise gives a slightly contrived example.
Exercise: 4 stars, optional (true_upto_n__true_everywhere)
Define a recursive function true_upto_n__true_everywhere that makes true_upto_n_example work.

(* 
Fixpoint true_upto_n__true_everywhere
(* FILL IN HERE *)

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.
*)
☐

(* $Date: 2014-06-05 07:22:21 -0400 (Thu, 05 Jun 2014) $ *)