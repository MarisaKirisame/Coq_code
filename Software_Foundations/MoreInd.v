Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
  apply nat_ind.
  trivial.
  intros.
  simpl in *.
  auto.
Qed.

Inductive ExSet : Type := 
| con1 : bool -> ExSet
| con2 : nat -> ExSet -> ExSet.

mytype_ind :
∀(X : Type) (P : mytype X → Prop),
(∀x : X, P (constr1 X x)) →
(∀n : nat, P (constr2 X n)) →
(∀m : mytype X, P m →
∀n : nat, P (constr3 X m n)) →
∀m : mytype X, P m
