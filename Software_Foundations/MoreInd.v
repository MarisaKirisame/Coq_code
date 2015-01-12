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

Inductive mytype (T : Type) :=
| constr1 : T -> mytype T
| constr2 : nat -> mytype T
| constr3 : mytype T -> nat -> mytype T.

Inductive foo (X Y : Type) :=
| bar : X -> foo X Y
| baz : Y -> foo X Y
| quux : (nat -> foo X Y) -> foo X Y.

Inductive bar' : Set :=
| bar1 : nat -> bar'
| bar2 : bar' -> bar'
| bar3 : bool -> bar' -> bar'.