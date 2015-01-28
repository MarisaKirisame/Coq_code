Require Import List Program Permutation.

Set Implicit Arguments.

Inductive permutation_type {A : Type} : list A -> list A -> Type :=
| perm_type_nil : permutation_type [] []
| perm_type_skip : forall (x : A) (l l' : list A),
    permutation_type l l' -> permutation_type (x :: l) (x :: l')
| perm_type_swap : forall (x y : A) (l : list A),
    permutation_type (y :: x :: l) (x :: y :: l)
| perm_type_trans : forall l l' l'' : list A,
    permutation_type l l' -> permutation_type l' l'' -> permutation_type l l''.

Definition permutation_reflexive : forall T (l : list T), permutation_type l l.
  induction l.
  constructor.
  constructor.
  trivial.
Defined.