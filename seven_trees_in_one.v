Require Import Program CoqUtil.Tactic.
Set Implicit Arguments.

Inductive Tree :=
| Empty
| Node : Tree -> Tree -> Tree.

Notation "[ a , b ]" := (Node a b).
Notation "0" := Empty.

Program Definition TreeDestructISO : Tree == (() + Tree ^ 2) :=
  {|f x :=
      match x with
        | 0 => inl tt
        | [a, b] => inr (a, (b, ()))
      end;
    g x :=
      match x with
        | inl _ => 0
        | inr (a, (b, _)) => [a, b]
      end|}.

Solve All Obligations with (
  program_simpl;
  repeat (
      match_destruct ||
                     match goal with
                         H : () |- _ => destruct H
                     end);
  trivial).

Program Definition P1ISO A : A == (A ^ 1) :=
  {|f x := (x, ());
    g x := fst x|}.
Next Obligation.
  destruct u; trivial.
Qed.

Program Definition P0ISO A : () == (A ^ 0) := ISO_refl _.


Print eq_rect.

Program Definition SLISO A C D : A == D -> (A + C) == (D + C) :=
  (*In memory of the great warrior*)
  _.