Require Export Omega Wf.
Set Implicit Arguments.
Inductive transitive_closure T (R : T -> T -> Prop) : T -> T -> Prop :=
| tco l r : R l r -> transitive_closure R l r
| tcs l m r : R l m -> transitive_closure R m r -> transitive_closure R l r.
Hint Constructors transitive_closure.

Definition wftc T (R : T -> T -> Prop) : well_founded R -> well_founded (transitive_closure R).
  unfold well_founded; intros.
  specialize (H a).
  induction H; constructor; intros.
  induction H1; auto.
  eapply IHtransitive_closure; auto.
Qed.

Definition StrongFix (A : Type) (R : A -> A -> Prop) : 
  well_founded R -> 
    forall P : A -> Type,
      (forall x : A, (forall y : A, transitive_closure R y x -> P y) -> P x) -> 
        forall x : A, P x := fun H => Fix (wftc H).

