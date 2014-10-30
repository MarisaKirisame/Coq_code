Unset Implicit Arguments.
Definition compose (A:Set) (g f:A -> A) (x:A) := g (f x).
Definition thrice (A:Set) (f:A -> A) := compose A f (compose A f f).
Eval compute in (thrice _ (thrice _) S 0).
Eval compute in (thrice (nat->nat) (thrice nat) S 0).
Lemma all_perm :
  forall (A:Type) (P:A -> A -> Prop),
    (forall x y:A, P x y) -> 
      forall x y:A, P y x.
  intros.
  apply H.
Qed.

Lemma all_perm' :
  forall (A:Type) (P:A -> A -> Prop),
    (forall x y:A, P x y) -> 
      forall x y:A, P y x.
  auto.
Qed.

Lemma resolution :
  forall (A:Type) (P Q R S:A -> Prop),
    (forall a:A, Q a -> R a -> S a) ->
      (forall b:A, P b -> Q b) -> 
        forall c:A, P c -> R c -> S c.
  intros.
  apply H;[apply H0|];assumption.
Qed.

Lemma resolution' :
  forall (A:Type) (P Q R S:A -> Prop),
    (forall a:A, Q a -> R a -> S a) ->
      (forall b:A, P b -> Q b) -> 
        forall c:A, P c -> R c -> S c.
  auto.
Qed.

Definition id : forall A:Set, A->A.
  auto.
Defined.

Definition diag : forall A B:Set, (A->A->B)->A->B.
  auto.
Defined.

Definition permute : forall A B C :Set,(A->B->C)->B->A->C.
  auto.
Qed.

Require Import ZArith.

Definition f_nat_Z : forall A:Set, (nat->A)->Z->A.
  intros.
  apply H.
  constructor.
Qed.