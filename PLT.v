Set Implicit Arguments.

Inductive vector T : nat -> Type :=
| VNil : vector T 0
| VCons : forall n, T -> vector T n -> vector T (S n).

Inductive AX { S : Type -> Prop } { Ar : forall s, S s -> nat } :=
| O : forall s (p : S s), vector AX (Ar s p) -> AX.

Inductive AllSatisfy { T : Type } { P : T -> Type } : forall n, vector T n -> Type :=
| SatNil : AllSatisfy (VNil T)
| SatCons : forall n (v : vector T n) e, P e -> AllSatisfy v -> AllSatisfy (VCons e v).

Fixpoint Induction (S : Type -> Prop) Ar (P : @AX S Ar -> Type)
  (F : forall s p (v : vector _ (Ar s p)),
    @AllSatisfy AX P _ v ->
      P (@O _ Ar s p v))
        (X : @AX S Ar) : P X.
  destruct X.
  apply F.
  induction v.
  constructor.
  constructor.
  apply Induction.
  trivial.
  trivial.
Defined.
