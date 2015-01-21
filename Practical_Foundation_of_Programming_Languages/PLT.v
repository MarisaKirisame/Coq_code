Set Implicit Arguments.

Require Import List Program.

Definition set T := T -> Prop.

Definition contain { T } (S : set T) R := S R.

Inductive vector T : nat -> Type :=
| VNil : vector T 0
| VCons : forall n, T -> vector T n -> vector T (S n).

Inductive ihlist { F : Type -> Type } : list Type -> Type :=
| ihnil : ihlist nil
| ihcons : forall T L, F T -> ihlist L -> ihlist (T :: L).

Implicit Arguments ihlist[].

Definition operator := list Type.

Inductive AXs
  { S : set Type }
    { Os : forall s, contain S s -> list operator }
    { Xs : forall s, contain S s -> list s } : Type -> Type :=
| XAXs : forall s (c : contain S s)(s' : s), In s' (Xs s c) -> AXs s
| OAXs : forall s (c : contain S s), forall op : operator, In op (Os s c) -> 
    ihlist (fun s' => AXs s') op -> AXs s.

Implicit Arguments AXs[].
Fixpoint Induction S Os Xs (P : forall T, AXs S Os Xs T -> Type)
  (FX : forall s (c : contain S s)(s' : s)(i : In s' (Xs s c)), P s (XAXs c s' i))
  T (AX : AXs S Os Xs T) : P T AX.
  destruct AX.
  apply FX.
  induction v.
  constructor.
  constructor.
  apply Induction.
  trivial.
  trivial.
Defined.
