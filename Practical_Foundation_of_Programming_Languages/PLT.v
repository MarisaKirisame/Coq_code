Set Implicit Arguments.

Require Import List Program.

Definition set T := T -> Prop.

Definition contain { T } (S : set T) R := S R.

Inductive vector T : nat -> Type :=
| VNil : vector T 0
| VCons : forall n, T -> vector T n -> vector T (S n).

Inductive ihlist { F : Type -> Type } : list Type -> Type :=
| ihnil : ihlist nil
| ihcons : forall T L (f : F T), ihlist L -> ihlist (T :: L).

Implicit Arguments ihlist[].

Definition operator := list Type.

Inductive AXs
  { S : set Type }
    { Os : forall s, contain S s -> list operator }
    { Xs : forall s, contain S s -> list s } : Type -> Type :=
| XAXs : forall s (c : contain S s)(s' : s), In s' (Xs s c) -> AXs s
| OAXs : forall s (c : contain S s)(op : operator), In op (Os s c) -> 
    ihlist (fun s' => AXs s') op -> AXs s.

Implicit Arguments AXs[].
Implicit Arguments OAXs[s c op S Os Xs].
Implicit Arguments XAXs[s c s' S Os Xs].
Implicit Arguments ihcons[T L F].

Inductive ihlist_forall (F : Type -> Type) { P : forall T, F T -> Type } : 
  forall L, ihlist F L -> Prop :=
| Forall_ihnil : ihlist_forall ihnil
| Forall_ihcons : forall (l : list Type)(L : ihlist F l)(T : Type)(t : F T), 
    P T t -> ihlist_forall L -> ihlist_forall (ihcons t L).

Implicit Arguments ihlist_forall[F].

Fixpoint Induction S Os Xs (P : forall T, AXs S Os Xs T -> Type)
  (FX : forall s (c : contain S s)(s' : s)(i : In s' (Xs s c)), P s (XAXs i))
  (FO : forall s (c : contain S s)(op : operator)(i : In op (Os s c))
    (l : ihlist (fun s' => AXs S Os Xs s') op), 
      ihlist_forall (fun t ax => P t ax) op l -> P s (OAXs i l))
  T (AX : AXs S Os Xs T) : P T AX.
  destruct AX;
  trivial.
  apply FO.
  clear i.
  induction i0;
  constructor.
  apply Induction;
  trivial.
  apply IHi0.
Defined.

Inductive isnat : Type -> Prop := isnat_nat : isnat nat.

Definition plus : list Type := (@cons Type nat (@cons Type nat nil)).

Definition natast := AXs isnat (fun _ _ => [plus]) (fun _ _ => nil) nat.

Goal natast -> False.
  intros.
  apply (Induction X).
Qed.