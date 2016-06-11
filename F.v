Require Import CoqUtil.ISO CoqUtil.Tactic.
Set Universe Polymorphism.
Set Implicit Arguemnts.

Definition F f :=
  forall x, (f x -> x) -> x.

Definition natF := F (fun x => option x).

Definition natFnat (n : natF) : nat :=
  n nat
    (fun n =>
       match n with
       | None => 0
       | Some x => S (f x)
       end).

Definition OF : natF :=
  fun _ f => f None.

Definition SF (n : natF) : natF :=
  fun _ f => f (Some (n _ f)).

Fixpoint natnatF (n : nat) : natF :=
  match n with
  | O => OF
  | S n => SF (natnatF n)
  end.

Program Definition natISO : ISO natF nat := Build_ISO natFnat natnatF _ _.
Next Obligation.
  induction x; compute in *; f_equal; trivial.
Qed.

Next Obligation.
  compute; repeat ext.
Admitted.

Definition WF (f : Type -> Type) :=
  forall r, (forall x, (x -> r) -> (f x -> r)) -> r.

Program Definition FWF f : ISO (F f) (WF f) := Build_ISO _ _ _ _.
Next Obligation.
  compute in *; ii.
  apply X; eauto.
Qed.

Next Obligation.
  compute in *; ii.
Admitted.