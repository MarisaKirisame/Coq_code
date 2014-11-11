Set Implicit Arguments.

CoInductive LList (A:Set) : Set :=
| LNil : LList A
| LCons : A -> LList A -> LList A.

Implicit Arguments LNil [A].

Require Import List.

Fixpoint list_llist (A : Set)(l : list A) : LList A :=
  match l with
  | nil => LNil
  | e :: l' => LCons e (list_llist l')
  end.

Require Import Image.

Goal forall (A : Set), injective _ _ (@list_llist A).
  unfold injective.
  induction x.
  intuition.
  destruct y.
  trivial.
  simpl in *.
  inversion H.
  intuition.
  simpl in *.
  induction y.
  simpl in *.
  inversion H.
  simpl in *.
  injection H.
  intuition.
  subst.
  f_equal.
  apply IHx.
  trivial.
Qed.

Definition LMap: forall (A B:Set), (A ->B) ->  LList A -> LList B.
  cofix.
  intros.
  refine(
    match H0 with
    | LNil => LNil
    | LCons e l => LCons (H e) (LMap _ _ H l)
    end).
Defined.

Inductive BugInfinite (A:Set) : LList A -> Prop :=
  BugInfinite_intro :
    forall a (l:LList A),
      BugInfinite l -> BugInfinite (LCons a l).

Goal forall (A : Set)(l : LList A), BugInfinite l -> False.
  intros.
  elim H.
  trivial.
Qed.