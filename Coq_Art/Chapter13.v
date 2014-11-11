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

Require Import Classical.

CoInductive Infinite (A:Set) : LList A -> Prop :=
  Infinite_LCons :
    forall (a:A) (l:LList A), Infinite l -> Infinite (LCons a l).

Inductive Finite (A:Set) : LList A -> Prop :=
| Finite_LNil : Finite LNil
| Finite_LCons : forall (a:A) (l:LList A), Finite l -> Finite (LCons a l).

Lemma Finite_not_Infinite :
  forall (A:Set) (l:LList A), Finite l -> ~ Infinite l.
  simple induction 1.
  unfold not in |- *; intro H0; inversion_clear H0.
  unfold not at 2 ; intros a l0 H1 H2 H3.
  inversion H3; auto.
Qed.

Lemma Not_Finite_Infinite :
  forall (A:Set) (l:LList A), ~ Finite l -> Infinite l.
  cofix H.
  destruct l.
  intros.
  absurd (Finite (@LNil A)).
  trivial.
  constructor.
  split.
  apply H.
  intuition.
  apply H0.
  constructor.
  trivial.  
Qed.

Lemma Not_Infinite_Finite :
  forall (A:Set) (l:LList A),
    ~ Infinite l -> Finite l.
  intros.
  case (classic (Finite l)).
  trivial.
  intros.
  elim H.
  apply Not_Finite_Infinite.
  trivial.
Qed.

Lemma Finite_or_Infinite :
  forall (A:Set)(l:LList A), Finite l \/ Infinite l.
  intros.
  case(classic (Finite l)).
  tauto.
  intro.
  right.
  apply Not_Finite_Infinite.
  trivial.
Qed.

Definition Infinite_ok (A:Set) (X:LList A -> Prop) :=
  forall l : LList A,
    X l ->  exists a : A, exists l' : LList A, l = LCons a l' /\ X l'.

Definition Infinite1 (A:Set) (l:LList A) :=
  exists X : LList A -> Prop, Infinite_ok X /\ X l.

Lemma ok_LNil :
  forall (A:Set) (X:LList A -> Prop), Infinite_ok X -> ~ X LNil.
  intros.
  unfold not in |- *; intro.
  case (H LNil).
  trivial.
  intuition.
  case H1.
  intuition.
  inversion H3.
Qed.

Lemma ok_LCons :
  forall (A:Set) (X:LList A -> Prop) (a:A) (l:LList A),
    Infinite_ok X -> X (LCons a l) -> X l.
  intuition.
  case (H (LCons a l)).
  trivial.
  intuition.
  destruct H1.
  intuition.
  injection H2.
  intuition.
  subst.
  trivial.
Qed.

Lemma Infinite1_LNil : forall A:Set, ~ Infinite1 (LNil (A:=A)).
  intuition.
  case H.
  intros.
  case H0.
  intuition.
  apply ok_LNil in H1.
  tauto.
Qed.

Lemma Infinite1_LCons :
  forall (A:Set) (a:A) (l:LList A), Infinite1 (LCons a l) -> Infinite1 l.
  intuition.
  case H.
  intuition.
  eexists.
  split.
  eauto.
  unfold Infinite_ok in *.
  ecase H1.
  eauto.
  intuition.
  case H0.
  intuition.
  injection H4.
  intuition.
  subst.
  trivial.
Qed.

Theorem Infinite1_Infinite : forall(A : Set)(l : LList A), Infinite1 l -> Infinite l.
  cofix.
  destruct l.
  intros.
  apply Infinite1_LNil in H.
  tauto.
  intros.
  constructor.
  apply Infinite1_Infinite.
  eapply Infinite1_LCons.
  eauto.
Qed.

Lemma Infinite_not_Finite :
  forall (A:Set) (l:LList A), Infinite l -> ~ Finite l.
  intuition.
  absurd (Infinite l).
  apply Finite_not_Infinite.
  trivial.
  trivial.
Qed.

Theorem LCons_Infinite : forall (A:Set)(a:A)(l:LList A), Infinite (LCons a l) -> Infinite l.
  intuition.
  apply Not_Finite_Infinite.
  apply Infinite_not_Finite in H.
  intuition.
  apply H.
  constructor.
  trivial.
Qed.

Theorem Infinite_Infinite1 : forall(A : Set)(l : LList A), Infinite l -> Infinite1 l.
  intuition.
  exists (@Infinite _).
  intuition.
  unfold Infinite_ok.
  intuition.
  remember l0.
  destruct l0.
  subst.
  apply Infinite_not_Finite in H0.
  elim H0.
  constructor.
  subst.
  repeat eexists.
  eapply LCons_Infinite.
  eauto.
Qed.