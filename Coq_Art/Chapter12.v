Require Export Relations.
Require Export List.

Module Type DEC_ORDER.
  Parameter A : Set.
  Parameter le : A -> A -> Prop.
  Parameter lt : A -> A -> Prop.
  Axiom ordered : order A le.
  Axiom lt_le_weak : forall a b:A, lt a b -> le a b.
  Axiom lt_diff : forall a b:A, lt a b -> a <> b.
  Axiom le_lt_or_eq : forall a b:A, le a b -> lt a b \/ a = b.
  Parameter lt_eq_lt_dec : forall a b:A, {lt a b} + {a = b} + {lt b a}.
End DEC_ORDER.

Module Type MORE_DEC_ORDERS.
  Parameter A : Set.
  Parameter le : A -> A -> Prop.
  Parameter lt : A -> A -> Prop.
  Axiom le_trans : transitive A le.
  Axiom le_refl : reflexive A le.
  Axiom le_antisym : antisymmetric A le.
  Axiom lt_irreflexive : forall a:A, ~ lt a a.
  Axiom lt_trans : transitive A lt.
  Axiom lt_not_le : forall a b:A, lt a b -> ~ le b a.
  Axiom le_not_lt : forall a b:A, le a b -> ~ lt b a.
  Axiom lt_intro : forall a b:A, le a b -> a <> b -> lt a b.
  Parameter le_lt_dec : forall a b:A, {le a b} + {lt b a}.
  Parameter le_lt_eq_dec : forall a b:A, le a b -> {lt a b} + {a = b}.
End MORE_DEC_ORDERS.

Module More_Dec_Orders (D: DEC_ORDER) : MORE_DEC_ORDERS with Definition
  A := D.A with Definition le := D.le with Definition lt := D.lt.
  Definition A := D.A.
  Definition le := D.le.
  Definition lt := D.lt.
  Theorem le_trans : transitive A le.
    case D.ordered.
    auto.
  Qed.

  Theorem le_refl : reflexive A le.
    case D.ordered.
    auto.
  Qed.

  Theorem le_antisym : antisymmetric A le.
    case D.ordered.
    auto.
  Qed.

  Theorem lt_intro : forall a b:A, le a b -> a <> b -> lt a b.
    intros a b H diff.
    case (D.le_lt_or_eq a b H); tauto.
  Qed.

  Theorem lt_irreflexive : forall a:A, ~ lt a a.
    intuition.  
    case (D.lt_diff _ _ H); trivial.
  Qed.

  Theorem lt_not_le : forall a b:A, lt a b -> ~ le b a.
    intros a b H H0.
    absurd (a = b).
    apply D.lt_diff; trivial.
    apply le_antisym; auto; apply D.lt_le_weak; assumption.
  Qed.

  Theorem le_not_lt : forall a b:A, le a b -> ~ lt b a.
    intros a b H H0; apply (lt_not_le b a); auto.  
  Qed.

  Theorem lt_trans : transitive A lt.
    unfold A, transitive in |- *.
    intros x y z H H0.
    apply (lt_intro x z).
    apply le_trans with y; apply D.lt_le_weak; assumption.
    intro e; rewrite e in H.
    absurd (y = z).
    intro e'; rewrite e' in H.
    apply (lt_irreflexive _ H).
    apply le_antisym; apply D.lt_le_weak; trivial.
  Qed.

  Definition le_lt_dec : forall a b:A, {le a b} + {lt b a}.
    intros a b; case (D.lt_eq_lt_dec a b).
    intro d; case d; auto.  
    left; apply D.lt_le_weak; trivial. 
    simple induction 1; left; apply le_refl.
    right; trivial.
  Defined.

  Definition le_lt_eq_dec : forall a b:A, le a b -> {lt a b} + {a = b}.
    intros a b H.
    case (D.lt_eq_lt_dec a b).
    trivial.
    intro H0; case (le_not_lt a b H H0).
  Defined.

End More_Dec_Orders.

Require Import ZArith.

Module List_Order (D: DEC_ORDER) <: DEC_ORDER with Definition
  A := list D.A .
  Definition A := list D.A .
  Fixpoint lt (l r : A) : Prop := 
    match l,r with
    | nil, nil => False
    | nil, _ => True
    | _, nil => False
    | el :: ll, er :: lr => (D.lt el er) \/ ((el = er)/\(lt ll lr))
    end.
  Definition le (l r : A) : Prop := ~ (lt r l).
  Lemma ordered : order A le.
    intuition.
    unfold reflexive.
    intuition.
    unfold le.
    induction x.
    tauto.
    simpl.
    intuition.
    apply IHx.
    apply D.lt_diff in H0.
    tauto.
    unfold transitive.
    induction x.
    destruct y,z; auto.
    intros.
    destruct y,z;unfold le,lt.
    try(
      absurd(le (a :: x) nil);
      unfold le,lt;
      (tauto||
        trivial)).
    try(
      absurd(le (a :: x) nil);
      unfold le,lt;
      (tauto||
        trivial)).
    try(
      absurd(le (a :: x) nil);
      unfold le,lt;
      (tauto||
        trivial)).
    intuition.
    unfold le in H.
    simpl in H.
    apply Decidable.not_or in H.
    destruct H.
    apply Decidable.not_and in H1.
    admit.
    admit.
    subst.
    assert(a=a0).
    admit.
    subst.
    unfold le in *.
    simpl in *.
    admit.
    unfold antisymmetric.
    unfold le.
    induction x.
    intros.
    unfold lt in *.
    destruct y;tauto.
    intros.
    simpl in *.
    induction y.
    simpl in *.
    tauto.
    simpl in *.
    apply Decidable.not_or in H.
    destruct H.
    assert(a=a0).
    admit.
    apply Decidable.not_and in H1.
    apply Decidable.not_or in H0.
    destruct H0.
    apply Decidable.not_and in H3.
    destruct H1,H3;try subst;try tauto.
    f_equal.
    auto.
    admit.
    admit.
  Qed.

  Axiom lt_diff : forall a b:A, lt a b -> a <> b.

  Lemma lt_le_weak : forall a b:A, lt a b -> le a b.
    induction a.
    induction b.
    unfold le,lt.
    tauto.
    simpl.
    intros.
    unfold le,lt.
    tauto.
    intros.
    unfold le,lt.
    destruct b.
    tauto.
    unfold not.
    intuition.
    admit.
    simpl in *.
    subst.
    destruct H.
    apply D.lt_diff in H.
    tauto.
    destruct H.
    clear H.
    fold lt in *.
    assert(a0<>b).
    apply lt_diff.
    auto.
    intuition.
    
  Axiom le_lt_or_eq : forall a b:A, le a b -> lt a b \/ a = b.
  Parameter lt_eq_lt_dec : forall a b:A, {lt a b} + {a = b} + {lt b a}.
End List_Order.