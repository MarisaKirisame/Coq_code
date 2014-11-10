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
  Fixpoint le (l r : A) : Prop :=
    match l,r with
    | nil, nil => True
    | nil, _ => True
    | _, nil => False
    | el :: ll, er :: lr => (D.lt el er) \/ ((el = er)/\(le ll lr))
    end.
  Module M := More_Dec_Orders D.
  Lemma ordered : order A le.
    intuition.
    unfold reflexive.
    intuition.
    induction x.
    auto with *.
    simpl.
    tauto.
    unfold transitive.
    induction x.
    simpl.
    destruct z; auto.
    simpl in *.
    destruct y.
    tauto.
    destruct z;auto.
    intros.
    intuition.
    simpl in *.
    intuition.
    left.
    eapply M.lt_trans;
    eauto.
    subst.
    tauto.
    subst.
    simpl in *.
    intuition.
    subst.
    right.
    intuition.
    eauto.
    unfold antisymmetric.
    induction x.
    destruct y.
    trivial.
    simpl in *.
    intuition.
    intuition.
    destruct y.
    simpl in *.
    tauto.
    simpl in *.
    intuition.
    apply M.lt_not_le in H1.
    intuition.
    elim H1.
    apply D.lt_le_weak.
    auto.
    subst.
    apply D.lt_diff in H1.
    tauto.
    subst.
    apply D.lt_diff in H1.
    tauto.
    clear H.
    subst.
    f_equal.
    auto.
  Qed.

  Lemma lt_diff : forall a b:A, lt a b -> a <> b.
    induction a.
    simpl in *.
    destruct b;auto.
    intuition.
    assert(nil<>a::b).
    auto with *.
    tauto.
    intros.
    simpl in *.
    destruct b;auto.
    destruct H.
    assert(a <> a1).
    apply D.lt_diff in H.
    trivial.
    intuition.
    apply H0.
    injection H1.
    trivial.
    destruct H.
    subst.
    assert(a0<>b).
    auto.
    intuition.
    apply H.
    injection H1.
    trivial.
  Qed.

  Lemma lt_le_weak : forall a b:A, lt a b -> le a b.
    induction a.
    induction b.
    auto with *.
    trivial.
    destruct b.
    trivial.
    simpl.
    intuition.
  Qed.

  Lemma le_lt_or_eq : forall a b:A, le a b -> lt a b \/ a = b.
    induction a.
    destruct b;
    tauto.
    destruct b;simpl in *.
    tauto.
    intuition.
    subst.
    ecase IHa.
    eauto.
    tauto.
    intuition.
    subst.
    tauto.
  Qed.

  Definition lt_eq_lt_dec : forall a b:A, {lt a b} + {a = b} + {lt b a}.
    induction a.
    destruct b.
    tauto.
    constructor 1.
    constructor 1.
    simpl.
    trivial.
    destruct b.
    simpl in *.
    constructor 2.
    trivial.
    simpl in *.
    assert({D.lt a a1} + {a = a1} + {D.lt a1 a}).
    apply D.lt_eq_lt_dec.
    destruct H.
    destruct s.
    tauto.
    subst.
    assert({lt a0 b} + {a0 = b} + {lt b a0}).
    apply IHa.
    destruct H.
    destruct s.
    tauto.
    subst.
    tauto.
    tauto.
    tauto.
  Defined.

End List_Order.