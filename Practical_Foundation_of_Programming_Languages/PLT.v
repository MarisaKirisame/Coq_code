Set Implicit Arguments.

Require Import List Program Permutation ProofIrrelevance.

Load pos.

Definition set T := T -> Prop.

Definition contain { T } (S : set T) R := S R.

Inductive vector T : nat -> Type :=
| VNil : vector T 0
| VCons : forall n, T -> vector T n -> vector T (S n).

Section AST.
  Variable S : set Type.
  Inductive s : Type := mks : forall T, contain S T -> s.
  Definition operator_inner (s' : s) := list s.
  Variable sdec : forall s' s'' : s, { s' = s'' } + { s' <> s'' }.
  Section OS_no_change.
    Variable Os : forall (s' : s), list (operator_inner s').
      (*variable is just operator with arity nil*)
    Inductive operator (s' : s) := 
    | mkop : forall o : operator_inner s', pos o (Os s') -> operator s'.
    Definition get_arity s' (ope : operator s') : list s := 
      match ope with mkop l _ => l end.
    Definition get_type s' : Type := match s' with mks T _ => T end.
    Definition get_arity_type s' (op : operator s') := map get_type (get_arity op).
    Inductive AXs : Type -> Type :=
    | OAXs : forall s' (op : operator s'), 
        ihlist (fun s' => AXs s') (get_arity_type op) -> AXs s.
    Fixpoint AST_rect (P : forall T, AXs T -> Type)
      (FO : forall s' (op : operator s')
        (l : ihlist (fun s' => AXs s') (get_arity_type op)), 
          @ihlist_forall _ (fun t ax => P t ax) (get_arity_type op) l -> P s (OAXs op l))
            T (AX : AXs T) : P T AX.
      destruct AX.
      apply FO.
      induction i;
      constructor;
      try apply AST_rect;
      trivial.
    Defined.
    Fixpoint AST_size T (ast : AXs T) : nat :=
      match ast with
      | OAXs _ _ il => 1 +
          ((fix ilind t (l : ihlist _ t) : nat := 
            match l with
            | ihnil => 0
            | ihcons _ _ a l' => AST_size a + ilind _ l'
            end) _ il)
      end.
    Definition ast_size : forall T (ast : AXs T), { n | n = AST_size ast }.
      intros.
      refine (@AST_rect (fun _ ast' => {n : nat | n = AST_size ast'}) _ T ast);
      intros;
      simpl in *.
      induction X.
      eauto.
      destruct p, IHX.
      exists (x + x0).
      subst.
      auto.
    Defined.
    Definition adjoin s' (v : operator_inner s') :
      forall s'',
        { ls : list (operator_inner s') | 
            (s' = s'' -> ls = v :: (Os s')) /\
            (s' <> s'' -> ls = Os s') }.
      intros.
      destruct (sdec s' s'').
      subst.
      eauto with *.
      exists (Os s').
      intuition.
    Defined.
    Definition remove_operator_inner s' (v : operator s') :
      forall s'',
        { ls : list (operator_inner s'') |
            (s' = s'' -> Permutation ((get_arity v) :: ls) (Os s')) /\
            (s' <> s'' -> ls = Os s') }.
      intros.
      destruct (sdec s' s'').
      subst.
      destruct v.
      destruct (remove p).
      simpl in *.
      exists x.
      tauto.
      exists (Os s').
      intuition.
    Defined.
    Definition remove_operator s' (v : operator s') : 
      forall s'', list (operator_inner s'') := 
        fun s'' => proj1_sig (remove_operator_inner v s'').
    Theorem mkop_inj : forall s' vl (sl sr : pos vl (Os s')), mkop sl = mkop sr -> sl = sr.
      inversion 1.
      apply Eqdep_dec.inj_pair2_eq_dec in H1;
      try apply list_eq_dec;
      trivial.
    Qed.
    Definition opdec : forall s' (opl opr : operator s'),
      { opl = opr } + { opl <> opr }.
      intros.
      destruct opl, opr;
      destruct (list_eq_dec sdec o o0);
      subst;
      unfold operator_inner in o0;
      try destruct (eq_pos_dec p p0).
      subst.
      tauto.
      right.
      intuition.
      apply mkop_inj in H.
      tauto.
      right.
      intuition.
      inversion H.
      tauto.
    Defined.
  End OS_no_change.
  Definition update_operator (s' : s) Os (op op' : operator Os s') : op <> op' -> 
    { newop : operator (remove_operator op') s' | get_arity op = get_arity newop }.
    intros.
    remember (mkop).
    destruct op.
    
Extraction ast_size. (*Testing if AST_rect is useful*)(*should not be defined with AST_size*)

Definition AST_substitute S Os T s' sdec
  (op : @operator S Os s') (ast : AXs Os T)
    (f : ihlist (fun s' => AXs Os s') (get_arity_type op) -> 
      ihlist (fun s' => AXs (remove_operator sdec op) s') (get_arity_type op))
  : AXs (remove_operator sdec op) T.
  eapply AST_rect;
  eauto.
  intros.
  destruct (sdec s' s'0).
  subst.
  destruct (opdec sdec op op0).
  subst.
  intuition.
  admit.
  admit.
  admit.
Defined.

Definition subst { S S' } (s : S)(Heq : S ~= S') : {s' : S' | s ~= s' }.
  subst.
  exists s0.
  trivial.
Defined.

Theorem subst_eq : forall S (eq : S ~= S)(s : S), JMeq s (proj1_sig(subst s eq)).
  intros.
  destruct (subst s0 eq).
  trivial.
Qed.