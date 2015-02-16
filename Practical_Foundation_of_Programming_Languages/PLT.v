Set Implicit Arguments.

Require Import List Program Permutation ProofIrrelevance.
Require Import tactic eq_dec hlist pos remove.

Theorem Permutation_occ : forall T (l : list T) r dec,
  Permutation l r -> forall t, count_occ dec r t = count_occ dec l t.
  intros.
  induction H;
  trivial;
  simpl in *;
  try destruct (dec x t);
  subst;
  auto.
  destruct (dec y t);
  trivial.
  omega.
Qed.

Definition set T := T -> Prop.

Definition contain { T } (S : set T) R := S R.

Inductive vector T : nat -> Type :=
| VNil : vector T 0
| VCons : forall n, T -> vector T n -> vector T (S n).

Section AST.
  Variable S : set Type.
  Inductive s : Type := mks : forall T, contain S T -> s.
  Definition operator_inner (s' : s) := list s.
  Variable sdec : eq_dec s.
  Definition oidec s : eq_dec (operator_inner s).
    unfold operator_inner.
    unfold eq_dec in *.
    apply list_eq_dec.
    trivial.
  Defined.
  Section OS_no_change.
    Inductive OperatorSet := 
    | mkOS : (forall (s' : s), list (operator_inner s')) -> OperatorSet.
    Variable Os : OperatorSet.
      (*variable is just operator with arity nil*)
    Definition get_loi (s' : s) : list (operator_inner s') :=
      match Os with mkOS P => P s' end.
    Inductive operator (s' : s) := 
    | mkop : forall o : operator_inner s', pos o (get_loi s') -> operator s'.
    Definition get_arity s' (ope : operator s') : list s := 
      match ope with mkop l _ => l end.
    Definition get_pos s' (ope : operator s') : 
      pos (get_arity ope) (get_loi s') :=
      match ope with mkop _ p => p end.
    Definition get_type s' : Type := match s' with mks T _ => T end.
    Definition get_arity_type s' (op : operator s') := 
      map get_type (get_arity op).
    Inductive AXs : Type -> Type :=
    | OAXs : forall s' (op : operator s'), 
        hlist (fun s' => AXs s') (get_arity_type op) -> AXs s.
    Fixpoint AST_rect (P : forall T, AXs T -> Type)
      (FO : forall s' (op : operator s')
        (l : hlist (fun s' => AXs s') (get_arity_type op)), 
          @hlist_forall
            _
            (fun t ax => P t ax)
            (get_arity_type op) l ->
              P s (OAXs op l)) T (AX : AXs T) :
        P T AX.
      destruct AX.
      apply FO.
      induction h;
      constructor;
      try apply AST_rect;
      trivial.
    Defined.
    Fixpoint AST_size T (ast : AXs T) : nat :=
      match ast with
      | OAXs _ _ il => 1 +
          ((fix ilind t (l : hlist _ t) : nat := 
            match l with
            | hnil => 0
            | hcons _ _ a l' => AST_size a + ilind _ l'
            end) _ il)
      end.
    Definition ast_size : forall T (ast : AXs T), { n | n = AST_size ast }.
      intros.
      refine (@AST_rect
        (fun _ ast' => {n : nat | n = AST_size ast'}) _ T ast);
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
            (s' = s'' -> ls = v :: (get_loi s')) /\
            (s' <> s'' -> ls = get_loi s') }.
      intros.
      destruct (sdec s' s'').
      subst.
      eauto with *.
      exists (get_loi s').
      intuition.
    Defined.
    Definition remove_operator_inner s' (v : operator s') :
      forall s'',
        { ls : (list (operator_inner s'') * list (operator_inner s'')) |
            (s' = s'' -> fst ls ++ (get_arity v) :: snd ls = (get_loi s')) /\
            (s' <> s'' -> fst ls = get_loi s' /\ snd ls = []) }.
      intros.
      destruct (sdec s' s'').
      subst.
      assert (
        {ls : list (operator_inner s'') * list (operator_inner s'') | 
            fst ls ++ get_arity v :: snd ls = get_loi s'' }).
      destruct v.
      destruct (remove_pos p).
      exists x.
      simpl in *.
      intuition.
      destruct X.
      exists x.
      tauto.
      exists (get_loi s', @nil (operator_inner s'')).
      tauto.
    Defined.
    Definition remove_operator_inner_wrapper s' (v : operator s') :
      { ls : forall s'',
        (list (operator_inner s'')*list (operator_inner s'')) |
          forall s'',
            (s' = s'' -> fst (ls s'') ++ (get_arity v) :: snd (ls s'') =
            (get_loi s')) /\
            (s' <> s'' -> fst (ls s'') = get_loi s' /\ snd (ls s'') = []) }.
      exists (fun s'' => ` (remove_operator_inner v s'')).
      intros.
      destruct remove_operator_inner.
      trivial.
    Defined.
    Definition remove_operator s' (v : operator s') : 
      forall s'', list (operator_inner s'') :=
        let lr := ` (remove_operator_inner_wrapper v) in fun s'' =>
          fst (lr s'') ++ snd (lr s'').
    Theorem mkop_inj : forall s' vl (sl sr : pos vl (get_loi s')),
      mkop sl = mkop sr -> sl = sr.
      inversion 1.
      apply Eqdep_dec.inj_pair2_eq_dec in H1;
      try apply list_eq_dec;
      trivial.
    Qed.
    Definition opdec : forall s', eq_dec (operator s').
      intros.
      destruct l, r;
      destruct (list_eq_dec sdec o o0);
      subst;
      unfold operator_inner in o0;
      try destruct (eq_pos_dec (list_eq_dec sdec) p p0).
      subst.
      tauto.
      right.
      intuition.
      apply mkop_inj in H.
      tauto.
      right.
      intuition.
      invc H.
      tauto.
    Defined.
  End OS_no_change.
  Global Arguments mkop { Os } { s' } { o } _.
  Definition loidec : forall s', eq_dec (list (operator_inner s')).
    intros.
    unfold eq_dec in *.
    unfold operator_inner.
    intros.
    repeat apply list_eq_dec.
    trivial.
  Defined.
  Definition update_operator (s' : s) Os (op op' : operator Os s') : 
    op <> op' -> 
      { newop : operator (remove_operator op') s' |
          get_arity op = get_arity newop /\ 
          ((pos_before (get_pos op)) = (pos_before (get_pos newop))\/
          (pos_after (get_pos op)) = (pos_after (get_pos newop))) }.
    destruct op, op'.
    intros.
    unfold remove_operator.
    destruct (remove_operator_inner_wrapper).
    simpl in *.
    assert (fst (x s') ++ o0 :: snd (x s') = Os s').
    specialize (a s').
    tauto.
  Defined.

End AST.
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