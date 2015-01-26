Set Implicit Arguments.

Require Import List Program Permutation ProofIrrelevance.

Definition set T := T -> Prop.

Definition contain { T } (S : set T) R := S R.

Inductive vector T : nat -> Type :=
| VNil : vector T 0
| VCons : forall n, T -> vector T n -> vector T (S n).

Inductive ihlist { F : Type -> Type } : list Type -> Type :=
| ihnil : ihlist nil
| ihcons : forall T L (f : F T), ihlist L -> ihlist (T :: L).

Implicit Arguments ihlist[].
Implicit Arguments ihcons[T L F].

Inductive pos T (t : T) (lt : list T) : Type :=
| pos_fst : Some t = hd_error lt -> pos t lt
| pos_skip : pos t (tail lt) -> pos t lt.

Fixpoint pos_lt_contain T (t : T) (p : pos t nil) : False.
  destruct p.
  discriminate.
  simpl in *.
  eapply pos_lt_contain.
  eauto.
Qed.

Fixpoint pos_nat T (t : T) l (p : pos t l) :=
  match p with
  | pos_fst _ => 0
  | pos_skip p' => S (pos_nat p')
  end.

Definition eq_pos_dec : forall T (t : T) ls (l r : pos t ls), { l = r } + { l <> r }.
  induction ls.
  intros.
  assert(False).
  eapply pos_lt_contain.
  eauto.
  tauto.
  intros.
  destruct l, r;
  simpl in *;
  try inversion e;
  subst;
  try(
    left;
    f_equal;
    apply proof_irrelevance);
  try(
    right;
    discriminate).
  destruct (IHls l r).
  subst.
  tauto.
  right.
  intuition.
  inversion H.
  subst.
  tauto.
Defined.

Definition remove T (t : T) (l : list T) (P : pos t l) :
  { l' : list T | Permutation (t :: l') l }.
  induction l.
  apply pos_lt_contain in P.
  tauto.
  destruct P.
  simpl in *.
  inversion e.
  subst.
  exists l.
  trivial.
  simpl in *.
  intuition.
  destruct X.
  exists (a :: x).
  assert(Permutation (a :: t :: x) (a :: l)).
  auto.
  eapply perm_trans in H.
  eauto.
  constructor.
Defined.

Inductive ihlist_forall (F : Type -> Type) { P : forall T, F T -> Type } : 
  forall L, ihlist F L -> Type :=
| Forall_ihnil : ihlist_forall ihnil
| Forall_ihcons : forall (l : list Type)(L : ihlist F l)(T : Type)(t : F T), 
    P T t -> ihlist_forall L -> ihlist_forall (ihcons t L).

Implicit Arguments ihlist_forall[F].

Section AST.
  Variable S : set Type.
  Inductive s : Type := mks : forall T, contain S T -> s.
  Definition operator_inner (s' : s) := list s.
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
  Theorem ast_size : forall T (ast : AXs T), { n | n = AST_size ast }.
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
  Variable sdec : forall s' s'' : s, { s' = s'' } + { s' <> s'' }.
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
  Theorem mkop_inj_eq : forall s' vl vr (sl : pos vl (Os s'))(sr : pos vr (Os s')), 
    mkop sl ~= mkop sr -> vl = vr.
    inversion 1.
    apply Eqdep_dec.inj_pair2_eq_dec in H1.
    admit.
    intros.
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
    apply mkop_inj in H.
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