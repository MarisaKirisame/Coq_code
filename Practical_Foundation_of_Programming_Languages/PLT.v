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

Fixpoint pos_rect' (P : forall T (t : T) (lt : list T), pos t lt -> Type)
  (PF : forall T (t : T) (lt : list T) (p : Some t = hd_error lt), P T t lt (pos_fst lt p))
    (PS : forall T (t : T) (lt : list T) (p : pos t (tail lt)), P T t (tail lt) p -> 
      P T t lt (pos_skip lt p))
    T (t : T) (lt : list T) (p : pos t lt)
  : P T t lt p.
  destruct p.
  trivial.
  apply PS.
  apply pos_rect';
  trivial.
Defined.

Definition pos_lt_contain T (t : T) (p : pos t nil) : False.
  remember [].
  generalize dependent Heql.
  refine (pos_rect' (fun _ _ _ _ => _ -> _) _ _ p);
  intros;
  subst;
  try tauto;
  discriminate.
Defined.

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

Inductive permutation_type {A : Type} : list A -> list A -> Type :=
| perm_type_nil : permutation_type [] []
| perm_type_skip : forall (x : A) (l l' : list A),
    permutation_type l l' -> permutation_type (x :: l) (x :: l')
| perm_type_swap : forall (x y : A) (l : list A),
    permutation_type (y :: x :: l) (x :: y :: l)
| perm_type_trans : forall l l' l'' : list A,
    permutation_type l l' -> permutation_type l' l'' -> permutation_type l l''.

Definition permutation_reflexive : forall T (l : list T), permutation_type l l.
  induction l.
  constructor.
  constructor.
  trivial.
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

Definition find_pos T (t : T) (l l' : list T) (P : pos t l) : permutation_type l l' -> pos t l'.
  induction 1.
  trivial.
  destruct P.
  simpl in *.
  inversion e.
  subst.
  constructor.
  trivial.
  simpl in *.
  intuition.
  apply pos_skip.
  trivial.
  inversion P.
  simpl in *.
  inversion H.
  subst.
  apply pos_skip.
  simpl in *.
  constructor.
  trivial.
  simpl in *.
  inversion H.
  inversion H0.
  subst.
  simpl in *.
  constructor.
  trivial.
  simpl in *.
  apply pos_skip.
  apply pos_skip.
  trivial.
  tauto.
Defined.

Theorem Permutation_permutation_type : forall T (l : list T) r (P : Permutation l r),
  permutation_type l r.
  intros.
  generalize dependent r.
  induction l.
  intros.
  destruct r.
  constructor.
  apply Permutation_nil in P.
  discriminate.
  intros.
  destruct r.
  symmetry in P.
  apply Permutation_nil in P.
  discriminate.
Admitted.

Ltac invc H := inversion H; subst; clear H.

Definition bring_to_front { T } 
  (dec : forall l r : T, { l = r } + { l <> r }) e : 
    forall l : list T, In e l -> { lr | Permutation l lr /\ hd_error lr = value e }.
  induction l.
  simpl in *.
  tauto.
  intros.
  destruct (dec e a).
  subst.
  exists (a :: l).
  auto.
  assert(In e l).
  simpl in *.
  intuition.
  clear H.
  intuition.
  invc X.
  intuition.
  destruct x.
  discriminate.
  simpl in *.
  invc H2.
  exists (e :: a :: x).
  split.
  assert (Permutation (a :: l) (a :: e :: x)).
  auto.
  eapply perm_trans.
  exact H.
  constructor.
  trivial.
Defined.

Definition pos_In : forall T (t : T) lt, pos t lt -> In t lt.
  induction 1.
  destruct lt.
  discriminate.
  invc e.
  simpl in *.
  tauto.
  destruct lt.
  trivial.
  simpl in *.
  tauto.
Qed.

Definition In_pos : forall T (t : T) (dec : forall l r : T, { l = r } + { l <> r })
  lt, In t lt -> pos t lt.
  induction lt.
  intros.
  simpl in *.
  tauto.
  intros.
  simpl in *.
  destruct (dec a t).
  subst.
  constructor.
  trivial.
  assert(In t lt).
  destruct H.
  tauto.
  trivial.
  apply pos_skip.
  simpl in *.
  tauto.
Defined.

Definition find_front_pos T (dec : forall l r : T, { l = r } + { l <> r }) (l r : list T) n t
  : n = length l -> Permutation (t :: l) r -> pos t r.
  generalize dependent l.
  generalize dependent r.
  induction n.
  intros.
  destruct l.
  simpl in *.
  clear H.
  apply Permutation_length_1_inv in H0.
  subst.
  constructor.
  trivial.
  discriminate.
  intros.
  destruct l.
  discriminate.
  invc H.
  destruct r.
  apply Permutation_length in H0.
  discriminate.
  destruct (dec t t1).
  subst.
  constructor.
  trivial.
  apply pos_skip.
  simpl in *.
  remember (bring_to_front dec).
  eapply IHn.
Definition Permutation_pos_find T (dec : forall l r : T, { l = r } + { l <> r })
  t n (l r : list T) (p : pos t l) (P : Permutation l r) : n = length r -> pos t r.
  generalize dependent r.
  generalize dependent l.
  induction n.
  intros.
  destruct l.
  simpl in *.
  apply pos_lt_contain in p.
  tauto.
  destruct r.
  symmetry in P.
  apply Permutation_nil in P.
  discriminate.
  discriminate.
  intros.
  destruct r.
  discriminate.
  simpl in *.
  inversion H.
  subst.
  clear H.
  destruct l.
  apply pos_lt_contain in p.
  tauto.
  destruct (bring_to_front dec p).
  intuition.
  destruct x.
  discriminate.
  simpl in *.
  inversion H0.
  subst.
  destruct p.
  simpl in *.
  inversion e.
  subst.
  admit.
  simpl in *.
Fixpoint update_pos T (t t' : T) (l : list T) (P : pos t l) (P' : pos t' l) { struct l } :
  t <> t' -> pos t' (` (remove P)).
  destruct l.
  apply pos_lt_contain in P'.
  tauto.
  intros.
  destruct P, P';
  try inversion e;
  try inversion e0;
  subst.
  tauto.
  simpl in P'.
  destruct (remove (pos_fst (t0 :: l) e)).
  simpl in *.
  apply Permutation_cons_inv in p.
  admit.
  simpl in *.
  destruct (remove P).
  simpl in *.
  constructor.
  trivial.
  simpl in *.
  remember (update_pos T t t' l P P' H).
  clear Heqp.
  destruct (remove P).
  simpl in *.
  apply pos_skip.
  trivial.
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