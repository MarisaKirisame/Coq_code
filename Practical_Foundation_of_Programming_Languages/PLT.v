Set Implicit Arguments.

Require Import List Program Permutation.

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

Inductive Pos A : A -> list A -> Type :=
| Pos_fst : forall a l, Pos a (a :: l)
| Pos_skip : forall a a' l, Pos a' l -> Pos a' (a :: l).

Definition remove T (t : T) (l : list T) (P : Pos t l) :
  { l' : list T | Permutation (t :: l') l }.
  induction P.
  exists l.
  trivial.
  destruct IHP.
  exists (a :: x).
  symmetry.
  eapply (@perm_trans _ _ (a :: a' :: x)).
  auto with *.
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
  Definition operator_inner { s : Type } (c : contain S s) := list Type.
  Variable Os : forall s (c : contain S s), list (operator_inner c).
    (*variable is just operator with arity nil*)
  Inductive operator { s : Type } (c : contain S s) := 
  | op : forall o : operator_inner c, Pos o (Os c) -> operator c.
  Definition get_arity s (c : contain S s) (ope : operator c) : list Type := 
    match ope with op l _ => l end.
  Inductive AXs : Type -> Type :=
  | OAXs : forall s (c : contain S s)(op : operator c), 
      ihlist (fun s' => AXs s') (get_arity op) -> AXs s.
  Fixpoint AST_rect (P : forall T, AXs T -> Type)
  (FO : forall s (c : contain S s)(op : operator c)
    (l : ihlist (fun s' => AXs s') (get_arity op)), 
      @ihlist_forall _ (fun t ax => P t ax) (get_arity op) l -> P s (OAXs op l))
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
    | OAXs _ _ _ il => 1 +
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
  Variable sdec : forall { s s' : Type } (c : contain S s)(c' : contain S s'),
    { s = s' } + { s <> s' }.
  Definition adjoin { s : Type } (c : contain S s) (v : operator_inner c) :
    forall s', contain S s' ->
      { ls : list (operator_inner c) | 
        (s = s' -> ls = v :: (Os c)) /\
        (s' <> s -> ls = Os c) }.
    intros.
    destruct (sdec c H).
    subst.
    eauto with *.
    exists (Os c).
    intuition.
  Defined.
  Check list_eq_dec.
  Definition remove_operator_inner { s : Type } (c : contain S s) (v : operator c) :
    forall s', contain S s' ->
      { ls : list (operator_inner c) |
        (s = s' -> Permutation ((get_arity v) :: ls) (Os c)) /\
        (s' <> s -> ls = Os c) }.
    intros.
    destruct (sdec c H).
    subst.
    destruct v.
    destruct (remove p).
    simpl in *.
    exists x.
    tauto.
    exists (Os c).
    intuition.
  Defined.
  Definition remove_operator { s : Type } (c : contain S s) (v : operator c) : 
    forall s' (c' : contain S s'), list (operator_inner c') := 
      fun s' c' => proj1_sig (remove_operator_inner v c').
End AST.

Extraction ast_size. (*Testing if AST_rect is useful*)(*should not be defined with AST_size*)

(*ihlist (fun s' => AXs s') (get_arity op)*)

Definition AST_substitute S Os T s sdec (c : contain S s)
  (op : operator Os c) (ast : AXs Os T)
    (f : ihlist (fun s' => AXs Os s') (get_arity op) -> 
      ihlist (fun s' => AXs (remove_operator sdec op) s') (get_arity op))
  : AXs (remove_operator sdec op) T.
  
Definition subst { S S' } (s : S)(Heq : S ~= S') : {s' : S' | s ~= s' }.
  subst.
  exists s.
  trivial.
Defined.

Theorem subst_eq : forall S (eq : S ~= S)(s : S), JMeq s (proj1_sig(subst s eq)).
  intros.
  destruct (subst s eq).
  trivial.
Qed.