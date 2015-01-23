Set Implicit Arguments.

Require Import List Program.

Definition set T := T -> Prop.

Definition contain { T } (S : set T) R := S R.

Inductive vector T : nat -> Type :=
| VNil : vector T 0
| VCons : forall n, T -> vector T n -> vector T (S n).

Inductive ihlist { F : Type -> Type } : list Type -> Type :=
| ihnil : ihlist nil
| ihcons : forall T L (f : F T), ihlist L -> ihlist (T :: L).

Implicit Arguments ihlist[].

Definition operator (S : Type) := list Type.
Definition variable (S : Type) := unit.

Inductive Pos A : A -> list A -> Type :=
| Pos_fst : forall a l, Pos a (a :: l)
| Pos_skip : forall a a' l, Pos a' l -> Pos a' (a :: l).

Inductive AXs
  { S : set Type }
    { Os : forall s, contain S s -> list (operator s) }
    { Xs : forall s, contain S s -> list (variable s) } : Type -> Type :=
| XAXs : forall s (c : contain S s)(va : variable s), Pos va (Xs s c) -> AXs s
| OAXs : forall s (c : contain S s)(op : operator s), Pos op (Os s c) -> 
    ihlist (fun s' => AXs s') op -> AXs s.

Implicit Arguments AXs[].
Implicit Arguments OAXs[s c op S Os Xs].
Implicit Arguments XAXs[s c va S Os Xs].
Implicit Arguments ihcons[T L F].

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

Definition adjoin { S : set Type } (Xs : forall s, contain S s -> list (variable s))
  { s : Type } { sdec : forall t, { s = t } + { s <> t } } (c : contain S s) (v : variable s) : 
    forall s' (c' : contain S s'),
      { ls : list (variable s') | 
          (forall (eq : s = s'), ls = v :: (Xs _ c)) /\
          (s' <> s -> ls = Xs _ c') }.
  intros.
  destruct (sdec s').
  subst.
  exists (v :: (Xs _ c)).
  intuition.
  exists (Xs s' c').
  intuition.
Defined.

Inductive ihlist_forall (F : Type -> Type) { P : forall T, F T -> Type } : 
  forall L, ihlist F L -> Type :=
| Forall_ihnil : ihlist_forall ihnil
| Forall_ihcons : forall (l : list Type)(L : ihlist F l)(T : Type)(t : F T), 
    P T t -> ihlist_forall L -> ihlist_forall (ihcons t L).

Implicit Arguments ihlist_forall[F].

Fixpoint AST_rect S Os Xs (P : forall T, AXs S Os Xs T -> Type)
  (FX : forall s (c : contain S s)(s' : variable s)(i : Pos s' (Xs s c)), P s (XAXs i))
  (FO : forall s (c : contain S s)(op : operator s)(i : Pos op (Os s c))
    (l : ihlist (fun s' => AXs S Os Xs s') op), 
      ihlist_forall (fun t ax => P t ax) op l -> P s (OAXs i l))
  T (AX : AXs S Os Xs T) : P T AX.
  destruct AX;
  trivial.
  apply FO.
  clear p.
  induction i;
  constructor;
  try apply AST_rect;
  trivial.
Defined.

Fixpoint AST_size S Os Xs T (ast : AXs S Os Xs T) : nat :=
  match ast with
  | XAXs _ _ _ _ => 1
  | OAXs _ _ _ _ il => 1 +
      ((fix ilind t (l : ihlist _ t) : nat := 
        match l with
        | ihnil => 0
        | ihcons _ _ a l' => AST_size a + ilind _ l'
        end) _ il)
  end.

Theorem ast_size : forall S Os Xs T (ast : AXs S Os Xs T), { n | n = AST_size ast }.
  intros.
  refine (@AST_rect S Os Xs (fun _ ast' => {n : nat | n = AST_size ast'}) _ _ T ast);
  intros;
  simpl in *.
  eauto.
  clear i.
  induction X.
  eauto.
  destruct p, IHX.
  exists (x + x0).
  subst.
  auto.
Defined.

Extraction ast_size. (*Testing if AST_rect is useful*)

Inductive subeq : forall S Xs Os s s'(x : variable s)(c : contain S s)(a : AXs S Os (adjoin Xs _ x _ c) Os s')(b : AXs S Xs Os s'), Prop :=.

Variables are given meaning by substitution. If x is a variable of sort s, a ∈ A[X , x ] s 0 ,
and b ∈ A[X ] s , then [ b/x ] a ∈ A[X ] s 0 is defined to be the result of substituting b for
every occurrence of x in a. The ast a is called the target, and x is called the subject, of the
substitution. Substitution is defined by the following equations:
1. [ b/x ] x = b and [ b/x ] y = y if x 6 = y.
For example, we may check that
ew
2. [ b/x ] o(a 1 ; . . . ;a n ) = o( [ b/x ] a 1 ; . . . ; [ b/x ] a n ).
[ num[2]/x ] plus(x; num[3]) = plus(num[2]; num[3]).
We may prove by structural induction that substitution on ast’s is well-defined.
Theorem 1.1. If a ∈ A[X , x ] , then for every b ∈ A[X ] there exists a unique c ∈ A[X ] such that
[ b/x ] a = c