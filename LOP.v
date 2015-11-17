Require Export Bool CoqCore.Tactic Program.
Record LOP := 
{ 
  IsTrue : bool; 
  IsFalse : bool;
  HasTruth : IsTrue || IsFalse = true
}.

Program Definition lnot l := 
{| 
  IsTrue := IsFalse l;
  IsFalse := IsTrue l;
  HasTruth := $(destruct l; simpl; repeat (match_destruct||compute in *); congruence)$
|}.

Program Definition lor l r := 
{| 
  IsTrue := IsTrue l || IsTrue r;
  IsFalse := IsFalse l && IsFalse r;
  HasTruth := $(destruct l; simpl; repeat (match_destruct||compute in *); congruence)$
|}.

Section ISO.
  Variable Var : Type.
  Definition VB := Var -> bool.
  Definition VL := Var -> LOP.
  Definition liff l r := (IsTrue l = IsTrue r) /\ (IsFalse l = IsFalse r).
  Infix "<-->" := liff (at level 60).
  Inductive NOC := N (noc : NOC) | O (l r : NOC) | C (v : Var).
  Fixpoint NOCBool noc (vb : VB) :=
    match noc with
    | N noc => negb (NOCBool noc vb)
    | O l r => NOCBool l vb || NOCBool r vb
    | C v => vb v
    end.
  Fixpoint NOCLOP noc (vl : VL) :=
    match noc with
    | N noc => lnot (NOCLOP noc vl)
    | O l r => lor (NOCLOP l vl) (NOCLOP r vl)
    | C v => vl v
    end.
  Goal forall l vb vl, (forall v, vb v = IsTrue (vl v)) -> NOCBool l vb = IsTrue (NOCLOP l vl).
    intros; induction l; simpl in *.
    erewrite IHl.
    Focus 3.
    repeat (
      match_destruct || 
      apply LOPFEQ ||
      DestructPremise ||
      match goal with
      | H : {| IsTrue := _ |} = {| IsTrue := _ |} |- _ => invcs H
      end ||
      simpl in *; ii; subst;
      unfold lnot, lor, or_ind, liff, negb, orb in *;
      try congruence).
    specialize(H (C v)); simpl in *.
End ISO.
