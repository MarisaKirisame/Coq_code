Require Import Bool Arith.
Load CpdtTactics.
Inductive I : Type := s : I.
Inductive O : Type := .
Inductive Prod(A B:Type):Type:=pair(_:A)(_:B).
Inductive Sum(A B:Type):Type:=inl(_:A)|inr(_:B).
Definition f(sum:Sum I O):I:=
  match sum with
    | inl _ => s
    | inr _ => s
  end.
Definition g(i:I):Sum I O:=
  match i with
    | s => (inl O)i
  end.
Theorem iso:forall i : I, f(g(i))=i.
  intro.
  destruct i.
  reflexivity.
Qed.
Definition pf T(pro:Prod O T):O:=
  match pro with 
    | pair o _ => o
  end.
Definition pg T(o:O):Prod O T:=
  match o with end.
Lemma prod_O_1 : forall(A:Type)(pro:Prod O A),pg A(pf pro) = pro.
  intros.
  destruct pro.
  destruct o.
Qed.