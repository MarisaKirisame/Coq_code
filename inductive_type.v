Inductive truth:Set:=Yes|No|Maybe.
Definition not(b:truth):truth:=
  match b with
  | Yes => No
  | No => Yes
  | Maybe => Maybe
  end.
Definition and(l r:truth):truth:=
  match l with
  | Yes => r
  | No => No
  | Maybe => 
      match r with
      | Yes => Maybe
      | No => No
      | Maybe => Maybe
      end
  end.
Definition or(l r:truth):truth:=not(and(not l)(not r)).
Lemma and_commutative:forall a b,and a b = and b a.
  destruct a,b;reflexivity.
Qed.
Lemma and_distributive:forall a b c, and a (or b c)=or(and a b)(and a c).
  destruct a,b,c;reflexivity.
Qed.
Require Import List.
Inductive slist(T:Set):Set:=
| Nil:slist T
| Single:T->slist T
| Concat:slist T->slist T->slist T.
Fixpoint flattern(S:Set)(sl:slist S):list S:=
  match sl with
  | Nil => nil
  | Single s => cons s nil
  | Concat l r => flattern S l ++ flattern S r
  end.
Lemma flattern_distributive:forall a b c, flattern a b ++ flattern a c = flattern a (Concat a b c).
  reflexivity.
Qed.
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
    | s => ((inl I)O)i
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
Lemma prod_O_1 : forall(A:Type)(pro:Prod O A),pg A(pf A pro) = pro.
  intros.
  destruct pro.
  destruct o.
Qed.