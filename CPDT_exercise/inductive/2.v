Require Import List.
Set Implicit Arguments.
Inductive slist(T:Set):Set:=
| Nil:slist T
| Single:T->slist T
| Concat:slist T->slist T->slist T.
Fixpoint flattern(S:Set)(sl:slist S):list S:=
  match sl with
  | Nil => nil
  | Single s => cons s nil
  | Concat l r => flattern l ++ flattern r
  end.
Lemma flattern_distributive:forall (a:Set)(b:slist a)c,
  flattern b ++ flattern c = flattern (Concat b c).
  reflexivity.
Qed.