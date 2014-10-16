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