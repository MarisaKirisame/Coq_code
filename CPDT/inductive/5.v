Inductive odd : Set:=
| OS : even -> odd
with even : Set:=
| O
| ES : odd -> even.

Fixpoint eeplus(l r : even) : even :=
  match l with
  | O => r
  | ES o => ES (oeplus o r)
  end
with oeplus(o : odd)(e : even) : odd:=
  match o with
  | OS e' => OS (eeplus e' e)
  end.

Scheme even_mut := Induction for even Sort Prop
with odd_mut := Induction for odd Sort Prop.

Lemma eeplus_O : forall e, eeplus e O = e.
  intros.
  apply (even_mut (fun x => eeplus x O = x)(fun x => eeplus (ES x) O = (ES x))).
  trivial.
  trivial.
  intros.
  simpl in *.
  f_equal.
  f_equal.
  trivial.
Qed.

Lemma eeplus_extract_l : forall l r, eeplus (ES (OS l)) r = ES (OS (eeplus l r)).
  trivial.
Qed.

Lemma eeplus_injec : forall l r1 r2, (r1 = r2) -> (eeplus l r1 = eeplus l r2).
  intros.
  apply (even_mut(fun x => eeplus x r1 = eeplus x r2)(fun x => x = x));
  subst;
  trivial.
Qed.

Lemma eeplus_extract_r : forall l r, eeplus l (ES (OS r)) = ES (OS (eeplus l r)).
  intros.
  apply (even_mut
          (fun x => eeplus x (ES (OS r)) = ES (OS (eeplus x r)))
          (fun x => eeplus (ES x) (ES (OS r)) = ES (OS (eeplus (ES x) r)))).
  trivial.
  trivial.
  intros.
  simpl in *.
  f_equal.
  f_equal.
  trivial.
Qed.

Lemma eeplus_comm:forall l r,eeplus l r=eeplus r l.
  intros.
  apply (even_mut
          (fun x => eeplus x r = eeplus r x)
          (fun x => eeplus (ES x) r = eeplus r (ES x))).
  simpl in *.
  symmetry.
  eapply eeplus_O.
  trivial.
  intros.
  simpl in *.
  rewrite eeplus_extract_r.
  f_equal.
  f_equal.
  trivial.
Qed.