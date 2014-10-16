Add LoadPath "../../".
Load CpdtTactics.
Inductive odd:Set:=
| OS : even -> odd
with even : Set:=
| O
| ES : odd -> even.
Fixpoint eeplus(l r:even):even:=
  match l with
  | O => r
  | ES o => ES (oeplus o r)
  end
with oeplus(o:odd)(e:even):odd:=
  match o with
  | OS e' => OS (eeplus e' e)
  end.
Scheme even_mut:=Induction for even Sort Prop
with odd_mut:=Induction for odd Sort Prop.
Lemma eeplus_O:forall e,eeplus e O = e.
  intros.
  apply (even_mut(fun x=>eeplus x O = x)(fun x=>eeplus (ES x) O = (ES x))).
  crush.
  crush.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.
Lemma eeplus_extract_l:forall l r,eeplus (ES(OS l)) r=ES(OS(eeplus l r)).
  crush.
Qed.
Lemma eeplus_injec:forall l r1 r2,(r1 = r2)->(eeplus l r1 = eeplus l r2).
  intros.
  apply (even_mut(fun x=>eeplus x r1 = eeplus x r2)(fun x=>x=x));crush.
Qed.
Lemma eeplus_extract_r:forall l r,eeplus l (ES(OS r))=ES(OS(eeplus l r)).
  intros.
  apply (even_mut
          (fun x=>eeplus x (ES (OS r)) = ES (OS (eeplus x r)))
          (fun x=>eeplus (ES x) (ES (OS r)) = ES (OS (eeplus (ES x) r))));crush.
Qed.
Lemma eeplus_comm:forall l r,eeplus l r=eeplus r l.
  intros.
  Check even_mut.
  apply (even_mut(fun x=>eeplus x r=eeplus r x)(fun x=>eeplus (ES x) r = eeplus r (ES x))).
  crush.
  apply (even_mut(fun x=>x=eeplus x O)(fun x=>ES x=eeplus (ES x) O)).
  crush.
  crush.
  crush.
  crush.
  intros.
  rewrite eeplus_extract_r.
  crush.
Qed.
