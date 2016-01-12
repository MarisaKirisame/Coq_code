Inductive SET := set T (F : T -> SET).
Definition T S := match S with set t _ => t end.
Definition F S : T S -> SET := match S with set _ f => f end.
Definition Contain L R : Prop := exists t : T L, F L t = R.
Definition NCSS : SET := set { s | ~~~Contain s s } (@proj1_sig _ _).
Definition NCSNCSS : ~~~Contain NCSS NCSS.
  intro H; apply H; intro C; destruct C as [[]]; simpl in *; subst; intuition.
Defined.
Definition CSNCSS : Contain NCSS NCSS := ex_intro _ (exist _ NCSS NCSNCSS) eq_refl.
Definition FALSE : False := NCSNCSS (fun x => x CSNCSS).