Inductive SET := set T (F : T -> SET).
Definition Contain L R : Prop := match L with set _ f => exists t, f t = R end.
Definition NCSS : SET := set { s | ~~~Contain s s } (@proj1_sig _ _).
Definition NCSNCSS : ~~~Contain NCSS NCSS :=
  fun H => H ltac:(destruct 1 as [[]]; simpl in *; subst; intuition).
Definition CSNCSS : Contain NCSS NCSS := ex_intro _ (exist _ NCSS NCSNCSS) eq_refl.
Definition FALSE : False := NCSNCSS (fun x => x CSNCSS).
