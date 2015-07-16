Require Export List Program Arith Omega MoreList.
Export Nat.
Set Implicit Arguments.
Inductive letter := M | I | U.
Inductive Generatable { init } : list letter -> Prop := 
| Init : Generatable init
| Rule1 : forall l, Generatable (l ++ [I]) -> Generatable (l ++ [I;U])
| Rule2 : forall l, Generatable (M :: l) -> Generatable (M :: l ++ l)
| Rule3 : forall l r, Generatable (l ++ I :: I :: I :: r) -> Generatable (l ++ U :: r)
| Rule4 : forall l r, Generatable (l ++ U :: U :: r) -> Generatable (l ++ r).
Arguments Generatable : clear implicits.
Arguments Init : clear implicits.
Hint Constructors Generatable letter.
Theorem Rule1' i l r : l = r ++ [I;U] -> Generatable i (r ++ [I]) -> Generatable i l.
  intros;subst;auto.
Qed.
Theorem Rule2' i l r : l = M :: r ++ r -> Generatable i (M :: r) -> Generatable i l.
  intros;subst;auto.
Qed.
Theorem Rule3' i li l r : li = l ++ U :: r -> 
  Generatable i (l ++ I :: I :: I :: r) -> Generatable i li.
  intros;subst;auto.
Qed.
Theorem Rule4' i li l r : li = l ++ r -> 
  Generatable i (l ++ U :: U :: r) -> Generatable i li.
  intros;subst;auto.
Qed.
Goal Generatable [M;I;U] [M;I;U;I;U].
  eapply Rule2';eauto;eauto.
Qed.
Goal Generatable [M;U;M] [M;U;M;U;M].
  eapply Rule2';eauto;eauto.
Qed.
Goal Generatable [M;U] [M;U;U].
  eapply Rule2';eauto;eauto.
Qed.
Goal Generatable [U;M;I;I;I;M;U] [U;M;U;M;U].
  eapply Rule3' with (l := [U;M])(r := [M;U]);eauto.
Qed.
Goal Generatable [M;I;I;I;I] [M;I;U].
  eapply Rule3' with (l := [M;I])(r := []);eauto.
Qed.
Goal Generatable [M;I;I;I;I] [M;U;I].
  eapply Rule3' with (l := [M])(r := [I]);eauto.
Qed.
Goal Generatable [M;I;I;I] [M;U].
  eapply Rule3' with (l := [M])(r := []);eauto.
Qed.
Goal Generatable [U;U;U] [U].
  eapply Rule4' with (l := [U])(r := []);eauto.
Qed.
Goal Generatable [M;U;U;U;I;I;I] [M;U;I;I;I].
  eapply Rule4' with (l := [M;U])(r := [I;I;I]);eauto.
Qed.
Theorem gen_non_div_three l : Generatable [M;I] l -> 
  ~ divide 3 (fold_left (fun (n : nat) e => match e with M => 0 | I => 1 | U => 3 end + n) l 0).
  induction 1;
  unfold divide in *;
  repeat (rewrite !fold_left_app in *||simpl in *);
  intuition;
  match goal with H : exists _, _ |- _ => destruct H end;
  omega||apply IHGeneratable.
  destruct x;omega||exists x;omega.
  erewrite (foldl_identity ((fun (n : nat) (e : letter) => match e with
                                              | M => 0
                                              | I => 1
                                              | U => 3
                                              end + n))) in H0.
Admitted.
Goal ~ Generatable [M;I] [M;U].
  intuition;apply gen_non_div_three in H.
  simpl in *;intuition.
Qed.