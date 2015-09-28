Require Export Eqdep.
Set Implicit Arguments.

Definition SET := forall T, T -> Prop.

Definition ContainSelf (S : SET) : Prop := S SET S.

Definition NotContainSelfSET : SET := 
  fun T r => (
    forall e : (T = SET), 
      eq_rect_r (fun T0 => T0 -> Prop) (fun s : SET => ~ ContainSelf s) e r).

Theorem NCSNCSS : ~ ContainSelf NotContainSelfSET.
  intro H; pose proof H as I.
  unfold ContainSelf in H.
  unfold NotContainSelfSET at 1 in H.
  specialize (H (eq_refl SET)); simpl in *.
  unfold eq_rect_r, eq_rect, eq_sym in *.
  exact (H I).
Qed.

Theorem NNCSNCSS : ~~ContainSelf NotContainSelfSET.
  unfold ContainSelf; intro H; apply H.
  unfold NotContainSelfSET at 1; intros.
  pose proof (UIP_refl _ _ e); subst.
  unfold eq_rect_r, eq_sym, eq_rect.
  assumption.
Qed.

Definition F : False := NNCSNCSS NCSNCSS.
