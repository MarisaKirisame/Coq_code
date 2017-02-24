Set Implicit Arguments.
Set Universe Polymorphism.

Definition equaliff T (l r : T) : Prop :=
  forall (P : T -> Prop), P l <-> P r.
Definition equalimpl T (l r : T) : Prop :=
  forall (P : T -> Prop), P l -> P r.

Theorem equaliff_refl T (l : T) : equaliff l l.
  unfold equaliff; intuition.
Qed.

Theorem equaliff_sym T (l r : T) : equaliff l r -> equaliff r l.
  unfold equaliff; intuition; specialize(H P); intuition.
Qed.

Theorem equaliff_trans T (l m r : T) : equaliff l m -> equaliff m r -> equaliff l r.
  unfold equaliff; intuition; specialize (H P); specialize (H0 P); intuition.
Qed.

Goal forall T (l r : T), equaliff l r -> equalimpl l r.
  unfold equaliff, equalimpl; intuition; specialize(H P); intuition.
Qed.

Goal forall T (l r : T), equalimpl l r -> equaliff l r.
  unfold equaliff, equalimpl; intuition.
  + apply H; trivial.
  + specialize(H (fun t => P t -> P l)); intuition.
Qed.

Goal forall T (l r : T), equaliff l r <-> l = r.
  intuition; subst; try apply equaliff_refl; [].
  unfold equaliff in *; specialize (H (fun x => r = x)); intuition.
Qed.