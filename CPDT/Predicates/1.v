Goal (True \/ False) /\ (False \/ True).
  constructor;
  [left|right];
  constructor.
Qed.

Goal forall P : Prop, P -> ~ ~P.
  unfold not.
  intros.
  apply H0.
  assumption.
Qed.

Goal forall P Q R, P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
  intros.
  destruct H.
  destruct H0;
  [left|right];
  constructor;
  assumption.
Qed.