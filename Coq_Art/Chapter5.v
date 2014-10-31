Lemma id_P : forall P:Prop, P -> P.
  intros.
  exact H.
Qed.

Lemma id_PP : forall P:Prop, (P -> P) -> P -> P.
  intros.
  assumption.
Qed.

Lemma imp_trans : forall P Q R :Prop, (P -> Q) -> (Q -> R) -> P -> R.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Lemma imp_perm :  forall P Q R :Prop, (P -> Q -> R) -> Q -> P -> R.
  intros.
  apply H;assumption.
Qed.

Lemma ignore_Q : forall P Q R :Prop, (P -> R) -> P -> Q -> R.
  intros.
  apply H.
  assumption.
Qed.

Lemma delta_imp :  forall P Q :Prop,(P -> P -> Q) -> P -> Q.
  intros.
  apply H;assumption.
Qed.
  
Lemma delta_impR :forall P Q :Prop, (P -> Q) -> P -> P -> Q.
  intros.
  apply H.
  apply H0.
Qed.

Lemma diamond : forall P Q R T:Prop, (P -> Q) -> 
                                  (P -> R) -> 
                                  (Q -> R -> T) -> 
                                  P -> T.
  intros.
  apply H1;[apply H|apply H0];assumption.
Qed.

Lemma weak_peirce : forall P Q:Prop, ((((P -> Q) -> P) -> P) -> Q) -> Q.
  intros.
  apply H.
  intros.
  apply H0.
  intros.
  apply H.
  intros.
  apply H1.
Qed.  