Section simple_proof.
  Variable P Q R S : Prop.
  Lemma id_P : P -> P.
    intros.
    assumption.
  Qed.
  Lemma id_PP : (P->P)->(P->P).
    intros.
    assumption.
  Qed.
  Lemma imp_trans : (P->Q)->(Q->R)->P->R.
    intros.
    apply H0.
    apply H.
    assumption.
  Qed.
  Lemma imp_perm : (P->Q->R)->(Q->P->R).
    intros.
    apply H.
    assumption.
    assumption.
  Qed.
  Lemma ignore_Q : (P->R)->P->Q->R.
    intros.
    apply H.
    assumption.
  Qed.
  Lemma delta_imp  : (P->P->Q)->P->Q.
    intros.
    apply H;assumption.
  Qed.
  Lemma delta_impR : (P->Q)->(P->P->Q).
    intros.
    apply H.
    assumption.
  Qed.
  Lemma diamond : (P->Q)->(P->R)->(Q->R->S)->P->S.
    intros.
    apply H1;try apply H;try apply H0;assumption.
  Qed.
  Lemma weak_peirce : ((((P->Q)->P)->P)->Q)->Q.
    intros.
    apply H.
    intros.
    apply H0.
    intros.
    apply H.
    intros.
    assumption.
  Qed.
End simple_proof.
Section cut.
  Variables P Q R T : Prop.
  Hypothesis H : P -> Q.
  Hypothesis H0 : Q -> R. 
  Hypothesis H1 : (P -> R) -> T -> Q.
  Hypothesis H2 : (P -> R) -> T.
  Lemma cut : Q.
    apply H1;intros;try apply H2;intros;try apply H0;try apply H;assumption.
  Qed.
  Lemma cut' : Q.
    cut (P -> R).
    intros;cut T;intros;try apply H1;try apply H2;assumption.
    intros;try apply H0;try apply H;try assumption.
  Qed.
  Lemma cut'' : Q.
    assert(P -> R).
    intros.
    apply H0.
    apply H.
    assumption.
    apply H1.
    assumption.
    apply H2.
    assumption.
  Qed.
End cut.
Section auto.
  Variables A B C D E F : Prop.
  Hypothesis H : A -> B.
  Hypothesis H' : B -> C.
  Hypothesis H'' : C -> D.
  Hypothesis H''' : D -> E.
  Hypothesis H'''' : E -> F.
  Lemma auto : A -> F.
    auto 6.
  Qed.
End auto.
