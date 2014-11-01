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

Section A_declared.
  Variables 
    (A : Set )
    (P Q : A->Prop)
    (R : A->A->Prop).
  Goal (forall a b:A, R a b) -> forall a b:A, R b a.
    intros.
    apply H.
  Qed.
  Goal (forall a:A, P a -> Q a) -> (forall a:A, P a) -> forall a:A, Q a.
    intros.
    apply H.
    apply H0.
  Qed.
  Goal (forall a b:A, R a b) -> forall a:A, R a a.
    intros.
    apply H.
  Qed.
End A_declared.

Goal forall P:Prop, ~ ~ ~ P -> ~ P.
  intros.
  unfold not.
  intros.
  apply H.
  unfold not.
  intros.
  apply H1.
  assumption.
Qed.

Goal forall P Q:Prop, ~ ~ ~ P -> P -> Q.
  unfold not.
  intros.
  elim H.
  intros.
  apply H1.
  assumption.
Qed.

Goal forall P Q:Prop, (P -> Q) -> ~ Q -> ~ P.
  unfold not.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Goal forall P Q R:Prop, (P -> Q) -> (P -> ~ Q) -> P -> R.
  unfold not.
  intros.
  elim H0;[|apply H];assumption.
Qed.

Definition dyslexic_imp := forall P Q:Prop, (P->Q)->Q->P.

Definition dyslexic_contrap :=forall P Q:Prop,(P->Q)->~P->~Q.

Goal dyslexic_imp -> False.
  unfold dyslexic_imp.
  intros.
  apply (H False True);trivial.
Qed.

Goal dyslexic_contrap -> False.
  unfold dyslexic_contrap.
  intros.
  apply (H False True);unfold not;trivial.
Qed.

Theorem abcd_c : forall (A:Set)(a b c d:A), a=c \/ b= c \/ c=c \/ d=c.
  intros.
  right.
  right.
  left.
  reflexivity.
Qed.

Lemma and_assoc : forall A B C:Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
  intros.
  apply and_assoc.
  assumption.
Qed.

Lemma and_imp_dist : forall A B C D:Prop,
                     (A -> B) /\ (C -> D) -> A /\ C -> B /\ D.
  intros.
  destruct H.
  destruct H0.
  split;[apply H|apply H1];assumption.
Qed.

Lemma not_contrad : forall A : Prop, ~(A /\ ~A).
  unfold not.
  intros.
  destruct H.
  apply H0.
  apply H.
Qed.

Lemma or_and_not : forall A B : Prop, (A\/B)/\~A -> B.
  unfold not.
  intros.
  destruct H.
  destruct H;[elim H0|];apply H.
Qed.

Definition peirce := forall P Q:Prop, ((P->Q)->P)->P.
Definition classic := forall P:Prop, ~~P -> P.
Definition excluded_middle := forall P:Prop, P\/~P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P/\~Q)->P\/Q.
Definition implies_to_or := forall P Q:Prop, (P->Q)->(~P\/Q).

Ltac first_step := 
       try unfold peirce;
       try unfold classic;
       try unfold excluded_middle;
       try unfold de_morgan_not_and_not;
       try unfold implies_to_or;
       try unfold not;
       split;
       intros.

Goal peirce <-> classic.
  first_step.
  apply(H P False);intros;elim H0;assumption.
  apply H.
  intros.
  apply H1.
  apply H0.
  intros.
  apply H.
  intros.
  apply H1.
  assumption.
Qed.

Goal classic <-> excluded_middle.
  first_step;
  [
    apply H;
    apply H;
    intros;
    apply H0;
    intros;
    apply H1;
    right;
    intros;
    apply H1;
    left;
    unfold not|

    assert(P \/ (P -> False));
    [
      apply H|
    
      destruct H1;
      [|elim H0]
    ]
  ];assumption.
Qed.

Goal excluded_middle <-> de_morgan_not_and_not.
  first_step;
  [
    destruct (H P);
    [
      left|
      
      right;
      destruct (H Q);
      [|
        elim H0;
        split
      ] 
    ]|
    
    apply H;
    intros;
    destruct H0;
    apply H1
  ];assumption.
Qed.

Goal de_morgan_not_and_not <-> implies_to_or.
  first_step;
  [
    apply H;
    intros;
    destruct H1;
    apply H1;
    intros;
    apply H2;
    apply H0|

    assert(~~P \/ ~~Q);
    [
      unfold not;
      apply H;
      intros;
      destruct H0;
      split|

      assert((~P\/P)/\(~Q\/Q));
      [
        split;
        apply H;
        intros|
        
        destruct H1;
        [left|right];
        destruct H2;
        [destruct H2|destruct H3];
        try assumption;
        elim H1
      ]
    ]
  ];
  assumption.
Qed.

Section on_ex. 
  Variables 
    (A:Type)
    (P Q:A -> Prop).
  Lemma ex_or : (exists x:A, P x \/ Q x) -> ex P \/ ex Q.
    intros;
    destruct H;
    destruct H;
    [left|right];
    exists x;
    assumption.
  Qed.
  
  Lemma ex_or_R : ex P \/ ex Q -> (exists x:A, P x \/ Q x).
    intros;
    destruct H;
    destruct H;
    exists x;
    [left|right];
    assumption.
  Qed.
  
  Lemma two_is_three : (exists x:A, forall R : A->Prop, R x) -> 2 = 3.
    intros;
    destruct H;
    apply( H (fun _ => _ = 3) ).
  Qed.

  Lemma forall_no_ex : (forall x:A, P x) -> ~(exists y:A, ~ P y).
    intros;
    unfold not;
    intros;
    destruct H0;
    apply H0;
    apply H.
  Qed.
End on_ex.
  