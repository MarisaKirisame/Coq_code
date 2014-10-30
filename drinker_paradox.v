Section drinker.
Require Import Classical Setoid.
  Variable Pubs People : Set.
  Variables InPub : People -> Pubs -> Prop.
  Variables Drinks : People -> Prop.
  Lemma drinker: forall p:Pubs, (exists a:People , InPub a p) 
         -> exists b:People, InPub b p /\ 
            (Drinks b -> forall c:People, InPub c p -> Drinks c).
    intros.
    destruct H.
    assert((forall c : People, InPub c p -> Drinks c)\/
           ~(forall c : People, InPub c p -> Drinks c)).
    apply classic.
    destruct H0.
    exists x.
    split.
    assumption.
    intros.
    apply H0.
    assumption.
    simpl in *.
    assert(exists b:People, InPub b p/\ ~ Drinks b).
    Focus 2.
    destruct H1.
    exists x0.
    destruct H1.
    split.
    assumption.
    congruence.
    assert((exists c : People, ~(InPub c p -> Drinks c))).
    apply not_all_ex_not.
    assumption.
    destruct H1.
    assert(InPub x0 p /\ ~ Drinks x0).
    apply imply_to_and.
    assumption.
    exists x0.
    assumption.
  Qed.
End drinker.
Print Assumptions drinker.