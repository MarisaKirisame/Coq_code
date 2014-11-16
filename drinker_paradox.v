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
    case(classic (forall c : People, InPub c p -> Drinks c)).
    eauto.
    intros.
    apply not_all_ex_not in H0.
    destruct H0.
    exists x0.
    tauto.
  Qed.
End drinker.
Print Assumptions drinker.
