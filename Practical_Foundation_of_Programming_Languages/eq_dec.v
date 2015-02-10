Definition eq_dec T := forall l r : T, { l = r } + { l <> r }.

Ltac dedec dec H :=
  match goal with
  | X : _ |- ?Y => 
      match Y with 
        context f [dec ?l ?r] => destruct (dec l r); H
      end
  | X : _ |- _ => 
      match type of X with
      | context [dec ?l ?r] =>
          destruct (dec l r);
          H
      end
  end.
