Goal forall T p (q : T -> T -> Prop) f x,
  p x -> 
    (forall x , p x -> exists y, q x y) ->
      (forall x y , q x y -> q y (f y)) -> 
        exists z , q z (f z).
  intros.
  destruct (H x);
  eauto.
Qed.