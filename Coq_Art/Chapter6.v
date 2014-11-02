Inductive season : Set := Spring | Summer | Fall | Winter.

Theorem bool_equal : forall (b:bool), b=true\/b=false.
  apply bool_ind;
  [apply or_introl|apply or_intror];
  apply refl_equal.
Qed.

Inductive month : Set := 
  January |
  February |
  March |
  April |
  May |
  June |
  July |
  August |
  September |
  October |
  November |
  December.

Check month_rec.

Definition season_of_month m :=
  (month_rec 
    (fun _:month => season) 
    Winter
    Winter
    Winter
    Spring
    Spring
    Spring
    Summer
    Summer
    Summer
    Fall
    Fall
    Fall) m.

Eval compute in season_of_month February.
