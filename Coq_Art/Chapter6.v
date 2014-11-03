Inductive season : Set := Spring | Summer | Fall | Winter.

Theorem bool_equal : forall (b:bool), b=true\/b=false.
  apply bool_ind;
  [apply or_introl|apply or_intror];
  apply refl_equal.
Qed.

Inductive month : Set := 
  January|
  February|
  March|
  April|
  May|
  June|
  July|
  August|
  September|
  October|
  November|
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

Definition season_of_month' m :=
  match m with
  | January => Winter
  | February => Winter
  | March => Winter
  | April => Spring
  | May => Spring
  | June => Spring
  | July => Summer
  | August => Summer
  | September => Summer
  | October => Winter
  | November => Winter
  | December => Winter
  end.

Definition bool_not( b : bool ) := if b then false else true.
Definition bool_or( l r : bool ) := if l then true else r.
Definition bool_and( l r : bool ) := if l then r else false.
Definition bool_eq( l r : bool ) := if l then r else bool_not r.
Definition bool_xor( l r : bool ) := bool_not (bool_eq l r).

Theorem bool_xor_not_eq : 
  forall b1 b2 : bool, (bool_xor b1 b2) = (bool_not (bool_eq b1 b2)).
  trivial.
Qed.

Theorem bool_not_and : 
  forall b1 b2 : bool,
    (bool_not (bool_and b1 b2)) =
    (bool_or (bool_not b1) (bool_not b2)).
  case b1, b2;auto.
Qed.

Theorem bool_not_not : forall b : bool, (bool_not (bool_not b))=b.
  intros.
  case b;auto.
Qed.

Theorem bool_tex : forall b : bool, (bool_or b (bool_not b))=true.
  intros.
  case b;auto.
Qed.

Theorem bool_eq_reflect : forall b1 b2 : bool, (bool_eq b1 b2)=true -> b1=b2.
  intros.
  case b1, b2;auto.
Qed.

Theorem bool_eq_reflect2 : forall b1 b2 : bool, 
  b1 = b2 ->
    (bool_eq b1 b2) = true.
  intros.
  case b1, b2;auto.
Qed.

Theorem bool_not_or : forall b1 b2 : bool,
  (bool_not (bool_or b1 b2)) = (bool_and (bool_not b1) (bool_not b2)).
  intros.
  case b1, b2;auto.
Qed.

Theorem bool_distr:  forall b1 b2 b3:bool,
  (bool_or (bool_and b1 b3) (bool_and b2 b3)) = (bool_and (bool_or b1 b2) b3).
  intros.
  case b1, b2, b3;auto.
Qed.

Require Import ZArith.

Record plane : Set := point {abscissa : Z; ordinate : Z}.

Definition absolute p :=
  match p with
  | Z0 => Z0
  | Zneg x => Zpos x
  | Zpos x => Zneg x
  end.

Open Scope Z_scope.

Definition manhatten l r := 
  absolute ((abscissa l) - (abscissa r)) + 
  absolute ((ordinate l) - (ordinate r)).

Close Scope Z_scope.

Inductive vehicle : Set :=
  bicycle : nat -> vehicle|
  motorized : nat -> nat -> vehicle.

Definition number_of_seats v : nat :=
  vehicle_rec (fun _ => nat) (fun x => x) (fun x _ => x) v.
