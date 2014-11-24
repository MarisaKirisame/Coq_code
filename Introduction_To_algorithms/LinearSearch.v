Require Import List.

Set Implicit Arguments.

Fixpoint LinearSearch (A : Type)(l : list A)(f : A -> bool) : option nat := 
  match l with
  | nil => None
  | l_head :: l_tail =>
      match f l_head with
      | true => Some O
      | false => 
          match LinearSearch l_tail f with
          | None => None
          | Some n => Some (S n)
          end
      end
  end.