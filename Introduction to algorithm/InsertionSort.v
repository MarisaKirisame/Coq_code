Require Import List Arith Recdef.

Fixpoint Insertion(n : nat)(l : list nat) := 
  match l with
  | nil => n :: nil
  | l_head :: l_tail => 
      match lt_dec n l_head with
      | left _ => n :: l_head ::l_tail
      | right _ => l_head :: Insertion n l_tail
      end
  end.

Function InsertionSort(l : list nat) { measure length l } : list nat := l.