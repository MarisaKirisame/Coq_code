Inductive Tree : Set :=
| Root
| Branch : Tree -> Tree -> Tree.

Require Import List.

Fixpoint AllRoot(l : list Tree) :=
  match l with
  | nil => true
  | l_head :: l_tail =>
      match l_head with
      | Root => AllRoot l_tail
      | Branch _ _ => false
      end
  end.

Definition Combine(T1 T2 T3 T4 T5 T6 T7 : Tree) : Tree :=
  match AllRoot (T1 :: T2 :: T3 :: T4 :: nil) with
  | false => (Branch (Branch (Branch (Branch (Branch (Branch T7 T6) T5) T4) T3) T2) T1)
  | true => 
      match T5 with
      | Branch T5a T5b => (Branch (Branch (Branch (Branch Root T7) T6) T5a) T5b)
      | Root => 
          match T6 with
          | Branch _ _ => (Branch (Branch (Branch (Branch (Branch T6 T7) Root) Root) Root) Root)
          | Root => 
              match T7 with
              | (Branch (Branch (Branch (Branch T7a T7b) T7c) T7d) T7e) =>
                  (Branch (Branch (Branch (Branch (Branch Root T7a) T7b) T7c) T7d) T7e)
              | _ => T7
              end
          end
      end
  end.

Definition Split(T : Tree) :
  { T1 : Tree & 
    { T2 : Tree & 
      { T3 : Tree &
        { T4 : Tree & 
          { T5 : Tree & 
            { T6 : Tree &
              { T7 : Tree | Combine T1 T2 T3 T4 T5 T6 T7 = T } } } } } } }.
  destruct T.
  do 7 (exists Root).
  trivial.
  destruct T1.
  do 6 (exists Root).
  exists (Branch Root T2).
  trivial.
  destruct T1_1.
  do 6 (exists Root).
  exists (Branch (Branch Root T1_2) T2).
  trivial.
  destruct T1_1_1.
  do 6 (exists Root).
  exists (Branch (Branch (Branch Root T1_1_2) T1_2) T2).
  trivial.
  destruct T1_1_1_1.
  do 4 (exists Root).
  exists (Branch T1_2 T2).
  exists T1_1_2.
  exists T1_1_1_2.
  trivial.
  destruct T1_1_1_1_1.
  do 6 (exists Root).
  exists (Branch (Branch (Branch (Branch T1_1_1_1_2 T1_1_1_2) T1_1_2) T1_2) T2).
  trivial.
  destruct T1_1_1_2.
  destruct T1_1_2.
  destruct T1_2.
  destruct T2.
  do 5 (exists Root).
  exists (Branch T1_1_1_1_1_1 T1_1_1_1_1_2).
  exists T1_1_1_1_2.
  trivial.
  exists (Branch T2_1 T2_2).
  do 3 (exists Root).
  exists T1_1_1_1_2.
  exists T1_1_1_1_1_2.
  exists T1_1_1_1_1_1.
  trivial.
  exists T2.
  exists (Branch T1_2_1 T1_2_2).
  do 2 (exists Root).
  exists T1_1_1_1_2.
  exists T1_1_1_1_1_2.
  exists T1_1_1_1_1_1.
  destruct T2;
  trivial.
  exists T2.
  exists T1_2.
  exists (Branch T1_1_2_1 T1_1_2_2).
  exists Root.
  exists T1_1_1_1_2.
  exists T1_1_1_1_1_2.
  exists T1_1_1_1_1_1.
  destruct T2, T1_2;
  trivial.
  exists T2.
  exists T1_2.
  exists T1_1_2.
  exists (Branch T1_1_1_2_1 T1_1_1_2_2).
  exists T1_1_1_1_2.
  exists T1_1_1_1_1_2.
  exists T1_1_1_1_1_1.
  destruct T2, T1_2, T1_1_2; trivial.
Defined.

Goal forall T1 T2 T3 T4 T5 T6 T7 : Tree, 
  match Split (Combine T1 T2 T3 T4 T5 T6 T7) with
  | existT T1' (existT T2' (existT T3' (existT T4' (existT T5' (existT T6' (exist T7' _)))))) => 
      T1 = T1' /\ T2 = T2' /\ T3 = T3' /\ T4 = T4' /\ T5 = T5' /\ T6 = T6' /\ T7 = T7'
  end.
  intros.
  destruct T1, T2, T3, T4, T5, T6, T7;
  simpl;
  try tauto.
  refine(
    match T7_1 with
    | (Branch (Branch (Branch (Branch _ _) _) _) _) => _
    | _ => _
    end);
  simpl;
  tauto.
Qed.