Require Import List.

Set Implicit Arguments.

Inductive Tree : Set :=
| Root
| Branch : Tree -> Tree -> Tree.

Definition AllRoot(l : list Tree) := 
  forallb (fun e => match e with Root => true | _ => false end) l.

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

Ltac clean :=
  repeat (
    match goal with
    | h : ?x = ?x |- _ => clear h
    | h : Tree |- _ => clear h
    | _ => idtac end).
Ltac l T := assert(T = Root);[solve [trivial]|];clean;simpl in *.
Ltac get_goal := match goal with |- ?x => x end.
Ltac r T :=
  match get_goal with ?x => assert (exists T1 T2 : Tree, T = Branch T1 T2 /\ x) end;
  [
    econstructor;
    econstructor;
    (split;[solve [trivial]|])|
    simpl in *;
    repeat(
      match goal with
      | h : exists _, _ |- _ => destruct h
      | _ => idtac end);
    tauto
  ];
  clean;simpl in *.

Ltac dol :=
  match get_goal with
  | context f [match ?X with _ => _ end] => 
      is_evar X;assert(@eq Tree X X);[solve [trivial]|clean];l X
  end.

Ltac dor :=
  match get_goal with
  | context f [match ?X with _ => _ end] => 
      is_evar X;assert(@eq Tree X X);[solve [trivial]|clean];r X
  end.

Ltac act :=
  f_equal;(solve[trivial]+dol+dor(*+match get_goal with Branch _ _ = ?X => destruct X end*)).
Ltac work := repeat econstructor;simpl;solve [repeat act].

Definition Split(T : Tree) :
  { T1 : Tree &
    { T2 : Tree &
      { T3 : Tree &
        { T4 : Tree &
          { T5 : Tree &
            { T6 : Tree &
              { T7 : Tree | Combine T1 T2 T3 T4 T5 T6 T7 = T } } } } } } }.
  unfold Combine.
  destruct T.
  work.
  destruct T1.
  work.
  destruct T1_1.
  work.
  destruct T1_1_1.
  work.
  destruct T1_1_1_1.
  work.
  destruct T1_1_1_1_1.
  work.
  destruct T2, T1_2, T1_1_2, T1_1_1_2;
  work.
Defined.