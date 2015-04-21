Require Import List.

Set Implicit Arguments.

Inductive Tree : Set :=
| Root
| Branch : Tree -> Tree -> Tree.

Definition AllRoot(l : list Tree) := 
  forallb (fun e => match e with Root => true | _ => false end) l.

Definition Combine_helper(T1 T2 T3 T4 T5 T6 T7 : Tree) : Tree :=
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

Definition Combine := 
  (prod_curry(prod_curry(prod_curry(prod_curry(prod_curry(prod_curry Combine_helper)))))).

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
      clean;l X
  end.

Ltac dor :=
  match get_goal with
  | context f [match ?X with _ => _ end] => 
      clean;r X
  end.

Ltac act := solve[trivial]+dol+dor.
Ltac work := unfold Combine_helper;repeat econstructor;simpl;solve [repeat act].

Definition Split_helper(T : Tree) :
  { T1 : Tree &
    { T2 : Tree &
      { T3 : Tree &
        { T4 : Tree &
          { T5 : Tree &
            { T6 : Tree &
              { T7 : Tree | Combine_helper T1 T2 T3 T4 T5 T6 T7 = T } } } } } } }.
  destruct T;
  [|destruct T1;
    [|destruct T1_1;[|
        destruct T1_1_1;[|
          destruct T1_1_1_1;[|
            destruct T1_1_1_1_1;
            [|destruct T2, T1_2, T1_1_2, T1_1_1_2 ]]]]]];
  work.
Defined.

Definition Split(T : Tree) : Tree * Tree * Tree * Tree * Tree * Tree * Tree :=
  match Split_helper T with
  | existT _ T1 (existT _ T2 (existT _ T3 
      (existT _ T4 (existT _ T5 (existT _ T6 (exist _ T7 _)))))) => 
      (T1, T2, T3, T4, T5, T6, T7)
  end.