Require Import List CoqCore.Tactic.

Set Implicit Arguments.

Inductive Tree :=
| Empty
| Node : Tree -> Tree -> Tree.

Definition IsEmpty T :=
  match T with
  | Empty => true
  | Node _ _ => false
  end.

Definition Combine_helper(T1 T2 T3 T4 T5 T6 T7 : Tree) : Tree :=
  match forallb IsEmpty (T1 :: T2 :: T3 :: T4 :: nil) with
  | false => (Node (Node (Node (Node (Node (Node T7 T6) T5) T4) T3) T2) T1)
  | true => 
      match T5 with
      | Node T5a T5b => (Node (Node (Node (Node Empty T7) T6) T5a) T5b)
      | Empty => 
          match T6 with
          | Node _ _ => (Node (Node (Node (Node (Node T6 T7) Empty) Empty) Empty) Empty)
          | Empty => 
              match T7 with
              | (Node (Node (Node (Node T7a T7b) T7c) T7d) T7e) =>
                  (Node (Node (Node (Node (Node Empty T7a) T7b) T7c) T7d) T7e)
              | _ => T7
              end
          end
      end
  end.

Definition Combine := 
  prod_curry(prod_curry(prod_curry(prod_curry(prod_curry(prod_curry Combine_helper))))).

Ltac l T := unify T Empty; simpl in *.

Ltac r T := 
  let lt := fresh in
    let rt := fresh in 
      evar (lt : Tree); evar (rt : Tree); unify T (Node lt rt); simpl in *.

Ltac dol := let g := get_goal in let F := (fun x => l x) in get_match g F.
Ltac dor := let g := get_goal in let F := (fun x => r x) in get_match g F.

Ltac act := unfold andb; dol + dor.

Ltac prepare_work := unfold Combine_helper, IsEmpty; simpl; repeat econstructor.

Ltac work := 
  prepare_work;
  solve [repeat (trivial; act)].

Ltac get_destruct_next N := 
  prepare_work;
  repeat act; repeat f_equal;
  match goal with
  |- _ = ?X => is_var X; set_result N X
  end.

Ltac detect_destruct :=
  make_sandbox Tree tt;
  [
    get_destruct_next tt;
    repeat match get_goal with context [?t] => is_evar t; l t end;
    exit_sandbox|
  ];
  let ret := get_result tt in destruct ret;
  clear_result tt.

Definition Split_helper(T : Tree) :
  { T1 : Tree &
    { T2 : Tree &
      { T3 : Tree &
        { T4 : Tree &
          { T5 : Tree &
            { T6 : Tree &
              { T7 : Tree | Combine_helper T1 T2 T3 T4 T5 T6 T7 = T } } } } } } }.
  repeat (work||detect_destruct).
Defined.

Definition Split(T : Tree) : Tree * Tree * Tree * Tree * Tree * Tree * Tree :=
  match Split_helper T with
  | existT _ T1 (existT _ T2 (existT _ T3 
      (existT _ T4 (existT _ T5 (existT _ T6 (exist _ T7 _)))))) => 
      (T1, T2, T3, T4, T5, T6, T7)
  end.

Goal forall t, Combine (Split t) = t.
  intros; unfold Split, Combine, Split_helper, prod_curry.
  repeat (match_type_destruct Tree; trivial).
Qed.

Goal forall t, Split (Combine t) = t.
  intros.
  destruct t as [[[[[[]]]]]].
  unfold Split.
  destruct Split_helper.
  destruct s as [? [? [? [? [? []]]]]].
  unfold Split, Combine, Split_helper, Combine_helper in *.
  repeat (
    unfold andb, IsEmpty in *;
    simpl in *;
    trivial;
    match_type_destruct Tree||
    discriminate||
    match goal with
    | H : _ = _ : Tree |- _ => invcs H
    end||
    subst).
Qed.