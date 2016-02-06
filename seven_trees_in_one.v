Require Import CoqUtil.Tactic.
Set Implicit Arguments.

Inductive Tree :=
| Empty
| Node : Tree -> Tree -> Tree.

Notation "[ a , b ]" := (Node a b).
Notation "0" := Empty.

Definition Combine_helper (T1 T2 T3 T4 T5 T6 T7 : Tree) : Tree :=
  match (T1, T2, T3, T4) with
  | (0, 0, 0, 0) => 
      match T5 with
      | Node T5a T5b => [[[[0, T7], T6], T5a], T5b]
      | 0 => 
          match T6 with
          | Node _ _ => [[[[[T6, T7], 0], 0], 0], 0]
          | 0 => 
              match T7 with
              | [[[[T7a, T7b], T7c], T7d], T7e] =>
                  [[[[[0, T7a], T7b], T7c], T7d], T7e]
              | _ => T7
              end
          end
      end
  | _ => [[[[[[T7, T6], T5], T4], T3], T2], T1]
  end.

Definition Combine X := 
  match X with (t1, t2, t3, t4, t5, t6, t7) => Combine_helper t1 t2 t3 t4 t5 t6 t7 end.

Ltac l T := unify T Empty; simpl in *.

Ltac r T := 
  let lt := fresh in
  let rt := fresh in 
  evar (lt : Tree); evar (rt : Tree); unify T (Node lt rt); simpl in *.

Ltac act := let res := get_match ltac:get_goal ltac:(fun x => x) in l res + r res.

Ltac prepare_work := repeat econstructor; compute.

Ltac work := 
  prepare_work;
  solve [repeat (trivial; compute; act)].

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
  intros; unfold Split, Combine.
  destruct Split_helper as [? [? [? [? [? [? []]]]]]]; subst.
  simpl in *; trivial.
Qed.

Goal forall t, Split (Combine t) = t.
  intros.
  destruct t as [[[[[[]]]]]].
  unfold Split; destruct Split_helper as [? [? [? [? [? [? []]]]]]].
  unfold Combine, Combine_helper in *.
  repeat (
    simpl in *;
    trivial;
    match_type_destruct Tree||
    discriminate||
    match goal with
    | H : _ = _ : Tree |- _ => invcs H
    end||
    subst).
Qed.