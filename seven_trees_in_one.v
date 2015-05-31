Require Import List Tactic.

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

Ltac l T := unify T Root;simpl in *.

Ltac r T := 
  let lt := fresh in
    let rt := fresh in 
      evar (lt : Tree);evar (rt : Tree);unify T (Branch lt rt);simpl in *.

Ltac dol :=
  match get_goal with
  | context f [match ?X with _ => _ end] => l X
  end.

Ltac dor :=
  match get_goal with
  | context f [match ?X with _ => _ end] => r X
  end.

Ltac act := dol+dor.

Ltac work := unfold Combine_helper;repeat econstructor;simpl;solve [repeat (trivial;act)].

Definition box P NT (N : NT) : Type := P.
Inductive sandbox_closer : Prop := ms : sandbox_closer -> sandbox_closer.
Theorem sandbox_closer_exit : sandbox_closer -> False.
  induction 1;trivial.
Qed.

Arguments box : simpl never.

Ltac make_sandbox T N := 
  let f := fresh in
    evar (f : box T N);
    let g := get_goal in 
      let H := fresh in
        assert(sandbox_closer -> g) as H;[intro|clear H].

Ltac exit_sandbox := 
  exfalso;
  match goal with
  | X : sandbox_closer |- _ => apply sandbox_closer_exit in X;tauto
  end.

Ltac set_result N T := match goal with | _ := ?X : box _ N |- _ => unify X T end.

Ltac get_result N := match goal with | _ := ?X : box _ N |- _ => X end.

Ltac clear_result N := match goal with | H := _ : box _ N |- _ => clear H end.

Ltac get_destruct_next N := 
  unfold Combine_helper;
  repeat econstructor;
  simpl;
  repeat act;
  repeat f_equal;
  match goal with
  |- _ = ?X => is_var X;set_result N X
  end.

Ltac detect_destruct :=
  make_sandbox Tree tt;
  [get_destruct_next tt;exit_sandbox|];
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
  Unshelve.
  all:trivial.
Defined.

Definition Split(T : Tree) : Tree * Tree * Tree * Tree * Tree * Tree * Tree :=
  match Split_helper T with
  | existT _ T1 (existT _ T2 (existT _ T3 
      (existT _ T4 (existT _ T5 (existT _ T6 (exist _ T7 _)))))) => 
      (T1, T2, T3, T4, T5, T6, T7)
  end.

Goal forall t, Combine (Split t) = t.
  intros.
  unfold Split, Combine, Split_helper.
  repeat (match_type_destruct Tree;trivial).
Qed.

Goal forall t, Split (Combine t) = t.
  intros.
  destruct t as [[[[[[]]]]]].
  unfold Split.
  destruct Split_helper.
  destruct s as [? [? [? [? [? []]]]]].
  unfold Split, Combine, Split_helper, Combine_helper in *.
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