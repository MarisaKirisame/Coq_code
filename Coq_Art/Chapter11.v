Set Implicit Arguments.
Unset Strict Implicit.

Require Import misc.
Require Export ZArith.
Open Scope Z_scope.

Inductive Z_btree : Set :=
| Z_leaf : Z_btree
| Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Inductive occ (n:Z) : Z_btree -> Prop :=
| occ_root : forall t1 t2:Z_btree, occ n (Z_bnode n t1 t2)
| occ_l : forall (p:Z) (t1 t2:Z_btree), occ n t1 -> occ n (Z_bnode p t1 t2)
| occ_r : forall (p:Z) (t1 t2:Z_btree), occ n t2 -> occ n (Z_bnode p t1 t2).

Inductive min (z:Z) (t:Z_btree) : Prop :=
  min_intro : (forall z':Z, occ z' t -> z < z') -> min z t.

Inductive maj (z:Z) (t:Z_btree) : Prop :=
  maj_intro : (forall z':Z, occ z' t -> z' < z) -> maj z t.

Inductive min' (z:Z) : Z_btree -> Prop :=
| min'_leaf : min' z Z_leaf
| min'_bnode : forall z' l r ,
      min' z l -> 
        min' z r -> 
          z < z' ->
            min' z (Z_bnode z' l r).

Inductive maj' (z:Z) : Z_btree -> Prop :=
| maj'_leaf : maj' z Z_leaf
| maj'_bnode : forall z' l r ,
      maj' z l -> 
        maj' z r -> 
          z > z' ->
            maj' z (Z_bnode z' l r).

Inductive search_tree : Z_btree -> Prop :=
| leaf_search_tree : search_tree Z_leaf
| bnode_search_tree :
    forall (z:Z) (t1 t2:Z_btree),
      search_tree t1 ->
        search_tree t2 ->
          maj z t1 -> min z t2 -> search_tree (Z_bnode z t1 t2).

Definition sch_tree : Set := sig search_tree.

Inductive INSERT (n:Z) (t t':Z_btree) : Prop :=
    insert_intro :
      (forall p:Z, occ p t -> occ p t') ->
      occ n t' ->
      (forall p:Z, occ p t' -> occ p t \/ n = p) ->
      search_tree t' -> INSERT n t t'.

Definition insert_spec (n:Z) (t:Z_btree) : Set :=
  search_tree t -> {t' : Z_btree | INSERT n t t'}.

Definition sch_insert_spec (n:Z)(t:sch_tree) :=
  { t' : sch_tree | let (tt,tt') := ((sig_extract _ _ t),(sig_extract _ _ t')) in INSERT n tt tt' }.

Inductive RMAX (t t':Z_btree) (n:Z) : Prop :=
    rmax_intro :
      occ n t ->
      (forall p:Z, occ p t -> p <= n) ->
      (forall q:Z, occ q t' -> occ q t) ->
      (forall q:Z, occ q t -> occ q t' \/ n = q) ->
      ~ occ n t' -> search_tree t' -> RMAX t t' n.

Inductive RM (n:Z) (t t':Z_btree) : Prop :=
    rm_intro :
      ~ occ n t' ->
      (forall p:Z, occ p t' -> occ p t) ->
      (forall p:Z, occ p t -> occ p t' \/ n = p) ->
      search_tree t' -> RM n t t' .

Definition rm_spec (n:Z) (t:Z_btree) : Set :=
  search_tree t -> {t' : Z_btree | RM n t t'}.

Definition sch_rm_spec (n:Z) (t:sch_tree) : Set :=
{ t' : sch_tree | let (tt, tt') := (sig_extract _ _ t, sig_extract _ _ t') in RM n tt tt' }.

