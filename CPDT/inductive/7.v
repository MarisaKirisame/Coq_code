Require Import Omega.

Set Implicit Arguments.

Inductive btree A :=
| bleaf : A -> btree A
| bnode : btree A -> btree A -> btree A.

Inductive trexp :=
| tnode : nat -> trexp
| tleaf : btree trexp -> trexp.

Fixpoint total t :=
  match t with
  | tnode n => n
  | tleaf bt => 
      (fix btree_total b := 
      match b with
      | bleaf t => total t
      | bnode l r => btree_total l + btree_total r
      end) bt
  end.

Fixpoint btree_total b :=
  match b with
  | bleaf t => total t
  | bnode l r => btree_total l + btree_total r
  end.

Fixpoint trexp_rect_mut
  (P : trexp -> Type)
  (P0 : btree trexp -> Type)
  (f : forall n, P (tnode n))
  (f0 : forall t , P0 t -> P (tleaf t))
  (f1 : forall b, P b -> P0 (bleaf b))
  (f2 : forall bl br, P0 bl -> P0 br -> P0 (bnode bl br))
  (t : trexp) : P t :=
  match t with
  | tnode n => f n
  | tleaf b =>
      f0
      b
      ((fix btree_rect_mut b : P0 b := 
        match b with
        | bleaf t => f1 t (trexp_rect_mut P P0 f f0 f1 f2 t)
        | bnode l r => f2 l r (btree_rect_mut l) (btree_rect_mut r)
        end) b)
  end.

Fixpoint increment t :=
  match t with
  | tnode n => tnode (S n)
  | tleaf bt =>
      tleaf
      ((fix btree_increment b :=
      match b with
      | bleaf t => bleaf (increment t)
      | bnode l r => bnode (btree_increment l) (btree_increment r)
      end) bt)
  end.

Fixpoint btree_increment b :=
  match b with
  | bleaf t => bleaf (increment t)
  | bnode l r => bnode (btree_increment l) (btree_increment r)
  end.

Goal forall t, total t <= total (increment t).
  intros.
  apply
    (trexp_rect_mut
      (fun x => total x <= total (increment x))
      (fun x => btree_total x <= btree_total (btree_increment x)));
  auto with *.
  intros.
  simpl in *.
  omega.
Qed.
