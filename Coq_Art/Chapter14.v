Set Implicit Arguments.
Require Import Arith.

Definition plus'(l r:nat) : nat :=
  nat_rec (fun _ => nat) r (fun _ => fun x => S x) l.

Definition pred_partial: forall (n : nat), n <> 0 ->  nat.
  intros n; case n.
  intros h; elim h; reflexivity.
  intros p h'; exact p.
Defined.

Theorem le_2_n_not_zero: forall (n : nat), 2 <= n ->  (n <> 0).
  intros n Hle; elim Hle; intros; discriminate.
Qed.

Scheme le_ind_max := Induction for le Sort Prop.

Theorem le_2_n_pred:
  forall (n : nat) (h : 2 <= n),  (pred_partial (le_2_n_not_zero h) <> 0).
  apply le_ind_max.
  intuition.
  simpl in *.
  inversion H.
  intuition.
  simpl in *.
  subst.
  inversion l.
Qed.

Require Import List.

Inductive lfactor (A:Set) : list A -> list A -> Prop :=
  lf1 : forall u:list A, lfactor nil u
| lf2 : forall (a:A) (u v:list A), lfactor u v ->
          lfactor (a :: u) (a :: v).

Fixpoint rfactor (A:Set) (u v:list A) { struct u } : 
  lfactor u v -> {w : list A | v = u ++ w}.
  refine(
    match u,v with
    | nil, nil => _
    | nil, ev :: lv => _
    | eu :: lu, nil => _
    | eu :: lu, ev :: lv => _
    end);simpl in *.
  econstructor.
  reflexivity.
  econstructor.
  reflexivity.
  intros.
  econstructor.
  instantiate( 1 := nil).
  inversion H.
  intros.
  assert({w : list A | lv = lu ++ w}).
  apply rfactor.
  inversion H.
  trivial.
  destruct H0.
  subst.
  assert(eu=ev).
  inversion H.
  trivial.
  subst.
  econstructor.
  reflexivity.
Qed.
  

