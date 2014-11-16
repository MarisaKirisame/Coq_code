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

Section update_def.
  Variables (A : Set) (A_eq_dec : forall (x y : A),  ({ x = y }) + ({ x <> y })).
  Variables (B : A ->  Set) (a : A) (v : B a) (f : forall (x : A),  B x).
  Definition update (x : A) : B x :=
    match A_eq_dec a x with
    | left h => eq_rec a B v x h
    | right h' => f x
    end.
End update_def.

Require Import Eqdep.

Theorem update_eq:
 forall (A : Set) (eq_dec : forall (x y : A),  ({ x = y }) + ({ x <> y }))
        (B : A ->  Set) (a : A) (v : B a) (f : forall (x : A),  B x),
  update eq_dec B a v f a = v.
  unfold update.
  intros.
  case (eq_dec a a).
  intuition.
  rewrite <- eq_rect_eq.
  trivial.
  tauto.
Qed.

Inductive ltree (A:Set) : Set :=
  lnode : A -> list (ltree A)-> ltree A.

Section correct_ltree_ind.
  Variables
    (A : Set)(P : ltree A -> Prop)(Q : list (ltree A)-> Prop).
  Hypotheses
    (H : forall (a:A)(l:list (ltree A)), Q l -> P (@lnode A a l))
    (H0 : Q nil)
    (H1 : forall t:ltree A, P t ->
    forall l:list (ltree A), Q l -> Q (cons t l)).
  Fixpoint ltree_ind2 (t:ltree A) : P t :=
    match t as x return P x with
    | lnode a l =>
        @H
          a
          l
          (((fix l_ind (l':list (ltree A)) : Q l' :=
            match l' as x return Q x with
            | nil => H0
            | cons t1 tl => @H1 t1 (ltree_ind2 t1) tl (l_ind tl)
            end)) l)
          end.
  Fixpoint ltree_ind3 (l : list (ltree A)) : Q l.
    destruct l.
    trivial.
    apply H1.
    apply ltree_ind2.
    apply ltree_ind3.
  Defined.
End correct_ltree_ind.

Fixpoint lcount (A : Set)(t : ltree A){ struct t } : nat :=
  match t with
  | lnode n l => 
      S 
      ((fix list_rec (l' : list (ltree A)) :=
        match l' with
        | nil => 0
        | l'_head :: l'_tail => (lcount l'_head) + (list_rec l'_tail)
        end) l)
  end.

Inductive ntree (A:Set) : Set :=
  nnode : A -> nforest A -> ntree A
with nforest (A:Set) : Set :=
  nnil : nforest A | ncons : ntree A -> nforest A -> nforest A.

Fixpoint ntree_to_ltree (A : Set)(t : ntree A) := 
  match t with
  | nnode n f => lnode n (nforest_to_lltree f)
  end
with nforest_to_lltree (A : Set)(n : nforest A) := 
  match n with
  | nnil => nil
  | ncons t f => (ntree_to_ltree t) :: (nforest_to_lltree f)
  end.

Fixpoint ltree_to_ntree (A : Set)(t : ltree A) :=
  match t with
  | lnode n l => 
      nnode
      n
      ((fix list_rec (l' : list (ltree A)) :=
        match l' with
        | nil => @nnil A
        | l'_head :: l'_tail => ncons (ltree_to_ntree l'_head) (list_rec l'_tail)
        end) l)
  end.

Fixpoint lltree_to_nforest (A : Set)(l : list (ltree A)) := 
  match l with
  | nil => @nnil A
  | l_head :: l_tail => ncons (ltree_to_ntree l_head) (lltree_to_nforest l_tail)
  end.

Scheme ntree_ind2 :=
  Induction for ntree Sort Prop
with nforest_ind2 :=
  Induction for nforest Sort Prop.

Goal forall A n, ltree_to_ntree (@ntree_to_ltree A n) = n.
  intros.
  einduction n using ntree_ind2.
  Focus 2.
  instantiate( 1 :=
    (fun n => (lltree_to_nforest (nforest_to_lltree n)) = n)).
  intuition.
  intuition.
  simpl.
  f_equal.
  rewrite <- IHn0 at 2.
  remember(nforest_to_lltree n0).
  generalize l.
  induction l0.
  trivial.
  simpl in *.
  f_equal.
  trivial.
  intuition.
  simpl in *.
  f_equal.
  trivial.
  trivial.
Qed.

Goal forall A n, ntree_to_ltree (@ltree_to_ntree A n) = n.
  intros.
  einduction n using ltree_ind2.
  Focus 2.
  instantiate( 1 :=
    (fun n => (nforest_to_lltree (lltree_to_nforest n)) = n)).
  intuition.
  intuition.
  simpl in *.
  f_equal.
  generalize l.
  einduction l0 using ltree_ind3.
  instantiate( 1 :=
    (fun n => (ntree_to_ltree (ltree_to_ntree n)) = n)).
  intuition.
  simpl in *.
  f_equal.
  trivial.
  trivial.
  intuition.
  simpl in *.
  f_equal.
  trivial.
  trivial.
  intuition.
  simpl in *.
  f_equal.
  trivial.
  trivial.
Qed.