Require Import List.
Require Import ZArith.
Open Scope Z_scope.
Inductive sorted : list Z -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall z:Z, sorted (z :: nil)
  | sorted2 :
      forall (z1 z2:Z) (l:list Z),
        z1 <= z2 ->
        sorted (z2 :: l) -> sorted (z1 :: z2 :: l).
Hint Resolve sorted0 sorted1 sorted2 : sort.
Theorem sorted_inv :
  forall (z:Z) (l:list Z), sorted (z :: l) -> sorted l.
  intros z l H.
  inversion H.
  constructor.
  assumption.
Qed.
Fixpoint nb_occ (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') =>
      match Z_eq_dec z z' with
      | left _ => S (nb_occ z l')
      | right _ => nb_occ z l'
      end
  end.
Definition equiv (l l':list Z) := forall z:Z, nb_occ z l = nb_occ z l'.
Lemma equiv_refl : forall l:list Z, equiv l l.
 unfold equiv.
 trivial.
Qed.
Lemma equiv_sym : forall l l':list Z, equiv l l' -> equiv l' l.
  unfold equiv.
  auto.
Qed.
Lemma equiv_trans :
 forall l l' l'':list Z,
   equiv l l' -> 
     equiv l' l'' -> 
       equiv l l''.
  intros l l' l'' H H0 z.
  eapply trans_eq.
  apply H.
  apply H0.
Qed.
Lemma equiv_cons :
 forall (z:Z) (l l':list Z),
   equiv l l' -> 
     equiv (z :: l) (z :: l').
  intros.
  intros z'.
  simpl.
  case (Z_eq_dec z' z);intros.
  try f_equal.
  apply H.
  apply H.
Qed.
Lemma equiv_perm :
 forall (a b:Z) (l l':list Z),
   equiv l l' -> 
     equiv (a :: b :: l) (b :: a :: l').
  intros a b l l' H z; simpl.
  case (Z_eq_dec z a); case (Z_eq_dec z b); 
  simpl; case (H z);intros;apply eq_refl.
Qed.
Hint Resolve equiv_cons equiv_refl equiv_perm : sort.
Fixpoint aux (z:Z) (l:list Z) {struct l} : list Z :=
  match l with
  | nil => z :: nil
  | cons a l' =>
      match Z_le_gt_dec z a with
      | left _ =>  z :: a :: l'
      | right _ => a :: (aux z l')
      end
  end.
Lemma aux_equiv : forall (l:list Z) (x:Z), 
                    equiv (x :: l) (aux x l).
  induction l as [|a l0 H].
  unfold equiv.
  reflexivity.
  simpl.
  intros x.
  case (Z_le_gt_dec x a);simpl;intros.
  apply equiv_refl.
  intros.
  apply equiv_trans with (a :: x :: l0).
  apply equiv_perm.
  apply equiv_refl.
  apply equiv_cons.
  apply H.
Qed.
Lemma aux_sorted :
  forall (l:list Z) (x:Z), sorted l -> sorted (aux x l).
  intros l x H; elim H; simpl.
  apply sorted1.
  intro z; case (Z_le_gt_dec x z); simpl; 
  auto with sort zarith.
  intros z1 z2; case (Z_le_gt_dec x z2); simpl; intros;
  case (Z_le_gt_dec x z1); simpl; auto with sort zarith.
Qed.
Definition sort :
    forall l:list Z, {l' : list Z | equiv l l' /\ sorted l'}.
  induction l as [| a l IHl]. 
  exists (nil (A:=Z)); split; auto with sort.
  case IHl; intros l' [H0 H1].
  exists (aux a l').
  split.
  apply equiv_trans with (a :: l'); auto with sort.
  apply aux_equiv.
  apply aux_sorted; auto.
Defined.