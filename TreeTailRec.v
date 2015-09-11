Require Export Arith List Program Omega Recdef MoreList.
Set Implicit Argumtnes.

Inductive T := Child (n : nat) | Branch (l r : T).

Definition Sum t : nat := T_rect (fun _ => nat) (@id nat) (fun _ l _ r => l + r) t.

Fixpoint SumClosure (t : T) (closure : (unit -> nat)) : nat :=
  match t with
  | Child n => n + closure tt
  | Branch l r => SumClosure l (fun _ => SumClosure r closure)
  end.

Goal forall t n, SumClosure t (fun _ => n) = Sum t + n.
  induction t; simpl in *; intuition.
  rewrite IHt2, IHt1; omega.
Qed.

Definition Size t : nat := T_rect (fun _ => nat) (fun _ => 1) (fun _ l _ r => (l + S r)) t.

Function SumStack (stack : list T) (acc : nat) 
  { measure (fun l => fold_left (fun l r => l + r) (map Size l) 0) stack } : nat :=
  match stack with
  | [] => acc
  | Child n :: s => SumStack s (n + acc)
  | Branch l r :: s => SumStack (l :: r :: s) acc
  end.
  all:intros; subst; simpl in *; change 1 with (0 + 1); rewrite !foldl_extract; intros; omega.
Defined.

Theorem SumStackSum l n : SumStack l n = n + fold_left (fun l r => l + r) (map Sum l) 0.
  eapply SumStack_ind; intros; subst; simpl in *; try omega.
  unfold id; change n0 with (0 + n0).
  rewrite foldl_extract by (intros; omega); simpl; omega.
Qed.

Theorem SumStackOne t : SumStack [t] 0 = Sum t.
  rewrite SumStackSum; trivial.
Qed.