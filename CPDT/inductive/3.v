Require Import Omega.

Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
| Var : nat -> exp
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote(b:binop):nat->nat->nat:=
  match b with
  | Plus => plus
  | Times => mult
  end.

Fixpoint expDenote(f:nat->nat)(e:exp):nat:=
  match e with
  | Const n => n
  | Binop b e1 e2 =>
      (binopDenote b)
      (expDenote f e1)
      (expDenote f e2)
  | Var n => f n
  end.

Fixpoint fold(e : exp) : exp:=
  match e with
  | Binop b e1 e2 =>
      match fold e1, fold e2 with
      | Var l, Var r => Binop b (Var l) (Var r)
      | Const l, Const r => (Const (binopDenote b l r))
      | _, _ => e
      end
  | _ => e
  end.

Lemma binop_comm : forall b l r,binopDenote b l r = binopDenote b r l.
  destruct b.
  intros.
  simpl in *.
  omega.
  auto with *.
Qed.

Lemma binop_injec : forall b l n m, n = m -> 
  binopDenote b l n = binopDenote b l m.
  destruct b.
  auto.
  auto.
Qed.

Lemma optimize_correctness : forall (e:exp)(f:nat->nat),
  expDenote f e= expDenote f (fold e).
  intros.
  induction e.
  trivial.
  trivial.
  simpl in *.
  remember (fold e1) as fe1.
  remember (fold e2) as fe2.
  destruct fe1, fe2;
  simpl in *;
  auto.
Qed.