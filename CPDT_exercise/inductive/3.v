Add LoadPath "../../".
Load CpdtTactics.
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
Inductive folded_exp : Set :=
| FVar : nat -> folded_exp
| FConst : nat -> folded_exp
| FBinop : binop -> noconst -> folded_exp -> folded_exp
with noconst:Set:=
| NCVar : nat -> noconst
| NCBinop: binop -> noconst -> folded_exp -> noconst.
Fixpoint fold(e:exp):folded_exp:=
  match e with
  | Const n => FConst n 
  | Var n => FVar n
  | Binop b e1 e2 =>
      match fold e1 with
      | FVar n => FBinop b (NCVar n) (fold e2)
      | FConst l => 
          match fold e2 with
          | FVar n => FBinop b (NCVar n)(FConst l)
          | FConst r => FConst ((binopDenote b)l r)
          | FBinop bi nc fo => FBinop b (NCBinop bi nc fo) (FConst l)
          end
      | FBinop bi nc fo => FBinop b (NCBinop bi nc fo) (fold e2)
      end
  end.
Fixpoint folded_exp_denote(f:nat->nat)(e:folded_exp):nat:=
  match e with
  | FConst n => n
  | FBinop b e1 e2 =>
      expDenote
        f
        (Binop 
          b
          (Const (noconst_denote f e1))
          (Const(folded_exp_denote f e2)))
  | FVar n => f n
  end
with noconst_denote(f:nat->nat)(e:noconst):nat:=
  match e with
  | NCVar n => f n
  | NCBinop b nc fo => 
      (binopDenote b)(noconst_denote f nc)(folded_exp_denote f fo)
  end.
Scheme folded_exp_mut:=Induction for folded_exp Sort Prop
with noconst_list_mut:=Induction for noconst Sort Prop.
Lemma binop_comm:forall b l r,binopDenote b l r = binopDenote b r l.
  destruct b;crush.
Qed.
Lemma binop_injec:forall b l n m,n=m->binopDenote b l n = binopDenote b l m.
  destruct b;crush.
Qed.
Lemma optimize_correctness:forall (e:exp)(f:nat->nat),
  expDenote f e=folded_exp_denote f (fold e).
  intros.
  induction e.
  crush.
  crush.
  simpl expDenote.
  rewrite IHe1.
  rewrite IHe2.
  crush.
  remember (fold e1).
  remember (fold e2).
  induction f0.
  crush.
  induction f1.
  crush.
  apply binop_comm.
  crush.
  crush.
  apply binop_comm.
  apply binop_injec.
  crush.
Qed.