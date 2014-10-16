Require Import Bool Arith.
Add LoadPath "../../".
Load CpdtTactics.
Inductive nat_binop : Set :=| TPlus | TTimes.
Inductive bool_binop : Set := | TEq | TLt.
Inductive nat_exp : Set :=
| NVar : nat -> nat_exp
| NConst : nat -> nat_exp
| NBinop : nat_binop -> nat_exp -> nat_exp -> nat_exp
| NCondition : bool_exp -> nat_exp -> nat_exp -> nat_exp
with bool_exp : Set :=
| BConst : bool -> bool_exp
| BBinop : bool_binop -> nat_exp -> nat_exp -> bool_exp
| BCondition : bool_exp -> bool_exp -> bool_exp -> bool_exp.
Definition nat_binop_denote(b : nat_binop)
  : nat -> nat -> nat :=
  match b with
  | TPlus => plus
  | TTimes => mult
  end.
Definition bool_binop_denote(b:bool_binop)
  : nat -> nat -> bool:=
  match b with
  | TEq => beq_nat
  | TLt => leb
  end.
Fixpoint nat_exp_denote(f:nat->nat)(e : nat_exp) : nat :=
  match e with
  | NConst n => n
  | NBinop b l r  => (nat_binop_denote b) (nat_exp_denote f l) (nat_exp_denote f r)
  | NVar n => f n
  | NCondition b l r => if bool_exp_denote f b then nat_exp_denote f l else nat_exp_denote f r
  end
with bool_exp_denote(f:nat->nat)(e:bool_exp):bool:=
  match e with
  | BConst b => b
  | BBinop b l r => (bool_binop_denote b) (nat_exp_denote f l) (nat_exp_denote f r)
  | BCondition b l r => if bool_exp_denote f b then bool_exp_denote f l else bool_exp_denote f r
  end.
Inductive folded_exp : Set :=
| FVar : nat -> folded_exp
| FConst : nat -> folded_exp
| FBinop : nat_binop -> noconst -> folded_exp -> folded_exp
| FCondition : bool_exp -> folded_exp -> folded_exp -> folded_exp
with noconst:Set:=
| NCVar : nat -> noconst
| NCBinop: nat_binop -> noconst -> folded_exp -> noconst
| NCCondition : bool_exp -> folded_exp -> folded_exp -> noconst.
Fixpoint fold(e:nat_exp):folded_exp:=
  match e with
  | NConst n => FConst n 
  | NBinop b e1 e2 =>
      match fold e1 with
      | FVar n => FBinop b (NCVar n) (fold e2)
      | FConst l => 
          match fold e2 with
          | FVar n => FBinop b (NCVar n)(FConst l)
          | FConst r => FConst ((nat_binop_denote b)l r)
          | FBinop bi nc fo => FBinop b (NCBinop bi nc fo) (FConst l)
          | FCondition b' t' f' => FBinop b (NCCondition b' t' f')(FConst l)
          end
      | FBinop bi nc fo => FBinop b (NCBinop bi nc fo) (fold e2)
      | FCondition b' t' f' => FCondition b' t' f'
      end
  | NVar n => FVar n
  | NCondition b' t' f' => FCondition b' (fold t') (fold f')
  end.
Fixpoint folded_exp_denote(f:nat->nat)(e:folded_exp):nat:=
  match e with
  | FConst n => n
  | FBinop b e1 e2 =>
      nat_exp_denote
        f
        (NBinop 
          b
          (NConst (noconst_denote f e1))
          (NConst(folded_exp_denote f e2)))
  | FVar n => f n
  | FCondition b' t' f' => if bool_exp_denote f b' then folded_exp_denote f t' else folded_exp_denote f f'
  end
with noconst_denote(f:nat->nat)(e:noconst):nat:=
  match e with
  | NCVar n => f n
  | NCBinop b nc fo => 
      (nat_binop_denote b)(noconst_denote f nc)(folded_exp_denote f fo)
  | NCCondition b' t' f' => if bool_exp_denote f b' then folded_exp_denote f t' else folded_exp_denote f f'
  end.
Scheme folded_exp_mut:=Induction for folded_exp Sort Prop
with noconst_list_mut:=Induction for noconst Sort Prop.
Lemma nat_binop_comm:forall b l r,nat_binop_denote b l r = nat_binop_denote b r l.
  destruct b;crush.
Qed.
Lemma nat_binop_injec:forall b l n m,n=m->nat_binop_denote b l n = nat_binop_denote b l m.
  destruct b;crush.
Qed.
