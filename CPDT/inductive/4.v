Require Import Bool Arith Omega.

Inductive nat_binop : Set :=
| Plus 
| Times.

Inductive bool_binop : Set := 
| Eq
| Lt.

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
  | Plus => plus
  | Times => mult
  end.

Definition bool_binop_denote(b:bool_binop)
  : nat -> nat -> bool:=
  match b with
  | Eq => beq_nat
  | Lt => leb
  end.

Fixpoint nat_exp_denote(f : nat -> nat )(e : nat_exp) : nat :=
  match e with
  | NConst n => n
  | NBinop b l r =>
      (nat_binop_denote b)
      (nat_exp_denote f l)
      (nat_exp_denote f r)
  | NVar n => f n
  | NCondition b l r => 
      if bool_exp_denote f b
      then nat_exp_denote f l
      else nat_exp_denote f r
  end
with bool_exp_denote(f : nat -> nat)(e : bool_exp) : bool :=
  match e with
  | BConst b => b
  | BBinop b l r => 
      (bool_binop_denote b)
      (nat_exp_denote f l)
      (nat_exp_denote f r)
  | BCondition b l r => 
      if bool_exp_denote f b
      then bool_exp_denote f l
      else bool_exp_denote f r
  end.

