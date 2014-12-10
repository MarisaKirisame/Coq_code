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
  | Lt => NPeano.ltb
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

Fixpoint nat_exp_fold(e : nat_exp) :=
  match e with
  | NBinop b e1 e2 =>
      match nat_exp_fold e1, nat_exp_fold e2 with
      | NConst l, NConst r => NConst (nat_binop_denote b l r)
      | e1, e2 => NBinop b e1 e2
      end
  | NCondition b e1 e2 => 
      match bool_exp_fold b with
      | BConst true => nat_exp_fold e1
      | BConst false => nat_exp_fold e2
      | b => NCondition b (nat_exp_fold e1) (nat_exp_fold e2)
      end
  | _ => e
  end
with bool_exp_fold(b : bool_exp) :=
  match b with
  | BBinop b e1 e2 => 
      match nat_exp_fold e1, nat_exp_fold e2 with
      | NConst l, NConst r => BConst (bool_binop_denote b l r)
      | e1, e2 => BBinop b e1 e2
      end
  | BCondition b e1 e2 =>
      match bool_exp_fold b with
      | BConst true => bool_exp_fold e1
      | BConst false => bool_exp_fold e2
      | b => BCondition b (bool_exp_fold e1) (bool_exp_fold e2)
      end
  | _ => b
  end.

Scheme nat_exp_scheme :=  Induction for nat_exp Sort Prop
with bool_exp_scheme := Induction for bool_exp Sort Prop.

Theorem fold_correct : forall e f,
  nat_exp_denote f e = nat_exp_denote f (nat_exp_fold e).
  intros.
  eapply(
    nat_exp_scheme
    (fun e => nat_exp_denote f e = nat_exp_denote f (nat_exp_fold e))
    (fun e => bool_exp_denote f e = bool_exp_denote f (bool_exp_fold e)));
  intros;
  repeat rewrite H;
  repeat rewrite H0;
  repeat rewrite H1;
  trivial;
  simpl in *;
  intros.
  remember (nat_exp_fold n0) as e0.
  destruct e0;
  simpl in *;
  auto.
  remember (nat_exp_fold n1) as e1.
  destruct e1;
  subst;
  simpl in *;
  auto.
  rewrite H, H0, H1.
  remember (bool_exp_fold b) as eb.
  destruct eb;
  simpl in *;
  auto.
  destruct b0;
  trivial.
  remember (nat_exp_fold n) as ne.
  destruct ne;
  trivial.
  eauto.
  simpl in *.
  remember (nat_exp_fold n0) as ne.
  destruct ne;
  subst;
  eauto.
  eauto.
  eauto.
  remember (bool_exp_fold b) as be.
  remember (bool_exp_denote f b) as bo.
  destruct be, bo;
  simpl in *;
  try rewrite <- H;
  trivial.
Qed.