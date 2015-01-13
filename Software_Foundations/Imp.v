Require Import Arith Omega.

Set Implicit Arguments.

Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => leb (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Program Definition aremove_const (a:aexp) : {ret: aexp| aeval ret = aeval a} :=
  match a with
  | APlus a (ANum 0) | APlus (ANum 0) a => a
  | AMinus a (ANum 0) => a
  | AMult a (ANum 1) | AMult (ANum 1) a => a
  | AMult _ (ANum 0) | AMult (ANum 0) _ => ANum 0
  | default => default
  end.
  Next Obligation.
    omega.
  Defined.
  Next Obligation.
    ring.
  Defined.
  Solve All Obligations using intros;intuition;discriminate.

Fixpoint aoptimize_inner
  (optimize_func : forall a,{ret: aexp| aeval ret = aeval a})(a:aexp) { struct a } : aexp :=
  proj1_sig 
    (optimize_func
      match a with
      | ANum n => ANum n
      | APlus l r => 
          APlus 
            (aoptimize_inner optimize_func l)
            (aoptimize_inner optimize_func r)
      | AMinus l r => 
          AMinus
            (aoptimize_inner optimize_func l)
            (aoptimize_inner optimize_func r)
      | AMult l r => 
          AMult 
            (aoptimize_inner optimize_func l)
            (aoptimize_inner optimize_func r)
    end).

Program Definition aoptimize
  (optimize_func : forall a,{ret: aexp| aeval ret = aeval a})(a:aexp) :
    {ret | aeval ret = aeval a} := aoptimize_inner optimize_func a.
  Next Obligation.
    induction a;
    simpl in *;
    repeat
      match goal with
      |- context f [optimize_func ?X] => 
          destruct (optimize_func X)
      end;
      simpl in *;
    trivial;
    rewrite e;
    auto.
  Defined.

Fixpoint BConst(b : bool) := if b then BTrue else BFalse.

Program Definition bremove_const (b : bexp) : {ret: bexp| beval ret = beval b} :=
  match b with
  | BEq (ANum l) (ANum r) => BConst (beq_nat l r)
  | BLe (ANum l) (ANum r) => BConst (leb l r)
  | BAnd b BTrue | BAnd BTrue b => b
  | BNot BFalse => BTrue
  | BNot BTrue | BAnd _ BFalse | BAnd BFalse _ => BFalse
  | default => default
  end.
  Solve Obligations using
    intuition;
    match goal with
    |- context f [BConst ?X] => 
      destruct X eqn:H1
    end;
    simpl in *;
    auto.
  Solve Obligations using
    intros;
    subst;
    simpl in *;
    ring.
  Solve Obligations using
    intros;
    intuition;
    simpl in *;
    discriminate.

Fixpoint boptimize_inner aoptimize_func
    (boptimize_func : forall b, {b'|beval b' = beval b})
      (b : bexp) : bexp :=
  proj1_sig(boptimize_func
    match b with
    | BEq l r => 
        BEq
          (proj1_sig(aoptimize aoptimize_func l))
          (proj1_sig(aoptimize aoptimize_func r))  
    | BLe l r => 
        BLe
          (proj1_sig(aoptimize aoptimize_func l))
          (proj1_sig(aoptimize aoptimize_func r))
    | BNot b' => BNot (boptimize_inner aoptimize_func boptimize_func b')
    | BAnd l r => 
        BAnd
          (boptimize_inner aoptimize_func boptimize_func l)
          (boptimize_inner aoptimize_func boptimize_func r)
    | default => default
    end).

Program Definition boptimize aoptimize_func
  (boptimize_func : forall b, {b'|beval b' = beval b})
    (b : bexp) :
      {ret | beval ret = beval b} := boptimize_inner aoptimize_func boptimize_func b.
  Next Obligation.
    induction b;
    compute [boptimize_inner];
    repeat
      match goal with
      |- context f [boptimize_func ?X] => 
        destruct (boptimize_func X)
      end;
    trivial;
    repeat
      match goal with
      |- context f [aoptimize aoptimize_func ?X] => 
        destruct (aoptimize aoptimize_func X)
      end;
    simpl in *;
    eauto;
    simpl in *;
    repeat
      match goal with
      |- context f [boptimize_func ?X] => 
        destruct (boptimize_func X)
      end;
    trivial;
    simpl in *;
    rewrite e;
    f_equal;
    trivial.
  Defined.
