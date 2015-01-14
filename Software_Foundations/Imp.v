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

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum : forall(n: nat),
    aevalR (ANum n) n
| E_APlus : forall(e1 e2: aexp) (n1 n2: nat),
    aevalR e1 n1 ->
      aevalR e2 n2 ->
        aevalR (APlus e1 e2) (n1 + n2)
| E_AMinus: forall(e1 e2: aexp) (n1 n2: nat),
    aevalR e1 n1 ->
      aevalR e2 n2 ->
        aevalR (AMinus e1 e2) (n1 - n2)
| E_AMult : forall(e1 e2: aexp) (n1 n2: nat),
    aevalR e1 n1 ->
      aevalR e2 n2 ->
        aevalR (AMult e1 e2) (n1 * n2).

Inductive bevalR : bexp -> bool -> Prop :=
| E_BTrue : bevalR BTrue true
| E_BFalse : bevalR BFalse false
| E_BEq : forall a1 a2 n1 n2,
    aevalR a1 n1 -> 
      aevalR a2 n2 -> 
        bevalR (BEq a1 a2) (beq_nat n1 n2)
| E_BLe : forall a1 a2 n1 n2,
    aevalR a1 n1 -> 
      aevalR a2 n2 -> 
        bevalR (BLe a1 a2) (leb n1 n2)
| E_BNot : forall b bo, 
    bevalR b bo ->
      bevalR (BNot b) (negb bo)
| E_BAnd : forall b1 b2 bo1 bo2,
    bevalR b1 bo1 -> 
      bevalR b2 bo2 ->
        bevalR (BAnd b1 b2) (andb bo1 bo2).

Theorem aevalR_correct : forall a n, aevalR a n <-> aeval a = n.
  split.
  induction 1;
  subst;
  trivial.
  intros.
  generalize dependent n.
  induction a;
  intros;
  subst;
  simpl in *;
  constructor;
  auto.
Qed.

Theorem bevalR_correct : forall b bo, bevalR b bo <-> beval b = bo.
  intuition.
  induction H;
  simpl in *;
  subst;
  trivial;
  f_equal;
  apply aevalR_correct;
  trivial.
  generalize dependent bo.
  induction b;
  intros;
  subst;
  simpl in *;
  constructor;
  auto;
  apply aevalR_correct;
  trivial.
Qed.

Inductive id : Type := Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
  intros.
  destruct id1, id2.
  destruct (eq_nat_dec n n0).
  subst.
  tauto.
  right.
  intuition.
  inversion H.
  tauto.
Defined.

Lemma eq_id : forall(T:Type) x (p q:T), (if eq_id_dec x x then p else q) = p.
  intros.
  destruct (eq_id_dec x x);
  tauto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if eq_id_dec x y then p else q) = q.
  intros.
  destruct (eq_id_dec x y);
  tauto.
Qed.

Definition state := id -> nat.

Definition empty_state : state := fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

Theorem update_eq : forall n x st,
  (update st x n) x = n.
  intros.
  unfold update.
  apply eq_id.
Qed.

Theorem update_neq : forall x2 x1 n st, x2 <> x1 ->
  (update st x2 n) x1 = (st x1).
  intros.
  unfold update.
  apply neq_id.
  trivial.
Qed.

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
  trivial.
Qed.

Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
  (update (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
  intros.
  unfold update.
  destruct (eq_id_dec x2 x1);
  trivial.
Qed.

Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
    (update st x1 n1) x2 = st x2.
  intros.
  subst.
  unfold update.
  destruct (eq_id_dec x1 x2);
  subst;
  trivial.
Qed.

Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 ->
    (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
  intros.
  unfold update.
  destruct (eq_id_dec x1 x3).
  subst.
  symmetry.
  apply neq_id.
  trivial.
  trivial.
Qed.