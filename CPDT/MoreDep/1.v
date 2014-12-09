Require Import List Recdef.

Set Implicit Arguments.

Inductive plist (P : nat -> Prop) : nat -> Set :=
| pnil : plist P 0
| ptcons : forall n m, P m -> plist P n -> plist P (S n)
| pfcons : forall n, nat -> plist P n -> plist P n.

Fixpoint papp
  (P : nat -> Prop)(n m : nat)(l : plist P n)(r : plist P m) :
    plist P (n + m) :=
      match l with
      | pnil => r
      | ptcons _ lm lp ll => ptcons lm lp (papp ll r)
      | pfcons _ ln ll => pfcons ln (papp ll r)
      end.

Fixpoint plistOut (P : nat -> Prop)(n : nat)(l : plist P n) : list nat :=
  match l with
  | pnil => nil
  | ptcons _ lm _ ll => lm :: plistOut ll
  | pfcons _ lm ll => lm :: plistOut ll
  end.

Fixpoint count_dec
  (P : nat -> Prop)(D : forall n, {P n}+{~P n})(l : list nat) : nat :=
  match l with
  | nil => 0
  | l_head :: l_tail => 
    match D l_head with
    | left _ => 1
    | right _ => 0 
    end +
    count_dec P D l_tail
  end.

Fixpoint plistIn
  (P : nat -> Prop)(D : forall n, {P n}+{~P n})(l : list nat) : 
    plist P (count_dec P D l) :=
  match l as l0 return (plist P (count_dec P D l0)) with
  | nil => pnil P
  | n :: l0 =>
      match D n as s0
      return (s0 = D n -> plist P ((if s0 then 1 else 0) + count_dec P D l0))
      with
      | left p => fun _ => ptcons n p (plistIn P D l0)
      | right _ => fun _ => pfcons n (plistIn P D l0)
      end eq_refl
  end.

Goal forall P D ls, plistOut (plistIn P D ls) = ls.
  induction ls.
  trivial.
  simpl in *.
  remember(D a).
  destruct s;
  simpl in *;
  f_equal;
  trivial.
Qed.

Fixpoint plength n P (ls : plist P n) : nat :=
  match ls with
  | pnil => 0
  | ptcons _ _ _ l => plength l
  | pfcons _ _ l => plength l
  end.

Function plist_plength_rect 
  (n : nat)
    (P : nat -> Prop)
      (F : forall n, plist P n -> Type)
        (pn : F 0 (pnil P))
          (ls : plist P n) { measure plength ls } :=
  match ls with
  | pnil => 1
  | _ => 1
  end.

Fixpoint grab n P (ls : plist P (S n)) : {x | P x} :=
  (match ls in plist _ m return S n = m -> {x | P x} with
  | pnil => 
    (fun H => 
      False_rec
        _
        (eq_rect
          (S n)
          (fun e : nat => 
            match e with
            | 0 => False
            | S _ => True
            end)
        I
        0
        H))
  | ptcons 0 n p l => (fun _ => exist P n p)
  | ptcons _ n p l => (fun _ => grab l)
  | pfcons 0 _ _ => 
    (fun H => 
      False_rec
        _
        (eq_rect
          (S n)
          (fun e : nat => 
            match e with
            | 0 => False
            | S _ => True
            end)
        I
        0
        H))
  | pfcons (S _) _ l => (fun _ => grab l)
  end eq_refl).