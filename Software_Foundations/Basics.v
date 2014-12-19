Require Import Arith Recdef Omega.

Definition nandb (b1:bool) (b2:bool) : bool := negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
  trivial.
Qed.

Example test_nandb2: (nandb false false) = true.
  trivial.
Qed.

Example test_nandb3: (nandb false true) = true.
  trivial.
Qed.

Example test_nandb4: (nandb true true) = false.
  trivial.
Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) := andb (andb b1 b2) b3.

Example test_andb31: (andb3 true true true) = true.
  trivial.
Qed.

Example test_andb32: (andb3 false true true) = false.
  trivial.
Qed.

Example test_andb33: (andb3 true false true) = false.
  trivial.
Qed.

Example test_andb34: (andb3 true true false) = false.
  trivial.
Qed.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => mult (factorial n') n
  end.

Example test_factorial1: (factorial 3) = 6.
  trivial.
Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
  trivial.
Qed.

Fixpoint blt_nat (n m : nat) : bool :=
  match n, m with
  | O, O => false
  | O, S _ => true
  | S _, O => false
  | S n', S m' => blt_nat n' m'
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
  trivial.
Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
  trivial.
Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
  trivial.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
  auto.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
  auto.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
  intros.
  simpl in *.
  destruct n;
  trivial.
Qed.

Theorem identity_fn_applied_twice : 
  forall(f : bool -> bool), (forall(x : bool), f x = x) ->
    forall(b : bool), f (f b) = b.
  intros.
  remember (H b).
  rewrite e.
  trivial.
Qed.

Theorem andb_eq_orb : 
  forall(b c : bool), (andb b c = orb b c) -> b = c.
  intros.
  destruct b;
  auto.
Qed.

Inductive bnat : Set :=
| BZero
| BEven : bnat -> bnat
| BOdd : bnat -> bnat.

Fixpoint BInc b :=
  match b with
  | BZero => BOdd BZero
  | BEven b' => BOdd b'
  | BOdd b' => BEven (BInc b')
  end.

Fixpoint bnat_to_nat b :=
  match b with
  | BZero => O
  | BEven b' => 2 * (bnat_to_nat b')
  | BOdd b' => 2 * (bnat_to_nat b') + 1
  end.

Function nat_to_bnat b { measure id b } :=
  match b with
  | O => BZero
  | _ => 
    match NPeano.modulo b 2 with
    | O => BEven (nat_to_bnat(NPeano.div b 2))
    | _ => BOdd (nat_to_bnat(NPeano.div b 2))
    end
  end.
  intros.
  unfold id.
  subst.
  remember(NPeano.div_mod (S n) 2).
  assert(S n = 2 * NPeano.div (S n) 2 + NPeano.modulo (S n) 2).
  apply e.
  discriminate.
  rewrite H at 2.
  destruct n.
  discriminate.
  subst.
  omega.
  intros.
  subst.
  unfold id.
  remember(NPeano.div_mod (S n) 2).
  assert(S n = 2 * NPeano.div (S n) 2 + NPeano.modulo (S n) 2).
  apply e.
  discriminate.
  rewrite H at 2.
  destruct n.
  subst.
  auto.
  subst.
  omega.
Defined.

Goal forall b, bnat_to_nat (BInc b) = S (bnat_to_nat b).
  intros.
  induction b;
  trivial;
  simpl in *;
  omega.
Qed.