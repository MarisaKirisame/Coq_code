Require Import "misc".

Theorem sig_extract_ok :
  forall (A:Set) (P:A -> Prop) (y:sig P), P (sig_extract A P y).
  intros.
  destruct y.
  auto.
Defined.

Require Import ZArith.
Print lt_dec.
Open Scope Z_scope.

Parameter
  div_pair :
    forall a b:Z,
      0 < b ->
      {p : Z * Z | a = fst p * b + snd p  /\ 0 <= snd p < b}.

Definition div : forall a b:Z,
    0 < b -> Z * Z.
  intros.
  apply (div_pair a b).
  auto.
Defined.

Close Scope Z_scope.

Definition sig_rec_simple (A:Set) (P: A -> Prop) (B : Set) :
  (forall x, P x -> B) -> (sig P) -> B.
  intros.
  destruct H0.
  eauto.
Defined.

Definition eqdec (A : Set) := forall a b : A, {a = b} + {a <> b}.

Definition nat_eq_dec : eqdec nat.
  unfold eqdec.
  induction a,b;auto with arith.
Defined.

Definition nat_3_rect :
  forall P : nat -> Type,
    P O ->
      P 1 ->
        P 2 ->
          (forall n, P n -> P (S (S (S n)))) -> 
            forall n, P n.
  intros.
  assert(3 > 0).
  omega.
  apply (nat_n_rect (exist _ 3 H));simpl.
  intros.
  do 4(
    destruct m;
    omega||auto).
  intros.
  rewrite plus_comm.
  simpl.
  auto.
Defined.

Definition nat_2_rect :
  forall P : nat -> Type,
    P O ->
      P 1 ->
        (forall n, P n -> P (S (S n))) -> 
          forall n, P n.
  intros.
  assert(2 > 0).
  omega.
  apply(nat_n_rect (exist _ 2 H));simpl.
  intros.
  do 3(
    destruct m;
    (omega||auto)).
  intros.
  rewrite plus_comm.
  simpl.
  auto.
Defined.

Definition nat_4_rect :
  forall P : nat -> Type,
    P O ->
      P 1 ->
        P 2 ->
          P 3 ->
            (forall n, P n -> P (S(S (S (S n))))) -> 
              forall n, P n.
  intros.
  assert(4 > 0).
  omega.
  apply (nat_n_rect (exist _ 4 H));simpl.
  intros.
  do 5(
    destruct m;
    omega||auto).
  intros.
  rewrite plus_comm.
  simpl.
  auto.
Defined.

Definition div3 (n : nat) : { r : nat | r * 3 <= n < r * 3 + 3 }.
  induction n using nat_3_rect;
  try(
    econstructor;
    instantiate( 1 := 0 );
    omega).
  destruct IHn.
  econstructor.
  instantiate( 1 := x + 1 ).
  omega.
Defined.

Fixpoint div2 (n:nat) : nat :=
  match n with 
  | 0 => 0
  | 1 => 0
  | S (S p) => S (div2 p)
  end.

Definition mod2 (n : nat) : { m : nat | n = (div2 n) + m }.
  induction n using nat_2_rect.
  repeat econstructor.
  repeat econstructor.
  destruct IHn.
  simpl.
  econstructor.
  f_equal.
  rewrite e at 1.
  auto.
Qed.
