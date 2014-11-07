Definition sig_extract: forall (A:Set) (P:A -> Prop), sig P -> A.
  intros.
  destruct H.
  auto.
Defined.

Theorem sig_extract_ok :
  forall (A:Set) (P:A -> Prop) (y:sig P), P (sig_extract A P y).
  intros.
  destruct y.
  auto.
Defined.

Require Import ZArith.

Open Scope Z_scope.

Parameter
  div_pair :
    forall a b:Z,
      0 < b ->
      {p : Z * Z | a = fst p * b + snd p  /\ 0 <= snd p < b}.

Goal forall a b:Z, 0 < b -> Z*Z.
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

Definition nat_3_rec :
  forall P : nat -> Type,
    P O ->
      P 1 ->
        P 2 ->
          (forall n, P n -> P (S (S (S n)))) -> 
            forall n, P n.
  intros.
  cut(P n * P (S n) * P (S (S n))).
  intros.
  destruct X3.
  destruct p.
  auto.
  elim n.
  auto.
  intros.
  destruct X3.
  destruct p.
  split.
  auto.
  auto.
Defined.

Lemma my_h : forall n r : nat, n < S r -> n = r \/ n < r.
  intros.
  omega.
Qed.

Definition div3 (n : nat) : { r : nat | r * 3 <= n < r * 3 + 3 }.
  induction n using nat_3_rec;
  try(
    econstructor;
    instantiate( 1 := 0 );
    omega).
  destruct IHn.
  econstructor.
  instantiate( 1 := x + 1 ).
  omega.
Qed.