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
  eapply (exist _).
  instantiate( 1 := x + 1 ).
  omega.
Qed.

Fixpoint fib(n : nat) : nat :=
  match n with
  | O => 1
  | S n' =>
      match n' with
      | O => 1
      | S n'' => (fib n') + (fib n'')
      end
  end.

Fixpoint fib_pair (n:nat) : nat * nat :=
  match n with
  | O => (1, 1)
  | S p => match fib_pair p with
           | (x, y) => (y, x + y)
           end
  end.

Definition linear_fib (n:nat) := fst (fib_pair n).

Lemma fib_pair_correct : forall n:nat, fib_pair n = (fib n, fib (S n)).
  induction n.
  auto.
  simpl.
  rewrite IHn.
  f_equal.
  destruct n.
  auto.
  rewrite <- plus_assoc.
  f_equal.
  simpl.
  omega.
Qed.

Goal forall n, fib n = linear_fib n.
  unfold linear_fib.
  intros.
  rewrite fib_pair_correct.
  auto.
Qed.

Goal forall n, (sig_extract _ _ (div3 n)) <= n.
  intros.
  remember(div3 n).
  destruct s.
  simpl.
  omega.
Qed.

Theorem div3_3 : (sig_extract _ _ (div3 3)) = 1.
  unfold sig_extract.
  remember (div3 3).
  destruct s.
  repeat(omega||destruct x).
Qed.

Theorem div3_S : forall n, (sig_extract _ _ (div3 (S (S (S n))))) = S (sig_extract _ _ (div3 n)).
  intros.
  remember(div3 (S (S (S n)))).
  remember(div3 n).
  destruct s.
  destruct s0.
  induction n using nat_3_rect;
  simpl;
  omega.
Qed.

Definition mod3 (n : nat) : { m : nat | n = (sig_extract _ _ (div3 n)) + m }.
  induction n using nat_3_rect;
  try destruct IHn;
  repeat econstructor.
  rewrite div3_S.
  instantiate(1 := x + 2).
  omega.
Defined.

Definition div2_mod2 : 
  forall n:nat, {q:nat & {r:nat | n = 2*q + r /\ r <= 1}}.
  intros.
  induction n using nat_2_rect.
  econstructor.
  econstructor.
  instantiate( 1 := 0 ).
  instantiate( 1 := 0 ).
  omega.
  econstructor.
  econstructor.
  instantiate( 1 := 1 ).
  instantiate( 1 := 0 ).
  omega.
  destruct IHn.
  destruct s.
  destruct a.
  econstructor.
  econstructor.
  instantiate( 1 := x0 ).
  instantiate( 1 := x + 1 ).
  omega.
Qed.

Fixpoint plus' (n m:nat){struct m} : nat :=
  match m with 
  | O => n
  | S p => S (plus' n p) 
  end.

Theorem plus'_O_n : forall n, plus' 0 n = n.
  intros.
  induction n;
  simpl;
  auto.
Qed.

Hint Resolve plus'_O_n.

Theorem plus'_assoc : forall n m p : nat, plus' n (plus' m p) = plus' (plus' n m) p.
  assert(forall n m, plus' (S m) n = S (plus' m n)).
  intros.
  induction n;
  simpl;
  auto.
  intros.
  induction m;
  simpl;
  auto.
  rewrite H.
  simpl.
  rewrite IHm.
  auto.
Qed.

Fixpoint plus'' (n m:nat) {struct m} : nat :=
  match m with 0 =>  n 
      | S p => plus'' (S n) p 
  end.

Theorem plus''_Sn_m m : forall n, plus'' (S n) m = S (plus'' n m).
  induction m.
  simpl;
  auto.
  intros.
  apply IHm.
Qed.

Hint Resolve plus''_Sn_m plus'_assoc.

Goal forall n m p : nat, plus'' n (plus'' m p) = plus'' (plus'' n m) p.
  assert(forall n m, plus'' n m = plus' n m).
  intros.
  induction m.
  auto.
  simpl.
  rewrite <- IHm.
  auto.
  intros.
  repeat rewrite H.
  auto.
Qed.

