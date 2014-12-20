Require Import Omega.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
  destruct b, c;
  trivial.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
  intros.
  omega.
Qed.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
  intros.
  omega.
Theorem plus_comm : ∀n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_assoc : ∀n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *) Admitted.
☐
Exercise: 2 stars (double_plus)
Consider the following function, which doubles its argument:

Fixpoint double (n:nat) :=
  match n with
  | O ⇒ O
  | S n' ⇒ S (S (double n'))
  end.

Use induction to prove this simple fact about double:

Lemma double_plus : ∀n, double n = n + n .
Proof.
  (* FILL IN HERE *) Admitted.
☐