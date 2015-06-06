Require Export Arith Omega.
Set Implicit Arguments.
Fixpoint fact_cps T (F : nat -> T) n : T :=
  match n with
  | O => F 1
  | S n' => fact_cps (fun n'' => F (n * n'')) n'
  end.
Theorem fact_cps_correct T (f : nat -> T) n : fact_cps f n = f (fact n).
  intros.
  revert f.
  induction n;
  intros.
  trivial.
  unfold fact_cps.
  fold fact_cps.
  rewrite IHn.
  trivial.
Qed.
Fixpoint fib n :=
  match n with
  | O => 1
  | S n' => 
      match n' with
      | O => 1
      | S n'' => fib n' + fib n''
      end
  end.
Fixpoint fib_cps T (F : nat -> T) n { struct n } :=
  match n with
  | O => F 1
  | S n' => 
      match n' with
      | O => F 1
      | S n'' => fib_cps (fun l => fib_cps (fun r => F (l + r)) n'') n'
      end
  end.
Theorem fib_cps_correct_helper T (f : nat -> T) n m : n <= m -> fib_cps f n = f (fib n).
  intros.
  revert f H.
  revert n.
  induction m;
  intros;
  destruct n;
  omega||trivial.
  unfold fib_cps.
  fold fib_cps.
  destruct n;trivial.
  rewrite !IHm;omega||trivial.
Qed.
Theorem fib_cps_correct T (f : nat -> T) n : fib_cps f n = f (fib n).
  eapply fib_cps_correct_helper;eauto.
Qed.