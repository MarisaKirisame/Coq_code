Set Implicit Arguments.
Fixpoint fact n := match n with | O => 1 | S n' => n * fact n' end.
Fixpoint fact_csp T (F : nat -> T) n : T :=
  match n with
  | O => F 1
  | S n' => fact_csp (fun n'' => F (n * n'')) n'
  end.
Goal forall T (f : nat -> T) n , fact_csp f n = f (fact n).
  intros.
  revert f.
  induction n;
  intros.
  trivial.
  unfold fact_csp.
  fold fact_csp.
  rewrite IHn.
  trivial.
Qed.