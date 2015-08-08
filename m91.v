Require Export MoreRelations Omega.
Inductive m91 : nat -> nat -> Prop :=
| gt91 : forall n, 100 < n -> m91 n (n - 10)
| le91 : forall n m p, n <= 100 -> m91 (11 + n) m -> m91 m p -> m91 n p.
Ltac run := 
  let H := fresh in
    simpl;
    match goal with 
    |- m91 ?n _ => 
        destruct (le_dec n 100) as [H|H];
        [
          omega||(eapply le91;omega||clear H;run)|
          omega||(eapply gt91;omega)
        ]
        end.
Goal forall n, n <= 100 -> m91 n 91.
  intros.
  repeat (omega||destruct n).
  par:run.
Qed.