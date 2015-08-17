Require Export Program Omega.
Obligation Tactic := program_simpl;omega.
Program Definition le_ind_using_nat_ind n (P : nat -> Prop)
  (p : P n)(p' : forall m : nat, n <= m -> P m -> P (S m)) n0 (lep : n <= n0) : P n0 := 
  nat_ind (fun x => P (x + n)) p (fun x => p' (x + n) _) (n0 - n).
Goal le_ind_using_nat_ind = le_ind.
  apply proof_irrelevance.
Qed.