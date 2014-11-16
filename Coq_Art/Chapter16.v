Require Import Omega.

Theorem divisor_smaller :
  forall m p:nat, 0 < m -> forall q:nat, m = q*p -> q <= m.
  induction m.
  auto with *.
  induction p.
  auto with *.
  intros.
  rewrite H0.
  rewrite mult_succ_r.
  auto with *.
Qed.

  
  