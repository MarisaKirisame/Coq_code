Require Import Arith Nat.

Import Nat.
Goal forall n, exists m, (1+2*n)*(1+2*n)=8*m+1.
  induction n.
  exists 0.
  trivial.
  destruct IHn.
  exists (x + n + 1).
  replace (1+2*S n) with ((1+2*n)+2) by ring.
  rewrite mul_add_distr_r.
  rewrite mul_add_distr_l.
  rewrite H.
  ring.
Qed.
