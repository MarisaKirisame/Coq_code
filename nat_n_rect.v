Set Implicit Arguments.

Require Import Program Arith Omega Recdef.

Fixpoint nat_n_rect_inner
  (lower : nat)
    (step : nat)
      (n : nat)
        (P : nat -> Type)
          (p2 : (forall m, m < (S step) -> P m))
            (p3 : (forall n, P n -> P ((S step) + n))) { struct lower } :
              n <= lower -> P n.
  destruct lower, n;
  intros;
  simpl in *;
  try (
    clear nat_n_rect_inner;
    solve [auto with *]).
  assert(n - step <= lower).
  omega.
  specialize (nat_n_rect_inner lower step (n - step) P p2 p3 H0).
  specialize (p3 _ nat_n_rect_inner).
  destruct (le_dec step n).
  rewrite le_plus_minus_r in p3.
  trivial.
  trivial.
  apply p2.
  omega.
Defined.

Definition nat_n_rect
  (step : nat)
    (n : nat)
      (P : nat -> Type)
        (p2 : (forall m, m < (S step) -> P m))
          (p3 : (forall n, P n -> P ((S step) + n))) :
            P n := nat_n_rect_inner P p2 p3 (le_n n).