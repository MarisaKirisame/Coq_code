Definition sum_5( a b c d e : nat ) := a + b + c + d + e.
Section sum_5'.
  Variable a b c d e : nat.
  Definition sum_5' := a + b + c + d + e.
End sum_5'.
Require Import ZArith.
Open Scope Z_scope.
Definition poly x := 2 * x * x + 3 * x + 3.
Section poly'.
  Variable x : Z.
  Definition poly' := 2 * x * x + 3 * x + 3.
End poly'.