Require Import Omega.

Fixpoint le_dec n m : { n <= m } + { n > m }.
  refine(
    match n, m with
    | O, O => _
    | S _, O => _
    | O, S _ => _
    | S _, S _ => _
    end);
  [
    left |
    left |
    right |
    case (le_dec n0 n1);
    [
      left |
      right
    ]
  ];
  omega.
Defined.
