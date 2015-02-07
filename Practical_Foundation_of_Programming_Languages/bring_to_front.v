Require Import Program Permutation List eq_dec tactic.

Definition bring_to_front { T } 
  (dec : eq_dec T) e : 
    forall l : list T, In e l -> 
      { lr : (list T) * (list T)
        | tail (fst lr) ++ e :: snd lr = l /\
          hd_error (fst lr ++ snd lr) = Some e /\
          ~In e (tail (fst lr)) }.
  induction l;
  intros;
  simpl in *.
  tauto.
  destruct (dec e a).
  subst.
  clear H.
  exists ([a], l).
  tauto.
  assert (In e l).
  intuition.
  intuition.
  clear H.
  invc X.
  destruct x.
  simpl in *.
  intuition.
  subst.
  exists (e::a::(tl l0), l1).
  simpl in *.
  intuition.
Defined.