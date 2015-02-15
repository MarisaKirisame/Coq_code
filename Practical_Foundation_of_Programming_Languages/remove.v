Require Import Plus Permutation Program List.
Require Import bring_to_front count tactic pos permutation_type eq_dec.

Set Implicit Arguments.

Definition remove_fst T (dec : eq_dec T) (t : T) l : In t l -> 
  { l' : (list T * list T) | 
      l = (fst l') ++ [t] ++ (snd l') /\ count_occ dec (fst l') t = 0 }.
  induction l.
  simpl in *.
  tauto.
  intros.
  destruct (dec t a).
  subst.
  exists (@nil T, l).
  simpl in *.
  tauto.
  assert (In t l).
  destruct H.
  subst.
  tauto.
  trivial.
  clear H.
  intuition.
  destruct X.
  destruct x.
  simpl in *.
  intuition.
  subst.
  exists ((a :: l0), l1).
  simpl in *.
  intuition.
  destruct (dec a t).
  subst.
  tauto.
  trivial.
Defined.

Definition remove_fst_join T (dec : eq_dec T) (t : T) l (P : In t l) :=
  fst (` (remove_fst dec t _ P)) ++ snd (` (remove_fst dec t _ P)).

Definition remove_pos T (t : T) l (p : pos t l) : 
  { l' : (list T * list T) | 
      l = (fst l') ++ [t] ++ (snd l') /\
      forall dec,
        count_occ dec (fst l') t = 
        count_occ dec (pos_before p) t }.
  induction l.
  eauto with *.
  depde p.
  simpl in *.
  exists (@nil T, l).
  simpl in *.
  tauto.
  simpl in *.
  specialize (IHl p0).
  destruct IHl.
  destruct x.
  simpl in *.
  intuition.
  subst.
  exists (a :: l0, l1).
  simpl in *.
  intuition.
  destruct (dec a t);
  auto.
Defined.

Definition remove_pos_join T (t : T) l (p : pos t l) :=
  let (l,r) := ` (remove_pos p) in l ++ r.