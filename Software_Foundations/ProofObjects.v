Load MoreLogic.

Set Implicit Arguments.

Theorem six_is_beautiful :
  beautiful 6.
  replace 6 with (3 + 3).
  apply b_sum;
  trivial.
  trivial.
Qed.

Definition six_is_beautiful' : beautiful 6 := b_sum b_3 b_3.

Theorem nine_is_beautiful :
  beautiful 9.
  replace 9 with (3 + 6).
  apply b_sum.
  trivial.
  apply six_is_beautiful.
  trivial.
Qed.

Definition nine_is_beautiful' : beautiful 9 := b_sum b_3 six_is_beautiful.

Program Definition b_times2': forall n, beautiful n -> beautiful (2*n) :=
  fun _ H => b_sum H H.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R := 
  fun _ _ _ L R => 
    match L with
    | conj P _ => 
      match R with
      | conj _ R => conj P R
      end
    end.

Definition gorgeous_plus13_po: forall n, gorgeous n -> gorgeous (13+n) :=
   fun _ N => g_plus5 (g_plus5 (g_plus3 N)).

Definition beautiful_gorgeous :
  forall n, beautiful n -> gorgeous n.
  intros.
  induction H;
  auto.
Qed.

Definition gorgeous_beautiful :
  forall n, gorgeous n -> beautiful n.
  intros.
  induction H;
  trivial;
  replace (S (S (S (S (S n))))) with (5 + n);
  replace (S (S (S n))) with (3 + n);
  auto.
Qed.

Definition beautiful_iff_gorgeous :
  forall n, beautiful n <-> gorgeous n :=
    fun _ => conj (fun H => beautiful_gorgeous H) (fun H => gorgeous_beautiful H).

Definition or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P := 
    fun _ _ H => 
      match H with
      | or_introl P => or_intror P
      | or_intror Q => or_introl Q
      end.

Definition p : ex (fun n => beautiful (S n)) :=
  (ex_intro (fun x => beautiful (S x)) 2) b_3.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
    [c;d] = [e;f] ->
      [a;b] = [e;f].
  intros.
  apply (trans_eq H).
  trivial.
Qed.