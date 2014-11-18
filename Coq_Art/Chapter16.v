Require Import
  Arith
  ZArith
  Omega
  List
  Zwf
  Relations
  Inverse_Image
  Transitive_Closure
  Zdiv.

Theorem divisor_smaller :
  forall m p:nat, 0 < m -> forall q:nat, m = q * p -> q <= m.
  induction m.
  auto with *.
  induction p.
  auto with *.
  intros.
  rewrite H0.
  rewrite mult_succ_r.
  auto with *.
Qed.

Theorem verif_divide :
  forall m p:nat, 0 < m -> 0 < p ->
    (exists q:nat, m = q*p)->(Z_of_nat m mod Z_of_nat p = 0)%Z.
  intros m p Hltm Hltp (q, Heq).
  subst.
  rewrite inj_mult.
  replace (Z_of_nat q * Z_of_nat p)%Z with (0 + Z_of_nat q * Z_of_nat p)%Z.
  rewrite Z_mod_plus.
  auto.
  omega.
  ring.
Qed.

Open Scope nat_scope.

Inductive bin : Set :=
| node: bin -> bin ->  bin
| leaf: nat ->  bin
| neutral: bin .

Fixpoint flatten_aux (t fin : bin) {struct t} : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten_aux t2 fin)
  | x => node x fin
  end.

Fixpoint flatten (t : bin) : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten t2)
  | x => x
  end.

Fixpoint remove_neutral1 (t : bin) : bin :=
  match t with
  | leaf n => leaf n
  | neutral => neutral
  | node neutral t' => remove_neutral1 t'
  | node t t' => node t (remove_neutral1 t')
  end.

Fixpoint remove_neutral2 (t : bin) : bin :=
  match t with
  | leaf n => leaf n
  | neutral => neutral
  | node t neutral => t
  | node t1 t2 => node t1 (remove_neutral2 t2)
  end.

Definition remove_neutral (t : bin) := remove_neutral2 (remove_neutral1 t).

Section assoc_eq.

Variables
  (A : Set) (f : A -> A ->  A) (zero_A : A)
  (assoc : forall (x y z : A),  f x (f y z) = f (f x y) z)
  (zero_left : forall (x : A),  f zero_A x = x)
  (zero_right : forall (x : A),  f x zero_A = x).

Fixpoint bin_A (l : list A) (t : bin) {struct t} : A :=
  match t with
  | node t1 t2 => f (bin_A l t1) (bin_A l t2)
  | leaf n => nth n l zero_A
  | neutral => zero_A
  end.

Theorem flatten_aux_valid_A:
  forall (l : list A) (t t' : bin),
    f (bin_A l t) (bin_A l t') = bin_A l (flatten_aux t t').
  induction t.
  simpl.
  intuition.
  rewrite <- IHt1.
  rewrite <- IHt2.
  auto.
  simpl.
  auto.
  simpl.
  auto.
Qed.

Theorem flatten_valid_A:
  forall (l : list A) (t : bin),  bin_A l t = bin_A l (flatten t).
  induction t.
  simpl.
  rewrite <- flatten_aux_valid_A.
  f_equal.
  trivial.
  trivial.
  trivial.
Qed.

Theorem flatten_valid_A_2:
  forall (t t' : bin) (l : list A),
    bin_A l (flatten t) = bin_A l (flatten t') ->  bin_A l t = bin_A l t'.
  intros.
  rewrite (flatten_valid_A l t).
  rewrite (flatten_valid_A l t').
  trivial.
Qed.

Theorem remove_neutral1_valid_A:
  forall (l : list A) (t : bin),  bin_A l (remove_neutral1 t) = bin_A l t.
  induction t.
  case t1.
  simpl.
  intros.
  f_equal.
  trivial.
  intros.
  simpl in *.
  f_equal.
  trivial.
  simpl in *.
  rewrite IHt2.
  trivial.
  auto.
  trivial.
  trivial.
Qed.

Theorem remove_neutral2_valid_A:
  forall (l : list A) (t : bin),  bin_A l (remove_neutral2 t) = bin_A l t.
  intros.
  elim t.
  destruct b0.
  simpl.
  intuition.
  f_equal.
  trivial.
  trivial.
  eauto.
  trivial.
  trivial.
Qed.

Theorem remove_neutral_equal:
  forall (t t' : bin) (l : list A),
    bin_A l (remove_neutral t) = bin_A l (remove_neutral t') ->
      bin_A l t = bin_A l t'.
  unfold remove_neutral.
  intros.
  repeat rewrite remove_neutral2_valid_A in *.
  repeat rewrite remove_neutral1_valid_A in *.
  trivial.
Qed.

End assoc_eq.

Ltac term_list f l zero v :=
  match v with
  | f ?X1 ?X2 =>
      let l1 := term_list f l zero X2 in
        term_list f l1 zero X1
  | zero => l
  | ?X1 => constr:(cons X1 l)
  end.

Ltac compute_rank l n v :=
  match l with
  | cons ?X1 ?X2 =>
      let tl := constr:X2 in
      match constr:(X1 = v) with
      | ?X1 = ?X1 => n
      | _ => compute_rank tl (S n) v
      end
  end.

Ltac model_aux l f zero v := 
  match v with
  | f ?X1 ?X2 => 
      let r1 := model_aux l f zero X1 with r2 := model_aux l f zero X2 in
        constr:(node r1 r2)
  | zero => constr:neutral
  | ?X1 => 
      let n := compute_rank l 0 X1 in
        constr:(leaf n)
  end.

Ltac model_A A f zero v := 
  let l := term_list f (nil (A:=A)) zero v in
    let t := model_aux l f zero v in
      constr:(bin_A A f zero l t).

Ltac assoc_eq A f zero assoc_thm neutral_left_thm neutral_right_thm :=
match goal with
| |- @eq A ?X1 ?X2 =>
  let term1 := model_A A f zero X1 with term2 := model_A A f zero X2 in
    (change (term1 = term2); apply flatten_valid_A_2 with ( 1 := assoc_thm );
      apply remove_neutral_equal
        with ( 1 := neutral_left_thm ) ( 2 := neutral_right_thm ); auto)
end.

Theorem reflection_test3:
  forall (x y z t u : Z),
    (x * (((y * z) *1 )* (t * u)) = 
    (x * (1 * y * 1)) * (z * (t * u)) * 1)%Z.
  intros.
  assoc_eq Z Zmult 1%Z Zmult_assoc Zmult_1_l Zmult_1_r.
Qed.