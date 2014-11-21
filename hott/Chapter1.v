Set Implicit Arguments.

Definition composite A B C(f : A -> B)(g : B -> C) : A -> C.
  tauto.
Defined.

Goal forall A B C D (h : A -> B) (g : B -> C) (f : C -> D),
  (composite h (composite g f)) = (composite (composite h g) f).
  trivial.
Qed.

Definition prod_uniq A B : forall x : A * B, (fst x, snd x) = x.
  tauto.
Defined.

Definition prod_rec A B C : (A -> B -> C) -> (A * B -> C).
  intros.
  remember(fst X0).
  remember(snd X0).
  apply X;
  trivial.
Defined.

Definition prod_ind :
  forall (A B : Type) (P : A * B -> Prop),
    (forall (a : A) (b : B), P (a, b)) -> forall p : A * B, P p.
  intros.
  rewrite <- prod_uniq.
  trivial.
Defined.

Fixpoint iter C (c0 : C) cs n :=
  match n with
  | O => c0
  | S n' => cs (iter c0 cs n')
  end.

Fixpoint nat_rec C (c0 : C) (cs : nat -> C -> C) (n : nat) : C := 
  fst 
    (@iter
      (C * nat)
      (c0, 0)
      (fun x => match x with (C',n') => ((cs n' C'), S n') end)
      n).

Fixpoint nat_rec' C (c0 : C) (cs : nat -> C -> C) (n : nat) : C := 
  match n with
  | O => c0
  | S n' => cs n' (nat_rec' c0 cs n')
  end.

Theorem nat_rec_O : forall C (c0 : C) cs, nat_rec c0 cs 0 = c0.
  trivial.
Qed.

Theorem iter_snd : forall C c0 cs n,
  (snd
    (iter
    (c0, 0)
    (fun x : C * nat => let (C', n') := x in (cs n' C', S n'))
    n))
  = n.
  induction n.
  trivial.
  simpl in *.
  remember(
    iter
    (c0, 0)
    (fun x : C * nat => let (C', n') := x in (cs n' C', S n')) 
    n).
  destruct y.
  rewrite <- IHn.
  trivial.
Qed.

Theorem nat_rec_Sn : forall C (c0 : C) cs n,
  nat_rec c0 cs (S n) = cs n (nat_rec c0 cs n).
  induction n.
  trivial.
  simpl in *.
  remember(iter (c0, 0)
             (fun x : C * nat => let (C', n') := x in (cs n' C', S n')) n).
  destruct y.
  simpl in *.
  f_equal.
  f_equal.
  assert(
    snd
    (iter (c0, 0)
    (fun x : C * nat => let (C', n') := x in (cs n' C', S n')) n) = n).
  apply iter_snd.
  rewrite <- H.
  remember(
    iter
    (c0, 0)
    (fun x : C * nat => let (C', n') := x in (cs n' C', S n'))
    n).
  destruct y.
  simpl.
  injection Heqy.
  trivial.
Qed.

Goal forall C (c0 : C) cs n, nat_rec c0 cs n = nat_rec' c0 cs n.
  induction n.
  trivial.
  simpl in *.
  rewrite <- IHn.
  rewrite <- nat_rec_Sn.
  trivial.
Qed.

Definition bool_rec (C : Type) l r b : C :=
  match b with
  | true => l
  | false => r
  end.
Print sum.