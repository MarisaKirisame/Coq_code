Definition var := nat.

Inductive prop : Set :=
| pvar : var -> prop
| pnot : prop -> prop
| pand : prop -> prop -> prop
| por : prop -> prop -> prop.

Fixpoint propDenote f s :=
  match s with
  | pvar n => is_true (f n)
  | pnot n => ~ (propDenote f n)
  | pand l r => (propDenote f l) /\ (propDenote f r)
  | por l r => (propDenote f l) \/ (propDenote f r)
  end.

Definition bool_true_dec : forall b, { b = true } + { b = true -> False }.
  intros.
  destruct b.
  tauto.
  right.
  discriminate.
Defined.

Definition decide : forall( truth : var -> bool ) ( p : prop ), { propDenote truth p } + { ~ propDenote truth p }.
  intros.
  induction p.
  simpl in *.
  remember (bool_true_dec (truth v)).
  inversion_clear s;
  trivial.
  inversion_clear IHp;
  auto;tauto.
  inversion_clear IHp1;
  inversion_clear IHp2;
  simpl in *;
  tauto.
  simpl in *;
  tauto.
Defined.

Definition negate : forall p : prop , { p' : prop | forall truth , propDenote truth p <-> ~ propDenote truth p' }.
  induction p;
  intros.
  simpl in *;
  exists(pnot (pvar v));
  intros;
  case(decide truth (pvar v));
  split;
  auto;
  tauto.
  eauto with *.
  simpl in *;
  inversion_clear IHp1;
  inversion_clear IHp2;
  exists (por x x0);
  intros;
  simpl in *;
  split;
  try inversion_clear H1;
  case(decide truth (por x x0));
  intros;
  simpl in *;
  try inversion_clear p;
  case (H truth);
  case (H0 truth);
  tauto.
  simpl in *;
  inversion_clear IHp1;
  inversion_clear IHp2;
  exists (pand x x0);
  split;
  intros;
  try inversion_clear H1;
  case(decide truth x);
  case(decide truth x0);
  case (H truth);
  case (H0 truth);
  intros;
  simpl in *;
  tauto.
Qed.