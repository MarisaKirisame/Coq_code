Require Import Arith Omega ArithRing Relations Setoid ZArith.

Fixpoint bdiv_aux (b m n:nat) {struct b} : nat * nat :=
  match b with
  | O => (0, 0)
  | S b' =>
      match le_gt_dec n m with
      | left H => match bdiv_aux b' (m - n) n with
                  | (q, r) => (S q, r)
                  end
      | right H => (0, m)
      end
  end.

Theorem bdiv_aux_correct1 :
  forall b m n:nat, m <= b -> 0 < n ->
    m = fst (bdiv_aux b m n) * n + snd (bdiv_aux b m n).
    intros b; elim b; simpl.
    intros.
    omega.
    intros b' Hrec m n Hleb Hlt.
    case (le_gt_dec n m).
    intros Hle.
    generalize (Hrec (m-n) n).
    case (bdiv_aux b' (m-n) n).
    intros.
    simpl in *.
    omega.
    trivial.
Qed.

Theorem bdiv_aux_correct2 :
  forall b m n:nat, m <= b -> 0 < n -> snd (bdiv_aux b m n) < n.
  intro b; elim b; auto with arith.
  simpl in |- *; intros b' Hrec m n Hle Hlt.
  case (le_gt_dec n m).
  generalize (Hrec (m - n) n).
  case (bdiv_aux b' (m - n) n).
  simpl.
  intros.
  omega.
  simpl.
  intros.
  omega.
Qed.

Lemma sub_decrease : forall b n m:nat, n <= S b -> 0 < m -> n - m <= b.
  intros.
  omega.
Qed.

Definition bdivspec :
  forall b n m:nat,
    n <= b -> 0 < m -> {q : nat &  {r : nat | n = m * q + r /\ r < m}}.
  fix 1.
  intros b; case b.
  intros n m Hle Hlt.
  rewrite <- (le_n_O_eq _ Hle).
  exists 0.
  exists 0.
  split;
  omega ||
  ring.
  intros b' n m Hle Hlt.
  case (le_gt_dec m n).
  intros.
  generalize (bdivspec b' (n - m) m (sub_decrease b' n m Hle Hlt) Hlt).
  intros [q' [r [Heq Hlt']]].
  exists (S q').
  exists r.
  split; auto with arith.
  replace (m * S q' + r) with (m * q' + r + m).
  omega.
  ring.
  intros Hgt.
  exists 0.
  exists n.
  split.
  omega.
  omega.
Qed.

Fixpoint sqrt_nat_inner(d n : nat) :=
  match d,n with
  | O, _ => (O, O)
  | _, O => (O, O)
  | S d', _ => 
      let (q,r0) := ((NPeano.div n 4),(NPeano.modulo n 4)) in
        let (s',r') := (sqrt_nat_inner d' q) in
          if lt_dec (4 * r' + r0) (4 * s' + 1)
          then (2 * s', 4 * r' + r0)
          else (2 * s' + 1, 4 * r' + r0 - 4 * s' - 1)
  end.

Inductive tree (A:Set) : Set :=
| leaf : tree A
| node : A -> tree A -> tree A -> tree A.

Inductive subtree (A:Set) (t:tree A) : tree A -> Prop :=
| tree_on_left : forall (t':tree A) (x:A), subtree A t (node A x t t')
| tree_on_right : forall (t':tree A) (x:A), subtree A t (node A x t' t).

Theorem well_founded_tree_sub : forall A:Set, well_founded (subtree A).
  intros.
  unfold well_founded.
  induction a.
  constructor.
  intros.
  inversion H.
  constructor.
  intuition.
  inversion H.
  trivial.
  trivial.
Qed.

Theorem wf_inclusion:
  forall (A:Set) (R S:A->A->Prop),
    inclusion A R S -> well_founded S -> well_founded R.
  unfold inclusion.
  intuition.
  constructor.
  intuition.
  eapply well_founded_ind.
  eexact H0.
  intuition.
  constructor.
  auto.
Qed.

Fixpoint div2 (n:nat) : nat := match n with S (S p) => S (div2 p) | _ => 0 end.

Theorem div2_ind :
  forall P:nat->Prop,
    P 0 -> P 1 -> (forall n, P n -> P (S (S n))) ->
    forall n, P n.
  intros.
  assert (H' : P n /\ P (S n)).
  elim n; intuition.
  intuition.
Qed.

Theorem double_div2_le : forall x:nat, div2 x + div2 x <= x.
  induction x using div2_ind.
  trivial.
  auto.
  simpl in *.
  omega.
Qed.

Theorem f_lemma : forall x v, v <= div2 x -> div2 x + v <= x.
  induction x using div2_ind.
  trivial.
  auto.
  intuition.
  simpl in *.
  destruct v.
  auto with *.
  apply le_S_n in H.
  rewrite plus_comm.
  simpl in *.
  repeat apply le_n_S.
  rewrite plus_comm.
  auto.
Qed.