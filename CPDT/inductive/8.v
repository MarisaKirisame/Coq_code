Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Goal forall n l r, NLeaf <> NNode l n r.
  unfold not.
  intros.
  change(match NLeaf with NLeaf => False | _ => True end).
  rewrite H.
  trivial.
Qed.

Goal forall ll ln lr rl rn rr, NNode ll ln lr = NNode rl rn rr -> ln = rn.
  intros.
  change(match NNode ll ln lr with NNode _ n _ => n = rn | _ => False end).
  rewrite H.
  trivial.
Qed.
