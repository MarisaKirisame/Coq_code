Set Implicit Arguments.

Inductive btree(T : Type) :=
| bleaf : T -> btree T
| bnode : btree T -> btree T -> btree T.

Section htree.

  Variable T : Type.

  Variable F : T -> Type.

  Inductive htree : btree T -> Type :=
  | hleaf : forall t, F t -> htree (bleaf t)
  | hnode : forall l r, htree l -> htree r -> htree (bnode l r).

  Variable elm : T.

  Inductive path : btree T -> Type :=
  | stop : path (bleaf elm)
  | left : forall l r, path l -> path (bnode l r)
  | right : forall l r, path r -> path (bnode l r).

  Definition tget t : htree t -> path t -> F elm.
    induction t.
    intros.
    inversion X0.
    inversion X.
    trivial.
    intros.
    inversion X0;
    inversion X;
    subst;
    tauto.
  Defined.

  Definition htmap2 b 
    (l r : htree b)(f : forall t, (F t) -> (F t) -> (F t)) : htree b.
    induction b.
    inversion l.
    inversion r.
    subst.
    constructor.
    apply(f t X X0).
    inversion l.
    inversion r.
    subst.
    constructor.
    apply(IHb1 X X1).
    apply(IHb2 X0 X2).
  Defined.

End htree.

Recursive Extraction tget htmap2.