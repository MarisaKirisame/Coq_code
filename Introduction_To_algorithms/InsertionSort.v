Require Import 
  Arith
  List
  Omega
  Orders
  Recdef
  Relations
  Permutation 
  Setoid
  Sorted.

Set Implicit Arguments.

Module Type InsertionSort(Import X:Orders.TotalLeBool).

  Fixpoint Insertion(n : X.t)(l : list X.t) := 
    match l with
    | nil => n :: nil
    | l_head :: l_tail => 
        match X.leb n l_head with
        | true => n :: l_head ::l_tail
        | false => l_head :: Insertion n l_tail
        end
    end.

  Fixpoint InsertionSort(l : list X.t) : list X.t :=
    match l with
    | nil => nil
    | l_head :: l_tail => Insertion l_head (InsertionSort l_tail)
    end.

  Theorem InsertionLength : forall n l, length(Insertion n l) = S (length l).
    intro.
    induction l.
    trivial.
    simpl in *.
    destruct (leb n a).
    trivial.
    intuition.
    simpl in *.
    auto.
  Qed.

  Theorem InsertionSortSameLength : forall l, length (InsertionSort l) = length l.
    intros.
    induction l.
    trivial.
    simpl in *.
    rewrite InsertionLength.
    auto.
  Qed.

  Theorem InsertionPermutationSelf : forall n l, 
    Permutation (n :: l) (Insertion n l).
    intros.
    induction l.
    trivial.
    simpl in *.
    case (leb n a).
    trivial.
    intros.
    assert(Permutation (n :: a :: l) (a :: n :: l)).
    constructor.
    apply(perm_trans H).
    auto.
  Qed.

  Theorem InsertionPermutation : 
    forall n l r, Permutation l r -> Permutation (n :: l) (Insertion n r).
    induction 1.
    trivial.
    simpl in *.
    case(leb n x).
    auto.
    intros.
    assert (Permutation (n :: x :: l) (x :: n :: l)) as T.
    constructor.
    apply(perm_trans T).
    auto.
    simpl in *.
    case(leb n x),(leb n y).
    constructor.
    constructor.
    constructor.
    constructor.
    assert (Permutation (n :: y :: x :: l) (n :: x :: y :: l)) as T.
    constructor.
    constructor.
    apply(perm_trans T).
    constructor.
    assert(Permutation (n :: y :: x :: l) (x :: y :: n :: l)) as T.
    assert(Permutation (n :: y :: x :: l) (x :: n :: y :: l)) as T.
    assert(Permutation (n :: y :: x :: l) (n :: x :: y :: l)) as T.
    constructor.
    constructor.
    apply(perm_trans T).
    constructor.
    apply(perm_trans T).
    constructor.
    constructor.
    apply(perm_trans T).
    constructor.
    constructor.
    apply InsertionPermutationSelf.
    assert (Permutation (n :: l) (n :: l')) as T.
    auto.
    apply(perm_trans T).
    trivial.
  Qed.

  Theorem InsertionSortPermutation : forall l, Permutation l (InsertionSort l).
    induction l.
    trivial.
    inversion IHl.
    trivial.
    subst.
    simpl in *.
    apply InsertionPermutation.
    trivial.
    subst.
    simpl in *.
    apply InsertionPermutation.
    trivial.
    subst.
    simpl in *.
    apply InsertionPermutation.
    trivial.
  Qed.

  Theorem InsertionSortNil : forall l, InsertionSort l = nil -> l = nil.
    intros.
    destruct l.
    trivial.
    simpl in *.
    remember(InsertionSort l).
    destruct l0.
    simpl in *.
    inversion H.
    simpl in *.
    destruct (leb t0 t1).
    inversion H.
    inversion H.
  Qed.

  Definition Sorted := Sorted (fun l r => is_true(X.leb l r)).

  Theorem SortedCons : forall e l, 
    Sorted (e :: l) -> 
      Sorted l.
    intros.
    induction l.
    constructor.
    inversion H.
    trivial.
  Qed.

  Theorem InsertionSorted : forall e l, 
    Sorted l -> 
      Sorted (Insertion e l).
    intros.
    induction l.
    simpl in *.
    constructor.
    auto.
    trivial.
    simpl in *.
    remember (X.leb e a).
    destruct b.
    constructor.
    trivial.
    auto.
    constructor.
    apply IHl.
    eapply SortedCons.
    eauto.
    induction l.
    simpl in *.
    constructor.
    case(X.leb_total a e).
    trivial.
    subst.
    eauto with *.
    simpl in *.
    remember (X.leb e a0).
    destruct b.
    constructor.
    case(X.leb_total a e).
    trivial.
    eauto with *.
    constructor.
    inversion H.
    subst.
    inversion H3.
    trivial.
  Qed.

  Theorem InsertionSortSorted : forall l, Sorted (InsertionSort l).
    induction l.
    simpl in *.
    constructor.
    simpl in *.
    apply InsertionSorted.
    trivial.
  Qed.

End InsertionSort.