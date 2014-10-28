Require Import List Bool.
Section InsertionSort.
  Variable T : Set.
  Variable F : T -> T -> bool.
  Fixpoint Insert( e : T )( l : list T ) : list T:=
  match l with
  | nil => e :: nil
  | e' :: rest =>
      if ( F e e' ) then
        e :: e' :: rest else
        e' :: Insert e rest
  end.
  Fixpoint InsertionSort( l : list T ) : list T:=
  match l with
  | nil => nil
  | e :: rest => Insert e ( InsertionSort rest )
  end.
End InsertionSort.
Section Find.
  Variable T : Set.
  Variable F : T -> bool.
  Fixpoint Find( l : list T ) : bool :=
  match l with
  | nil  => false
  | e :: l' => F e || Find l'
  end.
End Find.
Section Sorted.
  Variable T : Set.
  Variable F : T -> T -> bool.
  Fixpoint Sorted ( l : list T ) : bool :=
  match l with
  | nil => true
  | l' :: list' =>
      match list' with
      | nil => true  
      | r' :: list'' => F l' r' || Sorted list'
      end
  end.
End Sorted.
Section InsertEqual.
  Variable T : Set.
  Variable F : T -> T -> bool.
  Variable P : T -> bool.
  Lemma InsertEqual : forall (E : T)(L : list T),
          Find T P ( Insert T F E L ) = 
          Find T P L  || P E.
    intro.
    induction L.
    simpl;destruct (P E);reflexivity.
    simpl.
    destruct (F E a).
    simpl.
    destruct (P E),(P a),(Find T P L);reflexivity.
    simpl.
    rewrite IHL.
    destruct (P a);reflexivity.
  Qed.
End InsertEqual.
Section InsertSorted.
  Variable T : Set.
  Variable F : T -> T -> bool.
  Variable P : T -> bool.
  Lemma InsertSorted : forall L E,
      Is_true( Sorted T F L )->Is_true( Sorted T F (Insert T F E L) ).
    intros.
    induction L.
    reflexivity.
    simpl.
    remember (F E a).
    destruct b.
    simpl in *.
    rewrite <- Heqb.
    reflexivity.
    simpl in *.
  Admitted.
End InsertSorted.
Section InsertionSortSorted.
  Variable T : Set.
  Variable F : T -> T -> bool.
  Variable P : T -> bool.
  Lemma InsertionSortSorted : forall L,
    Is_true( Sorted T F ( InsertionSort T F L ) ).
    intros.
    induction L.
    reflexivity.
    simpl.
    apply InsertSorted.
    trivial.
  Qed.
End InsertionSortSorted.
Section InsertCorrect.
  Variable T : Set.
  Variable F : T -> T -> bool.
  Variable P : T -> bool.
  Lemma InsertCorrect : forall E L,
    Is_true (Sorted T F L) ->
      Find T P ( Insert T F E L ) = 
      Find T P L  || P E /\
      Is_true( Sorted T F ( Insert T F E L ) ).
    split.
    apply InsertEqual.
    apply InsertSorted.
    assumption.
  Qed.
End InsertCorrect.
Section InsertionSortEqual.
  Variable T : Set.
  Variable F : T -> T -> bool.
  Variable P : T -> bool.
  Lemma InsertionSortEqual : forall(L : list T),
    Find T P ( InsertionSort T F L ) = Find T P L.
    intros.
    destruct L.
    reflexivity.
    simpl.
  Admitted.
End InsertionSortEqual.
Section InsertionSortCorrect.
 Variable T : Set.
 Variable F : T -> T -> bool.
  Variable P : T -> bool.
  Lemma InsertionSortCorrect : forall L,
    Is_true( Sorted T F ( InsertionSort T F L ) ) /\
    Find T P ( InsertionSort T F L ) = Find T P L.
    intros.
    split.
    apply InsertionSortSorted.
    apply InsertionSortEqual.
  Qed.
End InsertionSortCorrect.
Print Assumptions InsertionSortCorrect.