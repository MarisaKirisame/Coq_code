Require Export Program CoqCommon.HList.
Set Implicit Arguments.
Definition FreeFunction := { T : Type & T -> Type }.
Definition InterpretFF (ff : FreeFunction) : Type := forall A : projT1 ff, (projT2 ff) A.
Section CompCoq.
  Variable l : list FreeFunction.
  Variable ff : hlist (fun x => (InterpretFF x * nat)%type) l.
  Inductive CompCoq : forall (T : Type) (F : T -> Type) (C : T -> nat), Type :=
  | CompId T : @CompCoq T (const T) (const 0)
  | CompApp T F (G : forall t, F t -> Type) m (M : member (existT _ T F) l) :
      (forall (t : T), @CompCoq (F t) (G t) (m t)) ->
      @CompCoq
        T 
        (fun x => G x (fst (hget M ff) x))
        (fun x => snd (hget M ff) + m x (fst (hget M ff) x)).
  Definition Yank T F C (CC : @CompCoq T F C) t : F t.
    induction CC; intros; simpl in *; auto.
  Defined.
End CompCoq.

