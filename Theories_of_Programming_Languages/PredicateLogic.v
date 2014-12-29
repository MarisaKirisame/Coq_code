Require Import ZArith Omega FSets.

Set Implicit Arguments.

Open Scope Z_scope.

  Section Pred.
    Definition var := nat.

    Inductive intexp :=
    | IConst : Z -> intexp
    | IVar : var -> intexp
    | IBinop : (Z -> Z -> Z) -> intexp -> intexp -> intexp
    | INegative : intexp -> intexp.

    Inductive assert :=
    | AConst : bool -> assert
    | ACmp : (Z -> Z -> Prop) -> intexp -> intexp -> assert
    | ABinop : (Prop -> Prop -> Prop) -> assert -> assert -> assert
    | AInverse : assert -> assert
    | AForall : var -> assert -> assert
    | AExists : var -> assert -> assert.

    Fixpoint ZDenote f i :=
      match i with
      | IConst n => n
      | IVar n => f n
      | IBinop b l r => b (ZDenote f l) (ZDenote f r)
      | INegative i' => 0 - (ZDenote f i')
      end.

    Fixpoint PredDenote f i :=
      match i with
      | AConst b => b = true
      | ACmp cmp l r => cmp (@ZDenote f l) (ZDenote f r)
      | ABinop F l r => F (PredDenote f l) (PredDenote f r)
      | AInverse p => ~PredDenote f p
      | AForall v a => 
          forall n : Z,
            PredDenote (fun m : var => if beq_nat v m then n else f m) a
      | AExists v a => 
          exists n : Z,
            PredDenote (fun m : var => if beq_nat v m then n else f m) a
      end.

    Definition valid a := forall f, PredDenote f a.

    Theorem PredForall : forall a, 
      valid a -> 
        forall v, valid (AForall v a).
      intros.
      unfold valid.
      simpl in *.
      intros.
      trivial.
    Qed.

    Theorem PredExists : forall a, 
      valid a -> 
        forall v, valid (AExists v a).
      intros.
      unfold valid.
      simpl in *.
      exists 0.
      trivial.
    Qed.

    Goal forall f,
      PredDenote 
        f
        (AForall O (ACmp eq (IVar O)(IBinop Zplus (IVar O) (IConst 0)))).
      intros.
      simpl in *.
      auto with *.
    Qed.
  End Pred.

  Fixpoint IFreeVar i :=
    match i with
    | IConst _ => nil
    | IVar v => v :: nil
    | IBinop _ l r => (IFreeVar l) ++ (IFreeVar r)
    | INegative i' => IFreeVar i'
    end.

  Fixpoint AFreeVar (a : assert):=
    match a with
    | AConst _ => nil
    | ACmp _ l r => (IFreeVar l) ++ (IFreeVar r)
    | ABinop _ l r => (AFreeVar l) ++ (AFreeVar r)
    | AInverse a' => AFreeVar a'
    | AForall v a'
    | AExists v a' => filter(fun n => negb(beq_nat n v))(AFreeVar a')
    end.

Close Scope Z_scope.