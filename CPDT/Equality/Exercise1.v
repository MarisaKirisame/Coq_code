Set Implicit Arguments.

Require Import List.

Section hlist.

  Variable T : Type.
  Variable F : T -> Type.

  Inductive hlist : list T -> Type :=
  | HNil : hlist nil
  | HCons : forall x ls, F x -> hlist ls -> hlist (x :: ls).

  Fixpoint happ (ls1 : list T) (hl1 : hlist ls1) : 
    forall ls2, hlist ls2 -> hlist (ls1 ++ ls2) :=
    match hl1 in hlist ls1
    return forall ls2, hlist ls2 -> hlist (ls1 ++ ls2) with
    | HNil => fun _ hl2 => hl2
    | HCons _ _ x hl1' => fun _ hl2 => HCons x (happ hl1' hl2)
    end.

  Variable elm : T.

  Inductive member : list T -> Type :=
  | first : forall ls, member (elm :: ls)
  | next : forall x ls, member ls -> member (x :: ls).

  Definition hget ls (mls : hlist ls) : member ls -> F elm.
    induction mls.
    intros.
    inversion X.
    intros.
    inversion X.
    trivial.
    subst.
    tauto.
  Defined.

End hlist.

Recursive Extraction happ hget.

Implicit Arguments HNil[T F].
Implicit Arguments HCons[T F x ls].
Implicit Arguments first[T elm ls].
Implicit Arguments next[T elm x ls].

Inductive type :=
| tbool
| tarrow : type -> type -> type.

Inductive exp : list type -> type -> Type :=
| const : forall ts, bool -> exp ts tbool
| var : forall t ts, member t ts -> exp ts t
| app : forall ts dom ran, exp ts (tarrow dom ran) -> exp ts dom -> exp ts ran
| abs : forall ts dom ran, exp (dom :: ts) ran -> exp ts (tarrow dom ran).

Fixpoint typeDenote t :=
  match t with
  | tbool => bool
  | tarrow l r => typeDenote l -> typeDenote r
  end.

Fixpoint expDenote ts t (e : exp ts t) : hlist typeDenote ts -> typeDenote t :=
  match e with
  | const _ b => fun _ => b
  | var _ _ mem => fun l => hget l mem
  | app _ _ _ l r => fun v => (expDenote l v)(expDenote r v)
  | abs _ _ _ e' => fun s => fun x => expDenote e' (HCons x s)
  end.

Definition liftVar ts1 ts2 t (t' : type)(m : member t (ts1 ++ ts2)) : 
  member t (ts1 ++ t' :: ts2).
  induction ts1;
  subst;
  simpl in *.
  constructor.
  trivial.
  inversion m;
  subst.
  constructor.
  constructor.
  tauto.
Defined.

Recursive Extraction liftVar.

Fixpoint lift' ts t ts1 ts2 t' (e : exp ts t) {struct e} :
  ts = ts1 ++ ts2 -> exp (ts1 ++ t' :: ts2) t.
  destruct e;
  intros;
  subst.
  constructor.
  apply b.
  constructor.
  apply liftVar.
  trivial.
  eapply app.
  eauto.
  eauto.
  apply abs.
  change(exp ((dom :: ts1) ++ t' :: ts2) ran).
  eapply lift'.
  eauto.
  trivial.
Defined.

Recursive Extraction lift'.

Definition lift ts t t' (e : exp ts t) : exp ( t' :: ts ) t :=
  lift' nil ts t' e eq_refl.

Definition eq_type_dec : forall l r : type, {l = r} + {l <> r}.
  induction l.
  destruct r.
  tauto.
  right.
  discriminate.
  destruct r.
  right.
  discriminate.
  case(IHl1 r1);
  case(IHl2 r2);
  intros;
  subst;
  try tauto;
  right;
  unfold not in *;
  intros H;
  inversion H;
  subst;
  tauto.
Defined.

Definition substVar : forall ts1 ts2 t (t' : type),
  member t (ts1 ++ t' :: ts2) -> (t' = t) + member t (ts1 ++ ts2).
  induction ts1.
  simpl in *.
  intros.
  inversion H;
  subst;
  tauto.
  intros.
  simpl in *.
  inversion H;
  subst.
  right.
  constructor.
  case(IHts1 ts2 t t').
  trivial.
  tauto.
  intros.
  right.
  constructor.
  trivial.
Defined.

Fixpoint subst' ts t ( e : exp ts t ) ts1 t' ts2 :
  ts = ts1 ++ t' :: ts2 -> exp ( ts1 ++ ts2 ) t' -> exp ( ts1 ++ ts2 ) t.
  intros.
  destruct e;
  subst.
  constructor.
  apply b.
  assert((t' = t) + (member t (ts1 ++ ts2))).
  eapply substVar.
  trivial.
  destruct H.
  subst.
  trivial.
  constructor.
  trivial.
  eapply app.
  eapply subst'.
  eauto.
  trivial.
  trivial.
  eauto.
  apply abs.
  change(exp ((dom :: ts1) ++ ts2) ran).
  eapply subst'.
  eauto.
  tauto.
  simpl in *.
  eapply lift.
  trivial.
Defined.

Definition subst t' ts t (H : exp ( t' :: ts ) t)(H0 : exp ts t') := 
  subst' H nil ts eq_refl H0.

Notation "x ::: y" := (HCons x y)(at level 0).
Notation "x +++ y" := (happ x y)(at level 0).

Goal forall ts1 ts2 t (t' : type)(m : member t (ts1 ++ ts2)) v
  (hl1 : hlist typeDenote ts1)(hl2 : hlist typeDenote ts2),
  hget (hl1 +++ (v ::: hl2)) (liftVar ts1 ts2 t' m) = hget (hl1 +++ hl2) m.

Goal forall t' ts t (e : exp (t' :: ts) t)
  (e' : exp ts t') (s : hlist typeDenote ts),
    expDenote (subst e e') s = expDenote e ((expDenote e' s) ::: s).

Prove a correctness theorem for each auxiliary function, leading up to the 
proof of subst correctness.

All of the reasoning about equality proofs in these theorems follows a regular
pattern. If you have an equality proof that you want to replace with eq refl
somehow, run generalize on that proof variable. Your goal is to get to the
point where you can rewrite with the original proof to change the type of the
generalized version. To avoid type errors
(the infamous "second-order unification failure messages), 
it will be helpful to run generalize on other pieces of the
proof context that mention the equality's lefthand side. You might also want to
use generalize dependent , which generalizes not just one variable but also all
variables whose types depend on it. generalize dependent has the sometimes-
helpful property of removing from the context all variables that it generalizes.
9Once you do manage the mind-bending trick of using the equality proof to rewrite
its own type, you will be able to rewrite with UIP_refl.
The ext eq axiom from the end of this chapter is available 
in the Coq standard library as functional extensionality 
in module FunctionalExtensionality,
and you will probably want to use it in the lift' and subst' correctness proofs.