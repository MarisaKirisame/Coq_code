Require Export CoqFunctor.Functor CoqMonad.OptionMonad Program CoqCore.Tactic.

Inductive E :=
| BConst (b : bool)
| NConst (n : nat)
| Plus (l r : E)
| Mult (l r : E)
| And (l r : E)
| Or (l r : E)
| Neg (l : E)
| ITE (i t e : E).

Inductive ITT := ITbool | ITnat.

Definition ITTEqDec (l r : ITT) : { l = r } + { l <> r }.
  decide equality.
Defined.

Definition AssertEQ l r := if ITTEqDec l r then Some unit else None.

Fixpoint ITTD (e : E) : option ITT :=
  match e with
  | BConst _ => ret ITbool
  | NConst _ => ret ITnat
  | Plus l r => 
      lt <- ITTD l;; rt <- ITTD r;; AssertEQ lt ITnat;; AssertEQ rt ITnat;; ret ITnat
  | Mult l r => 
      lt <- ITTD l;; rt <- ITTD r;; AssertEQ lt ITnat;; AssertEQ rt ITnat;; ret ITnat
  | And l r => 
      lt <- ITTD l;; rt <- ITTD r;; AssertEQ lt ITbool;; AssertEQ rt ITbool;; ret ITbool
  | Or l r => 
      lt <- ITTD l;; rt <- ITTD r;; AssertEQ lt ITbool;; AssertEQ rt ITbool;; ret ITbool
  | Neg e => et <- ITTD e;; AssertEQ et ITbool;; ret ITbool
  | ITE i t e => 
      it <- ITTD i;; tt <- ITTD t;; et <- ITTD e;; AssertEQ it ITbool;; AssertEQ tt et;; ret tt
  end.

Definition TD (i : ITT) := match i with ITbool => bool | ITnat => nat end.
Open Scope bool.

Program Fixpoint vd e v : ITTD e = Some v -> TD v := 
  match e with
  | BConst b => fun _ => eq_rect ITbool TD b v _
  | NConst n => fun _ => eq_rect ITnat TD n v _
  | Plus l r => fun _ => eq_rect ITnat TD (vd l ITnat _ + vd r ITnat _) v _
  | Mult l r => fun _ => eq_rect ITnat TD (vd l ITnat _ * vd r ITnat _) v _
  | And l r => fun _ => eq_rect ITbool TD (vd l ITbool _ && vd r ITbool _) v _
  | Or l r => fun _ => eq_rect ITbool TD (vd l ITbool _ || vd r ITbool _) v _
  | Neg e => fun _ => eq_rect ITbool TD (negb (vd e ITbool _)) v _
  | ITE i t e => fun _ => if vd i ITbool _ then vd t v _ else vd e v _
  end.
Solve All Obligations with 
  program_simpl; unfold AssertEQ in *; repeat match_destruct; congruence.

Definition simpl1 e : E :=
  match e with
  | Neg (BConst b) => BConst (negb b)
  | And (BConst l) (BConst r) => BConst (l && r)
  | _ => e
  end.

Ltac l :=
  repeat
    match goal with
    | H : Some ?X = Some ?Y |- _ => assert(X = Y) by (invcs H; trivial); subst X || subst Y
    end.

Program Definition VD e : match ITTD e with Some v => TD v | None => unit end :=
  match ITTD e with
  | Some v => vd e v _
  | None => tt
  end.

Theorem Simpl1PreserveT e :  ITTD (simpl1 e) = ITTD e.
  repeat (
    simpl in *; unfold eq_rect, AssertEQ, simpl1 in *; intros; subst;
    l; erewrite ?(UIP_refl _ _ _) in *; try match_destruct; simpl in *; try congruence).
Qed.

Theorem S : forall e, VD (simpl1 e) ~= VD e.
  repeat (
    simpl in *; unfold eq_rect, AssertEQ, simpl1 in *; intros; subst;
    l; erewrite ?(UIP_refl _ _ _) in *; try match_destruct; simpl in *; trivial).
Qed.