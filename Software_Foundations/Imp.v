Require Import Arith Omega List Program.

Set Implicit Arguments.

Inductive id : Type := Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
  intros.
  destruct id1, id2.
  destruct (eq_nat_dec n n0).
  subst.
  tauto.
  right.
  intuition.
  inversion H.
  tauto.
Defined.

Lemma eq_id : forall(T:Type) x (p q:T), (if eq_id_dec x x then p else q) = p.
  intros.
  destruct (eq_id_dec x x);
  tauto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if eq_id_dec x y then p else q) = q.
  intros.
  destruct (eq_id_dec x y);
  tauto.
Qed.

Definition state := id -> nat.

Definition empty_state : state := fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

Theorem update_eq : forall n x st,
  (update st x n) x = n.
  intros.
  unfold update.
  apply eq_id.
Qed.

Theorem update_neq : forall x2 x1 n st, x2 <> x1 ->
  (update st x2 n) x1 = (st x1).
  intros.
  unfold update.
  apply neq_id.
  trivial.
Qed.

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
  trivial.
Qed.

Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
  (update (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
  intros.
  unfold update.
  destruct (eq_id_dec x2 x1);
  trivial.
Qed.

Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
    (update st x1 n1) x2 = st x2.
  intros.
  subst.
  unfold update.
  destruct (eq_id_dec x1 x2);
  subst;
  trivial.
Qed.

Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 ->
    (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
  intros.
  unfold update.
  destruct (eq_id_dec x1 x3).
  subst.
  symmetry.
  apply neq_id.
  trivial.
  trivial.
Qed.

Inductive aexp : Type :=
| AId : id -> aexp
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state)(a : aexp) : nat :=
  match a with
  | AId i => st i
  | ANum n => n
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state)(b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Program Definition aremove_const (a:aexp) : {ret: aexp| forall st, aeval st ret = aeval st a} :=
  match a with
  | APlus a (ANum 0) | APlus (ANum 0) a => a
  | APlus (ANum l) (ANum r) => ANum (l + r)
  | AMinus a (ANum 0) => a
  | AMinus (ANum l) (ANum r) => ANum (l - r)
  | AMult a (ANum 1) | AMult (ANum 1) a => a
  | AMult _ (ANum 0) | AMult (ANum 0) _ => ANum 0
  | AMult (ANum l) (ANum r) => ANum (l * r)
  | default => default
  end.
  Next Obligation.
    omega.
  Defined.
  Next Obligation.
    ring.
  Defined.
  Solve All Obligations using intros;intuition;discriminate.

Fixpoint aoptimize_inner
  (optimize_func : 
    forall a,{ret: aexp| forall st, aeval st ret = aeval st a})(a:aexp) { struct a } : aexp :=
  proj1_sig 
    (optimize_func
      match a with
      | APlus l r => 
          APlus 
            (aoptimize_inner optimize_func l)
            (aoptimize_inner optimize_func r)
      | AMinus l r => 
          AMinus
            (aoptimize_inner optimize_func l)
            (aoptimize_inner optimize_func r)
      | AMult l r => 
          AMult 
            (aoptimize_inner optimize_func l)
            (aoptimize_inner optimize_func r)
      | default => default
    end).

Program Definition aoptimize
  (optimize_func : forall a,{ret: aexp| forall st, aeval st ret = aeval st a})(a:aexp) :
    {ret | forall st, aeval st ret = aeval st a} := aoptimize_inner optimize_func a.
  Next Obligation.
    induction a;
    simpl in *;
    repeat
      match goal with
      |- context f [optimize_func ?X] => 
          destruct (optimize_func X)
      end;
      simpl in *;
    trivial;
    rewrite e;
    auto.
  Defined.

Fixpoint BConst(b : bool) := if b then BTrue else BFalse.

Program Definition bremove_const (b : bexp) : 
  {ret: bexp| forall st, beval st ret = beval st b} :=
  match b with
  | BEq (ANum l) (ANum r) => BConst (beq_nat l r)
  | BLe (ANum l) (ANum r) => BConst (leb l r)
  | BAnd b BTrue | BAnd BTrue b => b
  | BNot BFalse => BTrue
  | BNot BTrue | BAnd _ BFalse | BAnd BFalse _ => BFalse
  | default => default
  end.
  Solve Obligations using
    intuition;
    match goal with
    |- context f [BConst ?X] => 
      destruct X eqn:H1
    end;
    simpl in *;
    auto.
  Solve Obligations using
    intros;
    subst;
    simpl in *;
    ring.
  Solve Obligations using
    intros;
    intuition;
    simpl in *;
    discriminate.

Fixpoint boptimize_inner aoptimize_func
  (boptimize_func : forall b, {b'| forall st, beval st b' = beval st b})
    (b : bexp) : bexp :=
  proj1_sig(boptimize_func
    match b with
    | BEq l r => 
        BEq
          (proj1_sig(aoptimize aoptimize_func l))
          (proj1_sig(aoptimize aoptimize_func r))  
    | BLe l r => 
        BLe
          (proj1_sig(aoptimize aoptimize_func l))
          (proj1_sig(aoptimize aoptimize_func r))
    | BNot b' => BNot (boptimize_inner aoptimize_func boptimize_func b')
    | BAnd l r => 
        BAnd
          (boptimize_inner aoptimize_func boptimize_func l)
          (boptimize_inner aoptimize_func boptimize_func r)
    | default => default
    end).

Program Definition boptimize aoptimize_func
  (boptimize_func : forall b, {b'| forall st, beval st b' = beval st b})
    (b : bexp) :
      {ret | forall st, beval st ret = beval st b} := 
        boptimize_inner aoptimize_func boptimize_func b.
  Next Obligation.
    induction b;
    compute [boptimize_inner];
    repeat
      match goal with
      |- context f [boptimize_func ?X] => 
        destruct (boptimize_func X)
      end;
    trivial;
    repeat
      match goal with
      |- context f [aoptimize aoptimize_func ?X] => 
        destruct (aoptimize aoptimize_func X)
      end;
    simpl in *;
    eauto;
    simpl in *;
    repeat
      match goal with
      |- context f [boptimize_func ?X] => 
        destruct (boptimize_func X)
      end;
    trivial;
    simpl in *;
    rewrite e;
    f_equal;
    trivial.
  Defined.

Inductive aevalR : state -> aexp -> nat -> Prop :=
| E_ANum : forall(n: nat) st,
    aevalR st (ANum n) n
| E_APlus : forall(e1 e2: aexp) (n1 n2: nat) st,
    aevalR st e1 n1 ->
      aevalR st e2 n2 ->
        aevalR st (APlus e1 e2) (n1 + n2)
| E_AMinus: forall(e1 e2: aexp) (n1 n2: nat) st,
    aevalR st e1 n1 ->
      aevalR st e2 n2 ->
        aevalR st (AMinus e1 e2) (n1 - n2)
| E_AMult : forall(e1 e2: aexp) (n1 n2: nat) st,
    aevalR st e1 n1 ->
      aevalR st e2 n2 ->
        aevalR st (AMult e1 e2) (n1 * n2)
| E_AId : forall id st, aevalR st (AId id) (st id).

Inductive bevalR : state -> bexp -> bool -> Prop :=
| E_BTrue : forall st, bevalR st BTrue true
| E_BFalse : forall st, bevalR st BFalse false
| E_BEq : forall a1 a2 n1 n2 st,
    aevalR st a1 n1 -> 
      aevalR st a2 n2 -> 
        bevalR st (BEq a1 a2) (beq_nat n1 n2)
| E_BLe : forall a1 a2 n1 n2 st,
    aevalR st a1 n1 -> 
      aevalR st a2 n2 -> 
        bevalR st (BLe a1 a2) (leb n1 n2)
| E_BNot : forall b bo st, 
    bevalR st b bo ->
      bevalR st (BNot b) (negb bo)
| E_BAnd : forall b1 b2 bo1 bo2 st,
    bevalR st b1 bo1 -> 
      bevalR st b2 bo2 ->
        bevalR st (BAnd b1 b2) (andb bo1 bo2).

Theorem aevalR_correct : forall a n st, aevalR st a n <-> aeval st a = n.
  split.
  induction 1;
  intros;
  subst;
  trivial.
  generalize dependent n.
  induction a;
  intros;
  subst;
  simpl in *;
  constructor;
  auto.
Qed.

Theorem bevalR_correct : forall b bo st, bevalR st b bo <-> beval st b = bo.
  intuition.
  induction H;
  simpl in *;
  subst;
  trivial;
  f_equal;
  apply aevalR_correct;
  trivial.
  generalize dependent bo.
  induction b;
  intros;
  subst;
  simpl in *;
  constructor;
  auto;
  apply aevalR_correct;
  trivial.
Qed.

Inductive com : Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com
| CBreak.

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Definition X := Id 0.
Definition Y := Id 1.
Definition Z := Id 2.

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

Inductive status : Type :=
| SContinue : status
| SBreak : status.

Inductive ceval : com -> status -> state -> state -> Prop :=
| E_Skip : forall st,
    ceval SKIP SContinue st st
| E_Ass : forall st a1 n x,
    aeval st a1 = n ->
      ceval (x ::= a1) SContinue st (update st x n)
| E_Seq : forall c1 c2 st st' st'' sta,
    ceval c1 SContinue st st' ->
      ceval c2 sta st' st'' ->
        ceval (c1 ;; c2) sta st st''
| E_SeqBreak : forall c1 c2 st st',
    ceval c1 SBreak st st' -> ceval (c1 ;; c2) SBreak st st'
| E_IfTrue : forall st st' b c1 c2 sta,
    beval st b = true ->
      ceval c1 sta st st' ->
        ceval (IFB b THEN c1 ELSE c2 FI) sta st st'
| E_IfFalse : forall st st' b c1 c2 sta,
    beval st b = false ->
      ceval c2 sta st st' ->
        ceval (IFB b THEN c1 ELSE c2 FI) sta st st'
| E_WhileEnd : forall b st c,
    beval st b = false ->
      ceval (WHILE b DO c END) SContinue st st
| E_WhileLoop : forall st st' st'' b c,
    beval st b = true ->
      ceval c SContinue st st' ->
        ceval (WHILE b DO c END) SContinue st' st'' ->
          ceval (WHILE b DO c END) SContinue st st''
| E_WhileBreak : forall st st' b c,
    beval st b = true ->
      ceval c SBreak st st' ->
          ceval (WHILE b DO c END) SContinue st st'
| E_Brake : forall st, ceval BREAK SBreak st st.

Example ceval_example2:
  ceval
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2)
      SContinue
      empty_state
        (update (update (update empty_state X 0) Y 1) Z 2).
  econstructor.
  constructor.
  simpl.
  reflexivity.
  econstructor.
  constructor.
  simpl.
  reflexivity.
  constructor.
  trivial.
Qed.

Definition pup_to_n : com :=
  Y ::= (ANum 0);;
  WHILE (BNot (BEq (ANum 0) (AId X)))
  DO
    Y ::= (APlus (AId Y) (AId X));; 
    X ::= (AMinus (AId X) (ANum 1))
  END.

Theorem pup_to_2_ceval :
  ceval
    pup_to_n
      SContinue
      (update empty_state X 2)
        (update 
          (update
            (update
              (update
                (update
                  (update
                    empty_state
                    X 2)
                  Y 0)
                Y 2)
              X 1)
            Y 3)
          X 0).
  unfold pup_to_n.
  repeat
    match goal with
    |- context f [ ceval ?C _ _ _ ] => 
        match C with
        | (WHILE _ DO _ END) => 
            try (apply E_WhileEnd; reflexivity); eapply E_WhileLoop; try reflexivity
        | (_ ::= _) => eapply E_Ass; try reflexivity
        | (_ ;; _) => eapply E_Seq; try reflexivity
        end
    end.
Qed.

Ltac invc H := inversion H; subst; clear H.

Ltac invc_stop := 
  repeat match goal with
  | [ H : ceval SKIP _ _ _ |- _ ] => invc H
  | [ H : ceval (CAss _ _) _ _ _ |- _ ] => invc H
  | [ H : ceval (CSeq _ _) _ _ _ |- _ ] => invc H
  | [ H : ceval (CIf _ _ _) _ _ _ |- _ ] => invc H
  | [ H : ceval BREAK _ _ _ |- _ ] => invc H
  end.

Theorem forall_split : 
  forall T L R,
    (forall s : T, L s /\ R s) <-> 
      (forall s, L s) /\ (forall s, R s).
  intuition;
  destruct (H s);
  trivial.
Qed.

Theorem ceval_deterministic: forall c st sta1 sta2 st1 st2,
  ceval c sta1 st st1 ->
    ceval c sta2 st st2 ->
      sta1 = sta2 /\ st1 = st2.
  intros.
  generalize dependent st2.
  generalize dependent sta2.
  assert
    ((forall sta2 st2, ceval c sta2 st st2 -> sta1 = sta2) /\ 
    (forall sta2 st2, ceval c sta2 st st2 -> st1 = st2)).
  induction H;
  intros;
  intuition;
  invc_stop;
  trivial;
  match goal with
  | [ H : _ = true |- _] => rewrite H in *
  | _ => idtac
  end;
  try discriminate;
  try
    (assert(SContinue = SBreak);
    eauto;
    discriminate);
  try
    (assert(SBreak = SContinue);
    eauto;
    discriminate);
  try (assert(st' = st'0);[eauto;fail|]);
  subst;
  eauto.
  invc H0;
  trivial.
  invc H0;
  trivial;
  match goal with
  | [ H : _ = true |- _] => rewrite H in *
  | _ => idtac
  end;
  try discriminate.
  invc H6;
  trivial.
  invc H6;
  trivial;
  match goal with
  | [ H : _ = true |- _] => rewrite H in *
  | _ => idtac
  end;
  try discriminate.
  try (assert(st' = st'0);[eauto;fail|]);
  subst;
  eauto.
  try
    (assert(SContinue = SBreak);
    eauto;
    discriminate).
  invc H3;
  trivial.
  invc H3;
  eauto with *.
  try
    (assert(SBreak = SContinue);
    eauto;
    discriminate).
  intuition;
  eauto.
Qed.

Goal forall st x y st',
  st X = x -> st Y = y -> ceval XtimesYinZ SContinue st st' -> st' Z = x * y.
  intros.
  invc H1.
  trivial.
Qed.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Theorem loop_never_stops : forall st sta st',
  ~(ceval loop sta st st').
  remember loop.
  unfold loop in *.
  intuition.
  induction H;
  invc Heqc;
  try discriminate.
  tauto.
  invc H0.
Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP => true
  | _ ::= _ => true
  | c1 ;; c2 => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | BREAK => true
  | WHILE _ DO _ END => false
  end.

Inductive no_whilesR: com -> Prop :=
| NSkip : no_whilesR SKIP
| NAss : forall id a, no_whilesR (id ::= a)
| NSeq : forall cl cr, no_whilesR cl -> no_whilesR cr -> no_whilesR (cl;;cr)
| NIf : forall b cl cr, 
    no_whilesR cl -> 
      no_whilesR cr -> 
        no_whilesR (IFB b THEN cl ELSE cr FI)
| NBreak : no_whilesR BREAK.

Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
  split.
  intros.
  induction c;
  simpl in *;
  try solve [constructor|discriminate];
  destruct (no_whiles c1) eqn:Hc;
  simpl in *;
  try discriminate;
  intuition;
  constructor;
  trivial.
  induction 1;
  trivial;
  simpl in *;
  auto with *.
Qed.

Theorem no_whilesR_terminate c : no_whilesR c -> forall st, exists st' sta, ceval c sta st st'.
  induction 1;
  intros.
  econstructor.
  econstructor.
  constructor.
  econstructor.
  econstructor.
  constructor.
  trivial.
  destruct (IHno_whilesR1 st).
  destruct H1.
  destruct x0.
  destruct (IHno_whilesR2 x).
  destruct H2.
  econstructor.
  econstructor.
  eapply E_Seq.
  eauto.
  eauto.
  econstructor.
  econstructor.
  constructor.
  eauto.
  destruct (IHno_whilesR1 st).
  destruct H1.
  destruct (IHno_whilesR2 st).
  destruct H2.
  destruct (beval st b) eqn:He.
  exists x.
  exists x0.
  constructor.
  trivial.
  trivial.
  exists x1.
  exists x2.
  apply E_IfFalse.
  trivial.
  trivial.
  econstructor.
  econstructor.
  econstructor.
Qed.

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

Fixpoint compile (a : aexp) : list sinstr :=
  match a with
  | ANum n => [SPush n]
  | AId i => [SLoad i]
  | APlus l r => (compile l) ++ (compile r) ++ [SPlus]
  | AMinus l r => (compile l) ++ (compile r) ++ [SMinus]
  | AMult l r => (compile l) ++ (compile r) ++ [SMult]
  end.

Definition sprocess st (stack : list nat) (s : sinstr) : list nat :=
  match stack, s with
  | _, SPush n => n :: stack
  | _, SLoad id => st id :: stack
  | n :: m :: st, SPlus => (m + n) :: st
  | n :: m :: st, SMinus => (m - n) :: st
  | n :: m :: st, SMult => (m * n) :: st
  | _, _ => nil
  end.

Fixpoint seval_inner (st : state) stack (linstr : list sinstr) : list nat :=
  match linstr with
  | nil => stack
  | linstr_head :: linstr_tail => seval_inner st (sprocess st stack linstr_head) linstr_tail
  end.

Definition seval st linstr := seval_inner st nil linstr.

Lemma seval_inner_split : forall st l r stack,
  seval_inner st stack (l ++ r) = seval_inner st (seval_inner st stack l) r.
  induction l.
  trivial.
  intros.
  simpl in *.
  trivial.
Qed.

Lemma seval_inner_correct :
  forall exp st stack, seval_inner st stack (compile exp) = (aeval st exp) :: stack.
  intros.
  generalize dependent stack;
  induction exp;
  try solve
  [
    destruct stack;
    trivial;
    simpl in *;
    destruct stack;
    trivial
  ];
  simpl in *;
  intros;
  repeat rewrite seval_inner_split;
  rewrite IHexp1;
  rewrite IHexp2;
  trivial.
Qed.

Theorem seval_correct : forall exp st, seval st (compile exp) = [aeval st exp].
  unfold seval.
  intros.
  apply seval_inner_correct.
Qed.