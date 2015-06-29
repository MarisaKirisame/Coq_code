Require Export List Permutation Program.
Set Implicit Arguments.
Variable ID : Type.
Inductive LL := 
| LAtomic : ID -> LL
| LInv : ID -> LL
| LTimes : LL -> LL -> LL
| LPlus : LL -> LL -> LL
| LWith : LL -> LL -> LL
| LPar : LL -> LL -> LL
| LOne | LZero | LTrue | LFalse
| LBang : LL -> LL
| LWhyNot : LL -> LL.
Fixpoint Dual l := 
  match l with
  | LAtomic i => LInv i
  | LInv i => LAtomic i
  | LTimes l r => LPar (Dual l) (Dual r)
  | LPlus l r => LWith (Dual l) (Dual r)
  | LPar l r => LTimes (Dual l) (Dual r)
  | LWith l r => LPlus (Dual l) (Dual r)
  | LOne => LFalse
  | LZero => LTrue
  | LTrue => LZero
  | LFalse => LOne
  | LBang l' => LWhyNot (Dual l')
  | LWhyNot l' => LBang (Dual l')
  end.
Theorem DualInvolution l : Dual (Dual l) = l.
  induction l;simpl in *;repeat match goal with H : _ = _ |- _ => rewrite !H end;trivial.
Qed.
Definition LImp l r := LPar (Dual l) r.
Inductive SeqCal : list LL -> Type :=
| SEx : forall l r, Permutation l r -> SeqCal l -> SeqCal r
| SInit : forall A, SeqCal [A;Dual A]
| SCut : forall l r A, SeqCal (A :: l) -> SeqCal (Dual A :: r) -> SeqCal (l ++ r)
| STimes : forall l r A B, SeqCal (A :: l) -> SeqCal (B :: r) -> 
    SeqCal (LTimes A B :: l ++ r)
| SPar : forall l A B, SeqCal (A :: B :: l) -> SeqCal (LPar A B :: l)
| SOne : SeqCal [LOne]
| SFalse : forall l, SeqCal (LFalse::l)
| SWith : forall l A B, SeqCal (A :: l) -> SeqCal (B :: l) -> SeqCal (LWith A B :: l)
| SPlusL : forall l A B, SeqCal (A :: l) -> SeqCal (LPlus A B :: l)
| SPlusR : forall l A B, SeqCal (B :: l) -> SeqCal (LPlus A B :: l)
| STrue : forall l, SeqCal (LTrue :: l)
| SWeak : forall l A, SeqCal (LWhyNot A :: l)
| SCon : forall l A, SeqCal (LWhyNot A :: LWhyNot A :: l) -> SeqCal (LWhyNot A :: l)
| SBang : forall l A, SeqCal (A :: map LWhyNot l) -> SeqCal (LBang A :: map LWhyNot l)
| SWhyNot : forall l A, SeqCal (A :: l) -> SeqCal (LWhyNot A :: l).
Hint Constructors SeqCal.
Definition LEq l r := LWith (LImp l r) (LImp r l).
Goal forall A B C, SeqCal [LEq (LTimes A (LPlus B C)) (LPlus (LTimes A B) (LTimes A C))].
  repeat (simpl;constructor).
  eapply SEx with [LWith (Dual B) (Dual C);LPlus (LTimes A B) (LTimes A C);Dual A].
  symmetry.
  eapply perm_trans.
  apply perm_swap.
  apply perm_skip.
  apply perm_swap.
  constructor;(eapply SEx;[apply perm_swap|]).
  apply SPlusL.
  admit.
  apply SPlusR.
  admit.
  eapply SEx with [LTimes A (LPlus B C);Dual A;Dual B].
  eapply perm_trans.
  apply perm_swap.
  apply perm_skip.
  apply perm_swap.
  change [Dual A;Dual B] with ([Dual A] ++ [Dual B]);auto.
  eapply SEx with [LTimes A (LPlus B C);Dual A;Dual C].
  eapply perm_trans.
  apply perm_swap.
  apply perm_skip.
  apply perm_swap.
  change [Dual A;Dual C] with ([Dual A] ++ [Dual C]);auto.
Admitted.