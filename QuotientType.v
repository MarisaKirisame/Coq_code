Require Fin Vector.
Require Import Program Arith Omega CoqCore.Tactic.
Set Implicit Arguments.

Inductive MFEDSL : nat -> Type :=
| MFEDSLE : MFEDSL 0
| MFEDSLPlus  n (pre : MFEDSL n) (l : Fin.t n) (r : Fin.t n) : MFEDSL (S n)
| MFEDSLMul   n (pre : MFEDSL n) (l : Fin.t n) (r : Fin.t n) : MFEDSL (S n)
| MFEDSLIntro n (pre : MFEDSL n) (num : nat) : MFEDSL (S n)
| MFEDSLDrop  n (pre : MFEDSL (S n)) (loc : Fin.t (S n)) : MFEDSL n.

Definition Vector_get { A } { n } (v : Vector.t A n) (f : Fin.t n) : A.
  induction v.
  + invcs f.
  + invcs f; [|apply IHv]; ii.
Defined.

Definition Vector_drop { A } { n } (v : Vector.t A n) (f : Fin.t n) : Vector.t A (pred n).
  induction v.
  + invcs f.
  + invcs f; [|destruct n; try solve [invcs H0]; constructor]; ii.
Defined.

Definition MFEDSLNC : forall n (d : MFEDSL n), Vector.t nat n :=
  MFEDSL_rect  (fun n _ => Vector.t nat n)
    (Vector.nil _) 
    (fun n pre H l r => Vector.cons _ (Vector_get H l + Vector_get H r) _ H)
    (fun n pre H l r => Vector.cons _ (Vector_get H l * Vector_get H r) _ H)
    (fun n pre H num => Vector.cons _ num _ H)
    (fun n pre H loc => Vector_drop H loc).

Inductive MFV n :=
| MKMFA : forall 
    (eqb : Fin.t n -> Fin.t n -> bool)
    (plus : Fin.t n -> Fin.t n -> MFV (n + 1))
    (mul : Fin.t n -> Fin.t n -> MFV (n + 1))
    (intro : nat -> Fin.t n -> MFV (n + 1))
    (drop : Fin.t n -> MFV (pred n)), MFV n.

Program Definition Fin_split l r (f : Fin.t (l + r)) : 
  { res : Fin.t l | ` (Fin.to_nat res) = ` (Fin.to_nat f) } + 
  { res : Fin.t r | ` (Fin.to_nat res) = ` (Fin.to_nat f) - l } :=
  match lt_dec (Fin.to_nat f) l with
  | in_left => inl (@Fin.of_nat_lt (Fin.to_nat f) l _)
  | in_right => inr (@Fin.of_nat_lt (Fin.to_nat f - l) r _)
  end.
Solve All Obligations with program_simpl; destruct Fin.to_nat; simpl in *; omega.
Solve All Obligations with program_simpl; rewrite Fin.to_nat_of_nat; trivial.

