Require Export ZArith Ring.
Set Implicit Arguments.
Record vector := { x : Z; y : Z; z : Z }.
Definition dotproduct l r : Z := x l * x r + y l * y r + z l * z r.
Definition crossproduct l r  := 
{| 
    x :=   y l * z r - z l * y r;
    y := -(x l * z r - z l * x r);
    z :=   x l * y r - y l * x r
|}.
Definition mulitply l r :=
{|
  x := l * x r;
  y := l * y r;
  z := l * z r;
|}.
Definition minus l r :=
{|
  x := x l - x r;
  y := y l - y r;
  z := z l - z r;
|}.
Notation "l ∘ r" := (dotproduct l r)(at level 40).
Notation "l ⨯ r" := (crossproduct l r)(at level 40).
Notation "l * r" := (mulitply l r).
Notation "l - r" := (minus l r).
Goal forall a b c, a ⨯ (b ⨯ c) = (a ∘ c) * b - (a ∘ b) * c.
  intros; compute[dotproduct crossproduct mulitply minus]; simpl.
  f_equal; ring.
Qed.

Goal forall a b c d, ((a ⨯ b) ∘ (c ⨯ d) = (a ∘ c) * (b ∘ d) - (b ∘ c) * (a ∘ d))%Z.
  intros; compute [dotproduct crossproduct]; simpl; ring.
Qed.