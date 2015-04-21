Require Export Relations Classical_sets.
Class PSet := 
{
  T : Type;
  R : relation T;
  R_antisymmetric : antisymmetric _ R;
  R_reflexive : reflexive _ R;
  R_transitive : transitive _ R
}.

Section PSet_Relations.
  Variable P : PSet.
  Definition greatest_element (g : T) : Prop := forall a, R a g.
  Definition least_element (g : T) : Prop := forall a, R g a.
  Theorem greatest_element_unique : 
    forall l r, greatest_element l -> greatest_element r -> l = r.
    intros.
    unfold greatest_element in *.
    apply R_antisymmetric;
    trivial.
  Qed.
  Theorem least_element_unique : 
    forall l r, least_element l -> least_element r -> l = r.
    intros.
    unfold least_element in *.
    apply R_antisymmetric;
    trivial.
  Qed.
  Definition maximal_element (g : T) := forall a, R g a -> a = g.
  Definition minimal_element (g : T) := forall a, R a g -> a = g.
  Theorem greatest_element_unique_maximal_element (g : T) : 
    greatest_element g -> (maximal_element g /\ forall a, maximal_element a -> a = g).
    unfold greatest_element, maximal_element.
    intuition.
    apply R_antisymmetric;
    trivial.
    symmetry.
    apply H0.
    trivial.
  Qed.
  Theorem least_element_unique_minimal_element (g : T) : 
    least_element g -> (minimal_element g /\ forall a, minimal_element a -> a = g).
    unfold least_element, minimal_element.
    intuition.
    apply R_antisymmetric;
    trivial.
    symmetry.
    apply H0.
    trivial.
  Qed.
  Definition upperbound (A : Ensemble T)(g : T) := forall a, A a -> R a g.
  Definition lowerbound (A : Ensemble T)(g : T) := forall a, A a -> R g a.
  Theorem greatest_element_upper_bound : 
    forall g, greatest_element g -> upperbound (fun _ => True) g.
    unfold upperbound, greatest_element.
    trivial.
  Qed.
  Theorem least_element_lower_bound : 
    forall g, least_element g -> lowerbound (fun _ => True) g.
    unfold lowerbound, least_element.
    trivial.
  Qed.
End PSet_Relations.
Definition symbol := nat.