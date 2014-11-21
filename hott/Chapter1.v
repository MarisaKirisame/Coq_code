Set Implicit Arguments.

Definition composite A B C(f : A -> B)(g : B -> C) : A -> C.
  tauto.
Defined.

Goal forall A B C D (h : A -> B) (g : B -> C) (f : C -> D),
  (composite h (composite g f)) = (composite (composite h g) f).
  trivial.
Qed.