Set Universe Polymorphism.
Set Implicit Arguemnts.

Definition F (f : Type -> Type) :=
  forall r, (forall x, (x -> r) -> (f x -> r)) -> r.

Definition natF := F (fun x => option x).

Definition natFnat (n : natF) : nat :=
  n _
    (fun _ f o =>
       match o with
       | None => 0
       | Some x => S (f x)
       end).

Definition OF : natF :=
  fun r f => f r (@id r) None.

Definition SF (n : natF) : natF :=
  fun r f => f natF (fun n => n r f) (Some n).
