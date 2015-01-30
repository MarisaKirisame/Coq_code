Set Implicit Arguments.

Inductive hlist (F : Type -> Type) : list Type -> Type :=
| hnil : hlist F nil
| hcons : forall T L (f : F T), hlist F L -> hlist F (T :: L).

Arguments hlist F _.
Arguments hcons { F } { T } { L } f _.
Arguments hnil { _ }.

Inductive hlist_forall (F : Type -> Type) { P : forall T, F T -> Type } : 
  forall L, hlist F L -> Type :=
| Forall_hnil : hlist_forall hnil
| Forall_hcons : forall (l : list Type)(L : hlist F l)(T : Type)(t : F T), 
    P T t -> hlist_forall L -> hlist_forall (hcons t L).

Arguments hlist_forall [F] P L _.

Definition hmap { F : Type -> Type } { M : Type -> Type } { MF : forall T, F T -> M (F T) }
  (lt : list Type)(hl : hlist F lt) : 
    hlist (fun T => M (F T)) lt.
  induction hl;
  constructor;
  auto.
Defined.