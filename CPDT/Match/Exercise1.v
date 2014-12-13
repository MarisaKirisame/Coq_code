Ltac deSome_inner := match goal with
| [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst; deSome_inner
| _ => intros
end.
Ltac deSome := deSome_inner; reflexivity.

Theorem test : forall (a b c d e f g : nat), 
  Some a = Some b -> Some b = Some c -> Some e = Some c -> Some f = Some g -> c = a.
  intros; deSome .
Qed.
