Ltac invc H := inversion H; subst; clear H.
Ltac depde H := dependent inversion H; subst; clear H.