Require Export ListMonad.
Set Implicit Arguments.
Eval compute in (fold_left (fun l r => l' <- l;;r' <- r;;ret (r' :: l')) [[1;2];[3;4];[5]] [[]]).