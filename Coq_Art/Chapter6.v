Require Import Arith List ZArith.

Inductive season : Set := Spring | Summer | Fall | Winter.

Theorem bool_equal : forall (b:bool), b=true\/b=false.
  apply bool_ind;
  [apply or_introl|apply or_intror];
  apply refl_equal.
Qed.

Inductive month : Set := 
  January|
  February|
  March|
  April|
  May|
  June|
  July|
  August|
  September|
  October|
  November|
  December.

Definition season_of_month m :=
  (month_rec 
    (fun _:month => season) 
    Winter
    Winter
    Winter
    Spring
    Spring
    Spring
    Summer
    Summer
    Summer
    Fall
    Fall
    Fall) m.

Definition season_of_month' m :=
  match m with
  | January => Winter
  | February => Winter
  | March => Winter
  | April => Spring
  | May => Spring
  | June => Spring
  | July => Summer
  | August => Summer
  | September => Summer
  | October => Winter
  | November => Winter
  | December => Winter
  end.

Definition bool_not( b : bool ) := if b then false else true.
Definition bool_or( l r : bool ) := if l then true else r.
Definition bool_and( l r : bool ) := if l then r else false.
Definition bool_eq( l r : bool ) := if l then r else bool_not r.
Definition bool_xor( l r : bool ) := bool_not (bool_eq l r).

Theorem bool_xor_not_eq : 
  forall b1 b2 : bool, (bool_xor b1 b2) = (bool_not (bool_eq b1 b2)).
  trivial.
Qed.

Theorem bool_not_and : 
  forall b1 b2 : bool,
    (bool_not (bool_and b1 b2)) =
    (bool_or (bool_not b1) (bool_not b2)).
  case b1, b2;auto.
Qed.

Theorem bool_not_not : forall b : bool, (bool_not (bool_not b))=b.
  intros.
  case b;auto.
Qed.

Theorem bool_tex : forall b : bool, (bool_or b (bool_not b))=true.
  intros.
  case b;auto.
Qed.

Theorem bool_eq_reflect : forall b1 b2 : bool, (bool_eq b1 b2)=true -> b1=b2.
  intros.
  case b1, b2;auto.
Qed.

Theorem bool_eq_reflect2 : forall b1 b2 : bool, 
  b1 = b2 ->
    (bool_eq b1 b2) = true.
  intros.
  case b1, b2;auto.
Qed.

Theorem bool_not_or : forall b1 b2 : bool,
  (bool_not (bool_or b1 b2)) = (bool_and (bool_not b1) (bool_not b2)).
  intros.
  case b1, b2;auto.
Qed.

Theorem bool_distr:  forall b1 b2 b3:bool,
  (bool_or (bool_and b1 b3) (bool_and b2 b3)) = (bool_and (bool_or b1 b2) b3).
  intros.
  case b1, b2, b3;auto.
Qed.

Record plane : Set := point {abscissa : Z; ordinate : Z}.

Definition absolute p :=
  match p with
  | Z0 => Z0
  | Zneg x => Zpos x
  | Zpos x => Zneg x
  end.

Open Scope Z_scope.

Definition manhatten l r := 
  absolute ((abscissa l) - (abscissa r)) + 
  absolute ((ordinate l) - (ordinate r)).

Close Scope Z_scope.

Inductive vehicle : Set :=
  bicycle : nat -> vehicle|
  motorized : nat -> nat -> vehicle.

Definition number_of_seats v : nat :=
  vehicle_rec (fun _ => nat) (fun x => x) (fun x _ => x) v.

Definition is_January v : bool :=
  month_rec
    (fun _ => bool) 
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    v.

Goal true <> false.
  unfold not.
  intros.
  change((fun b : bool => if b then False else True)true).
  rewrite H.
  trivial.
Qed.

Record RatPlus : Set := mkRat
  {top : nat; bottom : nat; bottom_condition : bottom <> 0}.

Definition r0 : RatPlus.
  apply (mkRat 1 2).
  auto.
Defined.

Definition r1 : RatPlus.
  apply (mkRat 2 4).
  auto.
Defined.

Definition eq_RatPlus : Prop := forall r r':RatPlus,
  top r * bottom r' = top r' * bottom r -> r = r'.

Goal eq_RatPlus -> False.
  unfold eq_RatPlus.
  intros.
  assert(r0=r1).
  apply H.
  simpl.
  reflexivity.
  discriminate H0.
Qed.

Section partial_functions.
  Variable P : nat -> Prop.
  Variable f : nat -> option nat.

  Hypothesis f_domain : forall n, P n <-> f n <> None.

  Definition g n : option nat := 
    match f (n+2) with None => None 
    | Some y => Some (y + 2)
    end.

  Lemma g_domain : forall n, P (n+2) <-> g n <> None.
    intros;
    case(f_domain (n + 2));
    intros H1 H2;
    unfold g;
    split;
    [
      remember (f (n + 2)) as o;
      destruct o;
      intros;
      [
        discriminate |
        
        apply H1;
        assumption
      ]|
      
      remember (f (n + 2)) as o;
      destruct o;
      intros;
      apply H2;
      discriminate||assumption
    ].
  Qed.
 
End partial_functions.

Definition lt3 n :=
  match n with
  | O => true
  | S O => true
  | _ => false
  end.

Fixpoint plus' l r {struct r}:=
  match r with
  | O => l
  | S x => S (plus' l x)
  end.

Goal forall x y, plus' x y = x + y.
  induction y.
  auto with arith.
  simpl.
  rewrite IHy.
  auto with arith.
Qed.

Open Scope Z_scope.

Fixpoint accumulate( begin time : nat )( f : nat -> Z ) : Z := 
  match time with
  | O => 0
  | S x => (f begin) + accumulate (S begin) x f
  end.

Eval compute in accumulate 0 10 (fun x => Z_of_nat (x * x)).

Fixpoint two_power x := match x with |O => 1 |S x => 2 * (two_power x) end.

Close Scope Z_scope.

Definition _1000 := xO (xO (xO (xI (xO (xI (xI (xI (xI (xH))))))))).

Definition _1024 := xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH))))))))).

Definition _25 := xI (xO (xO (xI xH))).

Definition _512 := xO (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))).

Definition is_even n := match n with | xO _ => true | _ => false end.

Definition div_2 n := 
  match n with
  | xO x => Zpos x
  | xI x => Zpos x
  | xH => Z0 end.

Definition div_4 n :=
  match div_2 n with
  | Z0 => Z0
  | Zpos x => div_2 x
  | Zneg x => div_2 x
  end.

Inductive bool' : Set := 
  true'|
  false'|
  and' : bool' -> bool' -> bool'|
  or' : bool' -> bool' -> bool'|
  not : bool' -> bool'.

Fixpoint bool'_denote b :=
  match b with
  | true' => true
  | false' => false
  | and' l r => bool_and (bool'_denote l) (bool'_denote r)
  | or' l r => bool_or (bool'_denote l) (bool'_denote r)
  | not x => bool_not (bool'_denote x)
  end.

Inductive F := one | N : F -> F | D : F -> F.

Fixpoint fraction f :=
  match f with
  | one => (1,1)
  | N x => let (a,b) := fraction x in (a+b,b)
  | D x => let (a,b) := fraction x in (a,a+b)
  end.

Inductive Z_btree : Set :=
| Z_leaf : Z_btree 
| Z_bnode : Z->Z_btree->Z_btree->Z_btree.

Fixpoint has_occurence find t :=
  match t with
  | Z_leaf => false
  | Z_bnode num l r =>
      bool_or
        (Zeq_bool num find)
        (bool_or
          (has_occurence find l)
          (has_occurence find r))
  end.

Open Scope Z_scope.

Fixpoint power( x : Z )( y : nat ):=
  match y with
  | O => 1
  | S y' => x * (power x y')
  end.

Close Scope Z_scope.

Fixpoint discrete_log p : nat :=
  match p with
  | xH => 0
  | xI p' => S (discrete_log p')
  | xO p' => S (discrete_log p')
end.

Inductive Z_fbtree : Set :=
| Z_fleaf : Z_fbtree 
| Z_fnode : Z  -> (bool -> Z_fbtree) -> Z_fbtree.

Fixpoint fzero_present t :=
  match t with
  | Z_fleaf => false
  | Z_fnode num f => 
      bool_or (Zeq_bool num 0) 
        (bool_or (fzero_present (f true)) (fzero_present (f false)))
  end.

Inductive Z_inf_branch_tree : Set :=
| Z_inf_leaf : Z_inf_branch_tree
| Z_inf_node : Z->(nat->Z_inf_branch_tree)->Z_inf_branch_tree.

Fixpoint zero_reachable t i :=
  match t with 
  | Z_inf_leaf => false
  | Z_inf_node num func =>
      bool_or
        (Zeq_bool num 0)
        ((fix reachable (z : nat) :=
          bool_or
            (zero_reachable (func z) i)
            match z with
            | O => false
            | S x => (reachable x)
            end) i)
  end.

Theorem plus_n_O : forall n, n+0 =n.
  intros.
  elim n.
  reflexivity.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Fixpoint f1 (t : Z_btree) : Z_fbtree :=
  match t with
  | Z_leaf => Z_fleaf
  | Z_bnode num l r => Z_fnode num (fun b => if b then f1 l else f1 r)
  end.

Fixpoint f2 (t : Z_fbtree) : Z_btree :=
  match t with
  | Z_fleaf => Z_leaf
  | Z_fnode num func => Z_bnode num (f2 (func true)) (f2 (func false))
  end.

Theorem f2_f1 : forall t: Z_btree, f2 (f1 t) = t.
  induction t.
  reflexivity.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.
Qed.

Theorem f1_f2 :
  (forall (A B:Set) (f g: A -> B),
    (forall a, f a = g a) -> f = g )->
      (forall t: Z_fbtree, f1 (f2 t) = t).
  induction t.
  reflexivity.
  simpl.
  f_equal.
  apply H.
  destruct a;
  apply H0.
Qed.

Fixpoint mult2 (n:nat) : nat :=
  match n with
    O => O
  | (S p) => (S (S (mult2 p)))
  end.

Goal forall n, n + n = mult2 n.
  induction n.
  reflexivity.
  rewrite <- plus_Snm_nSm.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Fixpoint sum_n (n:nat) : nat :=
  match n with
  | O => O 
  | (S p) => (plus (S p) (sum_n p))
  end.

Goal forall n, 2*(sum_n n) = n * (n+1).
  induction n.
  reflexivity.
  unfold sum_n.
  fold sum_n.
  rewrite mult_plus_distr_l.
  rewrite IHn.
  simpl.
  f_equal.
  rewrite plus_n_O.
  rewrite mult_succ_r.
  rewrite mult_plus_distr_l.
  rewrite plus_assoc_reverse.
  rewrite plus_assoc_reverse.
  f_equal.
  simpl.
  f_equal.
  rewrite plus_comm.
  reflexivity.
Qed.

Goal forall n, n <= sum_n n.
  induction n.
  reflexivity.
  simpl.
  apply le_n_S.
  apply le_plus_l.
Qed.

Fixpoint first_n(A : Type)(n : nat)(l : list A) :=
  match n with
  | O => nil
  | S x => 
      match l with
      | nil => nil
      | e :: next => e :: first_n A x next
      end
  end.

Fixpoint generate begin time : list nat :=
  match time with
  | O => nil
  | S x => begin :: generate (S begin) x
  end.

Fixpoint nth_option (A:Set)(n:nat)(l:list A) {struct l}
  : option A :=
  match n, l with
  | O, cons a tl => Some a
  | S p, cons a tl => nth_option A p tl
  | n, nil => None
  end.

Lemma nth_length : 
  forall (A:Set)(n:nat)(l:list A),
    nth_option _ n l = None <-> length l <= n.
  induction n;
  [
    destruct l;
    simpl;
    split;
    discriminate 1||auto;
    inversion 1|
    intros;
    destruct l;
    [
      split;
      auto with arith|
      
      simpl;
      split;
      case (IHn l);
      auto with arith
    ]
  ].
Qed.

Fixpoint split (A B : Set)(l : list(A * B)) : (list A) * (list B) := 
  match l with
  | nil => (nil, nil)
  | (a, b) :: l' => let (ll, lr) := split A B l' in (a :: ll, b :: lr)
  end.

Fixpoint combine (A B : Set)(ll : list A)(lr : list B) : list (A * B) := 
  match (ll, lr) with
  | (l :: ll', r :: lr') => (l, r) :: (combine A B ll' lr')
  | (_, _) => nil
  end.

Goal forall (A B : Set)(l : list (A * B)), 
  let ( l1,l2) :=  (split _ _ l) in combine _ _ l1 l2 = l.
  induction l.
  reflexivity.
  simpl.
  destruct (split A B l).
  destruct a.
  destruct IHl.
  reflexivity.
Qed.

Inductive btree(T : Set) : Set :=
  leaf : btree T | bnode : T->btree T->btree T->btree T.

Fixpoint to_b_tree_Z(t : Z_btree) : btree Z :=
  match t with
  | Z_leaf => leaf Z
  | Z_bnode z l r => bnode Z z (to_b_tree_Z l) (to_b_tree_Z r)
  end.

Fixpoint to_Z_btree(t : btree Z) : Z_btree :=
  match t with
  | leaf => Z_leaf
  | bnode z l r => Z_bnode z (to_Z_btree l) (to_Z_btree r)
  end.

Goal forall t, to_Z_btree (to_b_tree_Z t) = t.
  induction t.
  reflexivity.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.
Qed.

Goal forall t, to_b_tree_Z (to_Z_btree t) = t.
  induction t.
  reflexivity.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.
Qed.

Inductive htree (A:Set) : nat -> Set :=
  hleaf : A -> (htree A O)
| hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).

Definition first_of_htree
  (A : Set) (n : nat) (v : htree A n) (t : htree A (S n)) : htree A n :=
    match t in (htree _ n0) return (htree A (pred n0) -> htree A (pred n0)) with
    | hleaf _ => fun v' : htree A 0 => v'
    | hnode p _ t1 _ => fun _ : htree A p => t1
    end v.

Theorem injection_first_htree:
  forall (n : nat) (t1 t2 t3 t4 : htree nat n),
    hnode nat n O t1 t2 = hnode nat n O t3 t4 ->  t1 = t3.
  intros n t1 t2 t3 t4 h.
  change
  (first_of_htree nat n t1 (hnode nat n 0 t1 t2) =
  first_of_htree nat n t1 (hnode nat n 0 t3 t4)).
  rewrite h.
  reflexivity.
Qed.

Fixpoint make_htree (n:nat): htree Z n :=
  match n return htree Z n with
    0 => hleaf Z 0%Z
  | S p => hnode Z p 0%Z (make_htree p) (make_htree p)
  end.

Inductive binary_word : nat -> Set :=
  tail : binary_word 0
| push : forall n : nat, bool -> binary_word n -> binary_word (S n).

Fixpoint word_con (nl nr : nat) (wl : binary_word nl) (wr : binary_word nr) : binary_word (nl + nr) := 
  match wl in binary_word ln return binary_word (ln + nr) with
  | tail => wr
  | push l b w => push (l + nr) b (word_con l nr w wr)
  end.

Fixpoint binary_word_or (l : nat) (wl wr : binary_word l) : binary_word l.
  refine(
    match wl in binary_word n return binary_word n -> binary_word n with
    | tail => (fun x => x)
    | push ll lb lw => 
        (fun wr' : binary_word (S ll) => match wr' with
        | tail => (fun p : False => wr')
        | push rl rb rw => 
            (fun p : ll = rl => 
              push
              rl
              (bool_or lb rb) 
              (binary_word_or rl (eq_rec ll binary_word lw rl p) rw))
        end _)
    end wr).
    reflexivity.
Defined.

Theorem all_equal : forall x y : Empty_set, x = y.
  destruct x.
Qed.

Theorem all_diff : forall x y : Empty_set, x <> y.
  destruct x.
Qed.
