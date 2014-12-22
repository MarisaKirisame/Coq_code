Require Import List Arith.

Set Implicit Arguments.

Definition swap_pair a b (p : a * b) :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing_stuck : forall a b (p : a * b),
  p = (fst p, snd p).
  intros.
  destruct p.
  trivial.
Qed.

Theorem snd_fst_is_swap : forall a b (p : a * b),
  (snd p, fst p) = swap_pair p.
  intros.
  destruct p.
  trivial.
Qed.

Theorem fst_swap_is_snd : forall a b (p : a * b),
  fst (swap_pair p) = snd p.
  tauto.
Qed.

Definition nonzeros (l: list nat) : list nat := 
  filter (fun n => match n with O => false | _ => true end) l.

Fixpoint oddmembers (l:list nat) : list nat :=
  filter (fix odd n := match n with O => false | S n' => negb (odd n') end) l.

Fixpoint countoddmembers l := length (oddmembers l).

Fixpoint alternate (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | l1_head :: l1_tail, l2_head :: l2_tail =>
    l1_head :: l2_head :: alternate l1_tail l2_tail
  end.

Fixpoint count (v:nat) (s:list nat) : nat :=
  length
    (filter 
    (fun n => match eq_nat_dec v n with left _ => true | _ => false end) s).

Definition member (v:nat) (s:list nat) : bool := 
  match count v s with
  | O => false
  | _ => true
  end.

Fixpoint remove_all (v:nat) (s:list nat) := 
  filter (fun n => match eq_nat_dec v n with left _ => false | _ => true end) s.

Fixpoint remove_one (v:nat)(s:list nat) : list nat :=
  match s with
  | nil => nil
  | s_head :: s_tail => 
    match eq_nat_dec s_head v with
    | left _ => s_tail
    | _ => s_head :: remove_one v s_tail
    end
  end.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  (* FILL IN HERE *) admit.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
 (* FILL IN HERE *) Admitted.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
 (* FILL IN HERE *) Admitted.
☐
Exercise: 3 stars (bag_theorem)
Write down an interesting theorem about bags involving the functions count and add, and prove it. Note that, since this problem is somewhat open-ended, it's possible that you may come up with a theorem which is true, but whose proof requires techniques you haven't learned yet. Feel free to ask for help if you get stuck! 


Exercise: 3 stars (list_exercises)
More practice with lists.

Theorem app_nil_end : ∀l : natlist,
  l ++ [] = l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_involutive : ∀l : natlist,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.

There is a short solution to the next exercise. If you find yourself getting tangled up, step back and try to look for a simpler way.

Theorem app_assoc4 : ∀l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem snoc_append : ∀(l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  (* FILL IN HERE *) Admitted.

Theorem distr_rev : ∀l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  (* FILL IN HERE *) Admitted.

An exercise about your implementation of nonzeros:

Lemma nonzeros_app : ∀l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* FILL IN HERE *) Admitted.
☐
Exercise: 2 stars (beq_natlist)
Fill in the definition of beq_natlist, which compares lists of numbers for equality. Prove that beq_natlist l l yields true for every list l.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  (* FILL IN HERE *) admit.

Example test_beq_natlist1 : (beq_natlist nil nil = true).
 (* FILL IN HERE *) Admitted.
Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
 (* FILL IN HERE *) Admitted.
Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
 (* FILL IN HERE *) Admitted.

Theorem beq_natlist_refl : ∀l:natlist,
  true = beq_natlist l l.
Proof.
  (* FILL IN HERE *) Admitted.
☐

List Exercises, Part 2
Exercise: 2 stars (list_design)
Design exercise:

    Write down a non-trivial theorem involving cons (::), snoc, and app (++).
    Prove it.


(* FILL IN HERE *)
☐
Exercise: 3 stars, advanced (bag_proofs)
Here are a couple of little theorems to prove about your definitions about bags earlier in the file.

Theorem count_member_nonzero : ∀(s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

The following lemma about ble_nat might help you in the next proof.

Theorem ble_n_Sn : ∀n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "0".
    simpl. reflexivity.
  Case "S n'".
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_decreases_count: ∀(s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* FILL IN HERE *) Admitted.
☐
Exercise: 3 stars, optional (bag_count_sum)
Write down an interesting theorem about bags involving the functions count and sum, and prove it.

(* FILL IN HERE *)
☐
Exercise: 4 stars, advanced (rev_injective)
Prove that the rev function is injective, that is,
    ∀(l1 l2 : natlist), rev l1 = rev l2 → l1 = l2.
There is a hard way and an easy way to solve this exercise.

Exercise: 2 stars (hd_opt)
Using the same idea, fix the hd function from earlier so we don't have to pass a default element for the nil case.

Definition hd_opt (l : natlist) : natoption :=
  (* FILL IN HERE *) admit.

Example test_hd_opt1 : hd_opt [] = None.
 (* FILL IN HERE *) Admitted.

Example test_hd_opt2 : hd_opt [1] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
 (* FILL IN HERE *) Admitted.
☐
Exercise: 1 star, optional (option_elim_hd)
This exercise relates your new hd_opt to the old hd.

Theorem option_elim_hd : ∀(l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  (* FILL IN HERE *) Admitted.
☐

Dictionaries
As a final illustration of how fundamental data structures can be defined in Coq, here is the declaration of a simple dictionary data type, using numbers for both the keys and the values stored under these keys. (That is, a dictionary represents a finite map from numbers to numbers.)

Module Dictionary.

Inductive dictionary : Type :=
  | empty : dictionary
  | record : nat → nat → dictionary → dictionary.

This declaration can be read: "There are two ways to construct a dictionary: either using the constructor empty to represent an empty dictionary, or by applying the constructor record to a key, a value, and an existing dictionary to construct a dictionary with an additional key to value mapping."

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).

Here is a function find that searches a dictionary for a given key. It evaluates evaluates to None if the key was not found and Some val if the key was mapped to val in the dictionary. If the same key is mapped to multiple values, find will return the first one it finds.

Fixpoint find (key : nat) (d : dictionary) : natoption :=
  match d with
  | empty ⇒ None
  | record k v d' ⇒ if (beq_nat key k)
                       then (Some v)
                       else (find key d')
  end.

Exercise: 1 star (dictionary_invariant1)
Complete the following proof.

Theorem dictionary_invariant1' : ∀(d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
 (* FILL IN HERE *) Admitted.
☐
Exercise: 1 star (dictionary_invariant2)
Complete the following proof.

Theorem dictionary_invariant2' : ∀(d : dictionary) (m n o: nat),
  beq_nat m n = false → find m d = find m (insert n o d).
Proof.
 (* FILL IN HERE *) Admitted.
☐

End Dictionary.

End NatList.
