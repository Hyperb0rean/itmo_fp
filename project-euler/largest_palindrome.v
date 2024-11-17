Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Import ListNotations.

Require Import Wellfounded.

Search lt.
Search le.

Lemma digits_oblig (n m : nat) (p : n <> 0) (q : m > 1) : n / m < n.
Proof.
  apply Nat.div_lt.
  - destruct n. contradiction. apply Nat.lt_0_succ.
  - apply q.
Qed.

Lemma not_null (n: nat) : n<>0.
Admitted.
Lemma greater_1 (m: nat) : m > 1.
Admitted.


Definition digits (n : nat) : list nat :=
  Fix (lt_wf) (fun _ => list nat)
      (fun (n : nat) (digits : forall n', (n' < n) -> list nat) =>
        match n with
        | 0 => []
        | _ => digits (n / 10) (digits_oblig n 10 (not_null n) (greater_1 10))  ++ [n mod 10]
        end) 
    n.

Fixpoint list_beq {A: Type} (eq: A -> A -> bool) (x y : list A) : bool :=
  match x, y with
  | [], [] => true                 
  | _, [] => false                 
  | [], _ => false                 
  | h1 :: t1, h2 :: t2 =>         
      eq h1 h2 && list_beq eq t1 t2  
  end.

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S n', S m' => eqb n' m' 
  end.

Definition is_palindrome (n : nat) : bool :=
  let ds := digits n in
  list_beq eqb ds (rev ds).

Fixpoint find_max (i j max_prod upper_limit lower_limit : nat) : nat :=
max_prod.

Definition largest_palindrome (n : nat) : nat :=
  let upper_limit := (10 ^ n) - 1 in
  let lower_limit := 10 ^ (n - 1) in
  find_max upper_limit upper_limit 0 upper_limit lower_limit.

Compute largest_palindrome 2.
Example test_2: largest_palindrome 2 = 9009.
Proof. simpl. reflexivity. Qed.

Example test_3: largest_palindrome 3 = 906609.
Proof. simpl. reflexivity. Qed.
