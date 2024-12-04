Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Wf.
Import ListNotations.
Require Import Coq.Relations.Relation_Operators.
Require Import Wellfounded.

Print LoadPath.


Module ProjectEuler.

Lemma digits_oblig: forall n: nat, (0 <> n)-> (n / 10) < n.
Proof. 
intros n H.
destruct n as [| n'].
- contradiction H. reflexivity.
- apply Nat.div_lt.
+ apply Nat.lt_0_succ.
+ do 2 apply Nat.lt_succ_r.
  apply Nat.le_0_l.
  Qed.

Definition digits (n : nat) : list nat :=
  Fix (lt_wf) (fun _ => list nat)
      (fun (m : nat) (digits : forall n', (n' < m) -> list nat) =>
        match m, digits with
        | 0, _ => []
        | S m', digits => digits ((S m') / 10) (digits_oblig (S m') (Nat.neq_0_succ m')) ++ [m mod 10]
        end) 
    n.  

Example test_digits1: digits 123 = [1; 2; 3].
Proof. simpl. reflexivity. Qed.

Example test_digits2: digits 54321 = [5; 4; 3; 2; 1].
Proof. simpl. reflexivity. Qed.

Fixpoint list_beq {A: Type} (eq: A -> A -> bool) (x y : list A) : bool :=
  match x, y with
  | [], [] => true                 
  | _, [] => false                 
  | [], _ => false                 
  | h1 :: t1, h2 :: t2 =>         
      andb (eq h1 h2) (list_beq eq t1 t2)  
  end.

Definition is_palindrome (n : nat) : bool :=
  let ds := digits n in
  list_beq Nat.eqb ds (rev ds).

Definition max_palindrom(i j max_prod: nat): nat :=
  let p := i*j in
  if andb (is_palindrome p) (Nat.ltb max_prod p) then p else max_prod.

Program Fixpoint find_max_aux (p : nat * nat)
  (max_prod upper_limit lower_limit: nat) 
  {measure p (slexprod _ _ lt lt)} :=
  if Nat.eqb (fst p) lower_limit then max_prod else
    let new_prod := max_palindrom (fst p) (snd p) max_prod in
    match p with  
    | (_, S j') => find_max_aux (fst p, j') new_prod upper_limit lower_limit
    | (S i', 0) => find_max_aux (i', upper_limit) new_prod upper_limit lower_limit
    | (0, 0)   => new_prod 
end.

Next Obligation.
Proof.
  right. unfold lt. reflexivity.
Qed.

Next Obligation.
Proof.
  left. unfold fst. unfold lt. reflexivity.
Qed.

Next Obligation.
Proof.
  apply measure_wf.
  apply wf_slexprod.
  - apply lt_wf.
  - apply lt_wf.
Qed.

Definition find_max (upper_limit lower_limit : nat) : nat :=
  (find_max_aux (upper_limit, upper_limit) 0 upper_limit lower_limit). 


Definition largest_palindrome (n : nat) : nat :=
  let upper_limit := (10 ^ n) - 1 in
  let lower_limit := 10 ^ (n - 1) in
  find_max upper_limit lower_limit.

End ProjectEuler.
 