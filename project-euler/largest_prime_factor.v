
Require Import Arith.
Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Wf.
Require Import Coq.Relations.Relation_Operators.
Require Import Wellfounded.
Require Extraction.
Extraction Language OCaml.

Module ProjectEuler.

Definition is_prime (n : nat) : Prop :=
  n > 1 /\ forall d, d > 1 -> d < n -> Nat.modulo n d <> 0.

Fixpoint smallest_factor_aux (n d : nat) : nat :=
    match d with
    | S d' =>
        if Nat.eqb (Nat.modulo n d) 0 then n / d
        else smallest_factor_aux n d'
    | _ => 0 (*unreacheable*)
end.

(*Smallest factor not equal to 1 *)
Definition smallest_factor (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S n' => smallest_factor_aux n n'
  end.

Example test_smallest_factor_2: smallest_factor 2 = 2.
Proof. simpl. reflexivity. Qed.

Example test_smallest_factor_35: smallest_factor 35 = 5.
Proof. simpl. reflexivity. Qed.

Example test_smallest_factor_49: smallest_factor 49 = 7.
Proof. simpl. reflexivity. Qed.

Example test_smallest_factor_prime_13: smallest_factor 13 = 13.
Proof. simpl. reflexivity. Qed.


Program Fixpoint largest_prime_factor (n : nat) {measure n lt}: nat :=
   match n with
        | 0 => 0
        | 1 => 0 
        | S n' =>
            let factor := smallest_factor n in
            if Nat.eqb factor n then (S n')
            else largest_prime_factor ((S n') / factor)
        end.



Lemma factor_gt_1: forall n: nat, 0 <> n -> 1 <> n -> 1 < smallest_factor n.
    intros n H1 H2.
    destruct n as [|n].
    - contradiction H1. reflexivity.
    - destruct n as [|n].
    + contradiction H2. reflexivity.
    + unfold smallest_factor.
      induction n as [|n' IHn].
      -- simpl. unfold lt. reflexivity.
      Admitted. 

Next Obligation.
Proof.
    apply Nat.div_lt.
    - unfold lt. apply Nat.lt_0_succ.
    - apply factor_gt_1.
    + apply Nat.neq_0_succ.
    + apply n0.
Qed.
    
End ProjectEuler.

Set Extraction Optimize.

Set Extraction Output Directory "lib".

Extraction "largest_prime_factor.ml" ProjectEuler.largest_prime_factor.