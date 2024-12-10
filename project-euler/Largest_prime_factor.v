
Require Import Arith.
Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Wf.
Require Import Coq.Relations.Relation_Operators.
Require Import Wellfounded.
Require Import Coq.Lists.List.
Import ListNotations.

Module Largest_prime_factor.

Definition is_prime (n : nat) : Prop :=
  n > 1 /\ forall d, d > 1 -> d < n -> Nat.modulo n d <> 0.

Definition mod_eq0b (p: nat) (d: nat) : bool :=
  (p mod d) =? 0.

Definition factors (p: nat) : list nat :=
  filter (mod_eq0b p) (seq 2 p).

Definition smallest_factor (p : nat) : nat :=
  match factors p with
  | [] => p
  | x :: _ => x
  end.

Example test_smallest_factor_2: smallest_factor 2 = 2.
Proof. simpl. reflexivity. Qed.

Example test_smallest_factor_35: smallest_factor 35 = 5.
Proof. simpl. reflexivity. Qed.

Example test_smallest_factor_49: smallest_factor 49 = 7.
Proof. simpl. reflexivity. Qed.

Example test_smallest_factor_prime_13: smallest_factor 13 = 13.
Proof. simpl. reflexivity. Qed.

Theorem test_smallest_factor_prime: forall p: nat, (is_prime p) -> (smallest_factor p) = p.
Proof.
  intros p.
  unfold is_prime.
  intros [H1 H2].
  (* assert(C: exists d, (smallest_factor p) = d -> p mod d = 0). *)
  Admitted.

Program Fixpoint largest_prime_factor (n : nat) {measure n lt}: nat :=
   match n with
        | 0 => 0
        | 1 => 0 
        | S n' =>
            let factor := smallest_factor n in
            if Nat.eqb factor n then (S n')
            else largest_prime_factor ((S n') / factor)
        end.

Lemma lt_1_SSn: forall n: nat, 1 < (S (S n)).
Proof.
  intros. unfold lt.
  do 2 apply le_n_S.
  apply Nat.le_0_l.
Qed.

Search head.

Lemma factor_gt_1: forall n: nat,
       0 <> n -> 1 <> n -> 1 < smallest_factor n.
Proof. 
    intros n H1 H2.
    destruct n as [|n].
    - contradiction H1. reflexivity.
    - destruct n as [|n].
    + contradiction H2. reflexivity.
    + unfold smallest_factor.
      unfold factors.
      remember (S (S n)) as n'.
      remember (seq 2 n') as seq_2_n'.
      remember (filter (mod_eq0b n') seq_2_n') as fl.
      (* assert(H: fl = [] \/ (exists n: nat, ((Some n) = head fl) /\ fl <> [])). {
          destruct fl.
          + left. reflexivity.
          + right. exists (n0).
          t.
            apply hd_error_some_nil.
            unfold hd_error.
            reflexivity.   
      }
      destruct H.
      -- rewrite H. unfold lt. rewrite Heqn'. apply lt_1_SSn.
      -- destruct H. *)
       
        
      Admitted.

Search (Some _).

Next Obligation.
Proof.
    apply Nat.div_lt.
    - unfold lt. apply Nat.lt_0_succ.
    - apply factor_gt_1.
    + apply Nat.neq_0_succ.
    + apply n0.
Qed.
    
End Largest_prime_factor.