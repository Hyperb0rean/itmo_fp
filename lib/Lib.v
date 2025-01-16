Require Import ProjectEuler.Largest_palindrome.
Require Import ProjectEuler.Largest_prime_factor.
Require Import DataStructures.Binary_tree.
Require Import DataStructures.Red_black_tree.


Require Extraction.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "( , )" ]. 



Extraction Language OCaml.

Set Extraction Optimize.

Set Extraction Output Directory "lib".

(* Extraction "libcoq.ml" Largest_palindrome.largest_palindrome Largest_prime_factor.largest_prime_factor. *)
Extraction "libcoq.ml" Red_black_tree.