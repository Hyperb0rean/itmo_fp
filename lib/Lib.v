Require Import ProjectEuler.Largest_palindrome.
Require Import ProjectEuler.Largest_prime_factor.
Require Extraction.

Require Import Arith.
Require Import Nat.

Extraction Language OCaml.

Set Extraction Optimize.

Set Extraction Output Directory "lib".

Extraction "libcoq.ml" Largest_palindrome.largest_palindrome Largest_prime_factor.largest_prime_factor.