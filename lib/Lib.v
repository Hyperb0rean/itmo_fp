Require Import ProjectEuler.Largest_palindrome.
Require Import ProjectEuler.Largest_prime_factor.
Require Extraction.

Print LoadPath.

Extraction Language OCaml.

Set Extraction Optimize.

Set Extraction Output Directory "lib".

Extraction "largest_palindrome.ml" ProjectEuler.largest_palindrome.
Extraction "largest_prime_factor.ml" ProjectEuler.largest_prime_factor.