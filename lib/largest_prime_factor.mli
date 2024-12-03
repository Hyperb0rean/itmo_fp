type bool = True | False
type nat = O | S of nat
type ('a, 'b) prod = Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1
val snd : ('a1, 'a2) prod -> 'a2

module Nat : sig
  val sub : nat -> nat -> nat
  val eqb : nat -> nat -> bool
  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod
  val div : nat -> nat -> nat
  val modulo : nat -> nat -> nat
end

module ProjectEuler : sig
  val smallest_factor_aux : nat -> nat -> nat
  val smallest_factor : nat -> nat
  val largest_prime_factor : nat -> nat
end
