type bool = True | False
type nat = O | S of nat
type ('a, 'b) prod = Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1
val snd : ('a1, 'a2) prod -> 'a2

type 'a list = Nil | Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

type ('a, 'p) sigT = ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1
val projT2 : ('a1, 'a2) sigT -> 'a2
val add : nat -> nat -> nat
val mul : nat -> nat -> nat
val sub : nat -> nat -> nat

module Nat : sig
  val add : nat -> nat -> nat
  val mul : nat -> nat -> nat
  val sub : nat -> nat -> nat
  val eqb : nat -> nat -> bool
  val leb : nat -> nat -> bool
  val ltb : nat -> nat -> bool
  val pow : nat -> nat -> nat
  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod
  val div : nat -> nat -> nat
  val modulo : nat -> nat -> nat
end

val rev : 'a1 list -> 'a1 list

module ProjectEuler : sig
  val digits : nat -> nat list
  val list_beq : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool
  val is_palindrome : nat -> bool
  val max_palindrom : nat -> nat -> nat -> nat

  val find_max_aux_func :
    ((nat, nat) prod, (nat, (nat, nat) sigT) sigT) sigT -> nat

  val find_max_aux : (nat, nat) prod -> nat -> nat -> nat -> nat
  val find_max : nat -> nat -> nat
  val largest_palindrome : nat -> nat
end
