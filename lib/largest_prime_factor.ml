
type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

module Nat =
 struct
  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with
              | O -> n
              | S l -> sub k l)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod **)

  let rec divmod x y q u =
    match x with
    | O -> Pair (q, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q) y
       | S u' -> divmod x' y q u')

  (** val div : nat -> nat -> nat **)

  let div x y = match y with
  | O -> y
  | S y' -> fst (divmod x y' O y')

  (** val modulo : nat -> nat -> nat **)

  let modulo x = function
  | O -> x
  | S y' -> sub y' (snd (divmod x y' O y'))
 end

module ProjectEuler =
 struct
  (** val smallest_factor_aux : nat -> nat -> nat **)

  let rec smallest_factor_aux n d = match d with
  | O -> O
  | S d' ->
    (match Nat.eqb (Nat.modulo n d) O with
     | True -> Nat.div n d
     | False -> smallest_factor_aux n d')

  (** val smallest_factor : nat -> nat **)

  let smallest_factor n = match n with
  | O -> O
  | S n' -> (match n' with
             | O -> O
             | S _ -> smallest_factor_aux n n')

  (** val largest_prime_factor : nat -> nat **)

  let rec largest_prime_factor x = match x with
  | O -> O
  | S n' ->
    (match n' with
     | O -> O
     | S n0 ->
       let n'0 = S n0 in
       let factor = smallest_factor x in
       (match Nat.eqb factor x with
        | True -> S n'0
        | False -> largest_prime_factor (Nat.div (S n'0) factor)))
 end
