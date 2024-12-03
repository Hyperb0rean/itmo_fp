type bool = True | False
type nat = O | S of nat
type ('a, 'b) prod = Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function Pair (_, y) -> y

type 'a list = Nil | Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m = match l with Nil -> m | Cons (a, l1) -> Cons (a, app l1 m)

type ('a, 'p) sigT = ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function ExistT (_, h) -> h

(** val add : nat -> nat -> nat **)

let rec add n m = match n with O -> m | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m = match n with O -> O | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with O -> n | S k -> ( match m with O -> n | S l -> sub k l)

module Nat = struct
  (** val add : nat -> nat -> nat **)

  let rec add n m = match n with O -> m | S p -> S (add p m)

  (** val mul : nat -> nat -> nat **)

  let rec mul n m = match n with O -> O | S p -> add m (mul p m)

  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with O -> n | S k -> ( match m with O -> n | S l -> sub k l)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> ( match m with O -> True | S _ -> False)
    | S n' -> ( match m with O -> False | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> ( match m with O -> False | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m = leb (S n) m

  (** val pow : nat -> nat -> nat **)

  let rec pow n = function O -> S O | S m0 -> mul n (pow n m0)

  (** val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod **)

  let rec divmod x y q u =
    match x with
    | O -> Pair (q, u)
    | S x' -> (
        match u with O -> divmod x' y (S q) y | S u' -> divmod x' y q u')

  (** val div : nat -> nat -> nat **)

  let div x y = match y with O -> y | S y' -> fst (divmod x y' O y')

  (** val modulo : nat -> nat -> nat **)

  let modulo x = function O -> x | S y' -> sub y' (snd (divmod x y' O y'))
end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
  | Nil -> Nil
  | Cons (x, l') -> app (rev l') (Cons (x, Nil))

module ProjectEuler = struct
  (** val digits : nat -> nat list **)

  let rec digits x =
    match x with
    | O -> Nil
    | S m' ->
        app
          (let y = Nat.div (S m') (S (S (S (S (S (S (S (S (S (S O)))))))))) in
           digits y)
          (Cons (Nat.modulo x (S (S (S (S (S (S (S (S (S (S O)))))))))), Nil))

  (** val list_beq : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

  let rec list_beq eq x y =
    match x with
    | Nil -> ( match y with Nil -> True | Cons (_, _) -> False)
    | Cons (h1, t1) -> (
        match y with
        | Nil -> False
        | Cons (h2, t2) -> (
            match eq h1 h2 with True -> list_beq eq t1 t2 | False -> False))

  (** val is_palindrome : nat -> bool **)

  let is_palindrome n =
    let ds = digits n in
    list_beq Nat.eqb ds (rev ds)

  (** val max_palindrom : nat -> nat -> nat -> nat **)

  let max_palindrom i j max_prod =
    let p = mul i j in
    match
      match is_palindrome p with True -> Nat.ltb max_prod p | False -> False
    with
    | True -> p
    | False -> max_prod

  (** val find_max_aux_func :
      ((nat, nat) prod, (nat, (nat, nat) sigT) sigT) sigT -> nat **)

  let rec find_max_aux_func x =
    let p = projT1 x in
    let max_prod = projT1 (projT2 x) in
    let upper_limit = projT1 (projT2 (projT2 x)) in
    let lower_limit = projT2 (projT2 (projT2 x)) in
    let find_max_aux0 p0 max_prod0 upper_limit0 lower_limit0 =
      find_max_aux_func
        (ExistT (p0, ExistT (max_prod0, ExistT (upper_limit0, lower_limit0))))
    in
    match Nat.eqb (fst p) lower_limit with
    | True -> max_prod
    | False -> (
        let new_prod = max_palindrom (fst p) (snd p) max_prod in
        let (Pair (wildcard', n)) = p in
        match wildcard' with
        | O -> (
            match n with
            | O -> new_prod
            | S j' ->
                find_max_aux0
                  (Pair (fst p, j'))
                  new_prod upper_limit lower_limit)
        | S i' -> (
            match n with
            | O ->
                find_max_aux0
                  (Pair (i', upper_limit))
                  new_prod upper_limit lower_limit
            | S j' ->
                find_max_aux0
                  (Pair (fst p, j'))
                  new_prod upper_limit lower_limit))

  (** val find_max_aux : (nat, nat) prod -> nat -> nat -> nat -> nat **)

  let find_max_aux p max_prod upper_limit lower_limit =
    find_max_aux_func
      (ExistT (p, ExistT (max_prod, ExistT (upper_limit, lower_limit))))

  (** val find_max : nat -> nat -> nat **)

  let find_max upper_limit lower_limit =
    find_max_aux (Pair (upper_limit, upper_limit)) O upper_limit lower_limit

  (** val largest_palindrome : nat -> nat **)

  let largest_palindrome n =
    let upper_limit =
      sub (Nat.pow (S (S (S (S (S (S (S (S (S (S O)))))))))) n) (S O)
    in
    let lower_limit =
      Nat.pow (S (S (S (S (S (S (S (S (S (S O)))))))))) (sub n (S O))
    in
    find_max upper_limit lower_limit
end
