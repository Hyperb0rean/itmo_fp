open Libcoq

let rec nat_to_int (n : nat) : int =
  match n with O -> 0 | S m -> 1 + nat_to_int m

let rec int_to_nat (n : int) : nat =
  if n <= 0 then O else S (int_to_nat (n - 1))
