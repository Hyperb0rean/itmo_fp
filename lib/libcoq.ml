open Largest_palindrome

module Bridge = struct
  let rec nat_to_int (n : nat) : int =
    match n with O -> 0 | S m -> 1 + nat_to_int m
end
