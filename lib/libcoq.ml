module Largest_palindrome = struct
  let rec nat_to_int (n : Largest_palindrome.nat) : int =
    match n with O -> 0 | S m -> 1 + nat_to_int m

  let rec int_to_nat (n : int) : Largest_palindrome.nat =
    if n <= 0 then O else S (int_to_nat (n - 1))
end

module Largest_prime_factor = struct
  let rec nat_to_int (n : Largest_prime_factor.nat) : int =
    match n with O -> 0 | S m -> 1 + nat_to_int m

  let rec int_to_nat (n : int) : Largest_prime_factor.nat =
    if n <= 0 then O else S (int_to_nat (n - 1))
end
