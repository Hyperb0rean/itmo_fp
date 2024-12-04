open Itmo_fp.Libcoq
open Itmo_fp.Util

let () = print_endline "Test Largest prime factor 13195"

let () =
  let result =
    nat_to_int (Largest_prime_factor.largest_prime_factor (int_to_nat 13195))
  in
  assert (result = 29);
  Printf.printf "Test passed: %d = 29\n" result

let () = print_endline "Test Largest prime factor 6015"

let () =
  let result =
    nat_to_int (Largest_prime_factor.largest_prime_factor (int_to_nat 6015))
  in
  assert (result = 401);
  Printf.printf "Test passed: %d = 401\n" result
