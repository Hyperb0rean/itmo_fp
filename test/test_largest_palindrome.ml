open Itmo_fp.Largest_palindrome
open Itmo_fp.Libcoq

let () = print_endline "Test Largest palindrome 2"

let () =
  let result =
    Largest_palindrome.nat_to_int
      (ProjectEuler.largest_palindrome (Largest_palindrome.int_to_nat 2))
  in
  assert (result = 9009);
  Printf.printf "Test passed: %d = 9009\n" result
