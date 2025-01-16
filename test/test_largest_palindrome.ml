(* open Itmo_fp.Util
open Itmo_fp.Libcoq

let () = print_endline "Test Largest palindrome 2"

let () =
  let result =
    nat_to_int (Largest_palindrome.largest_palindrome (int_to_nat 2))
  in
  assert (result = 9009);
  Printf.printf "Test passed: %d = 9009\n" result *)
