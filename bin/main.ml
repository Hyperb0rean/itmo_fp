open Itmo_fp.Largest_palindrome
open Itmo_fp.Libcoq

let () =
  let formatted_string =
    Printf.sprintf "%d"
      (Largest_palindrome.nat_to_int
         (ProjectEuler.largest_palindrome (S (S O))))
  in
  print_endline formatted_string
