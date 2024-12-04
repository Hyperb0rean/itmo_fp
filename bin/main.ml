open Itmo_fp.Util
open Itmo_fp.Libcoq

let () =
  let formatted_string =
    Printf.sprintf "%d"
      (nat_to_int (Largest_palindrome.largest_palindrome (S (S O))))
  in
  print_endline formatted_string
