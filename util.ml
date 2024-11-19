let rec nat_to_int (n: nat): int =
  match n with
  | O -> 0
  | S m -> 1 + nat_to_int m


let () =
  let formatted_string = Printf.sprintf "%d" (nat_to_int (largest_palindrome (S ( S (S O))))) in
  print_endline formatted_string; 