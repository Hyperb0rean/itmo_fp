open Itmo_fp.Libcoq.Red_black_tree

let elem_eq a b =
  let k1, _ = a in
  let k2, _ = b in
  Int.equal k1 k2

let () = print_endline "Test Red_black_tree"
let first = insert 1 "one" (insert 2 "two" (insert 3 "three" mk_nil))
let second = insert 2 "two" (insert 1 "one" (insert 3 "three" mk_nil))

let () =
  foldr () (fun (key, str) -> fun () -> Printf.printf " (%d %s) " key str) first

let () =
  foldr ()
    (fun (key, str) -> fun () -> Printf.printf " (%d %s) " key str)
    second
;;

assert (rbtree_eqb first second)

let () = print_endline "Passed equality"
let left = insert 1 "one" (insert 2 "two" (insert 3 "three" mk_nil))
let right = insert 5 "two" (insert 4 "one" (insert 6 "three" mk_nil));;

assert (
  List.equal elem_eq
    [
      (1, "one"); (2, "two"); (3, "three"); (4, "four"); (5, "five"); (6, "six");
    ]
    (elements (union left right)))

let () = print_endline "Passed union"
