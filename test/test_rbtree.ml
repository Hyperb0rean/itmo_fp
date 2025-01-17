open Itmo_fp.Libcoq.Red_black_tree

let () = print_endline "Test Red_black_tree"
let first = insert 1 "one" (insert 2 "two" (insert 3 "three" mk_nil))
let second = insert 2 "two" (insert 1 "one" (insert 3 "three" mk_nil));;

assert (rbtree_eqb first second)

let () = print_endline "Passed equality"
let left = insert 1 "one" (insert 2 "two" (insert 3 "three" mk_nil))
let right = insert 5 "two" (insert 4 "one" (insert 6 "three" mk_nil));;

assert (
  elements_beq
    [
      (1, "one"); (2, "two"); (3, "three"); (4, "four"); (5, "five"); (6, "six");
    ]
    (elements (union left right)))

let () = print_endline "Passed union"
