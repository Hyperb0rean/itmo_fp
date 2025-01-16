open Itmo_fp.Libcoq.Red_black_tree

let print_pair (a, b) = Printf.printf "(%d, %s) " a b

let () =
  List.iter print_pair
    (elements
       (insert 1 "one"
          (insert 2 "two"
             (insert 5 "five"
                (insert 3 "three"
                   (insert 4 "four"
                      (insert 15 "fiveteen" (insert 7 "seven" mk_nil))))))))

let () = print_endline ""

let () =
  List.iter print_pair
    (elements
       (insert 0 "zero"
          (insert 1 "one"
             (insert 4 "four" (insert 2 "two" (insert (-1) "minus one" mk_nil))))))

let () = print_endline ""

let rec rbtree_iter f r l = function
  | Coq_nil -> ()
  | Coq_node (_, left, key, value, right) ->
      f (key, value);
      r ();
      rbtree_iter f r l left;
      l ();
      rbtree_iter f r l right

let tree =
  insert 1 "one"
    (insert 4 "four" (insert 2 "two" (insert (-1) "minus one" mk_nil)))
;;

rbtree_iter print_pair
  (fun () -> Printf.printf "r ")
  (fun () -> Printf.printf "l ")
  tree

let () = print_endline ""
let () = List.iter print_pair (elements tree)
