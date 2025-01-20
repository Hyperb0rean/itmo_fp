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
  | Coq_node (color, left, key, value, right) ->
      f (color, key, value);
      r ();
      rbtree_iter f r l left;
      l ();
      rbtree_iter f r l right

let print_node (c, a, b) =
  Printf.printf "(%s, %d, %s) "
    (match c with Red -> "red" | Black -> "black")
    a b

let tree =
  insert 1 "one"
    (insert 4 "four" (insert 2 "two" (insert (-1) "minus one" mk_nil)))
;;

rbtree_iter print_node
  (fun () -> Printf.printf "r ")
  (fun () -> Printf.printf "l ")
  tree

let () = print_endline "";;

rbtree_iter print_node
  (fun () -> Printf.printf "r ")
  (fun () -> Printf.printf "l ")
  (insert 0 "zero" tree)

let () = print_endline ""
let () = List.iter print_pair (elements tree)
let left = insert 2 "2" (insert 1 "1" (insert 3 "3" mk_nil))
let right = insert 5 "5" (insert 4 "4" (insert 6 "6" mk_nil))
let () = print_endline "";;

rbtree_iter print_node
  (fun () -> Printf.printf "r ")
  (fun () -> Printf.printf "l ")
  left

let () = print_endline "";;

rbtree_iter print_node
  (fun () -> Printf.printf "r ")
  (fun () -> Printf.printf "l ")
  right

let () = print_endline "";;

rbtree_iter print_node
  (fun () -> Printf.printf "r ")
  (fun () -> Printf.printf "l ")
  (union left right)

let () = print_endline ""
let () = List.iter print_pair (elements (union left right))
let () = print_endline ""
let () = print_endline ""

let () =
  foldr () (fun (key, str) -> fun () -> Printf.printf " (%d %s) " key str) left
