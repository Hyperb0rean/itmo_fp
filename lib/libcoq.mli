
val add : int -> int -> int

module Nat :
 sig
  val ltb : int -> int -> bool
 end

module Red_black_tree :
 sig
  type key = int

  type color =
  | Red
  | Black

  val color_rect : 'a1 -> 'a1 -> color -> 'a1

  val color_rec : 'a1 -> 'a1 -> color -> 'a1

  type 'v rbtree =
  | Coq_nil
  | Coq_node of color * 'v rbtree * key * 'v * 'v rbtree

  val rbtree_rect :
    'a2 -> (color -> 'a1 rbtree -> 'a2 -> key -> 'a1 -> 'a1 rbtree -> 'a2 ->
    'a2) -> 'a1 rbtree -> 'a2

  val rbtree_rec :
    'a2 -> (color -> 'a1 rbtree -> 'a2 -> key -> 'a1 -> 'a1 rbtree -> 'a2 ->
    'a2) -> 'a1 rbtree -> 'a2

  val mk_nil : 'a1 rbtree

  val lookup : key -> 'a1 rbtree -> 'a1 option

  val max : 'a1 rbtree -> (key * 'a1) option

  val min : 'a1 rbtree -> (key * 'a1) option

  module BalanceDetails :
   sig
    val rot_left : 'a1 rbtree -> 'a1 rbtree

    val rot_right : 'a1 rbtree -> 'a1 rbtree

    val flip_colors : 'a1 rbtree -> 'a1 rbtree

    val make_black : 'a1 rbtree -> 'a1 rbtree

    val balance : 'a1 rbtree -> 'a1 rbtree

    val insert_aux : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree
   end

  val insert : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree

  module UnionDetails :
   sig
    val black_height : 'a1 rbtree -> int

    val join_right : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree -> 'a1 rbtree

    val join_left : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree -> 'a1 rbtree

    val join : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree -> 'a1 rbtree

    val split : key -> 'a1 rbtree -> ('a1 rbtree * bool) * 'a1 rbtree
   end

  val union : 'a1 rbtree -> 'a1 rbtree -> 'a1 rbtree

  val delete : key -> 'a1 rbtree -> 'a1 rbtree * bool

  val size : 'a1 rbtree -> int

  module IterDetails :
   sig
    val elements_aux : 'a1 rbtree -> (key * 'a1) list -> (key * 'a1) list

    val next : key -> 'a1 rbtree -> (key * 'a1) option

    val iter_aux : ((key * 'a1) -> unit) -> key -> 'a1 rbtree -> int -> unit
   end

  val iter : ((key * 'a1) -> unit) -> 'a1 rbtree -> unit

  val elements : 'a1 rbtree -> (key * 'a1) list
 end
