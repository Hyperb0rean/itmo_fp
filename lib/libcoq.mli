
type 'a option =
| Some of 'a
| None



module Red_black_tree :
 sig
  type key = int

  type color =
  | Red
  | Black

  val color_rect : 'a1 -> 'a1 -> color -> 'a1

  val color_rec : 'a1 -> 'a1 -> color -> 'a1

  val flip_color : color -> color

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

  val rot_left : 'a1 rbtree -> 'a1 rbtree

  val rot_right : 'a1 rbtree -> 'a1 rbtree

  val flip_colors : 'a1 rbtree -> 'a1 rbtree

  val make_black : 'a1 rbtree -> 'a1 rbtree

  val balance : 'a1 rbtree -> 'a1 rbtree

  val ins : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree

  val insert : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree

  val elements_aux : 'a1 rbtree -> (key * 'a1) list -> (key * 'a1) list

  val elements : 'a1 rbtree -> (key * 'a1) list
 end
