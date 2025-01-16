
type 'a option =
| Some of 'a
| None



module Red_black_tree =
 struct
  type key = int

  type color =
  | Red
  | Black

  (** val color_rect : 'a1 -> 'a1 -> color -> 'a1 **)

  let color_rect f f0 = function
  | Red -> f
  | Black -> f0

  (** val color_rec : 'a1 -> 'a1 -> color -> 'a1 **)

  let color_rec f f0 = function
  | Red -> f
  | Black -> f0

  (** val flip_color : color -> color **)

  let flip_color = function
  | Red -> Black
  | Black -> Red

  type 'v rbtree =
  | Coq_nil
  | Coq_node of color * 'v rbtree * key * 'v * 'v rbtree

  (** val rbtree_rect :
      'a2 -> (color -> 'a1 rbtree -> 'a2 -> key -> 'a1 -> 'a1 rbtree -> 'a2
      -> 'a2) -> 'a1 rbtree -> 'a2 **)

  let rec rbtree_rect f f0 = function
  | Coq_nil -> f
  | Coq_node (c, r0, k, y, r1) ->
    f0 c r0 (rbtree_rect f f0 r0) k y r1 (rbtree_rect f f0 r1)

  (** val rbtree_rec :
      'a2 -> (color -> 'a1 rbtree -> 'a2 -> key -> 'a1 -> 'a1 rbtree -> 'a2
      -> 'a2) -> 'a1 rbtree -> 'a2 **)

  let rec rbtree_rec f f0 = function
  | Coq_nil -> f
  | Coq_node (c, r0, k, y, r1) ->
    f0 c r0 (rbtree_rec f f0 r0) k y r1 (rbtree_rec f f0 r1)

  (** val mk_nil : 'a1 rbtree **)

  let mk_nil =
    Coq_nil

  (** val lookup : key -> 'a1 rbtree -> 'a1 option **)

  let rec lookup x = function
  | Coq_nil -> None
  | Coq_node (_, t_left, k, v, t_right) ->
    if ( < ) x k
    then lookup x t_left
    else if ( < ) k x then lookup x t_right else Some v

  (** val rot_left : 'a1 rbtree -> 'a1 rbtree **)

  let rot_left = function
  | Coq_nil -> Coq_nil
  | Coq_node (tc, a, k, v, t_r) ->
    (match t_r with
     | Coq_nil -> Coq_node (tc, a, k, v, t_r)
     | Coq_node (rc, b, rk, rv, c) ->
       Coq_node (rc, (Coq_node (Red, a, k, v, b)), rk, rv, c))

  (** val rot_right : 'a1 rbtree -> 'a1 rbtree **)

  let rot_right = function
  | Coq_nil -> Coq_nil
  | Coq_node (tc, t_l, k, v, c) ->
    (match t_l with
     | Coq_nil -> Coq_node (tc, t_l, k, v, c)
     | Coq_node (lc, a, lk, lv, b) ->
       Coq_node (lc, a, lk, lv, (Coq_node (Red, b, k, v, c))))

  (** val flip_colors : 'a1 rbtree -> 'a1 rbtree **)

  let flip_colors t = match t with
  | Coq_nil -> t
  | Coq_node (c, r, k, v, r0) ->
    (match c with
     | Red -> t
     | Black ->
       (match r with
        | Coq_nil -> t
        | Coq_node (c0, ll, lk, lv, lr) ->
          (match c0 with
           | Red ->
             (match r0 with
              | Coq_nil -> t
              | Coq_node (c1, rl, rk, rv, rr) ->
                (match c1 with
                 | Red ->
                   Coq_node (Red, (Coq_node (Black, ll, lk, lv, lr)), k, v,
                     (Coq_node (Black, rl, rk, rv, rr)))
                 | Black -> t))
           | Black -> t)))

  (** val make_black : 'a1 rbtree -> 'a1 rbtree **)

  let make_black = function
  | Coq_nil -> Coq_nil
  | Coq_node (_, a, x, vx, b) -> Coq_node (Black, a, x, vx, b)

  (** val balance : 'a1 rbtree -> 'a1 rbtree **)

  let balance t = match t with
  | Coq_nil -> Coq_nil
  | Coq_node (c, l, k, vk, r) ->
    (match c with
     | Red -> t
     | Black ->
       (match l with
        | Coq_nil ->
          (match r with
           | Coq_nil -> t
           | Coq_node (c0, r0, _, _, r1) ->
             (match c0 with
              | Red ->
                (match r0 with
                 | Coq_nil ->
                   (match r1 with
                    | Coq_nil -> t
                    | Coq_node (c1, _, _, _, _) ->
                      (match c1 with
                       | Red -> flip_colors (make_black (rot_left t))
                       | Black -> t))
                 | Coq_node (c1, _, _, _, _) ->
                   (match c1 with
                    | Red ->
                      let temp_t = Coq_node (Black, l, k, vk, (rot_right r))
                      in
                      flip_colors (make_black (rot_left temp_t))
                    | Black ->
                      (match r1 with
                       | Coq_nil -> t
                       | Coq_node (c2, _, _, _, _) ->
                         (match c2 with
                          | Red -> flip_colors (make_black (rot_left t))
                          | Black -> t))))
              | Black -> t))
        | Coq_node (c0, r0, _, _, r1) ->
          (match c0 with
           | Red ->
             (match r0 with
              | Coq_nil ->
                (match r1 with
                 | Coq_nil ->
                   (match r with
                    | Coq_nil -> t
                    | Coq_node (c1, r2, _, _, r3) ->
                      (match c1 with
                       | Red ->
                         (match r2 with
                          | Coq_nil ->
                            (match r3 with
                             | Coq_nil -> t
                             | Coq_node (c2, _, _, _, _) ->
                               (match c2 with
                                | Red -> flip_colors (make_black (rot_left t))
                                | Black -> t))
                          | Coq_node (c2, _, _, _, _) ->
                            (match c2 with
                             | Red ->
                               let temp_t = Coq_node (Black, l, k, vk,
                                 (rot_right r))
                               in
                               flip_colors (make_black (rot_left temp_t))
                             | Black ->
                               (match r3 with
                                | Coq_nil -> t
                                | Coq_node (c3, _, _, _, _) ->
                                  (match c3 with
                                   | Red ->
                                     flip_colors (make_black (rot_left t))
                                   | Black -> t))))
                       | Black -> t))
                 | Coq_node (c1, _, _, _, _) ->
                   (match c1 with
                    | Red ->
                      let temp_t = Coq_node (Black, (rot_left l), k, vk, r) in
                      flip_colors (make_black (rot_right temp_t))
                    | Black ->
                      (match r with
                       | Coq_nil -> t
                       | Coq_node (c2, r2, _, _, r3) ->
                         (match c2 with
                          | Red ->
                            (match r2 with
                             | Coq_nil ->
                               (match r3 with
                                | Coq_nil -> t
                                | Coq_node (c3, _, _, _, _) ->
                                  (match c3 with
                                   | Red ->
                                     flip_colors (make_black (rot_left t))
                                   | Black -> t))
                             | Coq_node (c3, _, _, _, _) ->
                               (match c3 with
                                | Red ->
                                  let temp_t = Coq_node (Black, l, k, vk,
                                    (rot_right r))
                                  in
                                  flip_colors (make_black (rot_left temp_t))
                                | Black ->
                                  (match r3 with
                                   | Coq_nil -> t
                                   | Coq_node (c4, _, _, _, _) ->
                                     (match c4 with
                                      | Red ->
                                        flip_colors (make_black (rot_left t))
                                      | Black -> t))))
                          | Black -> t))))
              | Coq_node (c1, _, _, _, _) ->
                (match c1 with
                 | Red -> flip_colors (make_black (rot_right t))
                 | Black ->
                   (match r1 with
                    | Coq_nil ->
                      (match r with
                       | Coq_nil -> t
                       | Coq_node (c2, r2, _, _, r3) ->
                         (match c2 with
                          | Red ->
                            (match r2 with
                             | Coq_nil ->
                               (match r3 with
                                | Coq_nil -> t
                                | Coq_node (c3, _, _, _, _) ->
                                  (match c3 with
                                   | Red ->
                                     flip_colors (make_black (rot_left t))
                                   | Black -> t))
                             | Coq_node (c3, _, _, _, _) ->
                               (match c3 with
                                | Red ->
                                  let temp_t = Coq_node (Black, l, k, vk,
                                    (rot_right r))
                                  in
                                  flip_colors (make_black (rot_left temp_t))
                                | Black ->
                                  (match r3 with
                                   | Coq_nil -> t
                                   | Coq_node (c4, _, _, _, _) ->
                                     (match c4 with
                                      | Red ->
                                        flip_colors (make_black (rot_left t))
                                      | Black -> t))))
                          | Black -> t))
                    | Coq_node (c2, _, _, _, _) ->
                      (match c2 with
                       | Red ->
                         let temp_t = Coq_node (Black, (rot_left l), k, vk, r)
                         in
                         flip_colors (make_black (rot_right temp_t))
                       | Black ->
                         (match r with
                          | Coq_nil -> t
                          | Coq_node (c3, r2, _, _, r3) ->
                            (match c3 with
                             | Red ->
                               (match r2 with
                                | Coq_nil ->
                                  (match r3 with
                                   | Coq_nil -> t
                                   | Coq_node (c4, _, _, _, _) ->
                                     (match c4 with
                                      | Red ->
                                        flip_colors (make_black (rot_left t))
                                      | Black -> t))
                                | Coq_node (c4, _, _, _, _) ->
                                  (match c4 with
                                   | Red ->
                                     let temp_t = Coq_node (Black, l, k, vk,
                                       (rot_right r))
                                     in
                                     flip_colors
                                       (make_black (rot_left temp_t))
                                   | Black ->
                                     (match r3 with
                                      | Coq_nil -> t
                                      | Coq_node (c5, _, _, _, _) ->
                                        (match c5 with
                                         | Red ->
                                           flip_colors
                                             (make_black (rot_left t))
                                         | Black -> t))))
                             | Black -> t))))))
           | Black ->
             (match r with
              | Coq_nil -> t
              | Coq_node (c1, r2, _, _, r3) ->
                (match c1 with
                 | Red ->
                   (match r2 with
                    | Coq_nil ->
                      (match r3 with
                       | Coq_nil -> t
                       | Coq_node (c2, _, _, _, _) ->
                         (match c2 with
                          | Red -> flip_colors (make_black (rot_left t))
                          | Black -> t))
                    | Coq_node (c2, _, _, _, _) ->
                      (match c2 with
                       | Red ->
                         let temp_t = Coq_node (Black, l, k, vk,
                           (rot_right r))
                         in
                         flip_colors (make_black (rot_left temp_t))
                       | Black ->
                         (match r3 with
                          | Coq_nil -> t
                          | Coq_node (c3, _, _, _, _) ->
                            (match c3 with
                             | Red -> flip_colors (make_black (rot_left t))
                             | Black -> t))))
                 | Black -> t)))))

  (** val ins : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree **)

  let rec ins x vx = function
  | Coq_nil -> Coq_node (Red, Coq_nil, x, vx, Coq_nil)
  | Coq_node (c, a, y, vy, b) ->
    if ( < ) x y
    then balance (Coq_node (c, (ins x vx a), y, vy, b))
    else if ( < ) y x
         then balance (Coq_node (c, a, y, vy, (ins x vx b)))
         else Coq_node (c, a, x, vx, b)

  (** val insert : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree **)

  let insert x vx t =
    make_black (ins x vx t)

  (** val elements_aux :
      'a1 rbtree -> (key * 'a1) list -> (key * 'a1) list **)

  let rec elements_aux t acc =
    match t with
    | Coq_nil -> acc
    | Coq_node (_, l, k, v, r) ->
      elements_aux l ((k , v)::(elements_aux r acc))

  (** val elements : 'a1 rbtree -> (key * 'a1) list **)

  let elements t =
    elements_aux t []
 end
