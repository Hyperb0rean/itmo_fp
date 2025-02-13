
(** val add : int -> int -> int **)

let rec add = (+)

module Nat =
 struct
  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Stdlib.Int.succ n) m
 end

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
  | Coq_node (_, l, k, v, r) ->
    if ( < ) x k then lookup x l else if ( < ) k x then lookup x r else Some v

  (** val max : 'a1 rbtree -> (key * 'a1) option **)

  let rec max = function
  | Coq_nil -> None
  | Coq_node (_, _, k, vk, r) ->
    (match r with
     | Coq_nil -> Some (k , vk)
     | Coq_node (_, _, _, _, _) -> max r)

  (** val min : 'a1 rbtree -> (key * 'a1) option **)

  let rec min = function
  | Coq_nil -> None
  | Coq_node (_, l, k, vk, _) ->
    (match l with
     | Coq_nil -> Some (k , vk)
     | Coq_node (_, _, _, _, _) -> min l)

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

  let balance = function
  | Coq_nil -> Coq_nil
  | Coq_node (c, l, k, vk, r) ->
    (match c with
     | Red -> Coq_node (Red, l, k, vk, r)
     | Black ->
       (match l with
        | Coq_nil ->
          (match r with
           | Coq_nil -> Coq_node (Black, l, k, vk, r)
           | Coq_node (c0, b, y, vy, d) ->
             (match c0 with
              | Red ->
                (match b with
                 | Coq_nil ->
                   (match d with
                    | Coq_nil -> Coq_node (Black, l, k, vk, r)
                    | Coq_node (c1, c2, z, vz, d0) ->
                      (match c1 with
                       | Red ->
                         Coq_node (Red, (Coq_node (Black, l, k, vk, b)), y,
                           vy, (Coq_node (Black, c2, z, vz, d0)))
                       | Black -> Coq_node (Black, l, k, vk, r)))
                 | Coq_node (c1, b0, y0, vy0, c2) ->
                   (match c1 with
                    | Red ->
                      Coq_node (Red, (Coq_node (Black, l, k, vk, b0)), y0,
                        vy0, (Coq_node (Black, c2, y, vy, d)))
                    | Black ->
                      (match d with
                       | Coq_nil -> Coq_node (Black, l, k, vk, r)
                       | Coq_node (c3, c4, z, vz, d0) ->
                         (match c3 with
                          | Red ->
                            Coq_node (Red, (Coq_node (Black, l, k, vk, b)),
                              y, vy, (Coq_node (Black, c4, z, vz, d0)))
                          | Black -> Coq_node (Black, l, k, vk, r)))))
              | Black -> Coq_node (Black, l, k, vk, r)))
        | Coq_node (c0, a, x, vx, c1) ->
          (match c0 with
           | Red ->
             (match a with
              | Coq_nil ->
                (match c1 with
                 | Coq_nil ->
                   (match r with
                    | Coq_nil -> Coq_node (Black, l, k, vk, r)
                    | Coq_node (c2, b, y, vy, d) ->
                      (match c2 with
                       | Red ->
                         (match b with
                          | Coq_nil ->
                            (match d with
                             | Coq_nil -> Coq_node (Black, l, k, vk, r)
                             | Coq_node (c3, c4, z, vz, d0) ->
                               (match c3 with
                                | Red ->
                                  Coq_node (Red, (Coq_node (Black, l, k, vk,
                                    b)), y, vy, (Coq_node (Black, c4, z, vz,
                                    d0)))
                                | Black -> Coq_node (Black, l, k, vk, r)))
                          | Coq_node (c3, b0, y0, vy0, c4) ->
                            (match c3 with
                             | Red ->
                               Coq_node (Red, (Coq_node (Black, l, k, vk,
                                 b0)), y0, vy0, (Coq_node (Black, c4, y, vy,
                                 d)))
                             | Black ->
                               (match d with
                                | Coq_nil -> Coq_node (Black, l, k, vk, r)
                                | Coq_node (c5, c6, z, vz, d0) ->
                                  (match c5 with
                                   | Red ->
                                     Coq_node (Red, (Coq_node (Black, l, k,
                                       vk, b)), y, vy, (Coq_node (Black, c6,
                                       z, vz, d0)))
                                   | Black -> Coq_node (Black, l, k, vk, r)))))
                       | Black -> Coq_node (Black, l, k, vk, r)))
                 | Coq_node (c2, b, y, vy, c3) ->
                   (match c2 with
                    | Red ->
                      Coq_node (Red, (Coq_node (Black, a, x, vx, b)), y, vy,
                        (Coq_node (Black, c3, k, vk, r)))
                    | Black ->
                      (match r with
                       | Coq_nil -> Coq_node (Black, l, k, vk, r)
                       | Coq_node (c4, b0, y0, vy0, d) ->
                         (match c4 with
                          | Red ->
                            (match b0 with
                             | Coq_nil ->
                               (match d with
                                | Coq_nil -> Coq_node (Black, l, k, vk, r)
                                | Coq_node (c5, c6, z, vz, d0) ->
                                  (match c5 with
                                   | Red ->
                                     Coq_node (Red, (Coq_node (Black, l, k,
                                       vk, b0)), y0, vy0, (Coq_node (Black,
                                       c6, z, vz, d0)))
                                   | Black -> Coq_node (Black, l, k, vk, r)))
                             | Coq_node (c5, b1, y1, vy1, c6) ->
                               (match c5 with
                                | Red ->
                                  Coq_node (Red, (Coq_node (Black, l, k, vk,
                                    b1)), y1, vy1, (Coq_node (Black, c6, y0,
                                    vy0, d)))
                                | Black ->
                                  (match d with
                                   | Coq_nil -> Coq_node (Black, l, k, vk, r)
                                   | Coq_node (c7, c8, z, vz, d0) ->
                                     (match c7 with
                                      | Red ->
                                        Coq_node (Red, (Coq_node (Black, l,
                                          k, vk, b0)), y0, vy0, (Coq_node
                                          (Black, c8, z, vz, d0)))
                                      | Black -> Coq_node (Black, l, k, vk, r)))))
                          | Black -> Coq_node (Black, l, k, vk, r)))))
              | Coq_node (c2, a0, x0, vx0, b) ->
                (match c2 with
                 | Red ->
                   Coq_node (Red, (Coq_node (Black, a0, x0, vx0, b)), x, vx,
                     (Coq_node (Black, c1, k, vk, r)))
                 | Black ->
                   (match c1 with
                    | Coq_nil ->
                      (match r with
                       | Coq_nil -> Coq_node (Black, l, k, vk, r)
                       | Coq_node (c3, b0, y, vy, d) ->
                         (match c3 with
                          | Red ->
                            (match b0 with
                             | Coq_nil ->
                               (match d with
                                | Coq_nil -> Coq_node (Black, l, k, vk, r)
                                | Coq_node (c4, c5, z, vz, d0) ->
                                  (match c4 with
                                   | Red ->
                                     Coq_node (Red, (Coq_node (Black, l, k,
                                       vk, b0)), y, vy, (Coq_node (Black, c5,
                                       z, vz, d0)))
                                   | Black -> Coq_node (Black, l, k, vk, r)))
                             | Coq_node (c4, b1, y0, vy0, c5) ->
                               (match c4 with
                                | Red ->
                                  Coq_node (Red, (Coq_node (Black, l, k, vk,
                                    b1)), y0, vy0, (Coq_node (Black, c5, y,
                                    vy, d)))
                                | Black ->
                                  (match d with
                                   | Coq_nil -> Coq_node (Black, l, k, vk, r)
                                   | Coq_node (c6, c7, z, vz, d0) ->
                                     (match c6 with
                                      | Red ->
                                        Coq_node (Red, (Coq_node (Black, l,
                                          k, vk, b0)), y, vy, (Coq_node
                                          (Black, c7, z, vz, d0)))
                                      | Black -> Coq_node (Black, l, k, vk, r)))))
                          | Black -> Coq_node (Black, l, k, vk, r)))
                    | Coq_node (c3, b0, y, vy, c4) ->
                      (match c3 with
                       | Red ->
                         Coq_node (Red, (Coq_node (Black, a, x, vx, b0)), y,
                           vy, (Coq_node (Black, c4, k, vk, r)))
                       | Black ->
                         (match r with
                          | Coq_nil -> Coq_node (Black, l, k, vk, r)
                          | Coq_node (c5, b1, y0, vy0, d) ->
                            (match c5 with
                             | Red ->
                               (match b1 with
                                | Coq_nil ->
                                  (match d with
                                   | Coq_nil -> Coq_node (Black, l, k, vk, r)
                                   | Coq_node (c6, c7, z, vz, d0) ->
                                     (match c6 with
                                      | Red ->
                                        Coq_node (Red, (Coq_node (Black, l,
                                          k, vk, b1)), y0, vy0, (Coq_node
                                          (Black, c7, z, vz, d0)))
                                      | Black -> Coq_node (Black, l, k, vk, r)))
                                | Coq_node (c6, b2, y1, vy1, c7) ->
                                  (match c6 with
                                   | Red ->
                                     Coq_node (Red, (Coq_node (Black, l, k,
                                       vk, b2)), y1, vy1, (Coq_node (Black,
                                       c7, y0, vy0, d)))
                                   | Black ->
                                     (match d with
                                      | Coq_nil ->
                                        Coq_node (Black, l, k, vk, r)
                                      | Coq_node (c8, c9, z, vz, d0) ->
                                        (match c8 with
                                         | Red ->
                                           Coq_node (Red, (Coq_node (Black,
                                             l, k, vk, b1)), y0, vy0,
                                             (Coq_node (Black, c9, z, vz,
                                             d0)))
                                         | Black ->
                                           Coq_node (Black, l, k, vk, r)))))
                             | Black -> Coq_node (Black, l, k, vk, r)))))))
           | Black ->
             (match r with
              | Coq_nil -> Coq_node (Black, l, k, vk, r)
              | Coq_node (c2, b, y, vy, d) ->
                (match c2 with
                 | Red ->
                   (match b with
                    | Coq_nil ->
                      (match d with
                       | Coq_nil -> Coq_node (Black, l, k, vk, r)
                       | Coq_node (c3, c4, z, vz, d0) ->
                         (match c3 with
                          | Red ->
                            Coq_node (Red, (Coq_node (Black, l, k, vk, b)),
                              y, vy, (Coq_node (Black, c4, z, vz, d0)))
                          | Black -> Coq_node (Black, l, k, vk, r)))
                    | Coq_node (c3, b0, y0, vy0, c4) ->
                      (match c3 with
                       | Red ->
                         Coq_node (Red, (Coq_node (Black, l, k, vk, b0)), y0,
                           vy0, (Coq_node (Black, c4, y, vy, d)))
                       | Black ->
                         (match d with
                          | Coq_nil -> Coq_node (Black, l, k, vk, r)
                          | Coq_node (c5, c6, z, vz, d0) ->
                            (match c5 with
                             | Red ->
                               Coq_node (Red, (Coq_node (Black, l, k, vk,
                                 b)), y, vy, (Coq_node (Black, c6, z, vz,
                                 d0)))
                             | Black -> Coq_node (Black, l, k, vk, r)))))
                 | Black -> Coq_node (Black, l, k, vk, r))))))

  (** val insert_aux : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree **)

  let rec insert_aux x vx = function
  | Coq_nil -> Coq_node (Red, Coq_nil, x, vx, Coq_nil)
  | Coq_node (c, a, y, vy, b) ->
    if ( < ) x y
    then balance (Coq_node (c, (insert_aux x vx a), y, vy, b))
    else if ( < ) y x
         then balance (Coq_node (c, a, y, vy, (insert_aux x vx b)))
         else Coq_node (c, a, x, vx, b)

  (** val insert : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree **)

  let insert x vx t =
    make_black (insert_aux x vx t)

  (** val black_height : 'a1 rbtree -> int **)

  let rec black_height = function
  | Coq_nil -> 0
  | Coq_node (c, l, _, _, _) ->
    (match c with
     | Red -> black_height l
     | Black -> add (black_height l) (Stdlib.Int.succ 0))

  (** val join_right :
      key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree -> 'a1 rbtree **)

  let rec join_right k vk l r =
    let equal_h = (=) (black_height l) (black_height r) in
    (match l with
     | Coq_nil -> insert k vk r
     | Coq_node (c, ll, x, vx, lr) ->
       (match c with
        | Red -> Coq_node (Red, ll, x, vx, (join_right k vk lr r))
        | Black ->
          if equal_h
          then Coq_node (Red, l, k, vk, r)
          else let t' = Coq_node (Black, ll, x, vx, (join_right k vk lr r)) in
               balance t'))

  (** val join_left : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree -> 'a1 rbtree **)

  let rec join_left k vk l r =
    let equal_h = (=) (black_height l) (black_height r) in
    (match r with
     | Coq_nil -> insert k vk l
     | Coq_node (c, rl, x, vx, rr) ->
       (match c with
        | Red -> Coq_node (Red, (join_left k vk l rl), x, vx, rr)
        | Black ->
          if equal_h
          then Coq_node (Red, l, k, vk, r)
          else let t' = Coq_node (Black, (join_left k vk l rl), x, vx, rr) in
               balance t'))

  (** val join : key -> 'a1 -> 'a1 rbtree -> 'a1 rbtree -> 'a1 rbtree **)

  let join k vk l r =
    if Nat.ltb (black_height r) (black_height l)
    then let t' = join_right k vk l r in
         (match t' with
          | Coq_nil -> t'
          | Coq_node (c, _, _, _, r1) ->
            (match c with
             | Red ->
               (match r1 with
                | Coq_nil -> t'
                | Coq_node (c0, _, _, _, _) ->
                  (match c0 with
                   | Red -> make_black t'
                   | Black -> t'))
             | Black -> t'))
    else if Nat.ltb (black_height l) (black_height r)
         then let t' = join_left k vk l r in
              (match t' with
               | Coq_nil -> t'
               | Coq_node (c, r0, _, _, _) ->
                 (match c with
                  | Red ->
                    (match r0 with
                     | Coq_nil -> t'
                     | Coq_node (c0, _, _, _, _) ->
                       (match c0 with
                        | Red -> make_black t'
                        | Black -> t'))
                  | Black -> t'))
         else (match l with
               | Coq_nil -> Coq_node (Black, l, k, vk, r)
               | Coq_node (c, _, _, _, _) ->
                 (match c with
                  | Red -> Coq_node (Black, l, k, vk, r)
                  | Black ->
                    (match r with
                     | Coq_nil -> Coq_node (Black, l, k, vk, r)
                     | Coq_node (c0, _, _, _, _) ->
                       (match c0 with
                        | Red -> Coq_node (Black, l, k, vk, r)
                        | Black -> Coq_node (Red, l, k, vk, r)))))

  (** val split : key -> 'a1 rbtree -> ('a1 rbtree * bool) * 'a1 rbtree **)

  let rec split k = function
  | Coq_nil -> (Coq_nil , false) , Coq_nil
  | Coq_node (_, l, tk, vtk, r) ->
    if ( < ) k tk
    then let p , r' = split k l in p , (join tk vtk r' r)
    else if ( < ) tk k
         then let p , r' = split k r in
              let l' , b = p in ((join tk vtk l l') , b) , r'
         else (l , true) , r

  (** val size : 'a1 rbtree -> int **)

  let rec size = function
  | Coq_nil -> 0
  | Coq_node (_, l, _, _, r) ->
    add (add (size l) (Stdlib.Int.succ 0)) (size r)

  (** val next : key -> 'a1 rbtree -> (key * 'a1) option **)

  let rec next k = function
  | Coq_nil -> None
  | Coq_node (_, l, nk, vnk, r) ->
    if ( < ) k nk
    then (match next k l with
          | Some p -> Some p
          | None -> Some (nk , vnk))
    else if ( < ) nk k then next k r else min r

  (** val foldr_aux :
      'a2 -> ((key * 'a1) -> 'a2 -> 'a2) -> key -> 'a1 rbtree -> int -> 'a2 **)

  let rec foldr_aux init f k t fuel =
    match next k t with
    | Some p ->
      let nk , vnk = p in
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ -> init)
         (fun pfuel -> f (nk , vnk) (foldr_aux init f nk t pfuel))
         fuel)
    | None -> init

  (** val foldr : 'a2 -> ((key * 'a1) -> 'a2 -> 'a2) -> 'a1 rbtree -> 'a2 **)

  let foldr init f t =
    match min t with
    | Some p ->
      let fst , fstv = p in
      let fuel = size t in f (fst , fstv) (foldr_aux init f fst t fuel)
    | None -> init

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

  (** val eqb_aux : key -> 'a1 rbtree -> 'a1 rbtree -> int -> bool **)

  let rec eqb_aux k t1 t2 fuel =
    match next k t1 with
    | Some p ->
      let nk1 , _ = p in
      (match next k t2 with
       | Some p0 ->
         let nk2 , _ = p0 in
         ((fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> false)
            (fun pfuel ->
            if ( == ) nk1 nk2 then eqb_aux nk1 t1 t2 pfuel else false)
            fuel)
       | None -> false)
    | None ->
      (match next k t2 with
       | Some _ -> false
       | None ->
         ((fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> true)
            (fun _ -> false)
            fuel))

  (** val rbtree_eqb : 'a1 rbtree -> 'a1 rbtree -> bool **)

  let rbtree_eqb t1 t2 =
    let fuel = size t1 in
    (match min t1 with
     | Some p ->
       let k1 , _ = p in
       (match min t2 with
        | Some _ ->
          ((fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> false)
             (fun pfuel -> eqb_aux k1 t1 t2 pfuel)
             fuel)
        | None -> false)
     | None ->
       (match min t2 with
        | Some _ -> false
        | None ->
          ((fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> true)
             (fun _ -> false)
             fuel)))

  (** val union_aux : 'a1 rbtree -> (key * 'a1) list -> 'a1 rbtree **)

  let rec union_aux t1 = function
  | [] -> t1
  | p::tail -> let k , v = p in union_aux (insert k v t1) tail

  (** val union : 'a1 rbtree -> 'a1 rbtree -> 'a1 rbtree **)

  let union t1 t2 =
    match t1 with
    | Coq_nil ->
      (match t2 with
       | Coq_nil -> Coq_nil
       | Coq_node (_, _, _, _, _) -> t2)
    | Coq_node (_, _, _, _, _) ->
      (match t2 with
       | Coq_nil -> t1
       | Coq_node (_, _, _, _, _) -> union_aux t1 (elements t2))

  (** val delete : key -> 'a1 rbtree -> 'a1 rbtree * bool **)

  let delete k t =
    let p , r = split k t in
    let l , b = p in if b then (union l r) , true else t , false
 end
