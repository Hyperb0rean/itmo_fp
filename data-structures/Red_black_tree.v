
(*
https://koerbitz.me/posts/Red-Black-Trees-In-Coq-Part-0.html
https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html
*)
Require Import ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import DataStructures.Int.

Module Red_black_tree.

Definition key := Int.int.

Inductive color := Red | Black.

Definition flip_color (c: color) : color :=
  match c with
    | Red => Black
    | Black => Red
  end.

Inductive rbtree (V : Type) : Type :=
| nil : rbtree V
| node : color -> rbtree V -> key -> V -> rbtree V -> rbtree V.

Arguments nil {V}.
Arguments node {V}.


Definition mk_nil {V: Type} : rbtree V :=
  nil.

Fixpoint lookup {V : Type} (x: key) (t : rbtree V) : option V :=
  match t with
  | nil => None
  | node _ t_left k v t_right => if Int.ltb x k then lookup x t_left
                    else if Int.ltb k x then lookup x t_right
                         else Some v
  end.


(*
      k  - tc    
     / \
    a   rk - rc
       / \
      b   c
->
      rk - rc
     / \
 R- k   c
   / \
  a   b
*)

Definition rot_left {V: Type} (t: rbtree V) : rbtree V :=
  match t with
    | nil => nil
    | node tc a k v t_r =>
      match t_r with
        | nil => node tc a k v t_r
        | node rc b rk rv c => node rc (node Red a k v b) rk rv c
      end
  end.

(*
      k - tc
    / \
lc-lk  c
  / \
a    b   
->
     lk - lc
    / \
   a  k - R
     / \
    b   c   
*)

Definition rot_right {V: Type} (t: rbtree V) : rbtree V :=
  match t with
    | nil => nil
    | node tc t_l k v c =>
      match t_l with
        | nil => node tc t_l k v c
        | node lc a lk lv b => node lc a lk lv (node Red b k v c)
      end
  end.

Definition flip_colors {V: Type} (t: rbtree V) : rbtree V :=
  match t with
    | node Black (node Red ll lk lv lr) k v (node Red rl rk rv rr)
       => node Red (node Black ll lk lv lr) k v (node Black rl rk rv rr)
    | _ => t
  end.

Definition make_black {V : Type} (t : rbtree V) : rbtree V :=
  match t with
  | nil => nil
  | node _ a x vx b => node Black a x vx b
  end.

Definition balance
           {V : Type} (t : rbtree V) : rbtree V :=
  match t with
  | nil => nil
  | node Red _ _ _ _ => t
  | node Black l k vk r => 
    match l with
        | node Red (node Red _ _ _ _) _ _ _ =>
            flip_colors (make_black (rot_right t))
        | node Red _ _ _ (node Red _ _ _ _) =>
            let temp_t := node Black (rot_left l) k vk r in
            flip_colors (make_black (rot_right temp_t))
        | _ =>
    match r with
        | node Red (node Red _ _ _ _) _ _ _ =>
            let temp_t := node Black l k vk (rot_right r) in
            flip_colors (make_black (rot_left temp_t))
        | node Red _ _ _ (node Red _ _ _ _) =>
            flip_colors (make_black (rot_left t))
        | _ => t
    end
    end
  end.

Fixpoint ins {V : Type} (x : key) (vx : V) (t : rbtree V) : rbtree V :=
  match t with
  | nil => node Red nil x vx nil
  | node c a y vy b => if Int.ltb x y then balance (node c (ins x vx a) y vy b)
                   else if Int.ltb y x then balance (node c a y vy (ins x vx b))
                        else node c a x vx b
  end.

Definition insert {V : Type} (x : key) (vx : V) (t : rbtree V) : rbtree V :=
  make_black (ins x vx t).

Fixpoint elements_aux {V : Type} (t : rbtree V) (acc: list (key * V))
  : list (key * V) :=
  match t with
  | nil => acc
  | node _ l k v r => elements_aux l ((k, v) :: elements_aux r acc)
  end.

Definition elements {V : Type} (t : rbtree V) : list (key * V) :=
  elements_aux t [].

End Red_black_tree.