Require Import ZArith.
Require Import Coq.Lists.List.
Require Import Rbtree.Int.

Import ListNotations.


Module Red_black_tree.

Definition key := Int.int.

Inductive color := Red | Black.

Inductive rbtree (V : Type) : Type :=
| nil : rbtree V
| node : color -> rbtree V -> key -> V -> rbtree V -> rbtree V.

Arguments nil {V}.
Arguments node {V}.


Definition mk_nil {V: Type} : rbtree V :=
  nil.

Fixpoint bound {V : Type} (x: key) (t : rbtree V) : bool :=
  match t with
  | nil => false
  | node _ l k v r => if Int.ltb x k then bound x l
                    else if Int.ltb k x then bound x r
                         else true
  end.

Fixpoint lookup {V : Type} (x: key) (t : rbtree V) : option V :=
  match t with
  | nil => None
  | node _ l k v r => if Int.ltb x k then lookup x l
                    else if Int.ltb k x then lookup x r
                         else Some v
  end.

Fixpoint max {V: Type} (t: rbtree V) : option (key * V) :=
  match t with
  | nil => None
  | node _ _ k vk r 
    => match r with 
      | nil => Some (k, vk)
      | _ => max r
      end
  end.

Fixpoint min {V: Type} (t: rbtree V) : option (key * V) :=
  match t with
  | nil => None
  | node _ l k vk _ 
    => match l with 
      | nil => Some (k, vk)
      | _ => min l
      end
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

(*From Software foundations*)


(* Definition balance
           {V : Type} (t : rbtree V) : rbtree V :=
  match t with
  | nil => nil
  | node c l k vk r => 
    match c with
    | Red => node Red l k vk r
    | _ => match l with
          | node Red (node Red a x vx b) y vy c =>
              node Red (node Black a x vx b) y vy (node Black c k vk r)
          | node Red a x vx (node Red b y vy c) =>
              node Red (node Black a x vx b) y vy (node Black c k vk r)
          | _ => match r with
                | node Red (node Red b y vy c) z vz d =>
                    node Red (node Black l k vk b) y vy (node Black c z vz d)
                | node Red b y vy (node Red c z vz d) =>
                    node Red (node Black l k vk b) y vy (node Black c z vz d)
                | _ => node Black l k vk r
                end
          end
    end
  end. *)


Fixpoint insert_aux {V : Type} (x : key) (vx : V) (t : rbtree V) : rbtree V :=
  match t with
  | nil => node Red nil x vx nil
  | node c a y vy b => if Int.ltb x y then balance (node c (insert_aux x vx a) y vy b)
                   else if Int.ltb y x then balance (node c a y vy (insert_aux x vx b))
                        else node c a x vx b
  end.


Definition insert {V : Type} (x : key) (vx : V) (t : rbtree V) : rbtree V :=
  make_black (insert_aux x vx t).


(* assume balanced *)
Fixpoint black_height {V: Type} (t: rbtree V) : nat :=
  match t with
  | nil => 0  
  | node Black l _ _ _ => (black_height l) + 1
  | node Red l _ _ _ => (black_height l)
  end.

Fixpoint join_right {V: Type} (k: key) (vk: V) (l r: rbtree V) : rbtree V :=
  let equal_h := (black_height l) =? (black_height r) in  
  match l, equal_h with
  | nil, _ => insert k vk r
  | node Black ll x vx lr, false => 
    let t' := node Black ll x vx (join_right k vk lr r) in
    balance t'
  | node Black _ _ _ _, true => node Red l k vk r      
  | node Red ll x vx lr, _ => node Red ll x vx (join_right k vk lr r)   
    end.

Fixpoint join_left {V: Type} (k: key) (vk: V) (l r: rbtree V) : rbtree V :=
  let equal_h := (black_height l) =? (black_height r) in  
  match r, equal_h with
  | nil, _ => insert k vk l
  | node Black rl x vx rr, false => 
    let t' := node Black (join_left k vk l rl) x vx rr in
    balance t'
  | node Black _ _ _ _, true => node Red l k vk r      
  | node Red rl x vx rr, _ => node Red (join_left k vk l rl) x vx rr   
    end.

Definition join {V: Type} (k: key) (vk: V) (l r : rbtree V) : rbtree V :=
  if  (black_height r) <? (black_height l) then 
    let t' := join_right k vk l r in
    match t' with
    | node Red _ _ _ (node Red _ _ _ _) => make_black t'
    | _ => t'
    end
  else if (black_height l) <? (black_height r) then
    let t' := join_left k vk l r in
    match t' with
    | node Red (node Red _ _ _ _) _ _ _ => make_black t'
    | _ => t'
    end
  else 
    match l, r with
    | node Black _ _ _ _, node Black _ _ _ _ => node Red l k vk r
    | _,_ => node Black l k vk r
    end.

Fixpoint split {V: Type} (k: key) (t: rbtree V) : (rbtree V * bool * rbtree V) :=
  match t with
  | nil => (nil, false, nil)
  | node _ l tk vtk r => 
    if Int.ltb k tk then 
      let '(l', b, r') := (split k l) in
      (l', b, (join tk vtk r' r))
    else if Int.ltb tk k then 
      let '(l', b, r') := split k r in
      ((join tk vtk l l'), b, r')
    else (l, true, r)
  end.
  

Fixpoint union {V:Type} (t1 t2: rbtree V ) : rbtree V :=
  match t1, t2 with
  | nil, nil => nil
  | nil, _ => t2
  | _ ,nil => t1
  | node _ _ _ _ _, node _ l2 k2 vk2 r2 =>
    let '(l1, b, r1) := split k2 t1 in
    let tl := union l1 l2 in
    let tr := union r1 r2 in
    (join k2 vk2 tl tr)
  end.
  


Fixpoint size {V: Type} (t: rbtree V) : nat :=
  match t with 
  | nil => 0
  | node _ l _ _ r => (size l) + 1 + (size r)
  end.

Fixpoint next {V: Type} (k: key) (t: rbtree V) : option (key * V) := 
  match t with
  | nil => None
  | node _ l nk vnk r =>
      if Int.ltb k nk then
        match next k l with
        | None => Some (nk, vnk) 
        | some_v => some_v
        end
      else if Int.ltb nk k then
        next k r
      else 
        min r
  end.

Fixpoint foldr_aux {V R: Type} (init: R) (f: (key * V) -> R -> R) (k : key) (t: rbtree V) (fuel: nat) {struct fuel}: R :=
  match next k t, fuel with
  | Some (nk, vnk), S pfuel => 
    f (nk, vnk) (foldr_aux init f nk t pfuel)
  | _,_ => init
  end.


Definition foldr {V R: Type} (init: R) (f: (key * V) -> R -> R) (t: rbtree V) :=
  match min t with
  | Some (fst, fstv) => 
    let fuel := size t in
    f (fst, fstv) (foldr_aux init f fst t fuel)
  | _ => init
  end.

Fixpoint fast_elements_aux {V : Type} (t : rbtree V) (acc: list (key * V))
  : list (key * V) :=
  match t with
  | nil => acc
  | node _ l k v r => fast_elements_aux l ((k, v) :: fast_elements_aux r acc)
  end.


Definition fast_elements {V : Type} (t : rbtree V) : list (key * V) :=
fast_elements_aux t [].


Fixpoint elements {V : Type} (t : rbtree V) : list (key*V) :=
  match t with
  | nil => []
  | node c l k v r => elements l ++ (k, v) :: elements r
  end.

Fixpoint eqb_aux {V: Type} (k: key) (t1 t2: rbtree V) (fuel: nat) {struct fuel} : bool :=
  match next k t1, next k t2, fuel with
  | Some (nk1, _), Some (nk2, _), S pfuel =>
      if Int.eqb nk1 nk2 then
          eqb_aux nk1 t1 t2 pfuel
      else
        false  
  | None, None, O => true  
  | _,_,_ => false 
  end.

Definition rbtree_eqb {V: Type} (t1 t2: rbtree V) : bool :=
  let fuel := size t1 in
  match min t1, min t2, fuel with
  | Some (k1, _), Some (k2, _), S pfuel => 
  eqb_aux k1 t1 t2 pfuel
  | None, None, O => true 
  | _,_, _ => false 
  end.



Fixpoint slow_union_aux {V:Type} (t1: rbtree V) (el: list (key * V)) : rbtree V :=
  match el with
  | [] => t1
  | (k, v) :: tail => slow_union_aux (insert k v t1) tail
  end.


Definition slow_union {V:Type} (t1 t2: rbtree V ) : rbtree V :=
    match t1, t2 with
  | nil, nil => nil
  | nil, _ => t2
  | _ ,nil => t1
  | _, _ => slow_union_aux t1 (elements t2)
  end.


Definition delete {V: Type} (k: key) (t: rbtree V) : (rbtree V * bool) := 
  let '(l, b, r) := split k t in
  if b then (union l r, true)
  else (t, false).

      
Definition list_keys {V : Type} (lst : list (key * V)) :=
  map fst lst.
              

End Red_black_tree.