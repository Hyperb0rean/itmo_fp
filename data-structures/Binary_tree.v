
Require Import Coq.Strings.String.

Module Binary_search_tree.

Notation "∀ A , B" := (forall A , B) (at level 200).

Notation "∃ A , B" := (exists A , B) (at level 200).


Definition key := nat.
Definition cmp := key -> key -> bool.


Inductive tree (V: Type) : Type := 
| Leaf
| Node (l: tree V) (k: key) (val: V) (r: tree V).

Arguments Leaf {V}.
Arguments Node {V}.



Fixpoint lookup_lt {V : Type} (lt: @cmp) (x : key) (t : tree V)  : 
        option V :=
  match t with
  | Leaf => None
  | Node l y v r => if (lt x y) then lookup_lt lt x l
                 else if (lt y x) then lookup_lt lt x r
                     else Some v
  end.

Fixpoint insert_lt {V : Type} (lt: @cmp)  (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | Leaf => Node Leaf x v Leaf
  | Node l y v' r => if (lt x y) then Node (insert_lt lt x v l) y v' r
                 else if (lt y x) then Node l y v' (insert_lt lt x v r)
                      else Node l x v r
  end.

Definition lookup {V : Type}:  key -> tree V -> option V := (lookup_lt Nat.ltb) .
Definition insert {V : Type}:  key -> V -> tree V -> tree V := (insert_lt Nat.ltb) .


Module Tests.
Open Scope string_scope.

Definition test_tree := Node (Node Leaf 2 "two" (Node Leaf 3 "three" Leaf)) 4 "four" Leaf.

Example tree_test1 :
     insert 3 "three"
     (insert 2 "two" 
     (insert 4 "four" Leaf)) = test_tree.
  Proof. simpl. reflexivity. Qed.

Example tree_test2 :
     lookup 3 test_tree = Some "three".
  Proof. simpl. reflexivity. Qed.

Example tree_test3 :
lookup 5 test_tree = None.
Proof. simpl. reflexivity. Qed.
End Tests.



End Binary_search_tree.
