
Require Import Coq.Strings.String.

Module Binary_search_tree.

Notation "∀ A , B" := (forall A , B) (at level 200).

Notation "∃ A , B" := (exists A , B) (at level 200).


Inductive tree (K V: Type) : Type := 
| Leaf
| Node (l: tree K V) (key: K) (val: V) (r: tree K V).

Arguments Leaf {K V}.
Arguments Node {K V}.

Definition cmp {K: Type} := K -> K -> bool.


Fixpoint lookup {K V : Type} (x : K) (t : tree K V) (less: @cmp K) : 
        option V :=
  match t with
  | Leaf => None
  | Node l y v r => if (less x y) then lookup x l less
                 else if (less y x) then lookup x r less
                     else Some v
  end.

Fixpoint insert {K V : Type} (x : K) (v : V) (t : tree K V) (less: @cmp K) : tree K V :=
  match t with
  | Leaf => Node Leaf x v Leaf
  | Node l y v' r => if (less x y) then Node (insert x v l less) y v' r
                 else if (less y x) then Node l y v' (insert x v r less)
                      else Node l x v r
  end.


Module Tests.
Open Scope string_scope.

Definition test_tree := Node (Node Leaf 2 "two" (Node Leaf 3 "three" Leaf)) 4 "four" Leaf.

Example tree_test1 :
     insert 3 "three"
     (insert 2 "two" 
     (insert 4 "four" Leaf Nat.ltb) 
     Nat.ltb) Nat.ltb = test_tree.
  Proof. simpl. reflexivity. Qed.

Example tree_test2 :
     lookup 3 test_tree Nat.ltb = Some "three".
  Proof. simpl. reflexivity. Qed.

Example tree_test3 :
lookup 5 test_tree Nat.ltb = None.
Proof. simpl. reflexivity. Qed.
End Tests.



End Binary_search_tree.
