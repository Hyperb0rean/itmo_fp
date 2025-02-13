Require Import DataStructures.Int.
Require Import DataStructures.Red_black_tree.
Import Red_black_tree.
Require Import Lia.


Require Import ZArith.
Open Scope Z_scope.

Module Red_black_tree_proofs.

Module Monoid.

Lemma neutral_union_r: forall (V: Type) (t: rbtree V),
  (union t nil) = t.
Proof.
  intros.
  unfold union.
  destruct t.
  all: reflexivity.
Qed.

Lemma neutral_union_l: forall (V: Type) (t: rbtree V),
(union nil t) = t.
Proof.
  intros.
  unfold union.
  destruct t.
  all: reflexivity.
Qed.

Lemma union_node_nil: forall (V: Type) (l r: rbtree V) (c: color) (k: key) (v: V),
union (node c l k v r) nil <> nil.
Proof.
  intros.
  unfold union.
  discriminate.
Qed.
  
Lemma union_nil: forall (V: Type) (a b: rbtree V),
  union a b = nil -> a = nil /\ b = nil.
Proof.
  intros V a b.
  intros H.
  destruct a.
  -- rewrite neutral_union_l in H. auto.
  -- split.
  + destruct b.
  ++ discriminate.
  ++ Admitted.

Lemma union_comm : forall (V: Type) (a b: rbtree V),
  elements (union a b) = elements (union b a).
  intros.
  induction a,b.
  all: auto.
  Admitted.

Lemma insert_union_node: forall (V: Type) (l r: rbtree V) (c: color) (k: key) (v: V),
node c l k v r = insert k v (union l r).
Proof. Admitted.

Lemma insert_union_l: forall (V: Type) (l r: rbtree V) (k: key) (v: V),
union (insert k v l) r = insert k v (union l r).
Proof. Admitted.

Lemma insert_union_r: forall (V: Type) (l r: rbtree V) (k: key) (v: V),
union l (insert k v r) = insert k v (union l r).
Proof. Admitted.

Lemma elements_nil: forall (V: Type) (t: rbtree V),
  elements t  = elements nil -> t = nil.
Proof.
  intros V t.
  unfold elements.
  unfold elements_aux.
  Admitted.



Lemma insert_elements: forall (V: Type) (a b : rbtree V) (k: key) (v: V),
(elements a) = (elements b) -> elements (insert k v a) = elements (insert k v b).
Proof.
  intros V a b k v.
  destruct a, b.
  - auto. 
  - intros H. 
    remember  (node c b1 k0 v0 b2) as t.
    rewrite elements_nil with V t.
    all: auto.
  - intros H. 
    remember  (node c a1 k0 v0 a2) as t.
    rewrite elements_nil with V t.
    all: auto.
  - intros H.
    remember  (node c a1 k0 v0 a2) as aa.
    remember  (node c0 b1 k1 v1 b2) as bb.
    Admitted.


Lemma union_assoc: forall (V: Type) (a b c: rbtree V),
 elements (union a (union b c))  = elements (union (union a b) c).
 Proof.
  intros.
  generalize dependent a.
  generalize dependent c.
  induction b .
  -  intros. rewrite neutral_union_l. rewrite neutral_union_r. auto.
  -  rewrite insert_union_node. 
     (* remember (union (union a1 a2) (union b c)) as aa.
     remember (union (union (union a1 a2) b) c) as bb.
     rewrite insert_elements with V aa bb k v.
     -- reflexivity.
     -- rewrite Heqaa.
        rewrite Heqbb.
        remember (union a1 a2) as u. *)
        Admitted.
        
 
End Monoid.


Fixpoint ForallT {V : Type} (P: int -> V -> Prop) (t : rbtree V) : Prop :=
  match t with
  | nil => True
  | node c l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

Inductive BST {V : Type} : rbtree V -> Prop :=
| ST_nil : BST nil
| ST_node : forall (c : color) (l : rbtree V) (k : key) (v : V) (r : rbtree V),
    ForallT (fun k' _ => (Int.mk_z k') < (Int.mk_z k)) l ->
    ForallT (fun k' _ => (Int.mk_z k') > (Int.mk_z k)) r ->
    BST l ->
    BST r ->
    BST (node c l k v r).


Lemma nil_BST : forall (V : Type), BST (@mk_nil V).
Proof.
  unfold mk_nil. constructor.
Qed.

Theorem balance_BST: forall (V: Type) (t: rbtree V),
  BST t -> BST (balance t).
Proof.
  intros. 
  unfold balance.
    repeat match goal with
  | |- BST (match ?t with nil => _ | node _ _ _ _ _ => _ end) => destruct t
  | |- BST (match ?c with | Red => _ | Black => _ end) => destruct c
  | |- BST _ => constructor
    end; auto; try lia.
  - inversion H. auto.
  Admitted.

Lemma nilP: forall (V : Type) (P : key -> V -> Prop),
    ForallT P nil.
Proof.
  intros.
  unfold ForallT.
  reflexivity.
Qed.

(* Lemma balanceP : forall (V : Type) (P : key -> V -> Prop) 
        (c : color) (l r : rbtree V)
                   (k : key) (v : V),
    ForallT P l ->
    ForallT P r ->
    P k v ->
    ForallT P (balance (node c l k v r)).
Proof.
  intros. 
  unfold balance.
   unfold balance.
  repeat match goal with
  | |- ForallT P (match ?t with nil => _ | node _ _ _ _ _ => _ end) => destruct t
  | |- ForallT P (match ?c with | Red => _ | Black => _ end) => destruct c
  | H: ForallT P (node _ _ _ _ _) |- _ => destruct H; auto
  | |- ForallT P (node _ _ _ _ _) /\ ForallT P (node _ _ _ _ _) => split
  | H: ForallT P _ /\ ForallT P _ |- _ => repeat destruct H; auto
  end; auto.

  Qed. *)

  

End Red_black_tree_proofs.