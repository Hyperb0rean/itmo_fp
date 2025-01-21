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

Lemma union_assoc: forall (V: Type) (a b c: rbtree V),
 (union a (union b c)) = (union (union a b) c).
 Proof.
  intros.
  remember a as a'.
  induction a'.
  - rewrite neutral_union_l.
    rewrite neutral_union_l.
    reflexivity.
  - remember b as b'. destruct b'.
    +  auto. rewrite neutral_union_l. reflexivity.
    + remember c as c'. destruct c'.
      -- auto. rewrite neutral_union_r. rewrite neutral_union_r. reflexivity.
      -- auto. 
          rewrite -> Heqc'. rewrite -> Heqb'. rewrite -> Heqa'.
          rewrite -> Heqc' in IHa'1. rewrite -> Heqc' in IHa'2.   
          rewrite -> Heqb' in IHa'1. rewrite -> Heqb' in IHa'2. 
          
          simpl.

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