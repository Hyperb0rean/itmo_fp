Require Import DataStructures.Int.
Require Import DataStructures.Red_black_tree.
Import Red_black_tree.
Require Import Coq.Logic.FunctionalExtensionality.
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
  

End Monoid.

Lemma rot_right_nil : forall {V : Type} (t : rbtree V),
  t <> nil -> rot_right t <> nil.
Proof.
  intros. destruct t; auto.
  unfold rot_right.
  repeat
    match goal with
    | |- match ?t with nil => _ | node _ _ _ _ _ => _ end <> _ => destruct t
    | |- node _ _ _ _ _ <> nil => discriminate
    end.
Qed.

Lemma rot_left_nil : forall {V : Type} (t : rbtree V),
  t <> nil -> rot_left t <> nil.
Proof.
  intros. destruct t; auto.
  unfold rot_left.
  repeat
    match goal with
    | |- match ?t with nil => _ | node _ _ _ _ _ => _ end <> _ => destruct t
    | |- node _ _ _ _ _ <> nil => discriminate
    end.
Qed.

Lemma make_black_nil : forall {V : Type} (t : rbtree V),
  t <> nil -> make_black t <> nil.
Proof.
  intros. destruct t; auto.
  unfold make_black.
  discriminate.
Qed.

Lemma flip_colors_nil : forall {V : Type} (t : rbtree V),
  t <> nil -> flip_colors t <> nil.
Proof.
  intros. destruct t; auto.
  unfold flip_colors.
  repeat
    match goal with
    | |- match ?t with nil => _ | node _ _ _ _ _ => _ end <> _ => destruct t
    | |- node _ _ _ _ _ <> nil => discriminate
    | |- match ?c with Red => _ | Black => _ end <> _=> destruct c
    end.
Qed.

Lemma insert_aux_not_nil : forall {V : Type} (k : key) (v : V) (t : rbtree V),
    insert_aux k v t <> nil.
Proof.
  intros. destruct t; simpl.
  - discriminate.
  - unfold balance.
    repeat
      match goal with
      | |- (if ?x then _ else _) <> _ => destruct x
      | |- match ?c with Red => _ | Black => _ end <> _=> destruct c
      | |- match ?t with nil => _ | node _ _ _ _ _ => _ end <> _ => destruct t
      | |- node _ _ _ _ _ <> nil => discriminate
      | |- flip_colors  _ <> nil => apply flip_colors_nil
      | |- make_black  _ <> nil => apply make_black_nil
      end.
Qed.


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

Ltac unfold_tree := match goal with
| H: ForallT _ (node _ _ _ _ _) |- _ => destruct H as [? [? ?] ]
| H: BST (node _ _ _ _ _) |- _ => inversion H; clear H; subst
| |- BST (node _ _ _ _ _) => constructor
| |- BST (match ?c with Red => _ | Black => _ end) => destruct c
| |- BST (match ?t with nil => _ | node _ _ _ _ _ => _ end) => destruct t
| |- ForallT _ _ => repeat split
end; auto; try lia.

Lemma flip_colors_BST: forall {V: Type} (t: rbtree V),
  BST t -> BST (flip_colors t).
Proof.
  intros. unfold flip_colors.
  repeat unfold_tree.
Qed.

Lemma make_black_BST: forall {V: Type} (t: rbtree V),
  BST t -> BST (make_black t).
Proof.
  intros. unfold make_black. 
  destruct t. auto.
  inversion H. clear H. subst.
  constructor; auto.
Qed.

Search (_ > _ -> _ < _). 

Lemma ForallT_ex_imp {V: Type} (P Q: int -> V -> Prop) (t: rbtree V):
  (forall k v, P k v -> Q k v) -> ForallT P t -> ForallT Q t.
Proof.
  intros H HForall.
  induction t as [ | c l IHl k v r IHr]; auto.  
  simpl in HForall. simpl.
  destruct HForall as [HP [Hl Hr]].
  repeat split; auto. 
Qed.

Lemma ForallT_gt {V: Type} (t : rbtree V) (k k0 : key):
  mk_z k > mk_z k0 ->
  ForallT (fun k' _ => mk_z k' > mk_z k) t->
  ForallT (fun k' _ => mk_z k' > mk_z k0) t.
Proof.
  intros. eapply ForallT_ex_imp; eauto.
  intros. simpl in H1. lia.
Qed.


Lemma ForallT_lt {V: Type} (t : rbtree V) (k k0 : key):
  mk_z k < mk_z k0 ->
  ForallT (fun k' _ => mk_z k' < mk_z k) t->
  ForallT (fun k' _ => mk_z k' < mk_z k0) t.
Proof.
  intros. eapply ForallT_ex_imp; eauto.
  intros. simpl in H1. lia.
Qed.

Lemma rot_left_BST:  forall {V: Type} (t: rbtree V),
BST t -> BST (rot_left t).
Proof.
  intros. unfold rot_left.
  repeat unfold_tree.
  apply Z.gt_lt in H.
  apply ForallT_lt with k; auto.
Qed.

Lemma rot_right_BST:  forall {V: Type} (t: rbtree V),
BST t -> BST (rot_right t).
Proof.
  intros. unfold rot_right.
  repeat unfold_tree.
  apply Z.lt_gt in H.
  apply ForallT_gt with k; auto.
Qed.

   
Theorem balance_BST: forall {V : Type} (t : rbtree V),
    BST t -> BST (balance t).
Proof.
  intros. destruct t; unfold balance; auto.
  repeat
    match goal with
    | |- _ => unfold_tree
    | |- _ => apply flip_colors_BST
    | |- _ => apply make_black_BST
    | |- _ => apply rot_left_BST
    | |- _ => apply rot_right_BST
    end;
    auto; try lia.
Qed.






End Red_black_tree_proofs.