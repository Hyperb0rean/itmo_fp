

Require Import DataStructures.Int.
Require Import DataStructures.Red_black_tree.
Require Import DataStructures.Red_black_tree_proof.
Import Red_black_tree.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.
Require Import List.
Import ListNotations.
Import Red_black_tree_proof.

Module BST_list_proofs.

Search (In _ (_ ++ _)).  

Search app.

Search ((_, _) = (_, _)).

Search incl.

Lemma elemets_complete {V: Type} (k: key) (v: V) (t: rbtree V) :
  lookup k t = Some v -> In (k,v) (elements t).
Proof.
    unfold elements. 
    generalize dependent k.
    generalize dependent v.
    induction t as [| c l IHl k0 v0 r IHr]; simpl.
    - intros. discriminate.
    - intros v k. destruct (ltb k k0) eqn: Hlt.
      all: destruct (ltb k0 k) eqn: Hgt.
      +  apply ltb_lt in Hlt, Hgt; lia.
      +  clear IHr.
         intros Hlookup.
         apply IHl in Hlookup.
         apply in_or_app.
         left; auto.
      + clear IHl.
        intros Hlookup.
        apply IHr in Hlookup.
        apply in_or_app; auto.
        right.
        apply in_cons; auto.
      + apply ltb_f_lt in Hlt, Hgt; auto.
        intros Hveq.
        assert(Heq: (k, v) = (k0, v0)).
        ++ apply pair_equal_spec. split.
        +++ assert (Hkeq: (mk_z k0) = (mk_z k)). {apply BinInt.Z.le_antisymm; auto. }
            apply mk_z_inj; auto.
        +++ congruence. 
        ++ rewrite Heq. apply in_elt; auto.
Qed.

Definition uncurry {X Y Z : Type} (f : X -> Y -> Z) '(a, b) :=
  f a b.
Hint Transparent uncurry : core.

Search Forall.

Lemma elements_forall {V : Type}: forall (P : key -> V -> Prop) (t : rbtree V),
    ForallT P t ->
    Forall (uncurry P) (elements t).
Proof.
  intros P t.
  unfold elements.
  induction t as [| c l IHl k v r IHr]; auto.
  intros HForall.
  inversion HForall. clear HForall. subst.
  destruct H0 as [Hl Hr].
  apply IHl in Hl.
  apply IHr in Hr.
  apply Forall_app. split; auto.
  apply Forall_cons; auto.
Qed.


Lemma elements_relation {V : Type}: forall   (R : key -> key -> Prop) 
      (v: V) (t : rbtree V) 
      (k' k: key) ,
    ForallT (fun y _ => R y k') t ->
    In (k, v) (elements t) -> R k k'.
Proof.
  intros R v t k' k.
  
     



Lemma elemets_correct {V: Type}:
  forall (k: key) (v: V) (t: rbtree V),
  BST t -> In (k, v) (elements t) -> lookup k t = Some v.
Admitted.
    


End BST_list_proofs.