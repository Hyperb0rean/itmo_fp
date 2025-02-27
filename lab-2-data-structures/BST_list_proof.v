

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

Search In (_ ++ _ ).


Lemma elements_relation {V : Type} (R : key -> key -> Prop) 
    (t : rbtree V) 
    (k' k: key) (v: V) :
    ForallT (fun y _ => R y k') t ->
    In (k, v) (elements t) -> R k k'.
Proof.
  intros H.
  apply elements_forall in H.
  rewrite Forall_forall in H.
  unfold uncurry in H.
  apply H.
Qed.
     
Lemma elemets_correct {V: Type}:
  forall  (t: rbtree V) (k: key) (v: V),
  BST t -> In (k, v) (elements t) -> lookup k t = Some v.
Proof.
  intros t.
  induction t as [|c l IHl k' v' r IHr]; simpl;auto.
  - contradiction.
  - intros k v HBST.
    inversion HBST. clear HBST. subst.
    destruct (ltb k k') eqn: Hlt; intros; auto.
    all: destruct (ltb k' k) eqn: Hgt; auto.
    + apply ltb_lt in Hlt, Hgt; lia.
    + apply IHl with k v in H6; auto.
      apply ltb_lt in Hlt.
      apply in_app_iff in H.
      destruct H; auto.
      apply in_inv in H.
      destruct H.
      -- apply BinInt.Z.lt_neq in Hlt. 
         apply pair_equal_spec in H; destruct H.
         rewrite H in Hlt.
         apply mk_z_neq in Hlt. contradiction.
      -- apply elements_relation with (fun (y _ : key) =>
         BinInt.Z.gt (mk_z y) (mk_z k')) r k' k v in H.
         lia. exact H5.
    + apply IHr with k v in H7; auto.
      apply ltb_lt in Hgt.
      apply in_app_iff in H.
      destruct H; auto.
      -- apply elements_relation with (fun (y _ : key) =>
        BinInt.Z.lt (mk_z y) (mk_z k')) l k' k v in H.
        lia. exact H3.
      -- apply in_inv in H.
        destruct H; auto.
        apply BinInt.Z.lt_neq in Hgt. 
        apply pair_equal_spec in H; destruct H.
        rewrite H in Hlt.
        apply mk_z_neq in Hgt. contradiction.
    + apply ltb_f_lt in Hlt, Hgt.
      assert (Hkeq: (mk_z k') = (mk_z k)). {apply BinInt.Z.le_antisymm; auto. }
      apply mk_z_inj in Hkeq.
      subst.
      apply in_app_iff in H.
      destruct H.
      -- apply elements_relation with (fun (y _ : key) =>
      BinInt.Z.lt (mk_z y) (mk_z k)) l k k v in H.
      lia. exact H3.
      -- destruct H; auto.
      ++ apply pair_equal_spec in H; destruct H.
        congruence.
      ++ apply elements_relation with (fun (y _ : key) =>
         BinInt.Z.gt (mk_z y) (mk_z k)) r k k v in H.
         lia. exact H5. 
Qed.


End BST_list_proofs.