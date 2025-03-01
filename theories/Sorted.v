
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Rbtree.Int.
Require Import ZArith.
Open Scope Z_scope.

Module Sorted.

Inductive sorted {V: Type} : list (int*V) -> Prop :=
    | sorted_nil :
        sorted []
    | sorted_1 : forall x v,
        sorted [(x,v)]
    | sorted_cons : forall x vx y vy l,
        mk_z x <= mk_z y -> sorted ((y, vy) :: l) -> sorted ((x, vx) :: (y, vy) :: l).


Lemma sorted_app {V: Type} : forall l1 l2 x (vx: V),
    sorted l1 -> sorted l2 ->
    Forall (fun '(n, _) => mk_z n < mk_z x) l1 -> Forall (fun '(n,_) => mk_z n > mk_z x) l2 ->
    sorted (l1 ++ (x, vx) :: l2).
Proof.
    intros l1 l2 x Hl1 Hl2 Hlt Hgt.
    induction l1 as [|h t IHt].
    - intros. rewrite app_nil_l.
      inversion Hl2; clear Hl2; subst. 
      repeat constructor.
      + inversion Hlt; clear Hlt; subst; constructor. try lia.
      -- inversion H. lia.
      -- constructor.
      -- inversion H. lia.
      -- inversion H; clear H; subst; constructor; try lia; auto.
    - simpl. 
    inversion Hl2; subst.
    constructor.
    + destruct l2 as [|hd tl];  inversion Hlt; subst; try lia.
    all: inversion Hgt;lia.
    +  simpl in IHt.
       apply IHt; auto; constructor.
    + intros.
      simpl.
      assert(Ht: sorted (((y, vy) :: l) ++ (x, Hl1):: l2)); auto.
    -- apply IHt.
    +++ inversion Hl2. clear Hl2. subst; auto.
    +++ apply Forall_cons_iff; split; auto.
    * inversion Hgt; clear Hgt; subst; auto.
      inversion H5; clear H5; subst; auto.
    * inversion Hgt; clear Hgt; subst; auto.
      inversion H5; clear H5; subst; auto.
    +++ auto.
    -- constructor; auto.
Qed.


End Sorted.