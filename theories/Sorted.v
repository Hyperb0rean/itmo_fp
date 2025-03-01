
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

Inductive sorted_keys : list int -> Prop :=
    | sorted_keys_nil :
        sorted_keys []
    | sorted_keys_1 : forall x,
        sorted_keys [x]
    | sorted_keys_cons : forall x y l,
        mk_z x <= mk_z y -> sorted_keys (y :: l) -> sorted_keys (x :: y :: l).

Fixpoint merge l1 l2 {struct l1} :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      if Int.leb a1 a2 then a1 :: merge l1' l2 else a2 :: merge_aux l2'
  end
  in merge_aux l2.

Lemma merge_sorted {V: Type} :
    forall (l1 l2: list int),
        sorted_keys l1 -> sorted_keys l2 -> sorted_keys (merge l1 l2).
      intros l1 l2 Hl1 Hl2.
      unfold merge.
      induction Hl1 as [ | x | x y l Hxy Hsorted IHl1];
        induction Hl2 as [ | y' | y' z l' Hzy' Hsorted' IHl2];
        simpl; try constructor; auto.
      -  simpl.
        destruct  (Int.leb x y') eqn: Hlt.
        + constructor; try apply leb_le; auto. constructor.
        + constructor. apply Int.leb_f_le in Hlt. lia. constructor.
      - simpl; auto.
        destruct (Int.leb x y') eqn: Hlt.
        + constructor; try apply leb_le; auto. 
          constructor; try apply leb_le; auto. apply leb_le. lia.
        + destruct (Int.leb x z) eqn:Hlt2.
        -- constructor; try apply leb_f_le in Hlt; auto. lia.
        -- constructor. try apply leb_f_le in Hlt; auto. 
           auto.
      - destruct (Int.leb x y') eqn: Hlt.
        + destruct (Int.leb y y') eqn: Hlt2.
        all: constructor. try lia; auto.
        ++ destruct (Int.leb y y'); auto.
        ++ apply leb_le. auto.
        ++ auto.
        +  destruct (Int.leb y y'); auto.
        ++ constructor; apply leb_f_le in Hlt. 
        +++ lia.
        +++ constructor; auto.
        ++ constructor.
        +++ apply leb_f_le in Hlt. lia.
        +++ constructor; auto.     
    - destruct (Int.leb x y') eqn: Hlt; auto.
      all: destruct (Int.leb y z) eqn: Hlt3; auto.
      all: destruct (Int.leb x z) eqn: Hlt4; auto.
      all: destruct (Int.leb y y') eqn: Hlt2; auto.
      all: try constructor; try lia; auto.
      all: try apply leb_le; auto.
      all: try constructor.
      repeat match goal with 
      | H : Int.leb _ _ = true |- _ => apply leb_le in H
      | H : Int.leb _ _ = false |- _ => apply leb_f_le in H
      | |- Int.leb _ _ = true => apply leb_le
      | |- Int.leb _ _ = false => apply leb_f_le
      end; try lia; auto.
      all: auto.
Admitted. 


End Sorted.