
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import DataStructures.Int.
Require Import ZArith.
Open Scope Z_scope.

Module Sorted.

Inductive sorted : list int -> Prop :=
    | sorted_nil :
        sorted []
    | sorted_1 : forall x,
        sorted [x]
    | sorted_cons : forall x y l,
        mk_z x <= mk_z y -> sorted (y :: l) -> sorted (x :: y :: l).


Lemma sorted_app: forall l1 l2 x,
    sorted l1 -> sorted l2 ->
    Forall (fun n => mk_z n < mk_z x) l1 -> Forall (fun n => mk_z n > mk_z x) l2 ->
    sorted (l1 ++ x :: l2).
Proof.
    intros l1 l2 x Hl1 Hl2 Hlt Hgt.
    induction l1 as [|h t IHt].
    - rewrite app_nil_l.
      inversion Hl2; clear Hl2; subst. 
      repeat constructor.
      + constructor.
      ++ inversion Hgt; lia.
      ++ constructor.
      + constructor.
      ++ inversion Hgt; lia.
      ++ constructor; auto.
    - apply Forall_cons_iff in Hlt.
      destruct Hlt.
      inversion Hl1; clear Hl1; subst.
      + constructor; try lia.
      rewrite app_nil_l in IHt. apply IHt; auto; constructor.
Admitted.
        

    

End Sorted.