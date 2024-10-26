From LF Require Export basics.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  induction n.
  - rewrite -> plus_0_n.
    reflexivity.
  - symmetry. simpl. 
    rewrite <- plus_n_Sm.
    rewrite <- IHn.
    reflexivity.
    Qed.