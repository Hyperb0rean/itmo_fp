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

  Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
  Qed.

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  assert(H: n+m = m+n).
  - rewrite -> add_comm. reflexivity.
  - rewrite <- H. reflexivity.
  Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros.
  symmetry.
  induction n as [ | n' IHn].
  - rewrite -> mult_n_0. reflexivity.
  - assert(H_l: S n' * m = n' * m + m).
  + simpl. 
    rewrite -> IHn.
    rewrite <- add_comm.
    reflexivity.
  + simpl.
  Admitted.
    