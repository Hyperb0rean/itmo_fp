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

Lemma mul_m_Sn: forall m n: nat,
  m * S n = m * n + m.
  Proof.
    intros.
    induction m.
    - reflexivity.
    - simpl.
      rewrite -> IHm.
      rewrite -> add_assoc.
      rewrite -> plus_n_Sm.
      reflexivity.
    Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof. 
  intros.
  induction n.
  - rewrite -> mult_n_0. reflexivity.
  - rewrite -> mul_m_Sn.
    assert(H: S n * m = m + n * m).
  + reflexivity.
  + rewrite -> H.
    rewrite -> add_comm.
    rewrite -> IHn.
    reflexivity.
    Qed.
    
    