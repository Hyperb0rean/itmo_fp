Definition nandb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => match b2 with
              | true => false
              | false => true
            end
    | false => true
    end.
    
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.


Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n'=> S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Fixpoint factorial (n: nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.


Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint leb (n m : nat) : bool :=
  match n,m with
  | O, _ => true
  | S n', O => false
  | S n', S m' => leb n' m'
  end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
    match leb n m, leb m n with
    | false, false => false 
    | true, false => true
    | false, true => false
    | true, true => false
    end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: 2 <? 2 = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: 2 <? 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: 4 <? 2 = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H_1 H_2.
  rewrite -> H_1.
  rewrite <- H_2.
  reflexivity.
  Qed.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.


Theorem plus_0_n: forall n: nat, n + 0 = n.
    Proof. 
      induction n.
      - reflexivity.
      - simpl. rewrite -> IHn. reflexivity.  
      Qed.

Theorem mult_n_0: forall n: nat, n*0 = 0.
    Proof. 
      induction n.
      - reflexivity.
      - simpl. rewrite -> IHn. reflexivity.
      Qed.

Theorem mult_n_1: forall n: nat, n*1 = n.
    Proof. 
      induction n.
      - reflexivity.
      - simpl. rewrite -> IHn. reflexivity.
      Qed.

Theorem plus_1: forall n: nat, n + 1 = S n.
Proof. induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
  Qed. 

Theorem mult_n_Sm: forall n m: nat, n*S m = n + n*m.
    Proof.
    intros m n. 
    induction m.
    - reflexivity.
    - induction n.
    + simpl. 
      rewrite <- IHm.
      rewrite -> mult_n_1.
      reflexivity.
    + Admitted.

Theorem andb_true_elim2 : forall b c : bool,
 andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  - simpl. intros. rewrite -> H. reflexivity.
  - destruct c.
    -- reflexivity.
    -- simpl. intros. rewrite <- H. reflexivity.
  Qed.


Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [| n'].
  - reflexivity.
  - reflexivity.
  Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros [] [].
  - simpl. reflexivity.
  - simpl. intros. rewrite -> H. reflexivity.
  - simpl. intros. rewrite -> H. reflexivity.
  - simpl. reflexivity.
  Qed.


Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m: bin) : bin :=
  match m with
  | Z => B1 Z  
  | B0 n => B1 n
  | B1 n => B0 (incr n)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with 
  | Z => O
  | B0 n => (mult 2 (bin_to_nat n)) 
  | B1 n => plus 1 (mult 2 (bin_to_nat n))
  end.


Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.
  
  
  
