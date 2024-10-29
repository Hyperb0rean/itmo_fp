From LF Require Export basics.

Module Palindrome.
Inductive num: Type :=
| Nil
| Zero (_: num)
| One (_: num)
| Two (_: num)
| Three (_: num)
| Four (_: num)
| Five (_: num)
| Six (_: num)
| Seven (_: num)
| Eight (_: num)
| Nine (_: num)
.

Declare Scope palindrome_scope.
Open Scope palindrome_scope.

Notation "0" := Zero.
Notation "1" := One.
Notation "2" := Two.
Notation "3" := Three.
Notation "4" := Four.
Notation "5" := Five.
Notation "6" := Six.
Notation "7" := Seven.
Notation "8" := Eight.
Notation "9" := Nine.

Notation " [ x1 , .. , x2 ] " := (x2 .. ( x1 Nil) .. ).

Fixpoint succ (d : num) : num :=
  match d with
  | Nil => One Nil
  | Zero d => One d
  | One d => Two d
  | Two d => Three d
  | Three d => Four d
  | Four d => Five d
  | Five d => Six d
  | Six d => Seven d
  | Seven d => Eight d
  | Eight d => Nine d
  | Nine d => Zero (succ d)
  end. 

Notation " ++ x1 " := (succ x1) (at level 70).

Example test_succ: ++ [ 1, 2 ] =  [ 1, 3 ].
Proof. reflexivity. Qed.

Fixpoint reverse (d d' : num) :=
  match d with
  | Nil => d'
  | Zero d => reverse d (Zero d')
  | One d => reverse d (One d')
  | Two d => reverse d (Two d')
  | Three d => reverse d (Three d')
  | Four d => reverse d (Four d')
  | Five d => reverse d (Five d')
  | Six d => reverse d (Six d')
  | Seven d => reverse d (Seven d')
  | Eight d => reverse d (Eight d')
  | Nine d => reverse d (Nine d')
  end.

Fixpoint eq_num (a b : num) : bool :=
    match a, b with
    | Nil, Nil => true
    | Zero a, Zero b => (eq_num a b)
    | One a, One b => (eq_num a b)
    | Two a, Two b => (eq_num a b)
    | Three a, Three b => (eq_num a b)
    | Four a, Four b => (eq_num a b)
    | Five a, Five b => (eq_num a b)
    | Six a, Six b => (eq_num a b)
    | Seven a, Seven b => (eq_num a b)
    | Eight a, Eight b => (eq_num a b)
    | Nine a, Nine b => (eq_num a b)
    | _, _ => false
    end.

Notation " x1 =? x2 " := (eq_num x1 x2) (at level 70).

Example test_eq_num1: [ 1, 2 ] =? [ 1, 2 ] = true.
Proof. reflexivity. Qed.
Example test_eq_num2: [ 1, 2 , 4 ] =? [ 1, 3, 4 ] = false.
Proof. reflexivity. Qed.

Definition is_palindrom (a : num) := 
    eq_num a ( reverse a Nil ).


Example test_is_palindrom1: is_palindrom [ 1, 2, 1 ] = true.
Proof. reflexivity. Qed.
Example test_is_palindrom2: is_palindrom [ 1, 2, 3, 2, 1 ] = true.
Proof. reflexivity. Qed.
Example test_is_palindrom3: is_palindrom [ 1, 2, 3, 1 ] = false.
Proof. reflexivity. Qed.

Fixpoint succ_m (a: num) (m: nat) : num :=
    match m with
    | O => a
    | S m' => (succ_m (succ a) m')
    end. 


Notation " m + a " := (succ_m a m).

Example test_succ_m: 1 + [1, 3, 5] = [1, 3, 6].
Proof. simpl. reflexivity. Qed.
Example test_succ_m2: 9 + [1, 3, 5] = [1, 4, 4].
Proof. simpl. reflexivity. Qed.
Example test_succ_m3: 19 + [1, 3, 5] = [1, 5, 4].
Proof. simpl. reflexivity. Qed.

Fixpoint dec_to_nat (a: num) : nat :=
    match a with
    | Nil => O
    | Zero a' => mult 10 (dec_to_nat a')
    | One a' => (plus 1 (mult 10 (dec_to_nat a')))
    | Two a' => (plus 2 (mult 10 (dec_to_nat a')))
    | Three a' => (plus 3 (mult 10 (dec_to_nat a')))
    | Four a' => (plus 4 (mult 10 (dec_to_nat a')))
    | Five a' => (plus 5 (mult 10 (dec_to_nat a')))
    | Six a' => (plus 6 (mult 10 (dec_to_nat a')))
    | Seven a' => (plus 7 (mult 10 (dec_to_nat a')))
    | Eight a' => (plus 8 (mult 10 (dec_to_nat a')))
    | Nine a' => (plus 9 (mult 10 (dec_to_nat a')))
    end.

Definition mod_10 (a :num) : num :=
    match a with
    | Nil => Nil
    | One _ => (One Nil)
    | Two _ => (Two Nil)
    | Three _ => (Three Nil)
    | Four _ => (Four Nil)
    | Five _ => (Five Nil)
    | Six _ => (Six Nil)
    | Seven _ => (Seven Nil)
    | Eight _ => (Eight Nil)
    | Nine _ => (Nine Nil)
    | Zero _ => (Zero Nil)
    end.


Example test_mod_10: mod_10 [1, 2, 3] = [3].
Proof. simpl. reflexivity. Qed. 


End Palindrome.
