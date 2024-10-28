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

Notation " [ x1 , .. , x2 ] " := (x1 .. ( x2 Nil) .. ).

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

Example test_succ: ++ [ 1, 2 ] =  [ 2, 2 ].
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

End Palindrome.
