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

Fixpoint succ (a : num) : num :=
  match a with
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



End Palindrome.
