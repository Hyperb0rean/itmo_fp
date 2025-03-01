Require Import ZArith.
Require Extraction.
Require Import Lia .
 
Require Import Coq.extraction.ExtrOcamlNatInt.

Open Scope Z_scope.
Parameter int : Type.
Extract Inlined Constant int => "int".

Parameter mk_z : int -> Z.
Axiom mk_z_inj: forall (n m : int), mk_z n = mk_z m -> n = m.

Lemma mk_z_neq : forall (n m : int), mk_z n <> mk_z m -> n <> m.
Proof.
  intros n m H.
  contradict H.
  rewrite H.
  auto.
Qed.

Parameter ltb: int -> int -> bool.
Extract Inlined Constant ltb => "( < )".
Axiom ltb_lt : forall (n m : int), ltb n m = true <-> mk_z n < mk_z m.
Axiom ltb_f_lt : forall (n m : int), ltb n m = false <-> mk_z m <= mk_z n.

Lemma ltb_trans : forall a b c : int,
  ltb a b = true -> ltb b c = true -> ltb a c = true.
Proof.
  intros a b c H_ab H_bc.
  apply ltb_lt in H_ab.  
  apply ltb_lt in H_bc. 
  apply ltb_lt.          
  lia.                   
Qed.

Parameter leb: int -> int -> bool.
Extract Inlined Constant leb => "( <= )".
Axiom leb_le : forall (n m : int), leb n m = true <-> mk_z n <= mk_z m.
Axiom leb_f_le : forall (n m : int), leb n m = false <-> mk_z m < mk_z n.

Lemma leb_trans : forall a b c : int,
  leb a b = true -> leb b c = true -> leb a c = true.
Proof.
  intros a b c H_ab H_bc.
  apply leb_le in H_ab.  
  apply leb_le in H_bc.  
  apply leb_le.          
  lia.                   
Qed.


Parameter eqb: int -> int -> bool .
Extract Inlined Constant eqb => "( == )".
Axiom eqb_eq : forall (n m : int), eqb n m = true <-> mk_z n = mk_z m.


Close Scope Z_scope.
