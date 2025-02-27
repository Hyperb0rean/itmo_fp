Require Import ZArith.
Require Extraction.
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



Parameter leb: int -> int -> bool.
Extract Inlined Constant leb => "( <= )".
Axiom leb_le : forall (n m : int), leb n m = true <-> mk_z n <= mk_z m.
Axiom leb_f_le : forall (n m : int), leb n m = false <-> mk_z m < mk_z n.


Parameter eqb: int -> int -> bool .
Extract Inlined Constant eqb => "( == )".
Axiom eqb_eq : forall (n m : int), eqb n m = true <-> mk_z n = mk_z m.


Close Scope Z_scope.
