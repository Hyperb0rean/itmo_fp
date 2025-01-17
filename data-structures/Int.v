Require Import ZArith.
Require Extraction.
Require Import Coq.extraction.ExtrOcamlNatInt.

Open Scope Z_scope.
Parameter int : Type.
Extract Inlined Constant int => "int".

Parameter mk_z : int -> Z.
Axiom mk_z_inj: forall (n m : int), mk_z n = mk_z m -> n = m.

Parameter ltb: int -> int -> bool.
Extract Inlined Constant ltb => "( < )".
Axiom ltb_lt : forall (n m : int), ltb n m = true <-> mk_z n < mk_z m.


Parameter leb: int -> int -> bool.
Extract Inlined Constant leb => "( <= )".
Axiom leb_le : forall (n m : int), leb n m = true <-> mk_z n <= mk_z m.

Parameter zero: int.
Extract Inlined Constant zero => "0".


Close Scope Z_scope.
