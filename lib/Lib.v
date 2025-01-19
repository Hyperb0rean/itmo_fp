Require Import DataStructures.Red_black_tree.

Require Extraction.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "( , )" ]. 

Extraction Language OCaml.

Set Extraction Optimize.

Set Extraction Output Directory "lib".

Extraction "libcoq.ml" Red_black_tree.