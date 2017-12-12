Require Import Filter.
Require Extraction.

Module BDdL := VariableAlphabet <+ Types.

Extract Inductive prod => "(*)" [ "(,)" ].
Extract Constant fst => "fst".
Extract Constant snd => "snd".
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive sig => "" [ "" ].
Extract Constant BDdL.t => "int".
Extract Constant BDdL.eq_dec => "(fun x y -> x = y)".
Extraction Inline BDdL.eq_dec.

Extraction Language Ocaml.
Extraction "BDdL.ml" BDdL.SubtypeRelation.
