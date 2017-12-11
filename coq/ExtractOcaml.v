Require Import Filter.
Require Extraction.

Module BCD := VariableAlphabet <+ Types.

Extract Inductive prod => "(*)" [ "(,)" ].
Extract Constant fst => "fst".
Extract Constant snd => "snd".
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive sig => "'a" [ "" ].
Extract Constant BCD.t => "int".
Extract Constant BCD.eq_dec => "(fun x y -> x = y)".
Extraction Inline BCD.eq_dec.

Extraction Language Ocaml.
Extraction "BCD.ml" BCD.SubtypeRelation.
