Require Import Filter.
Require Extraction.

Module BDdL := VariableAlphabet <+ Types.

Extract Inductive prod => "(,)" [ "(,)" ].
Extract Constant fst => "Prelude.fst".
Extract Constant snd => "Prelude.snd".
Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sig => "'a" [ "" ].
Extract Constant BDdL.t => "Prelude.Int".
Extract Constant BDdL.eq_dec => "(Prelude.==)".
Extraction Inline BDdL.eq_dec.

Extraction Language Haskell.
Extraction "BDdL.hs" BDdL.SubtypeRelation.
