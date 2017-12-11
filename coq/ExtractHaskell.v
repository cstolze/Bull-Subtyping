Require Import Filter.
Require Extraction.

Module BCD := VariableAlphabet <+ Types.

Extract Inductive prod => "(,)" [ "(,)" ].
Extract Constant fst => "Prelude.fst".
Extract Constant snd => "Prelude.snd".
Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sig => "'a" [ "" ].
Extract Constant BCD.t => "Prelude.Int".
Extract Constant BCD.eq_dec => "(Prelude.==)".
Extraction Inline BCD.eq_dec.

Extraction Language Haskell.
Extraction "BCD.hs" BCD.SubtypeRelation.
