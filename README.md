# Presentation

This project implements a subtyping algorithm for a type system with a universal type (called Omega), and three type connectives: Arrow, Union, and Intersection.

The subtyping algorithm is formally proven in Coq and extracted to an ocaml (and a haskell) file.

The subtyping rules are taken from the Barbanera-Dezani-de'Liguoro paper called "Intersection and union types: syntax and semantics", and are formalized by the Subtype type in `coq/Filter.v`, which also formalize everything else.

# Dependencies
You need Coq version 8.7.0, and a decent version of OCaml.

# Build instructions
`$ make`

`make` will also generate a small executable, `ocaml/prototype.native`, where you can enter two types and see whether they are subtypes of each other.
The syntax of prototype.native is defined in `ocaml/src/interface/lexer.mly`, and, in short:
* -> stands for Arrow
* & stands for Intersection
* | stands for Union
* $ stands for Omega
* the precedences are such that `a -> b & c | d` stands for `(a -> (b & (c | d)))`