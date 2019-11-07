.PHONY: coq ocaml clean

COQC = coqc

default: all
all: coq ocaml

world: all

coq/Makefile:
	cd coq && coq_makefile -f _CoqProject -o Makefile
	mv coq/BDdL.ml ocaml/src/interface

coq: coq/Makefile
	$(MAKE) -C coq all

# coq/BDdL.hs: coq
coq/BDdL.ml: coq
coq/BDdL.mli: coq

# haskell/src/BDdL.hs: coq/BDdL.hs
#	sed -e s/_UU03c3_/s/g -e s/_UU03c4_/t/g -e s/_UU03b1_/a/g -e s/_UU03b2_/b/g coq/BDdL.hs > haskell/src/BDdL.hs

#.PHONY: haskell
#haskell: haskell/src/BDdL.hs
#	$(MAKE) -C haskell all

ocaml/src/extracted/BDdL.ml: coq/BDdL.ml coq/BDdL.mli
	test -d ocaml/src/extracted/ || mkdir -p ocaml/src/extracted/ && sed -e s/_UU03c3_/s/g -e s/_UU03c4_/t/g -e s/_UU03b1_/a/g -e s/_UU03b2_/b/g coq/BDdL.ml > ocaml/src/extracted/BDdL.ml && cp coq/BDdL.mli ocaml/src/extracted/

ocaml: ocaml/Makefile
	$(MAKE) -C ocaml native

clean:
	$(MAKE) -C coq clean || true
	rm coq/Makefile{,.conf} || true
#	$(MAKE) -C haskell clean
	$(MAKE) -C ocaml clean
