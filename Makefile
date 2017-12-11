OASIS = oasis
COQC = coqc

default: all
all: coq haskell ocaml

world: all

.PHONY: coq
coq:
	$(MAKE) -C coq all

coq/BDdL.hs: coq
coq/BDdL.ml: coq
coq/BDdL.mli: coq

haskell/src/BDdL.hs: coq/BDdL.hs
	sed -e s/_UU03c3_/s/g -e s/_UU03c4_/t/g -e s/_UU03b1_/a/g -e s/_UU03b2_/b/g coq/BDdL.hs > haskell/src/BDdL.hs

.PHONY: haskell
haskell: haskell/src/BDdL.hs
	$(MAKE) -C haskell all

ocaml/src/extracted/BDdL.ml: coq/BDdL.ml coq/BDdL.mli
	test -d ocaml/src/extracted/ || mkdir -p ocaml/src/extracted/ && sed -e s/_UU03c3_/s/g -e s/_UU03c4_/t/g -e s/_UU03b1_/a/g -e s/_UU03b2_/b/g coq/BDdL.ml > ocaml/src/extracted/BDdL.ml && cp coq/BDdL.mli ocaml/src/extracted/

ocaml/Makefile: ocaml/src/extracted/BDdL.ml
	cd ocaml && $(OASIS) setup -setup-update dynamic

.PHONY: ocaml
ocaml: ocaml/Makefile
	$(MAKE) -C ocaml all

.PHONY: microbenchmark
microbenchmark: haskell/dist/build/hsint/hsint ocaml/_build/src/benchmark/TestDriver.native
	./ocaml/_build/src/benchmark/TestDriver.native
	./haskell/dist/build/hsint/hsint

.PHONY: clean
clean:
	$(MAKE) -C coq mrproper
	$(MAKE) -C haskell clean
	$(MAKE) -C ocaml mrproper
