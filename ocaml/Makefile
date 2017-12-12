.PHONY: all clean byte native profile debug test

OCB_FLAGS = -I src/interface/ -I src/extracted/
OCB = ocamlbuild $(OCB_FLAGS)

all: native byte

clean:
	$(OCB) -clean

native:
	$(OCB) prototype.native

byte:
	$(OCB) prototype.byte
