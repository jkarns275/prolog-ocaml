OCB_FLAGS = -use-ocamlfind -use-menhir -pkg core -tag thread -I src -I lib
OCB = ocamlbuild $(OCB_FLAGS)

clean:
	$(OCB) -clean
build:
	$(OCB) prolog.native
run: 	build
	./prolog.native
