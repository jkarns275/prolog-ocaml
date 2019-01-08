clean:
	rm -rf ./*.native ./*.out ./*.cmo ./*.cmi
build:
	make clean
	ocamlc vec.ml
	ocamlc vec.cmo interner.ml
	ocamlc vec.cmo interner.cmo prolog.ml -o prolog.native
run:
	make build
	./prolog.native
