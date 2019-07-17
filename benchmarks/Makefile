
all: 
	ocamlc -c extracted_code.ml 
	ocamllex qlexer.mll
	ocamlyacc qparser.mly
	ocamlc -c ast.ml
	ocamlc -c qparser.mli
	ocamlc -c qparser.ml
	ocamlc -c qlexer.ml
	ocamlc -c main.ml
	ocamlfind ocamlmktop -o top ast.cmo qparser.cmo qlexer.cmo extracted_code.cmo main.cmo

clean:
	rm *.cmo *.cmi *.mli top

