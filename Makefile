.DEFAULT_GOAL := sqir

all:
	@dune build

sqir: FORCE
	@dune build SQIR

voqc: FORCE
	@dune build VOQC

examples: FORCE
	@dune build examples/examples
	@dune build examples/ghz

shor:
	@dune build examples/shor

clean:
	@dune clean

install:
	@dune install

uninstall:
	@dune uninstall

# hacky :) we should replace with dune in a future version
FILES=$(shell find . -name "*.v" -depth 1) 
doc: all
	mkdir -p docs
	cd _build/default && coqdoc -g --utf8 --toc --no-lib-name -d ../../docs -R . SQIR $(FILES)

.PHONY: all clean install uninstall doc
FORCE:
