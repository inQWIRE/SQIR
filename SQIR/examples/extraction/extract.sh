#!/bin/bash

# Perform extraction.
coqc -R ../../.. Top ShorExtr.v

# Remove unneeded files.
rm -f *.mli ShorExtr.vo

# Remove empty files for cleanliness.
rm -f ClassicalDedekindReals.ml ConstructiveCauchyReals.ml ROrderedType.ml

# Build extracted code.
dune build main.exe
