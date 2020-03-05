#!/bin/bash

# Perform extraction.
coqc -R ../.. Top Extraction.v

# Remove unneeded files .
rm -f .*.au *.glob *.mli *.cmi *.cmo Extraction.vo

# Remove empty files.
rm -f List.ml Nat.ml QArith_base.ml Specif.ml

# Replace FSetAVL and FMapAVL files with custom files, which are just wrappers 
# around OCaml's maps and sets.
rm -f Order* FMap* MSet* FSet* Bin* Int.ml PeanoNat.ml
cp OCamlSetMap/FMapAVL.ml OCamlSetMap/FSetAVL.ml OCamlSetMap/OrderedTypeEx.ml .
