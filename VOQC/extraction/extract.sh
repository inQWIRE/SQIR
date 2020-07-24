#!/bin/bash

# Perform extraction.
coqc -R ../.. Top Extraction.v

# Remove unneeded files.
rm -f .*.au *.glob *.mli *.cmi *.cmo Extraction.vo

# Remove empty files.
rm -f List.ml Nat.ml QArith_base.ml Specif.ml

# ml/extract contains custom FSetAVL and FMapAVL files, which are just wrappers 
# around OCaml's maps and sets.
rm -f Order* FMap* MSet* FSet* Bin* Int.ml PeanoNat.ml

# Move extracted files to a subdirectory.
mv Datatypes.ml GateCancellation.ml HadamardReduction.ml \
   NotPropagation.ml Optimize.ml RotationMerging.ml RzQGateSet.ml \
   UnitaryListRepresentation.ml ml/extracted
