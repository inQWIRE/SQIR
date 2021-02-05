#!/bin/bash

# Perform extraction.
coqc -R ../.. Top Extraction.v

# Remove unneeded files.
rm -f .*.au *.glob *.mli *.cmi *.cmo Extraction.vo

# Remove empty and unused files.
rm -f BinNums.ml Int.ml List.ml Nat.ml QArith_base.ml Specif.ml

# ml/extract contains custom FSetAVL and FMapAVL files, which are just wrappers 
# around OCaml's maps and sets.
rm -f Order* FMap* MSet* FSet*

# Move extracted files to a subdirectory.
mv Bin*.ml Datatypes.ml ConnectivityGraph.ml GateCancellation.ml \
   HadamardReduction.ml Layouts.ml NotPropagation.ml Optimize.ml PeanoNat.ml \
   RotationMerging.ml RzQGateSet.ml SimpleMapping.ml UnitaryListRepresentation.ml \
   ml/extracted
