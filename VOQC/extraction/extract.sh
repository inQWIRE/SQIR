#!/bin/bash

# Perform extraction.
coqc -R ../.. Top Extraction.v

# Remove unneeded files.
rm -f .*.au *.glob *.mli *.cmi *.cmo *.vo*

# Remove empty and unused files. Some files are unused because we manually
# extract types like R and Q. We also use custom FSetAVL and FMapAVL files
# (see ml/extracted), which are wrappers around OCaml's maps and sets.
rm -f BinNums.ml ClassicalDedekindReals.ml ConstructiveCauchyReals.ml \
      FMap* FSet* Int.ml List.ml MSet* Nat.ml Order* Rdefinitions.ml ROrderedType.ml \
      Ratan.ml Rtrigo1.ml Rtrigo_def.ml QArith_base.ml Specif.ml ZArith_dec.ml

# Move extracted files to a subdirectory.
mv Bin*.ml ChangeRotationBasis.ml CXCancellation.ml ConnectivityGraph.ml Datatypes.ml \
   GateCancellation.ml HadamardReduction.ml IBMGateSet.ml Layouts.ml NotPropagation.ml \
   Optimize.ml Optimize1qGates.ml PeanoNat.ml RotationMerging.ml RzQGateSet.ml \
   SimpleMapping.ml UnitaryListRepresentation.ml \
   ml/extracted
