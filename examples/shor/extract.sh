#!/bin/bash

# Change into the correct directory.
cd extraction

# Perform extraction.
echo "Extracting code..."
coqc ExtrOcamlList.v
coqc ExtrOcamlNatZ.v
coqc -R ../../../_build/default/SQIR SQIR ExtrOcamlR.v
coqc -R ../../../_build/default/SQIR SQIR -R ../../../_build/default/examples/examples Examples -R ../../../_build/default/examples/shor Shor Extraction.v

# Remove unneeded files.
echo "Deleting unneeded files..."
rm -f *.glob *.mli *.vo* .*.aux

# Remove empty and unused files.
rm -f Bin* ClassicalDedekindReals.ml ConstructiveCauchyReals.ml NumTheory.ml \
   QArith_base.ml Raxioms.ml Rdefinitions.ml Ring_theory.ml Rpow_def.ml \
   Rtrigo1.ml Specif.ml ZArith_dec.ml

# Move the remaining extracted files to the 'ml' subdirectory.
echo "Moving generated files to ml/..."
mv ExtractionGateSet.ml ContFrac.ml Datatypes.ml DiscreteProb.ml ExtrShor.ml \
   List0.ml Main.ml ModMult.ml Nat.ml PeanoNat.ml RCIR.ml RealAux.ml \
   Shor.ml Summation.ml \
   ml
   
# Build extracted code.
echo "Building extracted code..."
dune build run_shor.exe
