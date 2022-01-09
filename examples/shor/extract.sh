#!/bin/bash

# Change into the correct directory.
cd extraction

# Perform extraction.
echo "Extracting code..."
coqc -R ../../.. Top ShorExtr.v

# Remove unneeded files.
echo "Deleting unneeded files..."
rm -f *.glob *.mli *.vo*

# Remove empty files.
rm -f ClassicalDedekindReals.ml ConstructiveCauchyReals.ml List.ml \
   QArith_base.ml Rdefinitions.ml Ring_theory.ml Rpow_def.ml Rtrigo1.ml \
   Specif.ml ZArith_dec.ml

# Move the remaining extracted files to the 'ml' subdirectory.
echo "Moving generated files to ml/..."
mv AltGateSet.ml AltShor.ml Bin*.ml Datatypes.ml Main.ml ModMult.ml  \
   Nat.ml PeanoNat.ml RCIR.ml Shor.ml NumTheory.ml EulerTotient.ml ContFrac.ml Reduction.ml \
   ml
   
# Build extracted code.
echo "Building extracted code..."
dune build run_shor.exe
