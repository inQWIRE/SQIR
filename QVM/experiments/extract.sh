#!/bin/bash

# Compile AltVSQIR.
echo "Compiling AltVSQIR..."
coqc -R ../.. Top AltVSQIR.v

# Change into the extraction directory.
cd extraction

# Perform extraction.
echo "Extracting code..."
coqc -R ../../.. Top Extraction.v

# Remove unneeded files.
echo "Deleting unneeded files..."
rm -f *.glob *.mli *.vo*

# Remove empty files.
rm -f ClassicalDedekindReals.ml ConstructiveCauchyReals.ml \
   QArith_base.ml Rdefinitions.ml Ring_theory.ml Rpow_def.ml Rtrigo1.ml \
   Specif.ml ZArith_dec.ml

# Move the remaining extracted files to the 'ml' subdirectory.
echo "Moving generated files to ml/..."
mv AltGateSet.ml AltShor.ml AltVSQIR.ml Bin*.ml CLArith.ml Datatypes.ml \
   ModMult.ml Nat.ml PeanoNat.ml RCIR.ml RZArith.ml VSQIR.ml \
   ml

# Build extracted code.
echo "Building extracted code..."
dune build run_qvm.exe
