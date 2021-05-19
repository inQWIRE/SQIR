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
   QArith_base.ml Rdefinitions.ml Rpow_def.ml Rtrigo1.ml Specif.ml ZArith_dec.ml

# Move the remaining extracted files to the 'extracted' subdirectory.
echo "Moving generated files to extracted/..."
mv AltGateSet.ml AltShor.ml Bin*.ml Datatypes.ml ModMult.ml Nat.ml \
   PeanoNat.ml RCIR.ml Shor.ml ShorAux.ml ShorExtr.ml  \
   extracted
   
# Build extracted code.
echo "Building extracted code..."
dune build generate_circuit.exe
dune build post_process.exe
