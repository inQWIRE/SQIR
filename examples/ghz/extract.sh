#!/bin/bash

# Change into the correct directory.
cd extraction

# Perform extraction.
echo "Extracting code..."
coqc -R ../../.. Top ../../shor/extraction/ExtrOcamlList.v
coqc -R ../../.. Top ../../shor/extraction/ExtrOcamlR.v
coqc -R ../../.. Top ../../shor/extraction/ExtrOcamlNatZ.v
coqc -R ../../.. Top ExtrGHZ.v

# Remove unneeded files.
echo "Deleting unneeded files..."
rm -f *.glob *.mli *.vo* .*.aux

# Remove empty and unused files.
rm -f Bin* ClassicalDedekindReals.ml ConstructiveCauchyReals* \
   Datatypes.ml Nat.ml PeanoNat.ml Q* Rdefinitions.ml Ring_theory.ml \
   Specif.ml ZArith_dec.ml

# Move the remaining extracted files to the 'ml' subdirectory.
echo "Moving generated files to ml/..."
mv AltGateSet.ml AltGHZ.ml ml
   
# Build extracted code.
echo "Building extracted code..."
dune build ghz.exe
