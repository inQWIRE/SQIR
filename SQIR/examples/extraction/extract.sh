#!/bin/bash

# Compile Coq files in the current directory (will add to the Makefile later)
echo "Building AltGateSet.v..."
coqc -R ../../.. Top AltGateSet.v
echo "Building AltShor.v..."
coqc -R ../../.. Top AltShor.v

# Perform extraction.
echo "Extracting code..."
coqc -R ../../.. Top ShorExtr.v

# Remove unneeded files.
echo "Removing unneeded files..."
rm -f *.mli ShorExtr.vo

# Remove empty files.
rm -f ClassicalDedekindReals.ml ConstructiveCauchyReals.ml List.ml ROrderedType.ml

# Move the remaining extracted files to the 'extracted' subdirectory.
echo "Moving generated files to extracted/..."
mv AltGateSet.ml AltShor.ml \
   BinInt.ml BinPos.ml Nat.ml RCIR.ml Rtrigo1.ml ShorAux.ml \
   BinNat.ml Datatypes.ml PeanoNat.ml Rdefinitions.ml \
   ShorExtr.ml BinNums.ml ModMult.ml Rpow_def.ml Shor.ml \
   extracted

# Build extracted code.
echo "Building extracted code..."
dune build generate_circuit.exe
dune build post_process.exe
