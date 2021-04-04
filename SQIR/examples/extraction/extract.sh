#!/bin/bash

# Perform extraction.
coqc -R ../../.. Top ShorExtr.v

# Remove unneeded files.
rm -f *.mli ShorExtr.vo

# Remove empty files.
rm -f ClassicalDedekindReals.ml ConstructiveCauchyReals.ml List.ml ROrderedType.ml

# Move the remaining extracted files to the 'extracted' subdirectory.
mv BinInt.ml BinPos.ml Nat.ml RCIR.ml Rtrigo1.ml ShorAux.ml \
   BinNat.ml Datatypes.ml PeanoNat.ml Rdefinitions.ml \
   ShorExtr.ml BinNums.ml ModMult.ml Rpow_def.ml Shor.ml \
   extracted

# Build extracted code.
dune build generate_circuit.exe
dune build post_process.exe
