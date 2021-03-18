#!/bin/bash

# Perform extraction.
coqc -R ../../.. Top ShorExtr.v

# Remove unneeded files.
rm -f *.mli ShorExtr.vo

# Remove empty files.
rm -f ClassicalDedekindReals.ml ConstructiveCauchyReals.ml ROrderedType.ml

# Move the remaining extracted files to the 'extracted' subdirectory.
mv BinInt.ml BinPos.ml Nat.ml RCIR.ml Rtrigo1.ml ShorAux.ml \
   BinNat.ml Datatypes.ml PeanoNat.ml Rdefinitions.ml SQIR.ml \
   ShorExtr.ml BinNums.ml ModMult.ml QPE.ml Rpow_def.ml Shor.ml \
   UnitaryOps.ml RCIRplus.ml extracted

# Build extracted code.
dune build generate_circuit.exe
dune build post_process.exe
