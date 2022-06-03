# GHZ Example

This directory contains an implementation and proof of GHZ state preparation, plus an example for how to extract Coq/SQIR programs to OCaml/OpenQASM 2.0. You can use this as a model for extracting other SQIR programs.

How to "run" GHZ:
1. Run `make ghz` in the top-level directory (`../..`). This compiles the GHZ Coq definitions and proofs.
2. Run `./extract.sh` in this directory. This extracts our Coq definitions to OCaml.
3. Run `dune exec --root extraction -- ./ghz.exe N` where N is the number of qubits you want in the GHZ state. This runs our OCaml executable (`ghz.exe`) on the input `N`. It will produce a file called `ghz.qasm` that contains the generated OpenQASM code.
