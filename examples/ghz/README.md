# GHZ Example

This directory contains an implementation and proof of GHZ state preparation, plus an example for how to extract Coq/SQIR programs to OCaml/OpenQASM 2.0. You can use this as a model for extracting other SQIR programs.

How to "run" GHZ:
1. Run `make examples` in the top-level directory (`../..`). This compiles the GHZ Coq definitions and proofs (along with several other examples) and the extracted OCaml code in the `extraction/` directory.
2. In the current directory, run `dune exec --root extraction -- ./ghz.exe N` where N is the number of qubits you want in the GHZ state. This runs our OCaml executable (`ghz.exe`) on the input `N`. It will produce a file called `ghz.qasm` that contains the generated OpenQASM code.

The code in the `extraction/` directory was generated using the `./extract.sh` script. You can re-generate the extracted code using this script. Note that it was last tested with Coq version 8.15.2. Other versions of Coq will likely require modifications.