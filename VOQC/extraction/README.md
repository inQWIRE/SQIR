# Extraction to OCaml

Run `./extract.sh` to extract our verified optimizer. You can then build a .so verison of the optimizer with `dune build libvoqc.so.`

For performance, we have decided to:
* Extract Coq nat to OCaml int
* Extract Coq Q to OCaml Zarith Q
* Replace Coq's FMapAVL and FSetAVL implementations with OCaml's built-in Set and Map.

This makes the assumption that these OCaml data structures satify the properties proved about their corresponding Coq implementations. Note that nats are only used to identify qubit indices and we do not perform arithmetic over qubit indices, so an overflow is unlikely.

For details on our extraction process, see Extraction.v and extract.sh.

**TODO**: Explain the various dune files. The basic idea is to (1) compile the extracted VOQC code, (2) create C bindings for VOQC function, (3) compile the bindings, (4) wrap everything up in a shared object file.