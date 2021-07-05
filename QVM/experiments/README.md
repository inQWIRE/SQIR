# QVM Experiments

We evaluate QVM by looking at the sizes of SQIR circuits generated for:
* addition
* multiplication
* sin

## Running QVM

First, run `make qvm` in the top level (`../..`) directory. This will compile our Coq proofs. Then run `./extract.sh` in the current directory. This will extract our Coq definitions to OCaml and compile the resulting OCaml code.

Now you can run the QVM experiments with `dune exec --root extraction -- ./run_qvm.exe`

## Running Quipper

@Finn - can you add instructions for downloading/installing/running Quipper here?