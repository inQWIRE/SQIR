# QVM Experiments

## Running QVM

First, run `make qvm` in the top level (`../..`) directory. This will compile our Coq proofs. Then run `./extract.sh` in the current directory. This will extract our Coq definitions to OCaml and compile the resulting OCaml code.

Now you can run the QVM experiments with `dune exec --root extraction -- ./run_qvm.exe`. This will generate a bunch of QASM files with the following naming conventions:
* cl-adder-N.qasm, rz-adder-N.qasm - computes (x + y) using a TOFF-based or QFT-based adder
* rz-const-adder-N.qasm - computes (x + N) using a QFT-based adder
* cl-mul-N.qasm, rz-mul-N.qasm - computes (x * y) using a TOFF-based or QFT-based adder
* cl-const-mul-N.qasm, rz-const-mul-N.qasm - computes (x * N) using a TOFF-based or QFT-based adder
* cl-mod-mul-N.qasm, rz-mod-mul-N.qasm, sqir-mod-mul-N.qasm - computes (x * N % M) using a TOFF-based adder, a QFT-based adder, or our original definition in RCIR.

You can try simulating these programs with `python sanity_check.py <prog>` (requires Python 3 and `pip install qiskit jkq.ddsim`).

To run these programs through VOQC, clone the [mlvoqc](https://github.com/inQWIRE/mlvoqc) repository and follow the directions there for using `voqc_cli.exe`.

## Running Quipper

@Finn - can you add instructions for downloading/installing/running Quipper here?