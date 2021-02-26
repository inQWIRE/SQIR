# SQIR/examples/extraction

This directory contains code to extract the Coq formalism of Shor's algorithm to OCaml.

## Compiling Shor's

The first step is to compile the Coq code. You can do this by running `make shor` in the top-level (`../../..`) directory. Compiling the Shor code **requires Coq v8.10.1**. You can check your Coq version with `coqc -v`, and install the appropriate version with the commands below.
```
opam switch create coq.8.10.1 4.08.1      # makes a switch with OCaml v4.08.1 called "coq.8.10.1"
opam install coq.8.10.1                   # installs Coq
opam install --jobs=2 coq-interval        # installs intervals package
```
The next step is to run our extraction with `./extract.sh` in the current directory. This will produce (or refresh) a bunch of .ml files and compile them into an executable in the `_build` directory. You may need to install dune and zarith first (`opam install dune zarith`). If you are on MacOS, you may see the following warning:
```
ld: warning: directory not found for option '-L/opt/local/lib'
ld: warning: directory not found for option '-L/opt/homebrew/lib'
```
This is caused by our use of Zarith, and seems to be safe to ignore.

## Running Shor's

After following the directions above, you should have two executables in the `_build` directory: one that generates a circuit for the quantum part of Shor's algorithm and one that performs classical post-processing. You can run the first executable with `dune exec -- ./generate_circuit.exe -N <int> -a <int>` where `N` is the number you want to factor and `a` is a number coprime to `N`. This will produce an OpenQASM file `shor.qasm`. You can run the second executable with `dune exec -- ./post_process.exe -N <int> -a <int> -o <int>` where `o` is the measurement outcome from running the circuit.

## Guarantees

**TODO:** Text description of what our Coq proofs guarantee about the OCaml code.