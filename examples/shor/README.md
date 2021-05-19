# examples/shor

This directory contains code to extract the Coq formalism of Shor's algorithm to OCaml.

## Compiling Shor's

The first step is to compile the Coq code. You can do this by running `make shor` in the top-level (`../..`) directory. Note that this requires the Coq Interval package (`opam install coq-interval`).

The next step is to run our extraction with `./extract.sh` in the current directory. This will produce a bunch of .ml files in `extraction/extracted` and compile them into an executable in the `extraction/_build` directory. You may need to install dune and zarith first (`opam install dune zarith`). If you are on MacOS, you may see the following warning:
```
ld: warning: directory not found for option '-L/opt/local/lib'
ld: warning: directory not found for option '-L/opt/homebrew/lib'
```
This is caused by our use of zarith, and seems to be safe to ignore.

## Running Shor's

After following the directions above, you should have two executables in the `extracted/_build` directory: one that generates a circuit for the quantum part of Shor's algorithm and one that performs classical post-processing. You can run the first executable with `./generate_circuit.sh N a` where `N` is the number you want to factor and the `a` is a number coprime to `N`. This will produce an OpenQASM file `shor.qasm`. You can run the second executable with `./post_process.sh N a o` where `o` is a measurement outcome from running the circuit.

Example:
```
$ ./generate_circuit.sh 15 7
Generating circuit for N = 15 and a = 7...
Time to generate: 0.072962s
Counting gates...
35 qubits and 21909 gates.
Time to count gates: 0.000477s
Writing file to shor.qasm...
Time to write file: 0.248348s

$ # execute the resulting shor.qasm file (not shown here)

$ # say that the result of execution is 192
$ ./post_process.sh 15 7 192
Performing post-processing for N = 15, a = 7, and o = 192...
Result is: 4
```

## Guarantees

**TODO:** Text description of what our Coq proofs guarantee about the OCaml code.