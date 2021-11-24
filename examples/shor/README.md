# examples/shor

This directory contains the SQIR formalization of Shor's factoring algorithm.

## Directory Contents

Main file
* Main.v - prettified statements of correctness

Core formalization
* ModMult.v - modular exponentiation, defined in RCIR
* QPEGeneral.v - general statement of correctness for ../QPE.v
* RCIR.v - formalization of reversible circuits
* ResourceShor.v - proof about the resources (= gates) required for Shor's
* Shor.v - core formalization of Shor's algorithm

Utilities
* AltShor.v - Shor's algorithm defined in the new gate set; proofs that the new definition is equivalent to the old (Shor.v)
* Resources.v - facts about the number of gates used by various operations
* ShorAux.v - number theory results, reduction from fatorization to order finding, and other useful facts for Shor.v

## Compilation

The first step is to compile the Coq code. You can do this by running `make shor` in the top-level (`../..`) directory. Note that this requires the Coq Interval package (`opam install coq-interval`).

The next step is to extract the compiled Coq code to OCaml by running `./extract.sh` in the current directory. This will produce a bunch of .ml files in `extraction/extracted` and compile them into an executable in the `extraction/_build` directory. You may need to install dune and zarith first (`opam install dune zarith`). If you are on MacOS, you may see the following warning:
```
ld: warning: directory not found for option '-L/opt/local/lib'
ld: warning: directory not found for option '-L/opt/homebrew/lib'
```
This is caused by our use of zarith, and seems to be safe to ignore.

## Running Extracted Code

Our extracted code uses the ddsim simulator (through its Qiskit interface) to execute Shor's circuit (see extraction/run_circuit.py). So in order to run our extracted code you will need **Python version >= 3.6, qiskit, and ddsim**. Once you have a suitable version of Python, you can install the latter two with `pip install qiskit jkq.ddsim`. If you run into trouble with your Python environment, then consider using anaconda per [these directions for installing qiskit](https://qiskit.org/documentation/getting_started.html).

Now you should be able to run Shor's with our script `./run_shor.sh N a` where `N` is the number you want to factor and the `a` is a number coprime to `N`.

Example:
```
$ ./run_shor.sh 15 7
TODO: add check that N can be written as (p^k * q) for k>0, prime p>2, q>2, and p^k, q coprime
Running Shor's for N = 15 and a = 7...
Measurement outcome is 128
Failed to find non-trivial factor. Try another measurement outcome? (Y/n) Y
Measurement outcome is 192
Non-trivial factor is 3.
```

## Verified Properties

TODO: add text description of correctness

Some assumptions introduced by extraction (see extraction/ShorExtr.v)
* OCaml floats satisfy the same properties as Coq Real numbers. (Unfortunately this is *not true*, but maybe somewhat accurate? We can try to be more specific by listing all facts we use about Real numbers... but this may be a long list. -KH)
* The simulator we use to run Shor's returns a vector that is consistent with our uc_eval denotation function.
* OCaml rationals satisfy the same properties as Coq rational numbers.
* Our utility functions in Python and OCaml (e.g. for file parsing and running the simulator) do not introduce unintended behavior.
