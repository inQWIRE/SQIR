# Extraction to OCaml

To run extraction, use the `extract.sh` script in the directory above this (`..`). The files in the `ml` directory are all auto-generated except for [Run.ml](ml/Run.ml), which contains handwritten OCaml code to convert SQIR programs to OpenQASM and run a Python-based circuit simulator.

## Caveats to Correctness

In order to produce an executable program from our verified Coq specifications, we need to rely on some unverified code. For example, our formalization relies on Coq's mathematical definition of Reals, which is not computable. In order to get code we can run, we need to extract the Real type to a computable type. We also introduce some untrusted code for efficiency. For example, rather than running our Coq semantics function (uc_eval) and sampling from the resulting vector (apply_u, sample), we run a Python script that runs the SQIR program through a state-of-the-art simulator.

Our choices for extraction introduce the following assumptions:
* OCaml's Z type is a suitable standin for Coq's nat, Z, Pos, and N types and our modinv and modexp functions are identical to OCaml's Z.invert and Z.powm.
* OCaml floats satisfy the same properties as Coq Real numbers. Unfortunately this is *not true*, but hopefully reasonably realistic. It would be great (but a lot of work!) to prove our code correct with a Coq representation of floats instead of Reals.
* The simulator we use to run Shor's order finding circuit returns a measurement value that is consistent with the probability distribution produced by our uc_eval denotation function.
* Our utility functions in Python and OCaml for file parsing and I/O do not introduce unintended behavior.

## TODOs

* Extracting nat, Z, Pos, and N to OCaml's Z is a little hacky. It would be better to use Coq's BinNums definitions of Z, Pos, and N everywhere and then extract these representations directly. Note that we need to avoid extracting Coq's nat type because it is a unary representation and will almost always result in stack overflows in our use case.
* Our OCaml code should check that the precondtions of Shor's hold, i.e. the input N is not even, not prime, and not a prime power.
* In order to add print statements to code, we manually extract "sample" to a function that includes a printf -- is there are better way to do this?
* In our Python code for running the circuit (../run_circuit.py), it would be more accurate to draw a measurement outcome from the output quantum vector state rather than sampling.
* It would be great to have a set of "unit tests" to check that our extraction is not introducing unexpected behavior.