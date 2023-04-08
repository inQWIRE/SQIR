# examples/shor

This directory contains the SQIR formalization of Shor's factoring algorithm, which is described in our paper [A Formally Certified End-to-End Implementation of Shor's Factorization Algorithm](https://arxiv.org/abs/2204.07112). For questions about the code in this directory, contact Yuxiang Peng (@PicksPeng) or Kesha Hietala (@khieta).

## Directory Contents

Main file
* Main.v - Prettified definitions and statements of correctness. In particular, see `shor_body` and `end_to_end_shors`.

Core formalization
* ModMult.v - Modular exponentiation, defined in RCIR.
* QPEGeneral.v - General statement of correctness for examples/QPE.v.
* RCIR.v - Formalization of reversible circuits.
* ResourceShor.v - Proofs about the resources (i.e. number of gates) required for Shor's.
* Shor.v - Core formalization of Shor's algorithm.

Utilities
* ContFrac.v - Results about continued fractions.
* EulerTotient.v - Re-statement of Euler's totient function from the [coq-euler](https://github.com/taorunz/euler) library.
* ExtrShor.v - Shor's algorithm defined in a gate set amenable to extraction; proofs that the new definition is equivalent to the original.
* NumTheory.v - General number theory results.
* Reduction.v - Proof of the reduction from factorization to order finding.
* Resource.v - Facts about the number of gates used by different operations.

## Running Shor's

### Prerequisites

Compiling the extracted code requires dune and zarith (`opam install dune zarith`). 

Our extracted code uses the [ddsim simulator](https://github.com/iic-jku/ddsim) (through its Qiskit interface) to execute Shor's order finding circuit so running our extracted code requires **Python version >= 3.6, qiskit, and ddsim**. Once you have a suitable version of Python, you can install the latter two with `pip install qiskit jkq.ddsim`. If you run into trouble with your Python environment, then consider using anaconda per [these directions for installing Qiskit](https://qiskit.org/documentation/getting_started.html). 

To test your Python setup, run `python run_circuit.py test.qasm`. You should see the output 7, which corresponds to measuring '111'. Our OCaml code runs this command with a generated order finding circuit as input. If you find that you need to run a different command on your system (e.g., `python3.9 ...`), then you can modify line 47 of [extraction/ml/Run.ml](extraction/ml/Run.ml).

### Extraction to OCaml

You can compile the Coq code and extracted OCaml code in the `extraction/` directory by running `make shor` in the top-level (`../..`) directory.

The code in the `extraction/` directory was generated using the `./extract.sh` script. You can re-generate and re-build the extracted code using this script. Note that it was last tested with Coq version 8.15.2. Other versions of Coq will likely require modifications.

If you are on MacOS, you may see the following warnings:
```
ld: warning: directory not found for option '-L/opt/local/lib'
```
This is caused by our use of zarith, and seems to be safe to ignore.

### Running Extracted Code

Once you have compiled our extracted code, you can run it in two ways:
* `dune exec --root extraction -- ./run_shor.exe -N N [--niters n]` runs our implementation of Shor's algorithm to try to factor the number `N` using the ddsim simulator in place of a quantum computer. The `--niters` argument can be used to specify a maximum number of iterations to try. The default is 1.
* `dune exec --root extraction -- ./run_shor.exe -N N --gen-circuit a` generates a quantum circuit (called `shor_N_a.qasm`) for finding the order of `a` mod `N`. In this case our code doesn't do any simulation, which is useful if you want to use a custom simulator configuration.

### Example

Shor's algorithm is nondeterministic, so you will get different outcomes on different runs. The generated quantum circuits can be quite large, which makes them slow to simulate. If you find that the script is hanging then try a smaller N.

Here is the output of a run of (at most) 10 iterations of Shor's factoring algorithm applied to 15 on a 2015 MacBook Pro:
```
$ dune exec --root extraction -- ./run_shor.exe -N 15 --niters 10
TODO: add check that N can be written as (p^k * q) for k>0, prime p>2, q>2, and coprime(p^k, q)
Running Shor's for N = 15
Random sampling selected a = 8
Simulating circuit, this will take a little while...
	Outcome of simulation is 16777216
	Time taken: 540.331051s
Random sampling selected a = 8
Simulating circuit, this will take a little while...
	Outcome of simulation is 8388608
	Time taken: 576.320279s
Random sampling selected a = 7
Simulating circuit, this will take a little while...
	Outcome of simulation is 17288921088
	Time taken: 603.270518s
Random sampling selected a = 13
Simulating circuit, this will take a little while...
	Outcome of simulation is 109051904
	Time taken: 630.073799s
Random sampling selected a = 8
Simulating circuit, this will take a little while...
	Outcome of simulation is 67108864
	Time taken: 529.853721s
Random sampling selected a = 2
Simulating circuit, this will take a little while...
	Outcome of simulation is 25836912640
	Time taken: 473.426677s
Non-trivial factor is 3.
```
This output says that the algorithm tried 6 iterations. In the 6th iteration, it used the output from the circuit generated with a=2 to find the factor 3. 

## Verified Properties

The following key lemmas are proved in Main.v:
* `end_to_end_shors_correct` says that for any N > 1, if `end_to_end_shors` returns `Some x` then x is a nontrivial factor of N.
* `end_to_end_shors_fails_with_low_probability` says that for any N that is not prime, not even, and not a prime power, the probability that `end_to_end_shors` returns `None` (meaning that it failed to find a factor) is no more than (1 - (1 / 2) * (κ / INR (Nat.log2 N)^4))^niter) where κ is the constant (4 * exp(-2) / (PI ^ 2)), which is about 0.055, and niter is the number of iterations in the algorithm. Thus, the success probability of `end_to_end_shors` is poly-log in N.

In our extracted code, these correctness properties come with a few caveats. See the [README in the extraction directory](extraction/README.md) for details.
