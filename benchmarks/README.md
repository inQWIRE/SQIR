# Benchmarks

Utilities for running SQIRE program transformations on benchmark programs. We currently have two sets of benchmarks available: one used in the evaluation of previous optimizers and one that is randomly generated.

TODO: Add smaller benchmarks that can be run on current machines (e.g. the ones used in https://mrmgroup.cs.princeton.edu/papers/triq_ISCA2019.pdf).

## Setup

To run SQIRE transformations:
- Build SQIRE using the [compilation instructions](../README.md#compilation-instructions) in the top (`..`) directory.
- Run `extract.sh` to extract our SQIRE transformations to OCaml.
This will produce the file `BenchmarkGates.ml` in the `qasm-translation/src` directory.

To run Qiskit transformations:
- Qiskit requires python 3. Once you have installed python 3, you can install Qiskit using pip (`pip install qiskit`).

## Nam et al. Benchmarks

Our first set of benchmarks were used to evaluate the optimizers in the following two papers:

- Y. Nam, N.J. Ross, Y. Su, A.M. Childs, and D. Maslov. Automated optimization of large quantum circuits with continuous parameters. October 2017. Available from https://arxiv.org/abs/1710.07345.
- M. Amy, D. Maslov, and M. Mosca. Polynomial-time T-depth optimization of Clifford+T circuits via matroid partitioning. December 2013. Available from https://arxiv.org/abs/1303.2042.

We use the versions of the benchmarks available in the QFT_and_Adders directory of https://github.com/njross/optimizer.
We only consider the benchmarks in the QFT_and_Adders directory because the other benchmarks have z-rotations by arbitrary (float) angles, which we do not support.
We do not consider the results of optimizing gf2^E163_mult_before, gf2^E131_mult_before, or gf2^E128_mult_before because these programs are too large for our current implementation.
We could solve this problem by rewriting our transformation code to be tail recursive.
We also do not consider the results of optimizing mod_adder_1024 because the gate counts for this circuit are not reported in the Nam et al. paper.
The circuits were originally in the ASCII format of the Quipper language and we converted them to OpenQASM by first translating into SQIRE and then to OpenQASM (see the `qasm` branch of our development).

To characterize the performance of optimization passes on the Nam et al. benchmarks, we record the total number of gates after optimization.
To run SQIRE transformations , use the function `run_on_nam_benchmarks` in qasm-translation/src/main.ml.
This function takes an output filename as input.
To run Qiskit on the random benchmarks, use the command `python3 run_qiskit.py -name f` where `f` is the output filename.
To combine the two output files into one master file, use the command `generate_nam_comparison.py <output filename> <qiskit output file> <nam output file>`.

Example:
```
# begin in the benchmarks directory
python3 run_qiskit.py -nam qiskit_out.csv
cd qasm-translation
dune utop .
> Main.run_on_nam_benchmarks "../sqire_out.csv";;
cd ..
./generate_nam_comparison.py out.csv qiskit_out.csv sqire_out.csv
```

The final csv file, which can be imported into Excel, is `out.csv`.

## Random Benchmarks

The command `./generate_random_programs.py dir N Q G` will generate N programs with Q qubits and G gates in the `dir` directory. Gates are selected randomly from the set {H, X, Z, T, TDAG, P, PDAG, CNOT} and gate arguments are chosen randomly from the set of valid indices. For randomness we use Python's `randint` function.

To characterize the performance of optimization passes on the random benchmarks, we record the percentage reduction in number of H, X, CNOT, and z-rotation gates.
To run SQIRE transformations on the produced programs, use the function `run_on_random_benchmarks` in qasm-translation/src/main.ml.
This function takes random benchmark directory as input.
To run Qiskit on the random benchmarks, use the command `python3 run_qiskit.py -rand dir` where `dir` is the random benchmark directory.

Example:
```
# begin in the benchmarks directory
./generate_random_programs.py random-benchmarks 20 15 1000
python3 run_qiskit.py -rand random-benchmarks
cd qasm-translation
dune utop .
> Main.run_on_random_benchmarks "../random-benchmarks";;
```
