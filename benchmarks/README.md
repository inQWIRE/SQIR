# Benchmarks

This directory contains utilities for running SQIR program transformations on a set of benchmark programs used in the evaluation of two previous optimizers:
- Y. Nam, N.J. Ross, Y. Su, A.M. Childs, and D. Maslov. Automated optimization of large quantum circuits with continuous parameters. October 2017. Available from https://arxiv.org/abs/1710.07345.
- M. Amy, D. Maslov, and M. Mosca. Polynomial-time T-depth optimization of Clifford+T circuits via matroid partitioning. December 2013. Available from https://arxiv.org/abs/1303.2042.

We use the versions of the benchmarks available in the QFT_and_Adders directory of https://github.com/njross/optimizer.
We only consider the benchmarks in the QFT_and_Adders directory because the other benchmarks have z-rotations by arbitrary (float) angles, which we do not support.
We do not consider the results of optimizing gf2^E163_mult_before, gf2^E131_mult_before, or gf2^E128_mult_before because these programs are too large for our current implementation.
We could solve this problem by rewriting our transformation code to be tail recursive.
We also do not consider the results of optimizing mod_adder_1024 because the gate counts for this circuit are not reported in the Nam et al. paper.
The circuits were originally in the ASCII format of the Quipper language and we converted them to OpenQASM by using [PyZX](https://github.com/Quantomatic/pyzx)'s from_quipper_file function.

## Setup

To run SQIR optimizations:
- Build SQIR using the [compilation instructions](../README.md#compilation-instructions) in the top (`..`) directory.
- Run `extract.sh` to extract our SQIR transformations to OCaml.
This will produce the file `BenchmarkGates.ml` in the `qasm-translation/src` directory.

To run Qiskit transformations:
- Qiskit requires python 3. Once you have installed python 3, you can install Qiskit using pip (`pip install qiskit`).

## Instructions

To run SQIR transformations, use the function `run_on_nam_benchmarks` in qasm-translation/src/main.ml.
This function takes an output filename as input.  
It will print results to the screen, write results to the specified file, and write optimized versions of each benchmark with the suffix "_opt".
By default, it does not run on the two largest benchmarks (gf2^32 and gf2^64). 
To run on these benchmarks, directly call our `optimize` function.

Example:
```
cd qasm-translation
dune utop .
> Main.run_on_nam_benchmarks "../sqir_out.csv";;
```

To run Qiskit on the benchmarks, use the command `python3 run_qiskit.py f` where `f` is the output filename.
To combine the SQIR and Qiskit  output files into one master file, use the command `generate_nam_comparison.py <output filename> <qiskit output file> <SQIR output file>`.

