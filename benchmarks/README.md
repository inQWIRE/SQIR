# Meauring VOQC Performance

## Benchmarks

We use a set of benchmark programs used in the evaluation of two previous optimizers:
- M. Amy, D. Maslov, and M. Mosca. Polynomial-time T-depth optimization of Clifford+T circuits via matroid partitioning. December 2013. Available from https://arxiv.org/abs/1303.2042.
- Y. Nam, N.J. Ross, Y. Su, A.M. Childs, and D. Maslov. Automated optimization of large quantum circuits with continuous parameters. October 2017. Available from https://arxiv.org/abs/1710.07345.

We use the versions of the benchmarks in the nam_benchmarks sub-directory.
These benchmarks were taken from the QFT_and_Adders directory of https://github.com/njross/optimizer and converted to OpenQASM using [PyZX](https://github.com/Quantomatic/pyzx)'s from_quipper_file function.
We only consider the benchmarks in the QFT_and_Adders directory because the other benchmarks have z-rotations by arbitrary (float) angles, which we do not support.
We do not consider the results of optimizing gf2^E163_mult_before, gf2^E131_mult_before, or gf2^E128_mult_before because these programs are too large for our current implementation.
We could solve this problem by rewriting our optimization code to be tail recursive.
We also do not consider the results of optimizing mod_adder_1024 because the gate counts for this circuit are not reported in the Nam et al. paper.

## Running VOQC

First, run `make voqc` in the top (`..`) directory. This will create an executable `voqc` in the current directory. `voqc <prog> <N> <out>` will optimize program prog, which has N qubits, and write the optimized result to out. It will print the initial and final gate counts.

To run VOQC on all the benchmarks (excluding the slowest, gf2^64) run `./run_on_benchmarks.sh`.

## Other Optimizers

We are also interested in comparing VOQC's performance to existing unverified compilers.

(In progress...)

### Qiskit

Qiskit requires python 3. Once you have installed python 3, you can install Qiskit using pip (`pip install qiskit`).
To run Qiskit on the benchmarks, use the command `python3 run_qiskit.py f` where `f` is the output filename.

### quilc

### PyZX

### tket


