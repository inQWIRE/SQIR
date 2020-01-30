# Meauring VOQC Performance

## Benchmarks

We use a set of benchmark programs used in the evaluation of two previous optimizers:
- M. Amy, D. Maslov, and M. Mosca. Polynomial-time T-depth optimization of Clifford+T circuits via matroid partitioning. December 2013. Available from https://arxiv.org/abs/1303.2042.
- Y. Nam, N.J. Ross, Y. Su, A.M. Childs, and D. Maslov. Automated optimization of large quantum circuits with continuous parameters. October 2017. Available from https://arxiv.org/abs/1710.07345.

We use the versions of the benchmarks in the nam_benchmarks sub-directory.
These benchmarks were taken from the QFT_and_Adders directory of https://github.com/njross/optimizer and converted to OpenQASM using [PyZX](https://github.com/Quantomatic/pyzx)'s from_quipper_file function.
We only consider the benchmarks in the QFT_and_Adders directory because the other benchmarks have z-rotations by arbitrary (float) angles, which we do not currently support.
We do not consider the results of optimizing gf2^E163_mult_before, gf2^E131_mult_before, or gf2^E128_mult_before because these programs are too large for our current implementation.
We could solve this problem by rewriting our optimization code to be tail recursive.
We also do not consider the results of optimizing mod_adder_1024 because the gate counts for this circuit are not reported in the Nam et al. paper.

## Running VOQC

In the top (`..`) directory, run `make voqc`. This will compile the OCaml code we have extracted from the verified Coq code. If you have modified the Coq code, then be sure to run `make optimizer` first. To run the optimizer, run `dune exec ./voqc.exe <prog> <out> --root ../VOQC`, which will optimize program prog and write the optimized result to out. It will print the initial and final gate counts. `--root ../VOQC` is needed because the voqc executable is built in the ../VOQC directory.

*Example*: The following runs VOQC on the tof_3 benchmark and writes the result to out.qasm.
```
$ dune exec ./voqc.exe nam-benchmarks/tof_3.qasm out.qasm --root ../extraction
Original gates: 45 (T count: 21)
Optimized gates: 40 (T count: 15)
```

To run VOQC on all the benchmarks (excluding the slowest, gf2^64) run `./run_voqc.sh`.

## Other Optimizers

In our paper, we compare VOQC's performance to existing unverified compilers. We used the scripts in this directory to generate our data. If you are familiar with these compilers and see a problem with how we are running them, please let us know! (Contact <kesha@cs.umd.edu>.)

All of these scripts print gate count data to the console and write to a CSV file. A prerequisite for running these compilers is having Python 3 installed.

### PyZX

To install PyZX from source, clone PyZX's [github repository](https://github.com/Quantomatic/pyzx) and run `pip install -e .`. To run PyZX on the benchmarks, use the run_pyzx.py script. Note that you will need to run this from where PyZX was installed.

### Qiskit

To install Qiskit using pip, run `pip install qiskit`. To run Qiskit on the benchmarks, use the command `python3 run_qiskit.py f` where `f` is the output filename.

### tket

To install t|ket> using pip, run `pip install pytket`. To run tket on the benchmarks, use the command `python3 run_tket.py f` where `f` is the output filename.

