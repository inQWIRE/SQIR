# Meauring VOQC Performance

## Benchmarks

We use a set of benchmark programs used in the evaluation of a previous optimizer:
- Y. Nam, N.J. Ross, Y. Su, A.M. Childs, and D. Maslov. Automated optimization of large quantum circuits with continuous parameters. October 2017. Available from https://arxiv.org/abs/1710.07345.

We use the versions of the benchmarks in the Arithmetic_and_Toffoli, PF, and QFT_and_Adders directories.
These benchmarks were taken from the https://github.com/njross/optimizer and converted to OpenQASM using [PyZX](https://github.com/Quantomatic/pyzx)'s `from_quipper_file` function.
Currently, VOQC cannot handle the programs in the Large directory; these programs cause a stack overflow.
We can (and will) solve this problem by rewriting our optimization code to be tail recursive.

We have made some modifications to the programs in Nam's directory.
Programs in the QFT_and_Adders directory originally contained ancilla initialization and termination.
Angles were changed to X * PI
The gf2^X family or circuits and csum_mux_9 have been lightly edited to remove additional H gates that cause inconsistencies in the original gate count.

*The problem with floating point numbers*

For now, we translate from Nam's benchmarks by rouding to the nearest multiple of PI/2^15 using the Python script formatqasm.py (usage: `python formatqasm <input file> <output filename>`).

TODO (in progress):
* Parse full OpenQASM programs (including initialization/measurement) and optimize only the unitary portions.
* Improve accuracy of translation from original Nam benchmarks. In particular, we should reproduce their benchmarks using the exact angle rather than rounding from pre-generated programs.
* Performance improvements to VOQC (use tail recursion, extract to more efficient OCaml, etc.) so that we can run on benchmarks in the Large directory.

## Running VOQC

In the top (`../..`) directory, run `make voqc`. This will compile the OCaml code we have extracted from the verified Coq code. If you have modified the Coq code, then be sure to run `make optimizer` first. To run the optimizer, run `dune exec ./voqc.exe <prog> <out> --root ../extraction`, which will optimize program prog and write the optimized result to out. It will print the initial and final gate counts. `--root ../extraction` is needed because the voqc executable is built in the ../extraction directory.

*Example*: The following runs VOQC on the tof_3 benchmark and writes the result to out.qasm.
```
$ dune exec ./voqc.exe Arithmetic_and_Toffoli/tof_3.qasm out.qasm --root ../extraction
Original gates: 45 (T count: 21)
Optimized gates: 40 (T count: 15)
```

To run VOQC on all the benchmarks in the Arithmetic_and_Toffoli directory (excluding the slowest, gf2^64) run `./run_voqc.sh`.

## Other Optimizers

In our paper, we compare VOQC's performance to existing unverified compilers. We used the scripts in this directory to generate our data. If you are familiar with these compilers and see a problem with how we are running them, please let us know! (Contact <kesha@cs.umd.edu>.)

All of these scripts print gate count data to the console and write to a CSV file. A prerequisite for running these compilers is having Python 3 installed.

### PyZX

To install PyZX from source, clone PyZX's [github repository](https://github.com/Quantomatic/pyzx) and run `pip install -e .`. To run PyZX on the benchmarks, use the run_pyzx.py script. Note that you will need to run this from where PyZX was installed.

### Qiskit

To install Qiskit using pip, run `pip install qiskit`. To run Qiskit on the benchmarks, use the command `python3 run_qiskit.py f` where `f` is the output filename.

### tket

To install t|ket> using pip, run `pip install pytket`. To run tket on the benchmarks, use the command `python3 run_tket.py f` where `f` is the output filename.

