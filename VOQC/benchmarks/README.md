# Meauring VOQC Performance

## Benchmarks

We use a set of benchmark programs used in the evaluation of a previous optimizer by Nam et al.:
- Y. Nam, N. J. Ross, Y. Su, A. M. Childs, and D. Maslov. Automated optimization of large quantum circuits with continuous parameters. October 2017. Available from https://arxiv.org/abs/1710.07345.

We use the versions of the benchmarks in our Arithmetic_and_Toffoli, PF, and QFT_and_Adders directories.
These benchmarks were taken from the https://github.com/njross/optimizer and converted to OpenQASM using [PyZX](https://github.com/Quantomatic/pyzx)'s `from_quipper_file` function. 

We have made some modifications to the programs in Nam's directory. In particular, some programs in the QFT_and_Adders directory originally contained ancilla initialization and termination; PyZX removes these during conversion to OpenQASM. PyZX also converts z-axis rotation angles to the form 'x * pi' by rounding. For the PF benchmarks, we translate these rz gates to our rzq gates in the parser; for the QFT programs we have translated the rz gates to rzq gates in advance. Finally, the gf2^X family or circuits and csum_mux_9 have been lightly edited to remove additional H gates that caused inconsistencies in the original gate count.

For convenience, the file 'results.zip' contains the results of running VOQC, PyZX, Qiskit, and tket on the majority of benchmarks in the Arithmetic_and_Toffoli directory.

TODO:
* Parse full OpenQASM programs (including initialization/measurement) and optimize only the unitary portions.
* Improve accuracy of translation of PF benchmarks. In particular, we should use the exact rational angle rather than rounding from floats.

## Running VOQC

In the top (`../..`) directory, run `make voqc`. This will compile the OCaml code we have extracted from the verified Coq code. If you have modified the Coq code, then be sure to run `make optimizer` first. To run the optimizer, run `dune exec --root ../extraction -- ./voqc.exe -i <prog> -o <out>`, which will optimize program prog and write the optimized result to out. It will print the initial and final gate counts. `--root ../extraction` is needed because the voqc executable is built in the ../extraction directory. We also support a command line option `-n <N>` that specifies a number of iterations to consider in the resource count.

To run VOQC on all the benchmarks run `./run_voqc.sh`. This will take several hours and will create the files Arithmetic_and_Toffoli_results.csv, PF_results.csv and QFT_and_Adders.csv.

## Other Optimizers

In our paper, we compare VOQC's performance to existing unverified compilers. We used the scripts in this directory to generate our data. If you are familiar with these compilers and see a problem with how we are running them, please let us know! (Contact <kesha@cs.umd.edu>.)

All of these scripts print gate count data to the console and write to a CSV file. A prerequisite for running these compilers is having Python 3 installed.

### PyZX

To install PyZX from source, clone PyZX's [github repository](https://github.com/Quantomatic/pyzx) and run `pip install -e .`. To run PyZX on the benchmarks, use the run_pyzx.py script. Note that you will need to run this from where PyZX was installed.

### Qiskit

To install Qiskit using pip, run `pip install qiskit`. To run Qiskit on the benchmarks, use the command `python3 run_qiskit.py f` where `f` is the output filename.

### tket

To install t|ket> using pip, run `pip install pytket`. To run tket on the benchmarks, use the command `python3 run_tket.py f` where `f` is the output filename.

