# Meauring VOQC Performance

## Benchmarks

The benchmarks we use are in the [VOQC-benchmarks repository](https://github.com/inQWIRE/VOQC-benchmarks), added here as a submodule. For convenience, the file 'results.zip' contains the results of running VOQC, PyZX, Qiskit, and tket on all but the largest benchmarks in VOQC-benchmarks/Arithmetic_and_Toffoli.

## Running VOQC

In the top (`../..`) directory, run `make voqc`. This will compile the OCaml code we have extracted from the verified Coq code. If you have modified the Coq code, then be sure to run `make optimizer` first. To run the optimizer, run `dune exec --root .. -- ./voqc.exe -i <prog> -o <out>`, which will optimize program prog and write the optimized result to out. It will print the initial and final gate counts. `--root ..` is needed because the voqc executable is built in the parent directory. We also support a command line option `-n <N>` that specifies a number of iterations to consider in the resource count and an option '-l' that indicates whether to use a "light" version of the optimizer that excludes rotation merging.

To generate the data in our paper (which runs a variety of optimizers on a subset of the full benchmark suite) use the `run_bench.sh` script. It requires PyZX, Qiskit, and tket to be appropriately installed (see below).

To run the full version of VOQC on *all* the benchmarks run `./run_voqc.sh`. Some of the benchmarks are quite large, so this will take a while (~48 hours on a Macbook Pro running macOS Catalina with OCaml 4.10.0). This script creates files Arithmetic_and_Toffoli_results.csv, PF_results.csv, and QFT_and_Adders.csv to summarize results.

## Other Optimizers

In our paper, we compare VOQC's performance to existing unverified compilers. We used the scripts in this directory to generate our data. If you are familiar with these compilers and see a problem with how we are running them, please let us know! (Contact <kesha@cs.umd.edu>.)

All of these scripts print gate count data to the console and write to a CSV file. A prerequisite for running these compilers is having Python 3 installed.

### PyZX

To install PyZX from source, clone PyZX's [github repository](https://github.com/Quantomatic/pyzx) and run `pip install -e .`. To run PyZX on the benchmarks, use the run_pyzx.py script. Note that you will need to run this from where PyZX was installed.

### Qiskit

To install Qiskit using pip, run `pip install qiskit`. To run Qiskit on the benchmarks, use the command `python3 run_qiskit.py f` where `f` is the output filename.

### tket

To install t|ket> using pip, run `pip install pytket`. To run tket on the benchmarks, use the command `python3 run_tket.py f` where `f` is the output filename.

