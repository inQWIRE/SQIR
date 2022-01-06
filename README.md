# SQIR

![Logo](logo.png)

SQIR is a **S**mall **Q**uantum **I**ntermediate **R**epresentation for quantum programs. Its intended use is as an intermediate representation in a **V**erified **O**ptimizer for **Q**uantum **C**ircuits (VOQC), but we have also used it to implement verified versions of several quanutm algorithms.

We describe SQIR and its use in VOQC in our paper [A Verified Optimizer for Quantum Circuits](https://arxiv.org/abs/1912.02250), presented at POPL 2021. We describe the details of verifying SQIR programs in our paper [Proving Quantum Programs Correct](https://arxiv.org/abs/2010.01240), presented at ITP 2021. The code corresponding to both papers can be found in the [POPL2021 branch](https://github.com/inQWIRE/SQIR/tree/POPL2021) of this respository. Preliminary versions of this work were presented at QPL 2019 and PLanQC 2020, and follow-on work was presented at PLanQC 2021.

This repository contains our Coq formalization of SQIR and VOQC as well as several verified quantum algorithms. If you are interested in *running the VOQC compiler*, then you should look at our OCaml library ([inQWIRE/mlvoqc](https://github.com/inQWIRE/mlvoqc)) or Python library ([inQWIRE/pyvoqc](https://github.com/inQWIRE/pyvoqc)) instead. The OCaml library is extracted from our Coq definitions and the Python library is a wrapper around the OCaml library.

If you are interested in learning more about formal verification of quantum programs in general, we recommend Robert Rand's [Verified Quantum Computing tutorial](http://www.cs.umd.edu/~rrand/vqc/index.html).

## Table of Contents

- [SQIR](#sqir)
  - [Table of Contents](#table-of-contents)
  - [Setup](#setup)
  - [Compilation](#compilation)
  - [Directory Contents](#directory-contents)
    - [SQIR](#sqir-1)
    - [VOQC](#voqc)
    - [examples](#examples)
  - [Acknowledgements](#acknowledgements)
  - [Citations](#citations)

## Setup

To compile SQIR and VOQC, you will need [Coq](https://coq.inria.fr/) and the [Coq Interval package](http://coq-interval.gforge.inria.fr/). We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.12-8.14**. If you run into errors when compiling our proofs, first check your version of Coq (`coqc -v`).

Assuming you have opam installed (following the instructions in the link above), follow the steps below to set up your environment.
```
# environment setup
opam init
eval $(opam env)

# install some version of the OCaml compiler in a switch named "voqc"
opam switch create voqc 4.12.0
eval $(opam env)

# install Coq -- this will take a while!
opam install coq

# install Interval package (optional, needed to compile proofs in examples/shor)
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-interval
```

**TODO: add notes about installing QuantumLib**

*Notes*:
* Depending on your system, you may need to replace 4.12.0 in the instructions above with something like "ocaml-base-compiler.4.12.0". Any recent version of OCaml should be fine.
* We require Coq version >= 8.12. We have tested compilation with 8.12, 8.13, and 8.14.
* opam error messages and warnings are typically informative, so if you run into trouble then make sure you read the console output.

## Compilation

Run `make` to compile the core files of SQIR, `make voqc` to compile proofs about VOQC, `make examples` to compile proofs of correctness for example quantum algorithms (excluding those in examples/shor), and `make shor` to compile proofs about Shor's algorithm. Use `make all` to compile everything. 

Our proofs are resource intensive so expect `make all` to take a little while. If you have cores to spare, then you can speed things up by compiling with the `-j` flag (e.g. `make all -j8`). On a 2015 dual-core MacBook Pro running Coq version 8.14.0 compilation takes around 30 minutes.

## Directory Contents

### SQIR

Definition of the SQIR language.

- DensitySem.v : Density matrix semantics for general SQIR programs.
- Equivalences.v : Verified circuit equivalences for peephole optimizations.
- NDSem.v : Non-deterministic semantics for general SQIR programs.
- Run.v : 'run' function to describe running a quantum circuit and sampling from the output distribution.
- SQIR.v : Definition of the SQIR language (see 'ucom' and 'com').
- UnitaryOps.v : Utilities for manipulating unitary SQIR programs (e.g. 'invert', 'control').
- UnitarySem.v : Semantics for unitary SQIR programs.

We also rely on several files from the [QuantumLib](https://github.com/inQWIRE/QuantumLib) development, which we have linked as a git submodule in the externals directory.

### VOQC

Verified transformations of SQIR programs. The optimizations and mapping routines extracted to our OCaml library ([inQWIRE/mlvoqc](https://github.com/inQWIRE/mlvoqc)) are all listed in **Main.v**. So this file is a good starting point for getting familiar with VOQC.

The rest of the files in the VOQC directory can be split into the following categories:

- Utilities
  - GateSet.v : Coq module for describing a quantum gate set.
  - IBMGateSet.v : "IBM" gate set {U1, U2, U3, CX}.
  - NonUnitaryListRepresentation.v : List representation of non-unitary SQIR programs.
  - RzQGateSet.v : "RzQ" gate set {H, X, Rzq, CX}.
  - StandardGateSet.v : Full gate set {I, X, Y, Z, H, S, T, Sdg, Tdg, Rx, Ry, Rz, Rzq, U1, U2, U3, CX, CZ, SWAP, CCX, CCZ}.
  - UnitaryListRepresentation.v : List representation of unitary SQIR programs; includes utilities for manipulating program lists and gate set-independent proofs.

- Optimizations over unitary programs, inspired by those in [Qiskit](https://github.com/Qiskit/qiskit-terra) and [Nam et al. [2018]](https://www.nature.com/articles/s41534-018-0072-4)
  - ChangeRotationBasis.v : Auxiliary proof for Optimize1qGates.
  - CXCancellation.v : [CXCancellation](https://qiskit.org/documentation/stubs/qiskit.transpiler.passes.CXCancellation.html) from Qiskit.
  - GateCancellation.v : "Single-qubit gate cancellation" and "two-qubit gate cancellation" from Nam et al.
  - HadamardReduction.v : "Hadamard reduction" from Nam et al.
  - NotPropagation.v : "Not propagation" from Nam et al.
  - Optimize1qGates.v : [Optimize1qGates](https://qiskit.org/documentation/stubs/qiskit.transpiler.passes.Optimize1qGates.html) from Qiskit.
  - RotationMerging.v : "Rotation merging using phase polynomials" from Nam et al.

- Optimizations over non-unitary programs
  - PropagateClassical.v : Track classical states to remove redundant measurements and CNOT operations.
  - RemoveZRotationBeforeMeasure.v : Remove single-qubit z-axis rotations before measurement operations.

- Mapping routines
  - ConnectivityGraph.v : Utilities for describing an architecture connectivity graph. Includes graphs for linear nearest neighbor, 2D grid, and IBM Tenerife architectures.
  - Layouts.v : Utilities for describing a physical <-> logical qubit mapping.
  - MappingConstraints.v : Utilities for describing a program that satisfies architecture constraints.
  - SimpleMapping.v: Simple mapping for an architecture described by a directed graph.

- Experimental extensions
  - BooleanCompilation.v : Compilation from boolean expressions to unitary SQIR programs.

### examples

Examples of verifying correctness properties of quantum algorithms.

- Deutsch.v : Deutsch algorithm
- DeutschJozsa.v : Deutsch-Jozsa algorithm
- GHZ.v : GHZ state preparation
- Grover.v : Grover's algorithm
- QPE.v : Simplified quantum phase estimation
- shor/ : Shor's algorithm, including general quantum phase estimation (use `make shor` to compile separately, see the [README](examples/shor/README.md) in the shor directory for more details)
- Simon.v : Simon's algorithm
- Superdense.v : Superdense coding
- Teleport.v : Quantum teleportation
- Utilities.v : Miscellaneous utilities used in multiple examples
- Wiesner.v : Wiesner's [quantum money](https://en.wikipedia.org/wiki/Quantum_money), contributed by Adrian Lehmann

## Acknowledgements

This project is the result of the efforts of many people:
* Akshaj Gaur
* Aaron Green
* Kesha Hietala
* Shih-Han Hung
* Adrian Lehmann
* Liyi Li
* Yuxiang Peng
* Robert Rand
* Kartik Singhal
* Runzhou Tao
* Finn Voichick

Maintainer(s):
* Kesha Hietala (@khieta)
* Robert Rand (@rnrand)

This project is supported by the U.S. Department of Energy, Office of Science, Office of Advanced Scientific Computing Research, Quantum Testbed Pathfinder Program under Award Number DE-SC0019040 and the Air Force Office of Scientific Research under Grant Number FA95502110051.

## Citations

If you use SQIR or VOQC in your work, please cite our papers.

```
@inproceedings{hietala2021verified,
  author    = {Kesha Hietala and Robert Rand and Shih{-}Han Hung and Xiaodi Wu and Michael Hicks},
  title     = {A verified optimizer for Quantum circuits},
  journal   = {Proceedings of the {ACM} on Programming Languages},
  volume    = {5},
  number    = {{POPL}},
  pages     = {1--29},
  year      = {2021},
  url       = {https://doi.org/10.1145/3434318},
  doi       = {10.1145/3434318},
  timestamp = {Wed, 17 Feb 2021 08:54:02 +0100}
}
```

```
@article{hietala2020proving,
 author    = {Hietala, Kesha and Rand, Robert and Hung, Shih-Han and Li, Liyi and Hicks, Michael},
 booktitle = {12th International Conference on Interactive Theorem Proving (ITP 2021)},
 doi       = {10.4230/LIPIcs.ITP.2021.21},
 editor    = {Cohen, Liron and Kaliszyk, Cezary},
 isbn      = {978-3-95977-188-7},
 issn      = {1868-8969},
 pages     = {21:1--21:19},
 publisher = {Schloss Dagstuhl -- Leibniz-Zentrum für Informatik},
 series    = {Leibniz International Proceedings in Informatics (LIPIcs)},
 title     = {Proving Quantum Programs Correct},
 url       = {https://drops.dagstuhl.de/opus/volltexte/2021/13916},
 urn       = {urn:nbn:de:0030-drops-139160},
 volume    = {193},
 year      = {2021}
}
```

Alternatively, you can cite our repository using the information in [CITATION.cff](CITATION.cff).