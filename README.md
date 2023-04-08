# SQIR & VOQC

<img align="right" src="logo.png">

SQIR is a **S**mall **Q**uantum **I**ntermediate **R**epresentation for quantum programs. Its intended use is as an intermediate representation in a **V**erified **O**ptimizer for **Q**uantum **C**ircuits (VOQC), but we have also used it to implement verified versions of several quantum algorithms.

We first presented SQIR and its use in VOQC in our paper [A Verified Optimizer for Quantum Circuits](https://arxiv.org/abs/1912.02250) at POPL 2021. 
We provide additional details of verifying SQIR programs (including QPE and Grover's) in our paper [Proving Quantum Programs Correct](https://arxiv.org/abs/2010.01240), presented at ITP 2021. 
We describe a SQIR formalization of Shor's factoring algorithm in our draft [A Formally Certified End-to-End Implementation of Shor's Factorization Algorithm](https://arxiv.org/abs/2204.07112).

This repository contains our Coq formalization of SQIR and VOQC as well as several verified quantum algorithms. If you are interested in running the VOQC compiler, then you should look at our OCaml library ([inQWIRE/mlvoqc](https://github.com/inQWIRE/mlvoqc)) or Python library ([inQWIRE/pyvoqc](https://github.com/inQWIRE/pyvoqc)) instead. The OCaml library is extracted from our Coq definitions and the Python library is a wrapper around the OCaml library.

If you are interested in learning more about formal verification of quantum programs in general, we recommend Robert Rand's [Verified Quantum Computing tutorial](http://www.cs.umd.edu/~rrand/vqc/index.html).

## Table of Contents

- [SQIR \& VOQC](#sqir--voqc)
  - [Table of Contents](#table-of-contents)
  - [Setup](#setup)
  - [Compilation](#compilation)
  - [Using With Other Projects](#using-with-other-projects)
  - [Directory Contents](#directory-contents)
    - [SQIR](#sqir)
    - [VOQC](#voqc)
    - [examples](#examples)
  - [Acknowledgements](#acknowledgements)
  - [Citations](#citations)

## Setup

To compile SQIR and VOQC, you will need [Coq](https://coq.inria.fr/) and [QuantumLib](https://github.com/inQWIRE/QuantumLib) (version 1.1.0). In order to build the Shor proof, you will also need the [Coq Interval package](http://coq-interval.gforge.inria.fr/) and the [coq-euler](https://github.com/taorunz/euler) library. We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.12-8.16**. If you run into errors when compiling our proofs, first check your version of Coq (`coqc -v`).

Assuming you have opam installed (following the instructions in the link above), follow the steps below to set up your environment.
```
# environment setup
opam init
eval $(opam env)

# install some version of the OCaml compiler in a switch named "voqc"
opam switch create voqc 4.13.1
eval $(opam env)

# install Coq -- this will take a while!
opam install coq

# install the QuantumLib library
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-quantumlib.1.1.0

# Optional, if you want to compile the proofs in examples/shor
opam install coq-interval
opam pin coq-euler https://github.com/taorunz/euler.git
```

*Notes*:
* Depending on your system, you may need to replace 4.13.1 in the instructions above with something like "ocaml-base-compiler.4.13.1". Any recent version of OCaml should be fine.
* We require Coq version >= 8.12.
* opam error messages and warnings are typically informative, so if you run into trouble then make sure you read the console output.

## Compilation

After following the setup directions above, you can run `make` to compile the core files of SQIR, `make voqc` to compile proofs about VOQC, `make examples` to compile proofs of correctness for quantum algorithms (excluding those in examples/shor), and `make shor` to compile proofs about Shor's algorithm. Use `make all` to compile everything. 

Our proofs are resource intensive so expect `make all` to take a little while. If you have cores to spare, then you can speed things up by compiling with the `-j` flag (e.g., `make all -j8`). On a 2015 dual-core MacBook Pro running Coq version 8.15.2, compilation takes around 30 minutes.

## Using With Other Projects

To install SQIR, run 
```opam pin coq-sqir htts://github.com/inQWIRE/SQIR.git```

To pull subsequent updates, run `opam install coq-sqir`. 

To import SQIR files, use 
```Require Import SQIR.FILENAME```

## Directory Contents

### SQIR

Definition of the SQIR language.

- DensitySem.v : Density matrix semantics for general SQIR programs.
- Equivalences.v : Verified circuit equivalences for peephole optimizations.
- ExtractionGateSet.v : Expanded gate set used for extraction.
- GateDecompositions.v : Verified optimized decompositions for CH, CU1, CU2, CU3, CCU1, CSWAP, C3X, and C4X.
- NDSem.v : Non-deterministic semantics for general SQIR programs.
- DiscreteProb.v : Utilities to describe running a quantum program and sampling from the output probability distribution.
- SQIR.v : Definition of the SQIR language.
- UnitaryOps.v : Utilities for manipulating unitary SQIR programs.
- UnitarySem.v : Semantics for unitary SQIR programs.

### VOQC

Verified transformations of SQIR programs. The optimizations and mapping routines extracted to our OCaml library ([inQWIRE/mlvoqc](https://github.com/inQWIRE/mlvoqc)) are all listed in **Main.v**. So this file is a good starting point for getting familiar with VOQC.

The rest of the files in the VOQC directory can be split into the following categories:

- Utilities
  - GateSet.v : Coq module for describing a quantum gate set.
  - IBMGateSet.v : "IBM" gate set {U1, U2, U3, CX}.
  - NonUnitaryListRepresentation.v : List representation of non-unitary SQIR programs.
  - RzQGateSet.v : "RzQ" gate set {H, X, Rzq, CX}.
  - FullGateSet.v : Full gate set {I, X, Y, Z, H, S, T, Sdg, Tdg, Rx, Ry, Rz, Rzq, U1, U2, U3, CX, CZ, SWAP, CCX, CCZ}.
  - UnitaryListRepresentation.v : List representation of unitary SQIR programs; includes utilities for manipulating program lists and gate set-independent proofs.

- Optimizations over unitary programs, inspired by those in [Qiskit](https://github.com/Qiskit/qiskit-terra) and [Nam et al. [2018]](https://www.nature.com/articles/s41534-018-0072-4)
  - ChangeRotationBasis.v : Auxiliary proof for Optimize1qGates.
  - GateCancellation.v : "Single-qubit gate cancellation" and "two-qubit gate cancellation" from Nam et al.
  - HadamardReduction.v : "Hadamard reduction" from Nam et al.
  - NotPropagation.v : "Not propagation" from Nam et al.
  - Optimize1qGates.v : [Optimize1qGates](https://qiskit.org/documentation/stubs/qiskit.transpiler.passes.Optimize1qGates.html) from Qiskit.
  - RotationMerging.v : "Rotation merging using phase polynomials" from Nam et al.

- Optimizations over non-unitary programs
  - PropagateClassical.v : Track classical states to remove redundant measurements and CNOT operations.
  - RemoveZRotationBeforeMeasure.v : Remove single-qubit z-axis rotations before measurement.

- Mapping routines
  - ConnectivityGraph.v : Utilities for describing an architecture connectivity graph. Includes graphs for linear nearest neighbor and 2D grid architectures.
  - GreedyLayout.v : Generate a layout based on the input program and architecture.
  - Layouts.v : Utilities for describing a physical <-> logical qubit mapping (i.e., layout).
  - MappingConstraints.v : Utilities for describing a program that satisfies architecture constraints.
  - MappingGateSet.v : Mapping gate set U + {CX, SWAP}, where U is an arbitrary set of single-qubit gates.
  - MappingValidation.v : Check whether two programs (which differ only in SWAP placement) are equivalent.
  - SwapRoute.v: Simple mapping for an architecture described by a directed graph.

- Experimental extensions
  - BooleanCompilation.v : Compilation from boolean expressions to unitary SQIR programs.

### examples

Examples of verifying correctness properties of quantum algorithms.

- Deutsch.v : Deutsch algorithm
- DeutschJozsa.v : Deutsch-Jozsa algorithm
- ghz/ : GHZ state preparation
- Grover.v : Grover's algorithm
- QPE.v : Simplified quantum phase estimation
- shor/ : Shor's algorithm, including general quantum phase estimation (use `make shor` to compile separately, see the [README in the shor directory](examples/shor/README.md) for more details)
- Simon.v : Simon's algorithm
- Superdense.v : Superdense coding
- Teleport.v : Quantum teleportation
- Utilities.v : Miscellaneous utilities used in multiple examples
- Wiesner.v : Wiesner's [quantum money](https://en.wikipedia.org/wiki/Quantum_money), contributed by Adrian Lehmann

## Acknowledgements

This project is the result of the efforts of many people. The primary contacts for this project are Kesha Hietala (@khieta) and Robert Rand (@rnrand). Other contributors include:
* Le Chang
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

This project is supported by the U.S. Department of Energy, Office of Science, Office of Advanced Scientific Computing Research, Quantum Testbed Pathfinder Program under Award Number DE-SC0019040 and the Air Force Office of Scientific Research under Grant Number FA95502110051.

## Citations

If you use SQIR or VOQC in your work, please cite our papers.

```
@article{hietala2021verified,
  title         = {A Verified Optimizer for {{Quantum}} Circuits},
  author        = {Hietala, Kesha and Rand, Robert and Hung, Shih-Han and Wu, Xiaodi and Hicks, Michael},
  year          = {2021},
  month         = jan,
  journal       = {Proceedings of the ACM on Programming Languages},
  volume        = {5},
  number        = {POPL},
  eid           = {37},
  pages         = {37},
  numpages      = {29},
  doi           = {10.1145/3434318},
  archiveprefix = {arXiv},
  eprint        = {1912.02250},
  url           = {https://github.com/inQWIRE/SQIR},
  abstract      = {We present VOQC, the first fully verified optimizer for quantum circuits, written using the Coq proof assistant. Quantum circuits are expressed as programs in a simple, low-level language called SQIR, a simple quantum intermediate representation, which is deeply embedded in Coq. Optimizations and other transformations are expressed as Coq functions, which are proved correct with respect to a semantics of SQIR programs. SQIR uses a semantics of matrices of complex numbers, which is the standard for quantum computation, but treats matrices symbolically in order to reason about programs that use an arbitrary number of quantum bits. SQIR's careful design and our provided automation make it possible to write and verify a broad range of optimizations in VOQC, including full-circuit transformations from cutting-edge optimizers.},
  keywords      = {programming languages, formal verification, certified compilation, quantum computing, circuit optimization},
  note          = {POPL '21}
}
```

```
@inproceedings{hietala2020proving,
  title     = {{Proving Quantum Programs Correct}},
  author    = {Hietala, Kesha and Rand, Robert and Hung, Shih-Han and Li, Liyi and Hicks, Michael},
  year      = {2021},
  month     = jun,
  booktitle = {12th International Conference on Interactive Theorem Proving (ITP 2021)},
  editor    = {Cohen, Liron and Kaliszyk, Cezary},
  publisher = {{Schloss Dagstuhl -- Leibniz-Zentrum f{\"u}r Informatik}},
  address   = {Dagstuhl, Germany},
  series    = {Leibniz International Proceedings in Informatics (LIPIcs)},
  volume    = {193},
  eid       = {21},
  pages     = {21:1--21:19},
  doi       = {10.4230/LIPIcs.ITP.2021.21},
  url       = {https://github.com/inQWIRE/SQIR},
  abstract  = {As quantum computing progresses steadily from theory into practice, programmers will face a common problem: How can they be sure that their code does what they intend it to do? This paper presents encouraging results in the application of mechanized proof to the domain of quantum programming in the context of the SQIR development. It verifies the correctness of a range of a quantum algorithms including Grover's algorithm and quantum phase estimation, a key component of Shor's algorithm. In doing so, it aims to highlight both the successes and challenges of formal verification in the quantum context and motivate the theorem proving community to target quantum computing as an application domain.},
  keywords  = {formal verification, quantum computing, proof engineering}
}
```

Alternatively, you can cite our repository using the information in [CITATION.cff](CITATION.cff).
