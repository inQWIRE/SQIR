# SQIR & VOQC

SQIR is a **S**mall **Q**uantum **I**ntermediate **R**epresentation for quantum programs. Its intended use is as an intermediate representation (IR) in a **V**erified **O**ptimizer for **Q**uantum **C**ircuits (VOQC).

We describe SQIR and its use in VOQC in our draft [A Verified Optimizer for Quantum Circuits](https://arxiv.org/abs/1912.02250). We present details on verifying SQIR programs in our draft [Proving Quantum Programs Correct](https://arxiv.org/abs/2010.01240). Preliminary versions of this work were presented at QPL 2019 and PLanQC 2020.

This repository is split into two parts: SQIR and VOQC. If you are interested in formal verification of quantum programs, you should focus on the SQIR directory (we also recommend Robert Rand's [Verified Quantum Computing tutorial](http://www.cs.umd.edu/~rrand/vqc/index.html)). If you are interested in our verified compiler then take a look at the VOQC directory.

## Table of Contents

The bulk of this respository is Coq proofs about quantum programs and program transformations. Our verified program transformations can be *extracted* to OCaml to produce executable code. 

* [Notes for Artifact Evaluation](#notes-for-artifact-evaluation)
  * [VirtualBox Image](#virtualbox-image)
  * [Assumptions](#assumptions)
  * [Correspondence with Paper](#correspondence-with-paper)
* [Compilation](#compilation)
  * [Coq](#coq)
  * [OCaml](#ocaml)
* [Directory Contents](#directory-contents)
  * [SQIR](#sqir)
  * [VOQC](#voqc)
* [Acknowledgements](#acknowledgements)

## Notes for Artifact Evaluation

If you would like to build our code on your machine, compilation intructions are under [Compilation](#compilation) below. Alternatively, use our VirtualBox image (see below), which may save time. The contents of this repository are summarized in [Directory Contents](#directory-contents). For instructions on how to run the VOQC optimizer, see the [README in the VOQC sub-directory](VOQC/README.md). (TLDR; cd into the VOQC/benchmarks directory and run `./run_voqc_artifact.sh` to reproduce the results in Tables 2-3 of our paper.)

### VirtualBox Image

The VirtualBox image *TODO* contains precompiled versions of all of our Coq code and comes pre-installed with the relevant versions of the PyZX, tket, and Qiskit compilers. The username is `user` and the password is `password`. The POPL2021 branch of the SQIR repository is checked out in `~/SQIR`.

### Assumptions

There are no assumptions or axioms in the SQIR repository. However, we do use Coq's well-understood `functional_extensionality` axiom and we reuse [QWIRE](https://github.com/inQWIRE/QWIRE)'s libraries for matrices and complex numbers, which contain some axioms (detailed in Section 10 of Rand's [thesis](https://repository.upenn.edu/edissertations/3175/)).

As discussed at the end of Section 6 in the VOQC paper, we trust that the OCaml implementations of rational numbers, maps, and sets, used by the extracted code, are consistent with Coq’s. We also note that our translation between OpenQASM and SQIR is not formally verified.

### Correspondence with the VOQC paper

* **Section 3 - SQIR: A Small Quantum Intermediate Representation**
  * The definition of the SQIR language is in SQIR/src/SQIR.v (in particular, see the `ucom` and `com` types).
  * The unitary semantics are defined in SQIR/src/UnitarySem.v (see `uc_eval`).
  * The (density matrix-based) non-unitary semantics are defined in SQIR/src/DensitySem.v (see `c_eval`).
  * The GHZ example is in SQIR/examples/GHZ.v (see the `GHZ` program and `GHZ_correct` lemma).
  * The teleport example is in SQIR/examples/Teleport.v (see the `teleport` program and `teleport_correct` lemma in the DensityTeleport module).
* **Section 4 - Optimizing Unitary SQIR Programs**
  * The list representation of unitary SQIR programs is in VOQC/src/UnitaryListRepresentation.v (`gate_list`). This file also defines several operations over the list representation (e.g. `next_single_qubit_gate`) and equivalence between list programs (`uc_equiv_l`), all parameterized by input gate set. The semantics of a list program is computed by converting it to a SQIR program (`eval`).
  * The gate set we use in VOQC is defined in VOQC/src/RzQGateSet.v (`RzQ_Unitary`).
  * The entry point for our unitary optimizations is the `optimize` function in VOQC/src/Optimize.v. Our main correctness property is `optimize_sound`, which relies on `*_sound` lemmas about each of the component optimizations.
* **Section 5 - Other Verified Transformations**
  * The list representation of non-unitary SQIR programs is in VOQC/src/NonUnitaryListRepresentation.v (`com_list`).
  * As with the unitary optimizations, each non-unitary optimization has an associated `*_sound` lemma that shows that the transformation is semantics-preserving. The mapping transformations also have an associated `*_respects_constraints` lemma that shows that the output program satisfies architecture constraints.
* **Section 6 - Experimental Evaluation**
  * Our code for extracting from Coq to OCaml is in VOQC/extraction. See the READMEs in VOQC and VOQC/benchmarks for instructions on how to run our optimizer on the benchmarks in the VOQC paper. In summary: you can generate the data in Tables 2-3 using the `run_voqc_artifact.sh` script in the VOQC/benchmarks directory. You can generate the data in Appendix C using the `run_voqc.sh` script in VOQC/benchmarks (although this will take a long time due to the size of the benchmarks).

## Compilation

If you would like to compile our Coq proofs follow the instructions under 'Coq' below. If you just want to use the VOQC optimizer, follow the instructions under 'OCaml'.

### Coq

Dependencies:
  * OCaml version >= 4.08.1
  * Coq version >= 8.10.1

Run `make` to compile the core files of SQIR, `make optimizer` to compile proofs about VOQC, and `make examples` to compile proofs of correctness for small quantum programs. Use `make all` to compile everything. Our proofs are resource intensive so expect `make all` to take a little while. On a Macbook Pro running Coq version 8.12.0 and OCaml version 4.10.0 compilation takes around 30 minutes.

### OCaml

Dependencies:
  * OCaml version >= 4.08.1 
  * zarith (`opam install zarith`)
  * dune (`opam install dune`)
  * menhir (`opam install menhir`)
  * batteries (`opam install batteries`)
  * OpenQASM parser (`opam install openQASM`)

For convenience, we have already performed extraction from Coq to OCaml; the extracted files are in VOQC/extraction/ml. `make voqc` will produce an executable in VOQC/_build/default. See [the README in the VOQC directory](VOQC/README.md) for instructions on how to run the optimizer.

## Directory Contents

### SQIR

#### src

Definition of the SQIR language.

- src/SQIR.v : General definition of the SQIR language.
- src/UnitarySem.v : Semantics for unitary SQIR programs.
- src/DensitySem.v : Density matrix semantics for general SQIR programs.
- src/NDSem.v : Non-deterministic semantics for general SQIR programs.
- src/VectorStates.v : Utilities for describing states as vectors.
- src/UnitaryOps.v : Utilities for manipulating unitary SQIR programs (e.g. 'invert', 'control').
- src/Equivalences.v : Verified circuit equivalences for peephole optimizations.

We also rely on several files from the [QWIRE](https://github.com/inQWIRE/QWIRE) development, which we have linked as a git submodule in the externals directory.

#### examples

Examples of verifying correctness properties of simple SQIR programs.

- examples/DeutschJozsa.v : Deutsch-Jozsa algorithm
- examples/GHZ.v : GHZ state prepatation
- examples/Grover.v : Grover's algorithm (requires Coq version >= 8.12)
- examples/QPE.v : Quantum phase estimation (simplified)
- examples/QPEGeneral.v : Quantum phase estimation (general) -- this file is not built by default to minimize SQIR's dependencies; see notes at the top of that file
- examples/Simon.v : Simon's algorithm
- examples/Superdense.v : Superdense coding
- examples/Teleport.v : Quantum teleportation

### VOQC

#### src

Verified transformations of SQIR programs.

- Utilities
  - src/UnitaryListRepresentation.v : List representation of unitary SQIR programs; includes utilities for manipulating program lists and gate-set-independent proofs.
  - src/NonUnitaryListRepresentation.v : List representation of non-unitary SQIR programs.
  - src/RzQGateSet.v : Fixed gate set used in our optimizer.

- Optimizations on unitary programs
  - src/GateCancellation.v : 'Single-qubit gate cancellation' and 'two-qubit gate cancellation' optimizations from Nam et al.
  - src/HadamardReduction.v : 'Hadamard reduction' optimization from Nam et al.
  - src/NotPropagation.v : 'Not propagation' preprocessing step from Nam et al.
  - src/Optimize.v : Main optimization file; contains the high-level soundness proof.
  - src/RotationMerging.v : 'Rotation merging using phase polynomials' optimization from Nam et al.

- Optimizations on non-unitary programs
  - src/RemoveZRotationBeforeMeasure.v : Remove single-qubit z-axis rotations before measurement operations.
  - src/PropagateClassical.v : Track classical states to remove redundant measurements and CNOT operations.

- Mapping routines for unitary SQIR programs
  - src/SimpleMapping.v: Simple mapping for an architecture described by a directed graph.
  - src/MappingExamples.v: Verified circuit mapping examples for linear nearest neighbor, 2D grid, and IBM Tenerife architectures.
  - src/SimpleMappingWithLayout.v: Extends the simple mapping examples with an arbitrary initial layout.

- Experimental extensions
  - src/BooleanCompilation.v : Compilation from boolean expressions to unitary SQIR programs.

#### extraction

Code to extract unitary optimizations to OCaml (Extraction.v and extract.sh) and parse OpenQASM files into SQIR. Also contains pre-extracted versions of VOQC's optimizations. 

#### benchmarks

Instructions for running VOQC on the benchmarks presented in our paper can be found in [the README in the benchmarks directory](VOQC/benchmarks/README.md).

## Acknowledgements

This project is the result of the efforts of many people. The primary contacts for this project are Kesha Hietala (<kesha@cs.umd.edu>) and Robert Rand (<rand@uchicago.edu>). Other contributors include:
* Akshaj Gaur
* Shih-Han Hung
* Kartik Singhal

This project is supported by the U.S. Department of Energy, Office of Science, Office of Advanced Scientific Computing Research, Quantum Testbed Pathfinder Program under Award Number DE-SC0019040.
