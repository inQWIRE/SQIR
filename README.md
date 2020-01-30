# SQIR

## Overview

SQIR is a **S**mall **Q**uantum **I**ntermediate **R**epresentation for quantum programs.
Its main application is as an IR in a **V**erified **O**ptimizer for **Q**uantum **C**ircuits (VOQC).

We describe SQIR and VOQC in [this draft](https://www.cs.umd.edu/~mwh/papers/hietala19voqc.html). A preliminary version of this work was presented at QPL 2019.

## Compilation

Dependencies:
* For compiling SQIR/VOQC proofs
  * Coq version 8.10.1
* For compiling executable VOQC optimizer
  * OCaml version 4.08.1 
  * dune (`opam install dune`)
  * menhir (`opam install menhir`)
  * OCaml OpenQASM parser (`opam install openQASM`)

Run `make` to compile the core files of SQIR, `make optimizer` to compile proofs about the circuit optimizer, and `make examples` to compile proofs of correctness for small quantum programs. To compile an executable version of the optimizer (from OCaml code extracted from the Coq code), run `make voqc`. Use `make all` to compile everything. `make voqc` will produce an executable in `VOQC/_build/default`; see the benchmarks directory for instructions on running the optimizer. 

The development has been tested with Coq version 8.10.1 and OCaml version 4.08.1 on a MacBook Pro. Our proofs are resource intensive, so expect `make all` to take around an hour and a half (although compilation of the extracted code with `make voqc` should be quick). We have experienced memory errors on some Linux machines, we are working to resolve this.

## SQIR

### src

Definition of the SQIR language.

- src/SQIR.v : General definition of the SQIR language.
- src/UnitarySem.v : Semantics for unitary SQIR programs.
- src/DensitySem.v : Density matrix semantics for general SQIR programs.
- src/NDSem.v : Non-deterministic semantics for general SQIR programs.
- src/Composition.v : Utilities for describing composition of SQIR programs.
- src/ClassicalStates.v : Utilities for describing classical states.

We also rely on several files from the [QWIRE](https://github.com/inQWIRE/QWIRE) development, which we have linked as a git submodule in the externals directory.

### examples

Examples of verifying correctness properties of simple SQIR programs.

- examples/Deutsch.v    
- examples/DeutschJozsa.v
- examples/GHZ.v
- examples/Superdense.v
- examples/Teleport.v  

## VOQC

### src/optimizer

A verified optimizer for SQIR programs.

- Utilities
  - optimizer/Equivalences.v : Verified circuit equivalences for peephole optimizations.
  - optimizer/ListRepresentation.v : List representation of unitary and non-unitary SQIR programs; includes utilities for manipulating program lists and gate-set-independent proofs when possible.
  - optimizer/PI4GateSet.v : Fixed gate set used in our optimizer; includes gate set-specific proofs for utilities in ListRepresentation.v.
  - optimizer/Extraction.v : Rules for extracting VOQC to OCaml.

- Optimizations on unitary programs
  - optimizer/GateCancellation.v : 'Single-qubit gate cancellation' and 'two-qubit gate cancellation' optimizations from Nam et al.
  - optimizer/HadamardReduction.v : 'Hadamard reduction' optimization from Nam et al.
  - optimizer/NotPropagation.v : 'Not propagation' preprocessing step from Nam et al.
  - optimizer/RotationMerging.v : 'Rotation merging using phase polynomials' optimization from Nam et al.

- Optimizations on non-unitary programs
  - optimizer/RemoveZRotationBeforeMeasure.v : Remove single-qubit z-axis rotations before measurement operations.
  - optimizer/PropagateClassical.v : Track classical states to remove redundant measurements and CNOT operations.

### src/mapper

Mapping algorithms for SQIR programs.

- mapper/SimpleMapping.v: Simple mapping for an architecture described by a directed graph.
- mapper/SimpleMappingWithLayout.v: Extends the simple mapping examples with an arbitrary initial layout. **(WIP)**
- mapper/MappingExamples.v: Verified circuit mapping examples for linear nearest neighbor, 2D grid, and IBM Tenerife architectures.

### src/experimental

Experimental extensions to VOQC.

- experimental/BooleanCompilation.v : Compilation from boolean expressions to unitary SQIR programs.

### extraction

Code to extract unitary optimizations to OCaml (Extraction.v and extract.sh) and parse OpenQASM files into SQIR. Also contains pre-extracted versions of VOQC's optimizations (ExtractedCode.ml and ExtractedCode.mli). 

### benchmarks

Instructions for running VOQC on the benchmarks presented in our paper can be found in [the README in the benchmarks directory](VOQC/benchmarks/README.md).

## Acknowledgements

This project is supported by the U.S. Department of Energy, Office of Science, Office of Advanced Scientific Computing Research, Quantum Testbed Pathfinder Program under Award Number DE-SC0019040.
