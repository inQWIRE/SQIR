# SQIR
A *S*mall *Q*uantum *I*ntermediate *R*epresentation for a verified compiler.

## Compilation Instructions

Run `make` to compile the files in the core directory, `make optimizer` to compile code in the optimizer directory, `make mapper` to compile code in the mapper directory, and `make examples` to compile the code in the examples directory. Use `make all` to compile everything.

The development has been tested with Coq versions 8.9.1 and 8.10.2. Using Coq version 8.9.1 on a standard laptop, `make all` takes about ..hrs. So be patient.

## Directory Contents

### core

- core/SQIR.v : General definition of the SQIR language.
- core/UnitarySem.v : Semantics for unitary SQIR programs.
- core/DensitySem.v : Density matrix semantics for general SQIR programs.
- core/NDSem.v : Non-deterministic semantics for general SQIR programs.
- core/Utilities.v : Utilities for describing composition of SQIR programs and classical state vectors.

We also rely on several files from the [QWIRE](https://github.com/inQWIRE/QWIRE) development.

### hll-compiler

Compilation from higher-level languages to SQIR. Compilation from QWIRE is experimental (i.e. not done).

- compiler/BooleanCompilation.v : Compilation from boolean expressions to unitary SQIR programs.
- compiler/CompileFromQwire.v : Compilation from QWIRE to SQIR. **(WIP)**

### optimizer

Current progress on a verified optimizer for SQIR programs.

- Utilities
  - optimizer/Equivalences.v : Verified circuit equivalences useful for peephole optimizations.
  - optimizer/ListRepresentation.v : List representation of unitary and non-unitary SQIR programs.
  - optimizer/PI4GateSet.v : Fixed gate set used in our optimizer. (Although optimizations could be defined for any gate set.)

- Optimizations on unitary programs
  - optimizer/GateCancellation.v : Cancel gates adjacent to their inverses, propagate using the rules from Nam et al.
  - optimizer/HadamardReduction.v : 'Hadamard reduction' pass from Nam et al.
  - optimizer/NotPropagation.v : Based on the 'not propagation' preprocessing step from Nam et al.
  - optimizer/RotationMerging.v : 'Rotation merging using phase polynomials' optimization from Nam et al.
  - optimizer/SkipElimination.v : Toy optimization that removes identity gates.

- Optimizations on non-unitary programs
  - optimizer/RemoveZRotationBeforeMeasure.v : Remove single-qubit z-axis rotations before measurement operations.
  - optimizer/PropagateClassical.v : Track classical states to remove redundant measurements and CNOT operations.

### mapper

Mapping algorithms for SQIR programs.

- mapper/SimpleMapping.v: Simple mapping for an architecture described by a directed graph.
- mapper/SimpleMappingWithLayout.v: Extends the simple mapping examples with an arbitrary initial layout. **(WIP)**
- mapper/MappingExamples.v: Verified circuit mapping examples for linear nearest neighbor, 2D grid, and IBM Tenerife architectures.

### examples

Examples of verifying correctness properties of simple SQIR programs.

- examples/Deutsch.v    
- examples/DeutschJozsa.v
- examples/GHZ.v
- examples/Superdense.v
- examples/Teleport.v  

### benchmarks

Instructions for running the benchmarks described in our paper can be found in the README in the benchmarks directory.

## Remarks

A preliminary version of this work was presented at QPL 2019. For details, see the arXiv paper available [here](https://arxiv.org/pdf/1904.06319.pdf) and the code in the 'QPL2019' branch.
A revised submission is in progress; contact the authors if you are interested in a draft.

This project is supported by the U.S. Department of Energy, Office of Science, Office of Advanced Scientific Computing Research, Quantum Testbed Pathfinder Program under Award Number DE-SC0019040.
