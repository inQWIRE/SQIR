# SQIRE
A Small Quantum Intermediate Representation

## Compilation Instructions

Run `make` to compile the files in the core directory, `make optimizer` to compile code in the optimizer directory, `make mapper` to compile code in the mapper directory, and `make examples` to compile the code in the examples directory. Use `make all` to compile everything.

The development has been tested with Coq version 8.9.1.

## Directory Contents

### Core files

The files below are the core of SQIRE.

- core/SQIRE.v : General definition of the SQIRE language.
- core/UnitarySem.v : Semantics for unitary SQIRE programs.
- core/DensitySem.v : Density matrix semantics for general SQIRE programs.
- core/NDSem.v : Non-deterministic semantics for general SQIRE programs.
- core/Utilities.v : Utilities for describing composition of SQIRE programs and classical state vectors.

We rely on several files from the [QWIRE](https://github.com/inQWIRE/QWIRE) development.

### hll-compiler

Compilation from higher-level languages to SQIRE. Compilation from QWIRE is experimental (i.e. not done).

- compiler/BooleanCompilation.v : Compilation from boolean expressions to unitary SQIRE programs.
- compiler/CompileFromQwire.v : Compilation from QWIRE to SQIRE. **(WIP)**

### optimizer

SQIRE programs optimizations.

- optimizer/Equivalences.v : Verified circuit equivalences useful for peephole optimizations.
- optimizer/GateCancellation.v : Cancel gates adjacent to their inverses, propagate using the rules from Nam et al.
- optimizer/HadamardReduction.v : 'Hadamard reduction' pass from Nam et al.
- optimizer/ListRepresentation.v : List representation of unitary SQIRE programs used for implementing optimizations.
- optimizer/NonUnitaryOptimizations.v : Examples of optimizations on non-unitary programs.
- optimizer/NotPropagation.v : Based on the 'not propagation' preprocessing step from Nam et al.
- optimizer/PI4GateSet.v : Gate set used in our implementation of the Nam et al. optimizations.
- optimizer/RotationMerging.v : 'Rotation merging using phase polynomials' optimization from Nam et al.
- optimizer/SkipElimination.v : Toy optimization that removes identity operations.

### mapper

Mapping algorithms for SQIRE programs.

- mapper/SimpleMapping.v: Simple mapping for an architecture described by a directed graph.
- mapper/SimpleMappingWithLayout.v: Extends the simple mapping examples with an arbitrary initial layout. **(WIP)**
- mapper/MappingExamples.v: Verified circuit mapping examples for linear nearest neighbor, 2D grid, and IBM Tenerife architectures.

### examples

Examples of using SQIRE to verify correctness properties of simple quantum algorithms.

- examples/Deutsch.v    
- examples/DeutschJozsa.v
- examples/GHZ.v
- examples/Superdense.v
- examples/Teleport.v  

### benchmarks

Instructions for running the benchmarks described in our paper can be found in the README in the benchmarks directory.

## Remarks

This project is supported by the U.S. Department of Energy, Office of Science, Office of Advanced Scientific Computing Research, Quantum Testbed Pathfinder Program under Award Number DE-SC0019040.
