# SQIRE
A Small Quantum Intermediate Representation

## Compilation Instructions

To compile the code, use:
```
./configure.sh
make
```
Note that `make` will take a while. To add additional targets to the Makefile, edit the \_CoqProject file. By default, files in the core directory and select files from the optimizer and mapper directories are compiled. In case of compilation trouble, try `make clean` (and possibly manually removing any lingering `.vo` files) before running `./configure.sh`.  

The development has been tested with Coq version 8.8.2.

## Directory Contents

### Core files

The files below are the core of SQIRE.

- core/SQIRE.v : General definition of the SQIRE language.
- core/UnitarySem.v : Semantics for unitary SQIRE programs.
- core/DensitySem.v : Density matrix semantics for general SQIRE programs.
- core/NDSem.v : Non-deterministic semantics for general SQIRE programs.
- core/Compose.v : Composition of unitary SQIRE programs.
- core/Proportional.v : Defines proportional equality between matrices. **(should be moved to QWIRE)**
- core/Phase.v : General facts about the phase_shift matrix. **(should be moved to QWIRE)**
- core/Tactics.v : Useful tactics.

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
