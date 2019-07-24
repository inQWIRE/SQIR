# SQIRE
A Small Quantum Intermediate Representation

## Compilation Instructions

To compile the code, use:
```
./configure.sh
make
```
Note that `make` will take a while. To add additional targets to the Makefile, edit the \_CoqProject file. In case of compilation trouble, try `make clean` before running `./configure.sh`.  

The development has only been tested with Coq version 8.8.2.

## Directory Contents

### Core files

The files below are the core of SQIRE.

- SQIRE.v : General definition of the SQIRE language.
- UnitarySem.v : Semantics for unitary SQIRE programs.
- DensitySem.v : Density matrix semantics for general SQIRE programs.
- NDSem.v : Non-deterministic semantics for general SQIRE programs.
- Compose.v : Composition of unitary SQIRE programs.

We rely on several files from the [QWIRE](https://github.com/inQWIRE/QWIRE) development.

### compiler

Compilation from higher-level languages to SQIRE. Everything in this directory is experimental (i.e. not done).

- compiler/BooleanCompilation.v : Compilation from boolean expressions to unitary SQIRE programs.
- compiler/CompileFromQwire.v : Compilation from QWIRE to SQIRE.

### optimizer

SQIRE programs optimizations.

- optimizer/Equivalences.v : Verified circuit equivalences useful for various peephole optimizations.
- optimizer/GateCancellation.v : Cancel gates adjacent to their inverses, propagate using the rules from Nam et al.
- optimizer/HadamardReduction.v : 'Hadamard reduction' pass from Nam et al.
- optimizer/ListRepresentation.v : List representation of unitary SQIRE programs used for implementing optimizations.
- optimizer/NonUnitaryOptimizations.v : Examples of optimizations on non-unitary programs.
- optimizer/NotPropagation.v : Based on the 'not propagation' preprocessing step by Nam et al. (TODO: add handling for Toffoli gates.)
- optimizer/SkipElimination.v : Toy optimization that removes skip operations.

### mapper

Mapping algorithms for SQIRE programs.

- mapper/SimpleMapping.v: Verified circuit mapping examples for linear nearest neighbor and Tenerife architectures.

### examples

Examples of using SQIRE to verify correctness properties of simple quantum algorithms.

- examples/Deutsch.v    
- examples/DeutschJozsa.v *(needs to be updated)*
- examples/GHZ.v
- examples/Superdense.v
- examples/Teleport.v    

### benchmarks

*TODO*

## Remarks

This project is supported by the U.S. Department of Energy, Office of Science, Office of Advanced Scientific Computing Research, Quantum Testbed Pathfinder Program under Award Number DE-SC0019040.
