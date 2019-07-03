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

### SQIRE as an IR

The primary use case for SQIRE is as an IR in a verified compiler. The compiler directory contains current progress on transformations of SQIRE programs.

- compiler/Equivalences.v : Verified circuit equivalences useful for Optimizations.v.
- compiler/Mapping.v : Verified (basic) circuit mapping example.
- compiler/Optimizations.v : Verified optimizations of SQIRE programs including skip removal and not propagation.
- ~~compiler/CompileFromQwire.v : (IN PROGRESS) Current progress on verified compilation from QWIRE programs to SQIRE programs.~~ (not up-to-date)
- ~~compiler/BooleanCompilation.v : Verified compilation from boolean expressions to unitary SQIRE programs.~~ (not up-to-date)
- compiler/Representations.v : Alternative representations of unitary SQIRE programs useful for implementing transformations.

### SQIRE for General Verification

We also include several examples of using SQIRE for general verification. The files in the examples directory verify correctness properties of simple quantum algorithms.

- examples/Deutsch.v    
- ~~examples/DeutschJozsa.v~~ (not up-to-date)
- examples/GHZ.v
- examples/Superdense.v
- ~~Examples/Teleport.v~~ (not up-to-date)    
