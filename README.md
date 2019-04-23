# SQIRE
A Small Quantum Intermediate Representation

## Compilation Instructions

To compile the code, use:
```
git submodule init
git submodule update
./configure.sh
make
```
Note that `make` will take a while. To add additional targets to the Makefile, edit the \_CoqProject file. In case of compilation trouble, try `make clean` before running `./configure.sh`. You should only need to run the submodule commands once. 

Note that the teleport example is not currently compiled.

The development has only been tested with Coq version 8.8.2.

## Directory Contents

### Core files

The files below are specific to SQIRE.

- SQIRE.v : General definition of the SQIRE language.
- UnitarySem.v : Semantics for unitary SQIRE programs.
- DensitySem.v : Density matrix semantics for general SQIRE programs.
- NDSem.v : Non-deterministic semantics for general SQIRE programs.
- Compose.v : Composition of unitary SQIRE programs.

We rely on several files from the [QWIRE](https://github.com/inQWIRE/QWIRE) development.

### SQIRE as an IR

The primary use case for SQIRE is as an IR in a verified compiler. The compiler directory contains current progress on transformations of SQIRE programs.

- compiler/Equivalences.v : verifies several circuit equivalences useful for the optimizations in Transformations.v.
- compiler/Mapping.v : verifies a simple circuit mapping example.
- compiler/Optimizations.v : verifies several simple optimizations of SQIRE programs including skip removal and not propagation.
- compiler/CompileFromQwire.v : current progress on verified compilation from QWIRE programs to SQIRE programs.

### SQIRE for General Verification

We also include several examples of using SQIRE for general verification. The files in the examples directory verify correctness properties of simple quantum algorithms.

- examples/Deutsch.v    
- examples/DeutschJozsa.v
- examples/GHZ.v
- examples/Superdense.v
- examples/Teleport.v    
