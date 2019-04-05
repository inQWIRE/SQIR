# SQIMP
A Small Quantum Imperative Language for Program Verification

## Directory Contents

### Core files

The files below are generally useful for verification of quantum programs. They are taken directly from [QWIRE](https://github.com/inQWIRE/QWIRE).

- Prelim.v : A variety of general purpose definitions and tactics.
- Complex.v : Complex number library, modified from Coquelicot.
- Matrix.v : Matrix library.
- Quantum.v : Definition of unitary matrices and quantum operations.
- Dirac.v : Library for reasoning about quantum states as vectors instead of density matrices.

The files below are specific to SQIMP.

- SQIMP.v : General definition of the SQIMP language.
- UnitarySem.v : Semantics for unitary SQIMP programs.
- DensitySem.v : Density matrix-based semantics for general SQIMP programs.
- NDSem.v : Non-deterministic semantics for general SQIMP programs.

### SQIMP as an IR

The primary use case for SQIMP is as an IR in a verified compiler. The Transformations.v file verifies several transformations of SQIMP programs including simple optimizations and circuit mapping algorithms.

### SQIMP for General Verification

We also include several examples of using SQIMP for general verification. The files below verify correctness properties of several simple quantum algorithms.

- Deutsch.v    
- DeutschJozsa.v
- GHZ.v
- Superdense.v
- Teleport.v    
