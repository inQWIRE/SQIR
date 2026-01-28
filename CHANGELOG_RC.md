## RC Extension Change List

### Core additions
- `SQIR/RC_Syntax.v`: recursive command syntax with `CCall` and countable assertions (`IConj`).
- `SQIR/RC_Semantics.v`: denotational semantics with fixed-point interpretation for recursion.
- `SQIR/RC_Logic.v`: weakest-precondition calculus and soundness under stated semantic assumptions.

### Examples
- `examples/examples/RUSExample.v`: Recursive Unitary Sampling (RUS) gate.
- `examples/examples/QFTExample.v`: recursive QFT via procedure calls.
- `examples/examples/QuantumRandomWalkExample.v`: quantum random walk with `CWhile` and countable WP.

### Compatibility and packaging
- `SQIR/UnitarySem.v`, `SQIR/UnitaryOps.v`: adjusted imports to use `From SQIR Require ...`.
- `coq-sqir.opam`, `coq-voqc.opam`: version and dependency floor updates.
- `README.md`: added RC extension overview at the top.
