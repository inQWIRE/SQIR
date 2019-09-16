Require Coq.extraction.Extraction.

Require Import core.SQIRE.
Require Import Reals.

Require Coq.extraction.ExtrOcamlNatInt.
Require Coq.extraction.ExtrOcamlZInt.

(* From Leo's ExtractReal *)
Extract Constant R => "float".
Extract Constant R0 => "0.0".
Extract Constant R1 => "1.0".
Extract Constant Rinv => "(fun r -> 1.0 /. r)".
Extract Constant Ropp => "(fun r -> 0.0 -. r)".
Extract Constant Rmult => "(fun r1 r2 -> r1 *. r2)".
Extract Constant Rplus => "(+.)".

Extract Constant PI => "Float.pi".

Extraction Implicit H [dim].
Extraction Implicit X [dim].
Extraction Implicit Y [dim].
Extraction Implicit SQIRE.Z [dim].
Extraction Implicit ID [dim].
Extraction Implicit SKIP [dim].
Extraction Implicit Rz [dim].
Extraction Implicit T [dim].
Extraction Implicit TDAG [dim].
Extraction Implicit P [dim].
Extraction Implicit PDAG [dim].
Extraction Implicit CNOT [dim].
Extraction Implicit CZ [dim].
Extraction Implicit SWAP [dim].

Extraction "SqirGates.ml" com H X Y SQIRE.Z ID SKIP Rz T TDAG P PDAG CNOT CZ SWAP.
