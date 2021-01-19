Require Coq.extraction.Extraction.
Require Import UnitaryListRepresentation.
Require Import IBMGateSet.

(* Standard utilities for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* A few common functions not included in ExtrOcamlBasic. *)
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant negb => "not".
Extract Inlined Constant length => "List.length".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant rev => "List.rev".
Extract Inlined Constant rev_append => "List.rev_append".
Extract Inlined Constant fold_right => "(fun f a l -> List.fold_right f l a)".
Extract Inlined Constant forallb => "List.for_all".

(* Standard extraction from nat -> OCaml int. *)
Require Coq.extraction.ExtrOcamlNatInt.

(* Inline a few operations. *)
Extraction Inline plus mult Nat.eq_dec.
Extraction Inline Z.mul Z.div.

(* Custom Extraction of reals. *)
Extract Inlined Constant R0 => "(0.0)".
Extract Inlined Constant R1 => "(1.0)".
Extract Inlined Constant Rplus => "(+.)".
Extract Inlined Constant Rmult => "(*.)".
Extract Inlined Constant Ropp => "(-.)".
Extract Inlined Constant Rinv => "((/.) 1.0)".
Extract Inlined Constant Rltb => "(<)".
Extract Inlined Constant Rleb => "(<=)".


(* Set the dimension argument to be implicit everywhere -- it should be an
   unused argument everywhere in the OCaml code. *)

(* From ListRepresentation.v *)
Extraction Implicit next_single_qubit_gate' [dim].
Extraction Implicit next_single_qubit_gate [dim].
Extraction Implicit last_single_qubit_gate [dim].
Extraction Implicit next_two_qubit_gate' [dim].
Extraction Implicit next_two_qubit_gate [dim].
Extraction Implicit next_gate' [dim].
Extraction Implicit next_gate [dim].
Extraction Implicit does_not_reference_appl [dim].
Extraction Implicit does_not_reference [dim].
Extraction Implicit UnitaryListRepresentation.remove_prefix [dim].
Extraction Implicit UnitaryListRepresentation.remove_suffix [dim].
Extraction Implicit UnitaryListRepresentation.replace_pattern [dim].
Extraction Implicit try_rewrites [dim].
Extraction Implicit try_rewrites2 [dim].
Extraction Implicit propagate' [dim].
Extraction Implicit propagate [dim].
Extraction Implicit get_matching_prefix' [dim].
Extraction Implicit get_matching_prefix [dim].
Extraction Implicit LCR [dim].

(* From IBMGateSet.v *)
Extraction Implicit U1 [dim].
Extraction Implicit U2 [dim].
Extraction Implicit U3 [dim].
Extraction Implicit CNOT [dim].

(* Perform extraction. *)
Separate Extraction
  U1 U2 U3 CNOT.
