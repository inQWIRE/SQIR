Require Coq.extraction.Extraction.
Require Import optimizer.ListRepresentation.
Require Import optimizer.PI4GateSet.
Require Import optimizer.GateCancellation.
Require Import optimizer.HadamardReduction.

(* General utilies for bools, options, etc. *)
Require Coq.extraction.ExtrOcamlBasic.

(* Automatic extraction from nat/int -> OCaml int. We may not want to use these. *)
Require Coq.extraction.ExtrOcamlNatInt.
Require Coq.extraction.ExtrOcamlZInt.

(* A few list functions not included in ExtrOcamlBasic. *)
Extract Constant length => "List.length".
Extract Constant app => "List.append".
Extract Constant rev => "List.rev".

(* Set the dimension argument to be implicit everywhere -- it should be an
   unused argument everywhere in the OCaml code. *)

(* From ListRepresentation.v *)
Extraction Implicit next_single_qubit_gate [dim].
Extraction Implicit last_single_qubit_gate [dim].
Extraction Implicit next_two_qubit_gate [dim].
Extraction Implicit does_not_reference_appl [dim].
Extraction Implicit does_not_reference [dim].

(* From PI4GateSet.v *)
Extraction Implicit match_gate [n].
Extraction Implicit count_H_gates [dim].
Extraction Implicit count_X_gates [dim].
Extraction Implicit count_rotation_gates [dim].
Extraction Implicit count_CNOT_gates [dim].

(* From HadamardReduction.v *)
Extraction Implicit single_qubit_pattern_to_program [dim].
Extraction Implicit remove_single_qubit_pattern [dim].
Extraction Implicit replace_single_qubit_pattern [dim].
Extraction Implicit try_rewrites [dim].
Extraction Implicit apply_H_equivalence1 [dim].
Extraction Implicit apply_H_equivalence2 [dim].
Extraction Implicit apply_H_equivalence3 [dim].
Extraction Implicit apply_H_equivalence4 [dim].
Extraction Implicit apply_H_equivalence5 [dim].
Extraction Implicit apply_H_equivalence [dim].
Extraction Implicit apply_H_equivalences [dim].
Extraction Implicit hadamard_reduction [dim].

(* From CancelGates.v *)
Extraction Implicit search_for_commuting_X_pat [dim].
Extraction Implicit search_for_Rz_pat1 [dim].
Extraction Implicit search_for_Rz_pat2 [dim].
Extraction Implicit search_for_Rz_pat3 [dim].
Extraction Implicit search_for_commuting_Rz_pat [dim].
Extraction Implicit search_for_CNOT_pat1 [dim].
Extraction Implicit search_for_CNOT_pat2 [dim].
Extraction Implicit search_for_CNOT_pat3 [dim].
Extraction Implicit search_for_CNOT_pat4 [dim].
Extraction Implicit search_for_commuting_CNOT_pat [dim].
Extraction Implicit propagate_PI4 [dim].
Extraction Implicit propagate_H [dim].
Extraction Implicit propagate_X [dim].
Extraction Implicit propagate_CNOT [dim].
Extraction Implicit cancel_gates' [dim].
Extraction Implicit cancel_gates [dim].

(* Perform extraction to the file 'extracted_code.ml'. *)
Extraction "extracted_code.ml" count_H_gates count_X_gates count_rotation_gates count_CNOT_gates UPI4_Z UPI4_P UPI4_PDAG UPI4_T UPI4_TDAG cancel_gates hadamard_reduction.
