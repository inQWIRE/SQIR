Require Coq.extraction.Extraction.
Require Import optimizer.ListRepresentation.
Require Import optimizer.RzkGateSet.
Require Import optimizer.GateCancellation.
Require Import optimizer.HadamardReduction.
Require Import optimizer.RotationMerging.
Require Import optimizer.NotPropagation.
Require Import optimizer.Optimize.

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
Extraction Implicit single_qubit_pattern_to_program [U dim].
Extraction Implicit remove_single_qubit_pattern [U dim].
Extraction Implicit replace_single_qubit_pattern [U dim].
Extraction Implicit try_rewrites [U dim].
Extraction Implicit try_rewrites2 [U dim].
Extraction Implicit propagate [U dim].

(* From RzkGateSet.v *)
Extraction Implicit T [dim].
Extraction Implicit TDAG [dim].
Extraction Implicit P [dim].
Extraction Implicit PDAG [dim].
Extraction Implicit Z [dim].
Extraction Implicit Rz [dim].
Extraction Implicit H [dim].
Extraction Implicit X [dim].
Extraction Implicit CNOT [dim].
Extraction Implicit CCX [dim].
Extraction Implicit CCZ [dim].
Extraction Implicit match_gate [n].
Extraction Implicit combine_rotations [dim].
Extraction Implicit invert_rotation [dim].

(* From HadamardReduction.v *)
Extraction Implicit apply_H_equivalence1 [dim].
Extraction Implicit apply_H_equivalence2 [dim].
Extraction Implicit apply_H_equivalence3 [dim].
Extraction Implicit apply_H_equivalence4 [dim].
Extraction Implicit apply_H_equivalence5 [dim].
Extraction Implicit apply_H_equivalence [dim].
Extraction Implicit apply_H_equivalences [dim].
Extraction Implicit hadamard_reduction [dim].

(* From CancelGates.v *)
Extraction Implicit Rz_commute_rule1 [dim].
Extraction Implicit Rz_commute_rule2 [dim].
Extraction Implicit Rz_commute_rule3 [dim].
Extraction Implicit Rz_commute_rules [dim].
Extraction Implicit Rz_cancel_rule [dim].
Extraction Implicit H_cancel_rule [dim].
Extraction Implicit GateCancellation.X_commute_rule [dim].
Extraction Implicit GateCancellation.X_cancel_rule [dim].
Extraction Implicit CNOT_commute_rule1 [dim].
Extraction Implicit CNOT_commute_rule2 [dim].
Extraction Implicit CNOT_commute_rule3 [dim].
Extraction Implicit CNOT_commute_rule4 [dim].
Extraction Implicit CNOT_commute_rule5 [dim].
Extraction Implicit CNOT_commute_rules [dim].
Extraction Implicit CNOT_cancel_rule [dim].
Extraction Implicit propagate_Rz [dim].
Extraction Implicit propagate_H [dim].
Extraction Implicit GateCancellation.propagate_X [dim].
Extraction Implicit propagate_CNOT [dim].
Extraction Implicit cancel_single_qubit_gates' [dim].
Extraction Implicit cancel_single_qubit_gates [dim].
Extraction Implicit cancel_two_qubit_gates' [dim].
Extraction Implicit cancel_two_qubit_gates [dim].

(* From RotationMerging.v *)
Extraction Implicit next_gate [dim].
Extraction Implicit get_subcircuit' [dim].
Extraction Implicit get_subcircuit [dim].
Extraction Implicit find_merge [dim].
Extraction Implicit merge_at_beginning [dim].
Extraction Implicit merge_at_end [dim].
Extraction Implicit merge_rotations_at_beginning [dim].
Extraction Implicit merge_rotations_at_end [dim].
Extraction Implicit invert_gate [dim].
Extraction Implicit invert [dim].
Extraction Implicit merge_rotations [dim].

(* From NotPropagation.v *)
Extraction Implicit NotPropagation.propagate_X [dim].
Extraction Implicit not_propagation' [dim].
Extraction Implicit not_propagation [dim].

(* Optimize *)
Extraction Implicit optimize [dim].

(* Perform extraction to the file 'extracted_code.ml'. *)
Extraction "ExtractedCode.ml" 
  CCX CCZ
  URzk_Z URzk_P URzk_PDAG URzk_T URzk_TDAG URzk_Rz
  optimize.
