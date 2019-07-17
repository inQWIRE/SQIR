Require Coq.extraction.Extraction.
Require Import Representations.
Require Import Optimizations.
(*Require Import Mapping.*)

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
Extraction Implicit _H [dim].
Extraction Implicit _X [dim].
Extraction Implicit _PI4 [dim].
Extraction Implicit _Z [dim].
Extraction Implicit _P [dim].
Extraction Implicit _PDAG [dim].
Extraction Implicit _T [dim].
Extraction Implicit _TDAG [dim].
Extraction Implicit _CNOT [dim].
Extraction Implicit match_gate [n].
Extraction Implicit TOFF [dim].
Extraction Implicit next_single_qubit_gate [dim].
Extraction Implicit next_two_qubit_gate [dim].
Extraction Implicit does_not_reference [dim].
Extraction Implicit count_H_gates [dim].
Extraction Implicit count_X_gates [dim].
Extraction Implicit count_rotation_gates [dim].
Extraction Implicit count_CNOT_gates [dim].
Extraction Implicit single_qubit_pattern_to_program [dim].
Extraction Implicit propagate_not [dim].
Extraction Implicit propagate_nots [dim].
Extraction Implicit rm_nots [dim].
Extraction Implicit benchmark_to_list [dim].
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
Extraction Implicit cancel_gates_simple' [dim].
Extraction Implicit cancel_gates_simple [dim].
Extraction Implicit search_for_Rz_pat1 [dim].
Extraction Implicit search_for_Rz_pat2 [dim].
Extraction Implicit search_for_Rz_pat3 [dim].
Extraction Implicit search_for_CNOT_pat1 [dim].
Extraction Implicit search_for_CNOT_pat2 [dim].
Extraction Implicit search_for_CNOT_pat3 [dim].
Extraction Implicit search_for_CNOT_pat4 [dim].
Extraction Implicit search_for_commuting_X_pat [dim].
Extraction Implicit search_for_commuting_Rz_pat [dim].
Extraction Implicit search_for_commuting_CNOT_pat [dim].
Extraction Implicit propagate_PI4 [dim].
Extraction Implicit propagate_H [dim].
Extraction Implicit propagate_X [dim].
Extraction Implicit propagate_CNOT [dim].
Extraction Implicit cancel_gates' [dim].
Extraction Implicit cancel_gates [dim].

(* Perform extraction to the file 'quipper-to-sqire/extracted_code.ml'. *)
Extraction "quipper-to-sqire/extracted_code.ml" benchmark_to_list count_H_gates count_X_gates count_rotation_gates count_CNOT_gates cancel_gates_simple cancel_gates.

