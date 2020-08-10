Require Coq.extraction.Extraction.
Require Import UnitaryListRepresentation.
Require Import RzQGateSet.
Require Import GateCancellation.
Require Import HadamardReduction.
Require Import RotationMerging.
Require Import NotPropagation.
Require Import Optimize.

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

(* Custom Extraction of rationals. *)
Extract Inductive Q => "Q.t" [ "" ].
Extract Inlined Constant zero_Q => "(Q.of_int 0)".
Extract Inlined Constant two_Q => "(Q.of_int 2)".
Extract Inlined Constant Qplus => "Q.add".
Extract Inlined Constant Qminus => "Q.sub".
Extract Inlined Constant Qmult => "Q.mul".
Extract Inlined Constant Qeq_bool => "Q.equal".
Extract Inlined Constant Qle_bool => "Q.leq".
Extract Inlined Constant inject_Z => "Q.of_int".
Extract Inlined Constant Qnum => "(fun q -> Z.to_int (Q.num q))".
Extract Inlined Constant Qden => "(fun q -> Z.to_int (Q.den q))".    
Extract Constant URzQ_T => "RzQGateSet.URzQ_Rz (Q.of_ints 1 4)".
Extract Constant URzQ_P => "RzQGateSet.URzQ_Rz (Q.of_ints 1 2)".
Extract Constant URzQ_Z => "RzQGateSet.URzQ_Rz (Q.of_int 1)".
Extract Constant URzQ_PDAG => "RzQGateSet.URzQ_Rz (Q.of_ints 3 2)".
Extract Constant URzQ_TDAG => "RzQGateSet.URzQ_Rz (Q.of_ints 7 4)".
(* It's easier to extract this function by hand.
   bound is used in RzQGateSet; it puts a rational q in the range [0,2) *)
Extract Constant bound => 
  "let round_to_multiple_of_2 q = 
      let num = Q.num q in 
      let den = Q.den q in
      Z.mul (Z.of_int 2) (Z.div num (Z.mul den (Z.of_int 2))) in
   fun q ->
   if (Q.leq (Q.of_int 0) q) && not (Q.leq (Q.of_int 2) q) then q
   else if (Q.leq (Q.of_int 2) q)
        then Q.sub q (Q.of_bigint (round_to_multiple_of_2 q))
        else Q.add q (Q.of_bigint (round_to_multiple_of_2 q))".

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

(* From RzQGateSet.v *)
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
Extraction Implicit combine_rotations [dim].
Extraction Implicit invert_rotation [dim].
Extraction Implicit RzQGateSet.remove_prefix [dim].
Extraction Implicit RzQGateSet.remove_suffix [dim].
Extraction Implicit RzQGateSet.replace_pattern [dim].

(* From HadamardReduction.v *)
Extraction Implicit apply_H_equivalence1 [dim].
Extraction Implicit apply_H_equivalence2 [dim].
Extraction Implicit apply_H_equivalence3 [dim].
Extraction Implicit apply_H_equivalence4 [dim].
Extraction Implicit apply_H_equivalence5 [dim].
Extraction Implicit apply_H_equivalence [dim].
Extraction Implicit apply_H_equivalences' [dim].
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
Extraction Implicit find_merge' [dim].
Extraction Implicit find_merge [dim].
Extraction Implicit merge_at_beginning [dim].
Extraction Implicit merge_at_end [dim].
Extraction Implicit merge_rotations_at_beginning [dim].
Extraction Implicit merge_rotations_at_end [dim].
Extraction Implicit invert_gate [dim].
Extraction Implicit invert [dim].
Extraction Implicit merge_rotations [dim].

(* From NotPropagation.v *)
Extraction Implicit finalize [dim].
Extraction Implicit not_propagation' [dim].
Extraction Implicit not_propagation [dim].

(* Optimize *)
Extraction Implicit optimize [dim].
Extraction Implicit optimize_lcr [dim].

(* Perform extraction. *)
Separate Extraction
  CCX CCZ
  URzQ_Z URzQ_P URzQ_PDAG URzQ_T URzQ_TDAG URzQ_Rz 
  optimize optimize_lcr.
