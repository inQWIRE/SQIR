Require Import CXCancellation.
Require Import GateCancellation.
Require Import HadamardReduction.
Require Import NotPropagation.
Require Import Optimize1qGates.
Require Import RotationMerging.
Require Import SimpleMapping.
Require Import StandardGateSet.

(** Utilities for converting between gate sets preserve constraints **)

Lemma standard_to_IBM_preserves_mapping : forall {dim} (l : standard_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph UIBM_CNOT (standard_to_IBM l).
Proof.
  intros dim l is_in_graph H.
  unfold standard_to_IBM.
  induction l.
  constructor.
  rewrite change_gate_set_cons. 
  inversion H; subst.
  apply respects_constraints_directed_app; auto.
  dependent destruction u; repeat constructor.
  apply respects_constraints_directed_app; auto.
  repeat constructor.
  assumption.
Qed.

Lemma IBM_to_standard_preserves_mapping : forall {dim} (l : IBM_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph UIBM_CNOT l ->
  respects_constraints_directed is_in_graph U_CX (IBM_to_standard l).
Proof.
  intros dim l is_in_graph H.
  unfold IBM_to_standard.
  induction l.
  constructor.
  rewrite change_gate_set_cons. 
  inversion H; subst.
  apply respects_constraints_directed_app; auto.
  dependent destruction u; repeat constructor.
  apply respects_constraints_directed_app; auto.
  repeat constructor.
  assumption.
Qed.

Lemma standard_to_RzQ_preserves_mapping : forall {dim} (l : standard_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (standard_to_RzQ l).
Proof.
  intros dim l is_in_graph H.
  unfold standard_to_RzQ.
  induction l.
  constructor.
  rewrite change_gate_set_cons. 
  inversion H; subst.
  apply respects_constraints_directed_app; auto.
  dependent destruction u; repeat constructor.
  apply respects_constraints_directed_app; auto.
  repeat constructor.
  assumption.
Qed.

Lemma RzQ_to_standard_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph U_CX (RzQ_to_standard l).
Proof.
  intros dim l is_in_graph H.
  unfold RzQ_to_standard.
  induction l.
  constructor.
  rewrite change_gate_set_cons. 
  inversion H; subst.
  apply respects_constraints_directed_app; auto.
  dependent destruction u; repeat constructor.
  apply respects_constraints_directed_app; auto.
  repeat constructor.
  assumption.
Qed.

Lemma convert_to_rzq_preserves_mapping : forall {dim} (l : standard_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph U_CX (convert_to_rzq l).
Proof.
  intros dim l is_in_graph H.
  unfold convert_to_rzq.
  apply RzQ_to_standard_preserves_mapping.
  apply standard_to_RzQ_preserves_mapping.
  assumption.
Qed.

Lemma convert_to_ibm_preserves_mapping : forall {dim} (l : standard_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph U_CX (convert_to_ibm l).
Proof.
  intros dim l is_in_graph H.
  unfold convert_to_ibm.
  apply IBM_to_standard_preserves_mapping.
  apply standard_to_IBM_preserves_mapping.
  assumption.
Qed.

Lemma replace_rzq_preserves_mapping : forall {dim} (l : standard_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph U_CX (replace_rzq l).
Proof.
  intros dim l is_in_graph H.
  unfold replace_rzq.
  induction l.
  constructor.
  rewrite change_gate_set_cons. 
  inversion H; subst.
  apply respects_constraints_directed_app; auto.
  dependent destruction u; repeat constructor.
  simpl.
  destruct_Qeq_bool; repeat constructor.
  apply respects_constraints_directed_app; auto.
  repeat constructor.
  assumption.
Qed.

(** Optimizations preserve constraints **)
Require Import GateCancellationRespectsConstraints.
Require Import CXCancellationRespectsConstraints.
Require Import Optimize1qGatesRespectsConstraints.
Require Import HadamardReductionRespectsConstraints.
Require Import RotationMergingRespectsConstraints.
Require Import NotPropagationRespectsConstraints. 
Lemma cx_cancellation_preserves_mapping : forall {dim} (l : IBM_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph UIBM_CNOT l ->
  respects_constraints_directed is_in_graph UIBM_CNOT (cx_cancellation l).
Proof.
  intros.
  unfold cx_cancellation.
  apply cx_cancellation'_respects_constraints.
  assumption.
  constructor. 
Qed. 


Lemma optimize_1q_gates_preserves_mapping : forall {dim} (l : IBM_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph UIBM_CNOT l ->
  respects_constraints_directed is_in_graph UIBM_CNOT (optimize_1q_gates l).
Proof.
  intros.
  unfold optimize_1q_gates.
  
  apply simplify_1q_gates_respects_constraints.

  assumption. 
  apply optimize_1q_gates'_respects_constraints.
  assumption.
  assumption.
  constructor. constructor. 
Qed. 

Lemma cancel_single_qubit_gates_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (cancel_single_qubit_gates l).
Proof.
  intros.
  eapply cancel_single_qubit_gates_respects_constraints.
  apply H.
  reflexivity. 
Qed.

Lemma cancel_two_qubit_gates_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (cancel_two_qubit_gates l).
Proof.
  intros.
  eapply cancel_two_qubit_gates_respects_constraints.
  apply H.
  reflexivity. 
Qed.
(* Changed to respectful_hadamard_reduction which doesn't use 3 *)(*
Lemma hadamard_reduction_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (hadamard_reduction l).
Proof.
Admitted.
                                                                   *)
Lemma hadamard_reduction_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (respectful_hadamard_reduction l).
Proof.
  intros. 
  eapply respectful_hadamard_reduction_respects_constraints.
  apply H. 
  reflexivity.
Qed. 


Lemma merge_rotations_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (merge_rotations l).
Proof.
  intros. 
  eapply merge_rotations_respects_constraints.
  apply H.
  reflexivity. 
Qed. 


Lemma not_propagation_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (not_propagation l).
Proof.
  intros.
  eapply not_propagation_respects_constraints_directed. 
  assumption.
Qed.

Search "LCR".

Lemma LCR_preserves_mapping : forall {dim} (p l c r : standard_ucom_l dim) (opt : standard_ucom_l dim -> standard_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX p ->
  (forall p, respects_constraints_directed is_in_graph U_CX p -> 
        respects_constraints_directed is_in_graph U_CX (opt p)) ->
  LCR p opt (fun n => @match_gate n) = Some (l, c, r) ->
  respects_constraints_directed is_in_graph U_CX l
    /\ respects_constraints_directed is_in_graph U_CX c
    /\ respects_constraints_directed is_in_graph U_CX r.
Proof.
Admitted.
