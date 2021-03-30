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

(*** @Aaron ***)

Lemma cx_cancellation_preserves_mapping : forall {dim} (l : IBM_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph UIBM_CNOT l ->
  respects_constraints_directed is_in_graph UIBM_CNOT (cx_cancellation l).
Proof.
Admitted.

Lemma optimize_1q_gates_preserves_mapping : forall {dim} (l : IBM_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph UIBM_CNOT l ->
  respects_constraints_directed is_in_graph UIBM_CNOT (optimize_1q_gates l).
Proof.
Admitted.

Lemma cancel_single_qubit_gates_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (cancel_single_qubit_gates l).
Proof.
Admitted.

Lemma cancel_two_qubit_gates_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (cancel_two_qubit_gates l).
Proof.
Admitted.

Lemma hadamard_reduction_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (hadamard_reduction l).
Proof.
Admitted.

Lemma merge_rotations_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (merge_rotations l).
Proof.
Admitted.

Lemma not_propagation_preserves_mapping : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (not_propagation l).
Proof.
Admitted.

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
