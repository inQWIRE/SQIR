Require Import GateCancellation.
Require Import HadamardReduction.
Require Import NotPropagation.
Require Import Optimize1qGates.
Require Import RotationMerging.
Require Import RzQGateSet.
Require Import SwapRoute.
Require Import MappingValidation.
Require Import GreedyLayout.
Require Import FullGateSet.
Import FullList.

Local Close Scope Q_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.

(** This file contains the VOQC transformations that are extracted to OCaml, 
   along with their correctness properties. The definitions and proofs in this 
   file are largely wrappers around definitions and proofs in other files. **)

Definition circ := full_ucom_l.

Definition layout := Layouts.layout.

Definition c_graph : Type := nat * (nat -> nat -> bool).
Definition graph_dim (cg : c_graph) := fst cg.
Definition is_in_graph (cg : c_graph) := snd cg.

(* Cast function changes the dependent type; it will be extracted to a no-op *)
Fixpoint cast {dim} (c : circ dim) dim' : @circ dim' := 
  match c with 
  | [] => []
  | App1 g m :: t => App1 g m :: cast t dim'
  | App2 g m n :: t => App2 g m n :: cast t dim'
  | App3 g m n p :: t => App3 g m n p :: cast t dim'
  end.

(** * Utility functions **)

Definition check_well_typed {dim} (c : circ dim) (n : nat) :=
  uc_well_typed_l_b n (cast c n).
Definition convert_to_ibm {dim} (c : circ dim) :=
  FullGateSet.convert_to_ibm c.
Definition convert_to_rzq {dim} (c : circ dim) :=
  FullGateSet.convert_to_rzq c.
Definition replace_rzq {dim} (c : circ dim) :=
  FullGateSet.replace_rzq c.
Definition decompose_to_cnot {dim} (c : circ dim) :=
  FullGateSet.decompose_to_cnot c.

Lemma check_well_typed_correct : forall {dim} (c : circ dim) n,
  check_well_typed c n = true <-> uc_well_typed_l (cast c n).
Proof. intros. apply uc_well_typed_l_b_equiv. Qed.

Lemma convert_to_ibm_preserves_semantics : forall {dim} (c : circ dim),
  (convert_to_ibm c =l= c)%ucom.
Proof. intros. apply FullGateSet.convert_to_ibm_sound. Qed.

Ltac show_preserves_WT H :=
  eapply uc_equiv_l_implies_WT;
  [ symmetry; apply H | assumption ].

Ltac show_preserves_WT_cong H :=
  eapply uc_cong_l_implies_WT;
  [ symmetry; apply H | assumption ].

Lemma convert_to_ibm_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (convert_to_ibm c).
Proof. intros dim c H. show_preserves_WT (convert_to_ibm_preserves_semantics c). Qed.

Lemma convert_to_ibm_preserves_mapping : forall {dim} (l : full_ucom_l dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX l ->
  respects_constraints_directed (is_in_graph cg) U_CX (convert_to_ibm l).
Proof. 
  intros. 
  apply FullGateSet.convert_to_ibm_preserves_mapping.
  assumption.
Qed.

Lemma convert_to_ibm_uses_ibm_gates : forall {dim} (c : circ dim),
  forall_gates only_ibm (convert_to_ibm c).
Proof. intros. apply FullGateSet.convert_to_ibm_gates. Qed.

Lemma convert_to_rzq_preserves_semantics : forall {dim} (c : circ dim),
  (convert_to_rzq c ≅l≅ c)%ucom.
Proof. intros. apply FullGateSet.convert_to_rzq_sound. Qed.

Lemma convert_to_rzq_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (convert_to_rzq c).
Proof. 
  intros dim c H. 
  show_preserves_WT_cong (convert_to_rzq_preserves_semantics c). 
Qed.

Lemma convert_to_rzq_preserves_mapping : forall {dim} (l : full_ucom_l dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX l ->
  respects_constraints_directed (is_in_graph cg) U_CX (convert_to_rzq l).
Proof. 
  intros. 
  apply FullGateSet.convert_to_rzq_preserves_mapping.
  assumption.
Qed.

Lemma convert_to_rzq_uses_rzq_gates : forall {dim} (c : circ dim),
  forall_gates only_rzq (convert_to_rzq c).
Proof. intros. apply FullGateSet.convert_to_rzq_gates. Qed.

Lemma replace_rzq_preserves_semantics : forall {dim} (c : circ dim),
  (replace_rzq c =l= c)%ucom.
Proof. intros. apply FullGateSet.replace_rzq_sound. Qed.

Lemma replace_rzq_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (replace_rzq c).
Proof. intros dim c H. show_preserves_WT (replace_rzq_preserves_semantics c). Qed.

Lemma replace_rzq_preserves_mapping : forall {dim} (l : full_ucom_l dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX l ->
  respects_constraints_directed (is_in_graph cg) U_CX (replace_rzq l).
Proof. 
  intros. 
  apply FullGateSet.replace_rzq_preserves_mapping.
  assumption.
Qed.

Lemma replace_rzq_does_not_use_rzq_gates : forall {dim} (c : circ dim),
  forall_gates no_rzq (replace_rzq c).
Proof. intros. apply FullGateSet.replace_rzq_gates. Qed.

Lemma decompose_to_cnot_preserves_semantics : forall {dim} (c : circ dim),
  (decompose_to_cnot c =l= c)%ucom.
Proof. intros. apply FullGateSet.decompose_to_cnot_sound. Qed.

Lemma decompose_to_cnot_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (decompose_to_cnot c).
Proof.
  intros dim c H.
  show_preserves_WT (decompose_to_cnot_preserves_semantics c).
Qed.

Lemma decompose_to_cnot_uses_cnot_gates : forall {dim} (c : circ dim),
  forall_gates only_cnots (decompose_to_cnot c).
Proof. intros. apply FullGateSet.decompose_to_cnot_gates. Qed.

Definition count_I {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 U_I _ => true | _ => false end) l).
Definition count_X {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 U_X _ => true | _ => false end) l).
Definition count_Y {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 U_Y _ => true | _ => false end) l).
Definition count_Z {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 U_Z _ => true | _ => false end) l).
Definition count_H {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 U_H _ => true | _ => false end) l).
Definition count_S {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 U_S _ => true | _ => false end) l).
Definition count_T {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 U_T _ => true | _ => false end) l).
Definition count_Sdg {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 U_Sdg _ => true | _ => false end) l).
Definition count_Tdg {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 U_Tdg _ => true | _ => false end) l).
Definition count_Rx {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 (U_Rx _) _ => true | _ => false end) l).
Definition count_Ry {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 (U_Ry _) _ => true | _ => false end) l).
Definition count_Rz {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 (U_Rz _) _ => true | _ => false end) l).
Definition count_Rzq {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 (U_Rzq _) _ => true | _ => false end) l).
Definition count_U1 {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 (U_U1 _) _ => true | _ => false end) l).
Definition count_U2 {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 (U_U2 _ _) _ => true | _ => false end) l).
Definition count_U3 {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 (U_U3 _ _ _) _ => true | _ => false end) l).
Definition count_CX {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App2 U_CX _ _ => true | _ => false end) l).
Definition count_CZ {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App2 U_CZ _ _ => true | _ => false end) l).
Definition count_SWAP {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App2 U_SWAP _ _ => true | _ => false end) l).
Definition count_CCX {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App3 U_CCX _ _ _ => true | _ => false end) l).
Definition count_CCZ {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App3 U_CCZ _ _ _ => true | _ => false end) l).

Definition count_1q {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App1 _ _ => true | _ => false end) l).
Definition count_2q {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App2 _ _ _ => true | _ => false end) l).
Definition count_3q {dim} (l : circ dim) :=
  length (filter (fun g => match g with | App3 _ _ _ _ => true | _ => false end) l).
Definition count_total {dim} (l : circ dim) := length l.

Definition count_rzq_clifford {dim} (l : circ dim) :=
  let f g := match g with
             | App1 (U_Rzq q) _ =>
                 let q' := RzQGateSet.bound q in
                 Qeq_bool q' zero_Q || Qeq_bool q' half_Q || 
                   Qeq_bool q' three_halves_Q || Qeq_bool q' one_Q
             | _ => false end in
  length (filter f l).

Ltac rewrite_count :=
  symmetry; rewrite cons_to_app; rewrite filter_app, app_length; reflexivity. 

Lemma count_1q_correct : forall {dim} (l : circ dim),
  count_1q l 
    = (count_I l + count_X l + count_Y l + count_Z l +
       count_H l + count_S l + count_T l + count_Sdg l + count_Tdg l +
       count_Rx l + count_Ry l + count_Rz l + count_Rzq l + 
       count_U1 l + count_U2 l + count_U3 l)%nat.
Proof.
  intros dim l.
  induction l; simpl.
  reflexivity.
  replace (count_1q (a :: l)) with (count_1q [a] + count_1q l) 
    by (unfold count_1q; rewrite_count).
  replace (count_I (a :: l)) with (count_I [a] + count_I l) 
    by (unfold count_I; rewrite_count).
  replace (count_X (a :: l)) with (count_X [a] + count_X l) 
    by (unfold count_X; rewrite_count).
  replace (count_Y (a :: l)) with (count_Y [a] + count_Y l) 
    by (unfold count_Y; rewrite_count).
  replace (count_Z (a :: l)) with (count_Z [a] + count_Z l) 
    by (unfold count_Z; rewrite_count).
  replace (count_H (a :: l)) with (count_H [a] + count_H l) 
    by (unfold count_H; rewrite_count).
  replace (count_S (a :: l)) with (count_S [a] + count_S l) 
    by (unfold count_S; rewrite_count).
  replace (count_T (a :: l)) with (count_T [a] + count_T l) 
    by (unfold count_T; rewrite_count).
  replace (count_Sdg (a :: l)) with (count_Sdg [a] + count_Sdg l) 
    by (unfold count_Sdg; rewrite_count).
  replace (count_Tdg (a :: l)) with (count_Tdg [a] + count_Tdg l) 
    by (unfold count_Tdg; rewrite_count).
  replace (count_Rx (a :: l)) with (count_Rx [a] + count_Rx l) 
    by (unfold count_Rx; rewrite_count).
  replace (count_Ry (a :: l)) with (count_Ry [a] + count_Ry l) 
    by (unfold count_Ry; rewrite_count).
  replace (count_Rz (a :: l)) with (count_Rz [a] + count_Rz l) 
    by (unfold count_Rz; rewrite_count).
  replace (count_Rzq (a :: l)) with (count_Rzq [a] + count_Rzq l) 
    by (unfold count_Rzq; rewrite_count).
  replace (count_U1 (a :: l)) with (count_U1 [a] + count_U1 l) 
    by (unfold count_U1; rewrite_count).
  replace (count_U2 (a :: l)) with (count_U2 [a] + count_U2 l) 
    by (unfold count_U2; rewrite_count).
  replace (count_U3 (a :: l)) with (count_U3 [a] + count_U3 l) 
    by (unfold count_U3; rewrite_count).
  rewrite IHl. clear.
  repeat rewrite Nat.add_assoc.
  repeat rewrite (Nat.add_comm _ (_ [a])).
  repeat rewrite Nat.add_assoc.
  do 16 (apply f_equal2; auto).
  destruct a; dependent destruction f; reflexivity.
Qed.

Lemma count_2q_correct : forall {dim} (l : circ dim),
  count_2q l 
    = (count_CX l + count_CZ l + count_SWAP l)%nat.
Proof.
  intros dim l.
  induction l; simpl.
  reflexivity.
  replace (count_2q (a :: l)) with (count_2q [a] + count_2q l) 
    by (unfold count_2q; rewrite_count).
  replace (count_CX (a :: l)) with (count_CX [a] + count_CX l) 
    by (unfold count_CX; rewrite_count).
  replace (count_CZ (a :: l)) with (count_CZ [a] + count_CZ l) 
    by (unfold count_CZ; rewrite_count).
  replace (count_SWAP (a :: l)) with (count_SWAP [a] + count_SWAP l) 
    by (unfold count_SWAP; rewrite_count).
  rewrite IHl. clear.
  repeat rewrite Nat.add_assoc.
  repeat rewrite (Nat.add_comm _ (_ [a])).
  repeat rewrite Nat.add_assoc.
  do 3 (apply f_equal2; auto).
  destruct a; dependent destruction f; reflexivity.
Qed.

Lemma count_3q_correct : forall {dim} (l : circ dim),
  count_3q l 
    = (count_CCX l + count_CCZ l)%nat.
Proof.
  intros dim l.
  induction l; simpl.
  reflexivity.
  replace (count_3q (a :: l)) with (count_3q [a] + count_3q l) 
    by (unfold count_3q; rewrite_count).
  replace (count_CCX (a :: l)) with (count_CCX [a] + count_CCX l) 
    by (unfold count_CCX; rewrite_count).
  replace (count_CCZ (a :: l)) with (count_CCZ [a] + count_CCZ l) 
    by (unfold count_CCZ; rewrite_count).
  rewrite IHl. clear.
  repeat rewrite Nat.add_assoc.
  repeat rewrite (Nat.add_comm _ (_ [a])).
  repeat rewrite Nat.add_assoc.
  do 2 (apply f_equal2; auto).
  destruct a; dependent destruction f; reflexivity.
Qed.

Lemma count_total_correct : forall {dim} (l : circ dim),
  count_total l = (count_1q l + count_2q l + count_3q l)%nat.
Proof.
  intros dim l.
  induction l; simpl.
  reflexivity.
  replace (count_1q (a :: l)) with (count_1q [a] + count_1q l) 
    by (unfold count_1q; rewrite_count).
  replace (count_2q (a :: l)) with (count_2q [a] + count_2q l) 
    by (unfold count_2q; rewrite_count).
  replace (count_3q (a :: l)) with (count_3q [a] + count_3q l) 
    by (unfold count_3q; rewrite_count).
  rewrite IHl. clear.
  destruct a; dependent destruction f; simpl; lia.
Qed.

(** * IBM gate set optimizations **)

Definition optimize_ibm {dim} (c : circ dim) : circ dim :=
  IBM_to_full (Optimize1qGates.optimize_1q_gates (full_to_IBM c)).

Lemma optimize_ibm_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (optimize_ibm c ≅l≅ c)%ucom.
Proof. 
  intros dim c H.
  unfold optimize_ibm.
  erewrite IBM_to_full_cong.
  apply uc_equiv_cong_l.
  apply IBM_to_full_inv.
  apply Optimize1qGates.optimize_1q_gates_sound.
  apply FullGateSet.full_to_IBM_WT.
  assumption.
Qed.

Lemma optimize_ibm_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (optimize_ibm c).
Proof.
  intros dim c H.
  show_preserves_WT_cong (optimize_ibm_preserves_semantics c H).
Qed.

Lemma optimize_ibm_preserves_mapping : forall {dim} (c : circ dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX c -> 
  respects_constraints_directed (is_in_graph cg) U_CX (optimize_ibm c).
Proof. 
  intros. 
  apply IBM_to_full_preserves_mapping.
  apply Optimize1qGates.optimize_1q_gates_respects_constraints.
  apply full_to_IBM_preserves_mapping.
  assumption.
Qed.

(** * RzQ gate set optimizations **)

Definition not_propagation {dim} (c : circ dim) : circ dim :=
  RzQ_to_full (NotPropagation.not_propagation (full_to_RzQ c)).

Definition hadamard_reduction {dim} (c : circ dim) : circ dim :=
  RzQ_to_full (HadamardReduction.hadamard_reduction (full_to_RzQ c)).

Definition cancel_single_qubit_gates {dim} (c : circ dim) : circ dim :=
  RzQ_to_full (GateCancellation.cancel_single_qubit_gates (full_to_RzQ c)).

Definition cancel_two_qubit_gates {dim} (c : circ dim) : circ dim :=
  RzQ_to_full (GateCancellation.cancel_two_qubit_gates (full_to_RzQ c)).

Definition merge_rotations {dim} (c : circ dim) : circ dim :=
  RzQ_to_full (RotationMerging.merge_rotations (full_to_RzQ c)).

(* optimize_nam function applies our optimizations in the following order,
   as designed by Nam et al. :
   0, 1, 3, 2, 3, 1, 2, 4, 3, 2 
   
   0 - not propagation
   1 - hadamard reduction
   2 - single qubit gate cancellation
   3 - two qubit gate cancellation
   4 - rotation merging *) 

Definition optimize_nam {dim} (c : circ dim) : circ dim :=
  RzQ_to_full
    (GateCancellation.cancel_single_qubit_gates 
      (GateCancellation.cancel_two_qubit_gates 
        (RotationMerging.merge_rotations
          (GateCancellation.cancel_single_qubit_gates 
            (HadamardReduction.hadamard_reduction 
              (GateCancellation.cancel_two_qubit_gates 
                (GateCancellation.cancel_single_qubit_gates 
                  (GateCancellation.cancel_two_qubit_gates 
                    (HadamardReduction.hadamard_reduction 
                      (NotPropagation.not_propagation 
                        (full_to_RzQ c))))))))))). 

(* Light version of the optimizer that excludes rotation merging
   (used for evaluating on QFT & adder programs). *)
Definition optimize_nam_light {dim} (c : circ dim) : circ dim :=
  RzQ_to_full
    (GateCancellation.cancel_single_qubit_gates 
      (HadamardReduction.hadamard_reduction 
        (GateCancellation.cancel_two_qubit_gates 
          (GateCancellation.cancel_single_qubit_gates 
            (GateCancellation.cancel_two_qubit_gates 
              (HadamardReduction.hadamard_reduction 
                (NotPropagation.not_propagation 
                  (full_to_RzQ c)))))))).

(* LCR optimizer for multiple iterations. *)
Definition optimize_nam_lcr {dim} (c : circ dim) : option (circ dim * circ dim * circ dim) :=
  LCR c optimize_nam (fun n => @match_gate n).

Lemma cancel_single_qubit_gates_sound' : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> RzQList.uc_cong_l (GateCancellation.cancel_single_qubit_gates l) l.
Proof. 
  intros. apply RzQList.uc_equiv_cong_l. 
  apply GateCancellation.cancel_single_qubit_gates_sound. assumption. 
Qed.

Lemma cancel_two_qubit_gates_sound' : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> RzQList.uc_cong_l (GateCancellation.cancel_two_qubit_gates l) l.
Proof. 
  intros. apply RzQList.uc_equiv_cong_l. 
  apply GateCancellation.cancel_two_qubit_gates_sound. assumption. 
Qed.

Lemma merge_rotations_sound' : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> RzQList.uc_cong_l (RotationMerging.merge_rotations l) l.
Proof. 
  intros. apply RzQList.uc_equiv_cong_l. 
  apply RotationMerging.merge_rotations_sound. assumption.
Qed.

Ltac show_preserves_semantics_nam :=
  unfold not_propagation, hadamard_reduction, cancel_single_qubit_gates, cancel_two_qubit_gates, merge_rotations, optimize_nam, optimize_nam_light;
  erewrite RzQ_to_full_cong;
  [ apply RzQ_to_full_inv 
  | repeat (try rewrite NotPropagation.not_propagation_sound;
            try rewrite HadamardReduction.hadamard_reduction_sound;
            try rewrite cancel_single_qubit_gates_sound';
            try rewrite cancel_two_qubit_gates_sound';
            try rewrite merge_rotations_sound';
            try apply FullGateSet.full_to_RzQ_WT;
            try apply NotPropagation.not_propagation_WT;
            try apply HadamardReduction.hadamard_reduction_WT;
            try apply GateCancellation.cancel_single_qubit_gates_WT;
            try apply GateCancellation.cancel_two_qubit_gates_WT;
            try apply RotationMerging.merge_rotations_WT;
            try assumption; try reflexivity) ].

Lemma not_propagation_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (not_propagation c ≅l≅ c)%ucom.
Proof. intros. show_preserves_semantics_nam. Qed.

Lemma not_propagation_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (not_propagation c).
Proof.
  intros dim c H.
  show_preserves_WT_cong (not_propagation_preserves_semantics c H).
Qed.

Ltac show_preserves_mapping_nam :=
  unfold not_propagation, hadamard_reduction, cancel_single_qubit_gates, cancel_two_qubit_gates, merge_rotations, optimize_nam, optimize_nam_light;
  repeat (try apply RzQ_to_full_preserves_mapping;
          try apply NotPropagation.not_propagation_respects_constraints;
          try apply HadamardReduction.hadamard_reduction_respects_constraints;
          try apply GateCancellation.cancel_single_qubit_gates_respects_constraints;
          try apply GateCancellation.cancel_two_qubit_gates_respects_constraints;
          try apply RotationMerging.merge_rotations_respects_constraints;
          try apply full_to_RzQ_preserves_mapping;
          try assumption).

Lemma not_propagation_preserves_mapping : forall {dim} (c : circ dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX c -> 
  respects_constraints_directed (is_in_graph cg) U_CX (not_propagation c).
Proof. intros. show_preserves_mapping_nam. Qed.

Lemma hadamard_reduction_preserves_semantics : forall {dim} (c : circ dim),
  (hadamard_reduction c ≅l≅ c)%ucom.
Proof. intros. show_preserves_semantics_nam. Qed.

Lemma hadamard_reduction_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (hadamard_reduction c).
Proof.
  intros dim c H.
  show_preserves_WT_cong (hadamard_reduction_preserves_semantics c).
Qed.

Lemma hadamard_reduction_preserves_mapping : forall {dim} (c : circ dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX c -> 
  respects_constraints_directed (is_in_graph cg) U_CX (hadamard_reduction c).
Proof. intros. show_preserves_mapping_nam. Qed.

Lemma cancel_single_qubit_gates_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (cancel_single_qubit_gates c ≅l≅ c)%ucom.
Proof. intros. show_preserves_semantics_nam. Qed.

Lemma cancel_single_qubit_gates_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (cancel_single_qubit_gates c).
Proof.
  intros dim c H.
  show_preserves_WT_cong (cancel_single_qubit_gates_preserves_semantics c H).
Qed.

Lemma cancel_single_qubit_gates_preserves_mapping : forall {dim} (c : circ dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX c -> 
  respects_constraints_directed (is_in_graph cg) U_CX (cancel_single_qubit_gates c).
Proof. intros. show_preserves_mapping_nam. Qed.

Lemma cancel_two_qubit_gates_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (cancel_two_qubit_gates c ≅l≅ c)%ucom.
Proof. intros. show_preserves_semantics_nam. Qed.

Lemma cancel_two_qubit_gates_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (cancel_two_qubit_gates c).
Proof.
  intros dim c H.
  show_preserves_WT_cong (cancel_two_qubit_gates_preserves_semantics c H).
Qed.

Lemma cancel_two_qubit_gates_preserves_mapping : forall {dim} (c : circ dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX c -> 
  respects_constraints_directed (is_in_graph cg) U_CX (cancel_two_qubit_gates c).
Proof. intros. show_preserves_mapping_nam. Qed.

Lemma merge_rotations_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (merge_rotations c ≅l≅ c)%ucom.
Proof. intros. show_preserves_semantics_nam. Qed.

Lemma merge_rotations_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (merge_rotations c).
Proof.
  intros dim c H.
  show_preserves_WT_cong (merge_rotations_preserves_semantics c H).
Qed.

Lemma merge_rotations_preserves_mapping : forall {dim} (c : circ dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX c -> 
  respects_constraints_directed (is_in_graph cg) U_CX (merge_rotations c).
Proof. intros. show_preserves_mapping_nam. Qed.

Lemma optimize_nam_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (optimize_nam c ≅l≅ c)%ucom.
Proof. intros. show_preserves_semantics_nam. Qed.

Lemma optimize_nam_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (optimize_nam c).
Proof.
  intros dim c H.
  show_preserves_WT_cong (optimize_nam_preserves_semantics c H).
Qed.

Lemma optimize_nam_preserves_mapping : forall {dim} (c : circ dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX c -> 
  respects_constraints_directed (is_in_graph cg) U_CX (optimize_nam c).
Proof. intros. show_preserves_mapping_nam. Qed.

Lemma optimize_nam_light_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (optimize_nam_light c ≅l≅ c)%ucom.
Proof. intros. show_preserves_semantics_nam. Qed.

Lemma optimize_nam_light_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (optimize_nam_light c).
Proof.
  intros dim c H.
  show_preserves_WT_cong (optimize_nam_light_preserves_semantics c H).
Qed.

Lemma optimize_nam_light_preserves_mapping : forall {dim} (c : circ dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX c -> 
  respects_constraints_directed (is_in_graph cg) U_CX (optimize_nam_light c).
Proof. intros. show_preserves_mapping_nam. Qed.

Lemma optimize_nam_lcr_preserves_semantics : forall {dim} (c0 l c r : circ dim) n,
  n > 2 -> uc_well_typed_l c0 -> 
  optimize_nam_lcr c0 = Some (l, c, r) ->
  (niter c0 n ≅l≅ (l ++ (niter c (n - 2)) ++ r))%ucom.
Proof. 
  intros dim c0 l c r n Hn WT H.
  eapply LCR_correct in H.
  apply H.
  all: try assumption.
  apply optimize_nam_preserves_semantics.
  apply optimize_nam_preserves_WT.
Qed.

Lemma niter_WT : forall {dim} (c : circ dim) n,
  uc_well_typed_l c -> uc_well_typed_l (niter c n).
Proof.
  intros dim c n WT.
  induction n.
  constructor.
  eapply uc_well_typed_l_implies_dim_nonzero.
  apply WT.
  simpl.
  apply uc_well_typed_l_app; split; assumption.
Qed.

Lemma niter_WT_inv : forall {dim} (c : circ dim) n,
  n > 0 -> uc_well_typed_l (niter c n) -> uc_well_typed_l c.
Proof.
  intros dim c n Hn WT.
  destruct n; try lia.
  induction n; simpl in WT.
  rewrite app_nil_r in WT.
  assumption.
  apply IHn; try lia.
  simpl.
  apply uc_well_typed_l_app in WT as [_ WT].
  assumption.
Qed.

Lemma optimize_nam_lcr_preserves_WT : forall {dim} (c0 l c r : circ dim) n,
  n > 2 -> uc_well_typed_l c0 -> 
  optimize_nam_lcr c0 = Some (l, c, r) ->
  uc_well_typed_l l /\ uc_well_typed_l c /\ uc_well_typed_l r.
Proof.
  intros dim c0 l c r n Hn WT H.
  apply optimize_nam_lcr_preserves_semantics with (n0:=n) in H; try assumption.
  apply uc_cong_l_implies_WT in H.
  apply uc_well_typed_l_app in H as [H1 H23].
  apply uc_well_typed_l_app in H23 as [H2 H3].
  repeat split; try assumption.
  apply niter_WT_inv with (n0:=n-2).
  lia. apply H2.
  apply niter_WT.
  assumption.
Qed.

Lemma optimize_nam_lcr_preserves_mapping : forall {dim} (c0 l c r : circ dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX c0 -> 
  optimize_nam_lcr c0 = Some (l, c, r) ->
  respects_constraints_directed (is_in_graph cg) U_CX l
    /\ respects_constraints_directed (is_in_graph cg) U_CX c
    /\ respects_constraints_directed (is_in_graph cg) U_CX r.
Proof. 
  intros dim c0 l c r cg Hcg H.
  eapply MappingConstraints.LCR_respects_constraints in H as [H0 [H1 H2]].
  repeat split. 
  apply H0. apply H2. apply H1.
  intros.
  apply optimize_nam_preserves_mapping.
  assumption.
  assumption.
Qed.

(** * Full 'optimize' function *)

Definition optimize {dim} (c : circ dim) : circ dim :=
  optimize_ibm (optimize_nam c).

Lemma optimize_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (optimize c ≅l≅ c)%ucom.
Proof. 
  intros dim c H.
  unfold optimize.
  rewrite optimize_ibm_preserves_semantics.
  apply optimize_nam_preserves_semantics.
  assumption.
  apply optimize_nam_preserves_WT.
  assumption.
Qed.

Lemma optimize_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (optimize c).
Proof.
  intros dim c H.
  show_preserves_WT_cong (optimize_preserves_semantics c H).
Qed.

Lemma optimize_preserves_mapping : forall {dim} (c : circ dim) (cg : c_graph),
  respects_constraints_directed (is_in_graph cg) U_CX c -> 
  respects_constraints_directed (is_in_graph cg) U_CX (optimize c).
Proof. 
  intros. 
  apply optimize_ibm_preserves_mapping.
  apply optimize_nam_preserves_mapping.
  assumption.
Qed.

(** * Circuit mapping **)

Definition swap_route {dim} (c : circ dim) (lay : layout) (cg : c_graph) (get_path : nat -> nat -> list nat) :=
  let n := graph_dim cg in
  let (c,_) := SwapRoute.swap_route (full_to_map (cast c n)) lay get_path in
  map_to_full c.
  
Definition decompose_swaps {dim} (c : circ dim) (cg : c_graph) :=
  map_to_full (SwapRoute.decompose_swaps_and_cnots (full_to_map c) (is_in_graph cg)).

Definition trivial_layout n : layout := Layouts.trivial_layout n.
Definition check_list l : bool := Layouts.check_list l.
Definition list_to_layout l : layout := Layouts.list_to_layout l.
Definition layout_to_list (lay : layout) n : list nat := 
  map (fun ox => match ox with Some x => x | _ => O end) (Layouts.layout_to_list n lay).
Definition greedy_layout {dim} (c : circ dim) (cg : c_graph) (get_nearby : nat -> list nat) (qubit_ordering : list nat) : layout :=
  GreedyLayout.greedy_layout (full_to_map c) (graph_dim cg) 
                             get_nearby qubit_ordering.

Definition beq_tup t t' := 
  match t, t' with
  | (n1, n2), (n1', n2') => (n1 =? n1') && (n2 =? n2')
  end.

Definition c_graph_from_coupling_map (n : nat) (cmap : list (nat * nat)) : c_graph :=
  (n, fun n1 n2 => existsb (beq_tup (n1, n2)) cmap).

Definition make_lnn n : c_graph := (n, LNN.is_in_graph n).

(*
Definition make_tenerife (_:unit) : c_graph := (5, Tenerife.is_in_graph).
Definition make_lnn_ring n : c_graph := (n, LNNRing.is_in_graph n).
Definition make_grid m n : c_graph := (m * n, Grid.is_in_graph m n).
*)

Module SRP := SwapRouteProofs FullGateSet.
Import SRP.

Definition get_path_valid (cg : c_graph) (get_path : nat -> nat -> list nat) :=
  ConnectivityGraph.get_path_valid (fst cg) get_path (snd cg).

Lemma eval_full_to_map : forall {dim} (c : circ dim),
  MapList.eval (full_to_map c) = eval c.
Proof. Admitted.

Lemma swap_route_preserves_semantics : forall {dim} (c : circ dim) (lay : layout) (cg : c_graph) (get_path : nat -> nat -> list nat),
  let n := graph_dim cg in
  uc_well_typed_l (cast c n) ->
  layout_bijective n lay ->
  get_path_valid cg get_path ->
  cast c n ≡x swap_route c lay cg get_path.
Proof. 
  intros dim c lay cg get_path n WT WF Hpath.
  subst n.
  unfold swap_route.
  destruct (SwapRoute.swap_route (full_to_map (cast c (graph_dim cg))) lay get_path) eqn:sr.
  assert (srWF:=sr).
  apply SRP.swap_route_WF in srWF; auto.
  apply SRP.swap_route_sound in sr; auto.
  unfold uc_equiv_perm_ex in sr.
  unfold uc_equiv_perm.
  exists (get_log lay). exists (get_phys l).
  repeat split.
  apply get_log_perm. assumption.
  apply get_phys_perm. assumption.

admit.

  apply full_to_map_WT. assumption.
  intros n1 n2 Hn1 Hn2 Hneq.
  destruct (Hpath n1 n2 Hn1 Hn2 Hneq) as [_ [_ [_ [H _]]]].
  apply H.
  apply full_to_map_WT. assumption.
  intros n1 n2 Hn1 Hn2 Hneq.
  destruct (Hpath n1 n2 Hn1 Hn2 Hneq) as [_ [_ [_ [H _]]]].
  apply H.
Admitted.

(*
Lemma swap_route_preserves_WT : forall {dim} (c : circ dim) (lay : layout),
  uc_well_typed_l (cast c (graph_dim cg)) ->
  layout_bijective (graph_dim cg) lay ->
  uc_well_typed_l (swap_route c lay cg).
Proof. 
  intros dim c lay WT WF. 
  specialize (swap_route_preserves_semantics _ _ WT WF) as H.
  destruct H as [p1 [p2 [Hp1 [Hp2 H]]]].
  apply list_to_ucom_WT. 
  apply uc_eval_nonzero_iff.
  apply list_to_ucom_WT in WT.
  apply uc_eval_nonzero_iff in WT.
  intro contra.
  unfold eval in H.
  rewrite contra in H.
  rewrite Mmult_0_r, Mmult_0_l in H.
  contradiction.
Qed.

Lemma swap_route_respects_constraints_undirected : forall {dim} (c : circ dim) (lay : layout),
    uc_well_typed_l (cast c (graph_dim cg)) ->
    layout_bijective (graph_dim cg) lay ->
    respects_constraints_undirected (is_in_graph cg) (swap_route c lay cg).
Proof.
  intros dim c lay WT WF.
  unfold swap_route.
  destruct (SwapRoute.swap_route (full_to_map (cast c (graph_dim cg))) lay (get_path cg)) eqn:sr.
Admitted.
*)

(*
  Lemma decompose_swaps_preserves_semantics : forall {dim} (c : circ dim),

  Lemma decompose_swaps_WT : forall {dim} (c : circ dim),

  Lemma decompose_swaps_respects_constraints : forall {dim} (c : circ dim),
*)

Lemma trivial_layout_well_formed : forall n, layout_bijective n (trivial_layout n).
Proof. intros. apply Layouts.trivial_layout_bijective. Qed.

Lemma list_to_layout_well_formed : forall l, 
  check_list l = true -> layout_bijective (length l) (list_to_layout l).
Proof. intros l H. apply Layouts.check_list_layout_bijective. auto. Qed.

Lemma greedy_layout_well_formed : forall {dim} (c : circ dim) (cg : c_graph) (get_nearby : nat -> list nat) (qubit_ordering : list nat), 
  layout_bijective (graph_dim cg) (greedy_layout c cg get_nearby qubit_ordering).
Proof. intros. apply GreedyLayout.greedy_layout_bijective. Qed.

(** * Mapping validation **)

Definition remove_swaps {dim} (c : circ dim) (lay : layout) :=
  let (c,_) := MappingValidation.remove_swaps (full_to_map c) lay in
  map_to_full c.

Definition check_swap_equivalence {dim} (c1 c2 : circ dim) (lay1 lay2 : layout) :=
  MappingValidation.is_swap_equivalent (full_to_map c1) (full_to_map c2) lay1 lay2
    (fun n => @MappingGateSet.match_gate (FullGateSet.U 1) n FullGateSet.match_gate).

Definition check_constraints {dim} (c : circ dim) (cg : c_graph) :=
  MappingValidation.check_constraints (full_to_map c) (is_in_graph cg).

Lemma remove_swaps_preserves_semantics : forall {dim} (c : circ dim) (lay : layout),
  uc_well_typed_l c -> 
  layout_bijective dim lay ->
  remove_swaps c lay ≡x c.
Proof. 
  intros dim c lay WT WF. 
  unfold remove_swaps.
  destruct (MappingValidation.remove_swaps (full_to_map c) lay) eqn:rs.
Admitted.

Lemma remove_swaps_preserves_WT : forall {dim} (c : circ dim) (lay : layout),
  uc_well_typed_l c -> 
  layout_bijective dim lay ->
  uc_well_typed_l (remove_swaps c lay).
Proof.
Admitted.

Lemma check_swap_equivalence_correct : forall dim (c1 c2 : circ dim) (lay1 lay2 : layout),
  check_swap_equivalence c1 c2 lay1 lay2 = true ->
  c1 ≡x c2.
Proof.
Admitted.

Lemma check_constraints_correct : forall dim (c : circ dim) (cg : c_graph),
  check_constraints c cg = true ->
  respects_constraints_directed (is_in_graph cg) U_CX (cast c (graph_dim cg)).
Proof. 
  intros dim c cg H. 
Admitted.

(** * Examples of verified composition of transformations **)

Definition optimize_then_map {dim} (c : circ dim) :=
  let cg := make_lnn 10 in            (* 10-qubit LNN architecture *)
  if check_well_typed c 10            (* check c is well-typed & uses <=10 qubits *)
  then 
    let lay := greedy_layout c cg     (* greedy layout *)
               (LNN.get_nearby 10)
               (LNN.qubit_ordering 10) in
    let c1 := optimize_nam c in       (* optimization #1 *)
    let c2 := optimize_ibm c1 in      (* optimization #2 *)
    Some (swap_route c2 lay cg        (* map *)
                     LNN.get_path)
  else None.

Definition map_then_optimize {dim} (c : circ dim) :=
  let cg := make_lnn 10 in            (* 10-qubit LNN architecture *)
  if check_well_typed c 10            (* check c is well-typed & uses <=10 qubits *)
  then 
    let lay := greedy_layout c cg     (* greedy layout *)
               (LNN.get_nearby 10)
               (LNN.qubit_ordering 10) in
    let c1 := swap_route c lay cg     (* map *)
                         LNN.get_path in
    let c2 := optimize_nam c1 in      (* optimization #1 *)
    Some (optimize_ibm c2)            (* optimization #2 *)
  else None.

(*

Lemma cast_same : forall {dim} (c : circ dim), cast c dim = c.
Proof. 
  intros dim c. 
  induction c. 
  reflexivity. 
  simpl. 
  destruct a; rewrite IHc; reflexivity.
Qed.

Lemma optimize_then_map_preserves_semantics : forall (c : circ 10) c' la',
  optimize_then_map c = Some (c', la') -> 
  c ≅ c' with (@phys2log dim (trivial_layout 10)) and (log2phys la').
Proof.
  intros c c' la' H.
  unfold optimize_then_map in H.
  destruct (check_well_typed c 10) eqn:WT; inversion H.
  apply check_well_typed_correct in WT.
  rewrite cast_same in WT.
  clear H.
  apply swap_route_sound in H1.
  all: unfold get_dim, make_lnn in *; simpl fst in *.
  apply uc_eq_perm_uc_cong_l with (l2:=cast (optimize_ibm (optimize_nam c)) 10).
  rewrite cast_same.
  rewrite optimize_ibm_preserves_semantics.
  rewrite optimize_nam_preserves_semantics.
  reflexivity.
  assumption.
  apply optimize_nam_preserves_WT.
  assumption.
  rewrite cast_layout_same in H1.
  apply uc_eq_perm_implies_uc_cong_perm.
  apply H1.
  rewrite cast_same.
  apply optimize_ibm_preserves_WT.
  apply optimize_nam_preserves_WT.
  assumption.
  rewrite cast_layout_same.
  apply trivial_layout_well_formed.
Qed.

Lemma optimize_then_map_respects_constraints : forall (c : circ 10) c' la',
  optimize_then_map c = Some (c', la') -> 
  respects_constraints_directed LNN10.is_in_graph U_CX c'.
Proof.
  intros c c' la' H.
  unfold optimize_then_map in H.
  destruct (check_well_typed c 10) eqn:WT; inversion H.
  apply check_well_typed_correct in WT.
  rewrite cast_same in WT.
  clear H. 
  eapply swap_route_respects_constraints_directed; try apply H1.
  all: unfold get_dim, make_lnn; simpl fst.
  rewrite cast_same.
  apply optimize_ibm_preserves_WT.
  apply optimize_nam_preserves_WT.
  assumption.
  rewrite cast_layout_same.
  apply trivial_layout_well_formed.
Qed.

Lemma map_then_optimize_preserves_semantics : forall (c : circ 10) c' la',
  map_then_optimize c = Some (c', la') -> 
  c ≅ c' with (@phys2log dim (trivial_layout 10)) and (log2phys la').
Proof.
  intros c c' la' H.
  unfold map_then_optimize in H.
  destruct (check_well_typed c 10) eqn:WT; inversion H.
  apply check_well_typed_correct in WT.
  rewrite cast_same in WT.
  clear H.
  destruct (swap_route c (trivial_layout 10) (make_lnn 10)) eqn:res.
  inversion H1; subst; clear H1.
  assert (WTs:=res).
  apply swap_route_WT in WTs.
  apply swap_route_sound in res.
  all: unfold get_dim, make_lnn in *; simpl fst in *.
  rewrite cast_same, cast_layout_same in res.
  apply uc_eq_perm_uc_cong_l_alt with (l2:=f).
  apply uc_eq_perm_implies_uc_cong_perm.
  apply res.
  rewrite optimize_ibm_preserves_semantics.
  rewrite optimize_nam_preserves_semantics.
  reflexivity.
  assumption.
  apply optimize_nam_preserves_WT.
  assumption.
  rewrite cast_same.
  assumption.
  rewrite cast_layout_same.
  apply trivial_layout_well_formed.
  rewrite cast_same.
  assumption.
  rewrite cast_layout_same.
  apply trivial_layout_well_formed.
Qed.

Lemma map_then_optimize_respects_constraints : forall (c : circ 10) c' la',
  map_then_optimize c = Some (c', la') -> 
  respects_constraints_directed LNN10.is_in_graph U_CX c'.
Proof.
  intros c c' la' H.
  unfold map_then_optimize in H.
  destruct (check_well_typed c 10) eqn:WT; inversion H.
  apply check_well_typed_correct in WT.
  rewrite cast_same in WT.
  clear H. 
  destruct (swap_route c (trivial_layout 10) (make_lnn 10)) eqn:res.
  inversion H1; subst; clear H1.
  apply swap_route_respects_constraints_directed in res.
  replace LNN10.is_in_graph with (get_is_in_graph (make_lnn 10)) by reflexivity.
  apply optimize_ibm_preserves_mapping.
  apply optimize_nam_preserves_mapping.
  simpl. assumption. 
  rewrite cast_same.
  assumption.
  rewrite cast_layout_same.
  apply trivial_layout_well_formed.
Qed.
*)
