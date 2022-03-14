Require Import CXCancellation.
Require Import GateCancellation.
Require Import HadamardReduction.
Require Import NotPropagation.
Require Import Optimize1qGates.
Require Import RotationMerging.
Require Import RzQGateSet.
Require Import SimpleMapping.
Require Import FullGateSet.
Import FullList.

Local Close Scope Q_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.


(** This file contains the VOQC transformations that are extracted to OCaml, 
   along with their correctness properties. The definitions and proofs in this 
   file are largely wrappers around other definitions and proofs. **)

Definition circ := full_ucom_l.
Inductive gate_counts : Set :=
  | BuildCounts : nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> 
                  nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> gate_counts.
Definition layout := qmap.
Definition c_graph : Type := nat * (nat -> nat -> list nat) * (nat -> nat -> bool).
Definition get_dim (cg : c_graph) := fst (fst cg).
Definition get_get_path (cg : c_graph) := snd (fst cg).
Definition get_is_in_graph (cg : c_graph) := snd cg.
(* Cast functions change dependent types --> will be extracted to no-ops *)
Fixpoint cast {dim} (c : circ dim) dim' : @circ dim' := 
  match c with 
  | [] => []
  | App1 g m :: t => App1 g m :: cast t dim'
  | App2 g m n :: t => App2 g m n :: cast t dim'
  | App3 g m n p :: t => App3 g m n p :: cast t dim'
  end.
Definition cast_layout {dim} (la : layout dim) dim' : layout dim' := la.


(** Utility functions **)

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

Lemma convert_to_ibm_preserves_mapping : forall {dim} (l : full_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph U_CX (convert_to_ibm l).
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

Lemma convert_to_rzq_preserves_mapping : forall {dim} (l : full_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph U_CX (convert_to_rzq l).
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

Lemma replace_rzq_preserves_mapping : forall {dim} (l : full_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph U_CX l ->
  respects_constraints_directed is_in_graph U_CX (replace_rzq l).
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

(* Functions for counting gates *)
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

Definition count_gates {dim} (l : circ dim) :=
  BuildCounts (count_I l) (count_X l) (count_Y l) (count_Z l)
     (count_H l) (count_S l) (count_T l) (count_Sdg l) (count_Tdg l)
     (count_Rx l) (count_Ry l) (count_Rz l) (count_Rzq l)
     (count_U1 l) (count_U2 l) (count_U3 l)
     (count_CX l) (count_CZ l) (count_SWAP l)
     (count_CCX l) (count_CCZ l).

Definition total_gate_count {dim} (l : circ dim) := length l.

Definition count_clifford_rzq {dim} (l : circ dim) :=
  let f g := match g with
             | App1 (U_Rzq q) _ =>
                 let q' := RzQGateSet.bound q in
                 Qeq_bool q' zero_Q || Qeq_bool q' half_Q || 
                   Qeq_bool q' three_halves_Q || Qeq_bool q' one_Q
             | _ => false end in
  length (filter f l).

Definition scale_count (gc : gate_counts) n0 :=
  let (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u) := gc in
  BuildCounts (n0*a) (n0*b) (n0*c) (n0*d) (n0*e) (n0*f) (n0*g) 
              (n0*h) (n0*i) (n0*j) (n0*k) (n0*l) (n0*m) (n0*n) 
              (n0*o) (n0*p) (n0*q) (n0*r) (n0*s) (n0*t) (n0*u).

Definition add_counts (gc gc' : gate_counts) :=
  let (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u) := gc in
  let (a',b',c',d',e',f',g',h',i',j',k',l',m',n',o',p',q',r',s',t',u') := gc' in
  BuildCounts (a+a') (b+b') (c+c') (d+d') (e+e') (f+f') (g+g') 
              (h+h') (i+i') (j+j') (k+k') (l+l') (m+m') (n+n') 
              (o+o') (p+p') (q+q') (r+r') (s+s') (t+t') (u+u').

Definition count_gates_lcr {dim} (lcr : circ dim * circ dim * circ dim) n :=
  let (lc, r) := lcr in
  let (l, c) := lc in
  let ln := count_gates l in
  let cn := count_gates c in
  let rn := count_gates r in
  add_counts (add_counts ln (scale_count cn (n - 2))) rn.

Lemma count_gate_types_sums_to_total : forall {dim} (l0 : circ dim),
  let (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u) := count_gates l0 in
  total_gate_count l0 = (a + b + c + d + e + f + g + h + i + j + k + l + m + n + o + p + q + r + s + t + u)%nat.
Proof.
  intros dim l0.
  destruct (count_gates l0) eqn:H.
  inversion H; subst.
  clear H.
  induction l0.
  reflexivity.
  unfold count_I, count_X, count_Y, count_Z, count_H, count_S, count_T, 
         count_Sdg, count_Tdg, count_Rx, count_Ry, count_Rz, count_Rzq, 
         count_U1, count_U2, count_U3, count_CX, count_CZ, count_SWAP, 
         count_CCX, count_CCZ.
  replace (total_gate_count (a :: l0)) with (S (total_gate_count l0)) by reflexivity.
  simpl length.
  rewrite IHl0.
  destruct a; dependent destruction f; simpl length;
  repeat rewrite <- plus_Snm_nSm; repeat rewrite plus_Sn_m; reflexivity.
Qed.

Lemma add_counts_correct : forall {dim} (c1 c2 : circ dim),
  add_counts (count_gates c1) (count_gates c2) = count_gates (c1 ++ c2).
Proof.
  intros dim c1 c2.
  unfold count_gates, add_counts.
  unfold count_I, count_X, count_Y, count_Z, count_H, count_S, count_T, 
         count_Sdg, count_Tdg, count_Rx, count_Ry, count_Rz, count_Rzq, 
         count_U1, count_U2, count_U3, count_CX, count_CZ, count_SWAP, 
         count_CCX, count_CCZ.
  repeat rewrite filter_app.
  repeat rewrite app_length.
  reflexivity.
Qed.

Lemma scale_count_correct : forall {dim} (c : circ dim) n,
  scale_count (count_gates c) n = count_gates (FullList.niter c n).
Proof.
  intros dim c n.
  induction n.
  reflexivity.
  simpl.
  rewrite <- add_counts_correct, <- IHn.
  reflexivity.
Qed.

Lemma count_gates_lcr_correct : forall {dim} (l c r : circ dim) n,
  count_gates_lcr (l,c,r) n = count_gates (l ++ FullList.niter c (n - 2) ++ r).
Proof.
  intros.
  rewrite app_assoc.
  unfold count_gates_lcr.
  rewrite <- 2 add_counts_correct.
  rewrite <- scale_count_correct.
  reflexivity.
Qed.


(** IBM optimizations **)

Definition optimize_1q_gates {dim} (c : circ dim) : circ dim :=
  IBM_to_full (Optimize1qGates.optimize_1q_gates (full_to_IBM c)).

Definition cx_cancellation {dim} (c : circ dim) : circ dim :=
  IBM_to_full (CXCancellation.cx_cancellation (full_to_IBM c)).

Definition optimize_ibm {dim} (c : circ dim) : circ dim :=
  IBM_to_full 
    (CXCancellation.cx_cancellation 
      (Optimize1qGates.optimize_1q_gates 
        (full_to_IBM c))).

Lemma optimize_1q_gates_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (optimize_1q_gates c ≅l≅ c)%ucom.
Proof. 
  intros dim c H.
  unfold optimize_1q_gates.
  erewrite IBM_to_full_cong.
  apply uc_equiv_cong_l.
  apply IBM_to_full_inv.
  apply Optimize1qGates.optimize_1q_gates_sound.
  apply FullGateSet.full_to_IBM_WT.
  assumption.
Qed.

Lemma optimize_1q_gates_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (optimize_1q_gates c).
Proof.
  intros dim c H.
  show_preserves_WT_cong (optimize_1q_gates_preserves_semantics c H).
Qed.

Ltac show_preserves_mapping_ibm :=
  unfold optimize_1q_gates, cx_cancellation, optimize_ibm;
  repeat (try apply IBM_to_full_preserves_mapping;
          try apply Optimize1qGates.optimize_1q_gates_respects_constraints;
          try apply CXCancellation.cx_cancellation_respects_constraints;
          try apply full_to_IBM_preserves_mapping;
          try assumption).

Lemma optimize_1q_gates_preserves_mapping : forall {dim} (c : circ dim) (cg : c_graph),
  respects_constraints_directed (get_is_in_graph cg) U_CX c -> 
  respects_constraints_directed (get_is_in_graph cg) U_CX (optimize_1q_gates c).
Proof. intros. show_preserves_mapping_ibm. Qed.

Lemma cx_cancellation_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (cx_cancellation c =l= c)%ucom.
Proof.
  intros dim c WT.
  unfold cx_cancellation. 
  erewrite IBM_to_full_equiv.
  apply IBM_to_full_inv.
  apply CXCancellation.cx_cancellation_sound. 
  apply FullGateSet.full_to_IBM_WT.
  assumption.
Qed.

Lemma cx_cancellation_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (cx_cancellation c).
Proof.
  intros dim c H.
  show_preserves_WT (cx_cancellation_preserves_semantics c H).
Qed.

Lemma cx_cancellation_preserves_mapping : forall {dim} (c : circ dim) (cg : c_graph),
  respects_constraints_directed (get_is_in_graph cg) U_CX c -> 
  respects_constraints_directed (get_is_in_graph cg) U_CX (cx_cancellation c).
Proof. intros. show_preserves_mapping_ibm. Qed.

Lemma optimize_ibm_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (optimize_ibm c ≅l≅ c)%ucom.
Proof. 
  intros dim c WT.
  unfold optimize_ibm. 
  erewrite IBM_to_full_cong.
  apply uc_equiv_cong_l.
  apply IBM_to_full_inv.
  eapply IBMList.uc_cong_l_trans.
  apply IBMList.uc_equiv_cong_l.
  apply CXCancellation.cx_cancellation_sound. 
  eapply IBMList.uc_cong_l_implies_WT. 
  symmetry.
  apply Optimize1qGates.optimize_1q_gates_sound.
  apply FullGateSet.full_to_IBM_WT.
  assumption.
  apply FullGateSet.full_to_IBM_WT.
  assumption. 
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
  respects_constraints_directed (get_is_in_graph cg) U_CX c -> 
  respects_constraints_directed (get_is_in_graph cg) U_CX (optimize_ibm c).
Proof. intros. show_preserves_mapping_ibm. Qed.


(** Nam optimizations **)

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
  respects_constraints_directed (get_is_in_graph cg) U_CX c -> 
  respects_constraints_directed (get_is_in_graph cg) U_CX (not_propagation c).
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
  respects_constraints_directed (get_is_in_graph cg) U_CX c -> 
  respects_constraints_directed (get_is_in_graph cg) U_CX (hadamard_reduction c).
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
  respects_constraints_directed (get_is_in_graph cg) U_CX c -> 
  respects_constraints_directed (get_is_in_graph cg) U_CX (cancel_single_qubit_gates c).
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
  respects_constraints_directed (get_is_in_graph cg) U_CX c -> 
  respects_constraints_directed (get_is_in_graph cg) U_CX (cancel_two_qubit_gates c).
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
  respects_constraints_directed (get_is_in_graph cg) U_CX c -> 
  respects_constraints_directed (get_is_in_graph cg) U_CX (merge_rotations c).
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
  respects_constraints_directed (get_is_in_graph cg) U_CX c -> 
  respects_constraints_directed (get_is_in_graph cg) U_CX (optimize_nam c).
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
  respects_constraints_directed (get_is_in_graph cg) U_CX c -> 
  respects_constraints_directed (get_is_in_graph cg) U_CX (optimize_nam_light c).
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
  respects_constraints_directed (get_is_in_graph cg) U_CX c0 -> 
  optimize_nam_lcr c0 = Some (l, c, r) ->
  respects_constraints_directed (get_is_in_graph cg) U_CX l
    /\ respects_constraints_directed (get_is_in_graph cg) U_CX c
    /\ respects_constraints_directed (get_is_in_graph cg) U_CX r.
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


(** Mapping **)

Definition check_layout {dim} (la : layout dim) (n : nat) :=
  layout_well_formed_b n (cast_layout la n).

Definition check_graph (cg : c_graph) : bool :=
  let n := get_dim cg in
  let get_path := get_get_path cg in
  let is_in_graph := get_is_in_graph cg in
  ConnectivityGraph.check_graph n get_path is_in_graph.

Definition check_constraints {dim} (c : circ dim) (cg : c_graph) :=
  let n := get_dim cg in
  let is_in_graph := get_is_in_graph cg in
  respects_constraints_directed_b is_in_graph (cast c n).

Definition swap_route {cdim ldim} (c : circ cdim) (la : layout ldim) (cg : c_graph) :=
  let n := get_dim cg in
  let get_path := get_get_path cg in
  let is_in_graph := get_is_in_graph cg in
  SimpleMapping.swap_route (cast c n) (cast_layout la n) get_path is_in_graph. 

Definition make_tenerife (_:unit) : c_graph := 
  (5, Tenerife.get_path, Tenerife.is_in_graph).
Definition make_lnn n : c_graph := 
  (n, LNN.get_path, LNN.is_in_graph n).
Definition make_lnn_ring n : c_graph := 
  (n, LNNRing.get_path n, LNNRing.is_in_graph n).
Definition make_grid m n : c_graph := 
  (m * n, Grid.get_path n, Grid.is_in_graph m n).

Definition trivial_layout n : layout n := Layouts.trivial_layout n.
Definition list_to_layout l : layout (length l) :=
  Layouts.list_to_layout l.
Definition layout_to_list {dim} (la : layout dim) n :=
  Layouts.layout_to_list n (cast_layout la n).

Lemma check_layout_correct : forall {dim} (la : layout dim) n,
  check_layout la n = true -> layout_well_formed n (cast_layout la n).
Proof. intros. apply layout_well_formed_b_equiv. assumption. Qed.

Definition graph_well_formed (cg : c_graph) :=
  let dim := get_dim cg in
  let get_path := get_get_path cg in
  let is_in_graph := get_is_in_graph cg in
  forall n1 n2, n1 < dim -> n2 < dim -> n1 <> n2 -> 
           valid_path n1 n2 is_in_graph dim (get_path n1 n2).

Lemma check_graph_correct : forall (cg : c_graph),
  check_graph cg = true -> graph_well_formed cg.
Proof. 
  unfold graph_well_formed. 
  intros.
  apply ConnectivityGraph.check_graph_correct; assumption. 
Qed.

Lemma check_constraints_correct : forall {dim} (c : circ dim) (cg : c_graph),
  check_constraints c cg = true <-> 
  respects_constraints_directed (get_is_in_graph cg) U_CX (cast c (get_dim cg)).
Proof. intros. apply respects_constraints_directed_b_equiv. Qed.

Module MappingProofs.

 (* Assume the existence of a c_graph that satisfies graph_well_formed *)
  Parameter cg : c_graph.
  Axiom cg_WF : graph_well_formed cg.

  Module CG <: ConnectivityGraph.
  Definition dim := get_dim cg.
  Definition get_path := get_get_path cg.
  Definition is_in_graph := get_is_in_graph cg.
  Definition get_path_valid := cg_WF.
  End CG.

  Module SMP := SimpleMappingProofs CG.
  Import SMP.

  Lemma swap_route_preserves_semantics : forall {cdim ldim} 
        (c : circ cdim) (la : layout ldim) c' la',
    uc_well_typed_l (cast c dim) ->
    layout_well_formed dim (cast_layout la dim) ->
    swap_route c la cg = (c', la') ->
    (cast c dim) ≡ c' with (@phys2log dim (cast_layout la dim)) and (log2phys la').
  Proof. intros. apply swap_route_sound; assumption. Qed.

  Lemma swap_route_preserves_WT : forall {cdim ldim} 
        (c : circ cdim) (la : layout ldim) c' la',
    uc_well_typed_l (cast c dim) ->
    layout_well_formed dim (cast_layout la dim) ->
    swap_route c la cg = (c', la') ->
    uc_well_typed_l c'.
  Proof. 
    intros cdim ldim c la c' la' WT WF H. 
    apply (swap_route_preserves_semantics _ _ _ _ WT WF) in H.
    unfold uc_eq_perm in H.
    apply list_to_ucom_WT. 
    apply uc_eval_nonzero_iff.
    apply list_to_ucom_WT in WT.
    apply uc_eval_nonzero_iff in WT.
    intro contra.
    unfold eval in H.
    unfold dim, CG.dim in *.
    rewrite contra in H.
    rewrite Mmult_0_r in H.
    rewrite Mmult_0_l in H.
    contradiction.
  Qed.

  Lemma swap_route_respects_constraints : forall {cdim ldim} 
        (c : circ cdim) (la : layout ldim) c' la',
    uc_well_typed_l (cast c dim) ->
    layout_well_formed dim (cast_layout la dim) ->
    swap_route c la cg = (c', la') ->
    respects_constraints_directed (get_is_in_graph cg) U_CX c'.
  Proof.
    intros cdim ldim c la c' la' WT WF H. 
    apply swap_route_respects_constraints_directed in H; assumption. 
  Qed.

  Lemma swap_route_layout_well_formed : forall {cdim ldim} 
        (c : circ cdim) (la : layout ldim) c' la',
    uc_well_typed_l (cast c dim) ->
    layout_well_formed dim (cast_layout la dim) ->
    swap_route c la cg = (c', la') ->
    layout_well_formed dim la'.
  Proof.
    intros cdim ldim c la c' la' WT WF H. 
    apply swap_route_well_formed in H; assumption. 
  Qed.

End MappingProofs.

Lemma make_tenerife_well_formed : graph_well_formed (make_tenerife ()).
Proof.
  unfold graph_well_formed, make_tenerife.
  intros.
  apply Tenerife.get_path_valid; assumption.
Qed.

Lemma make_lnn_well_formed : forall n, graph_well_formed (make_lnn n).
Proof.
  unfold graph_well_formed, make_lnn.
  intros.
  apply LNN.get_path_valid; assumption.
Qed.

Lemma make_lnn_ring_well_formed : forall n, graph_well_formed (make_lnn_ring n).
Proof.
  unfold graph_well_formed, make_lnn_ring.
  intros.
  apply LNNRing.get_path_valid; assumption.
Qed.

Lemma make_grid_well_formed : forall m n, graph_well_formed (make_grid m n).
Proof.
  unfold graph_well_formed, make_grid.
  intros.
  apply Grid.get_path_valid; assumption.
Qed.

Lemma trivial_layout_well_formed : forall n, layout_well_formed n (trivial_layout n).
Proof. intros. apply Layouts.trivial_layout_well_formed. Qed.


(** Examples of composing transformations **)

Definition safe_map {cdim ldim} (c : circ cdim) (la : layout ldim) (cg : c_graph) :=
  let n := get_dim cg in
  let get_path := get_get_path cg in
  let is_in_graph := get_is_in_graph cg in
  if check_well_typed c n && check_layout la n && check_graph cg
  then Some (swap_route c la cg) 
  else None.

Module MappingProofs'.

 (* Assume the existence of inputs s.t. safe_map returns Some (_,_) *)
  Parameters cdim ldim : nat.
  Parameter c : circ cdim.
  Parameter la : layout ldim.
  Parameter cg : c_graph.
  Axiom safe_map_returns_Some : exists c' la', safe_map c la cg = Some (c', la').

  Lemma cg_WF : graph_well_formed cg.
  Proof. 
    unfold graph_well_formed. 
    intros n1 n2 Hn1 Hn2 Hneq.
    specialize safe_map_returns_Some as H.
    destruct H as [c' [la' H]].
    unfold safe_map in H.
    destruct (check_graph cg) eqn:Hcg.
    apply check_graph_correct; assumption.
    rewrite andb_false_r in H.
    inversion H.
  Qed.

  Module CG <: ConnectivityGraph.
  Definition dim := get_dim cg.
  Definition get_path := get_get_path cg.
  Definition is_in_graph := get_is_in_graph cg.
  Definition get_path_valid := cg_WF.
  End CG.

  Module SMP := SimpleMappingProofs CG.
  Import SMP.

  Lemma safe_map_preserves_semantics : forall c' la',
    safe_map c la cg = Some (c', la') ->
    (* No additional assumptions! *)
    (cast c (get_dim cg)) ≡ c' with (@phys2log dim (cast_layout la dim)) and (@log2phys dim la').
  Proof. 
    intros c' la' H.
    unfold safe_map in H.
    destruct (check_well_typed c (get_dim cg)) eqn:HWT;
      destruct (check_layout la (get_dim cg)) eqn:HWF;
      destruct (check_graph cg);
      simpl in H; inversion H; subst.
    apply check_well_typed_correct in HWT.
    apply check_layout_correct in HWF.
    apply swap_route_sound; assumption. 
  Qed.

  Lemma safe_map_respects_constraints : forall c' la',
    safe_map c la cg = Some (c', la') ->
    (* No additional assumptions! *)
    respects_constraints_directed (get_is_in_graph cg) U_CX c'.
  Proof. 
    intros c' la' H.
    unfold safe_map in H.
    destruct (check_well_typed c (get_dim cg)) eqn:HWT;
      destruct (check_layout la (get_dim cg)) eqn:HWF;
      destruct (check_graph cg);
      simpl in H; inversion H; subst.
    apply check_well_typed_correct in HWT.
    apply check_layout_correct in HWF.
    eapply swap_route_respects_constraints_directed; try apply H1; assumption. 
  Qed.

End MappingProofs'.

(* We require c's dim to be 10 for now - otherwise the proof is a pain.
   We can easily remove this requirement once we remove the dimension from
   a program's type. -KH *)
Definition optimize_then_map (c : circ 10) :=
  let gr := make_lnn 10 in         (* 10-qubit LNN architecture *)
  let la := trivial_layout 10 in   (* trivial layout on 10 qubits *)
  if check_well_typed c 10         (* check that c is well-typed & uses <=10 qubits *)
  then 
    let c' := optimize_nam c in    (* optimization #1 *)
    let c'' := optimize_ibm c' in  (* optimization #2 *)
    Some (swap_route c'' la gr)    (* map *)
  else None.

Module LNN10 <: ConnectivityGraph.
  Definition dim := 10.
  Definition get_path := LNN.get_path.
  Definition is_in_graph := LNN.is_in_graph 10.
  Definition get_path_valid := LNN.get_path_valid 10.
End LNN10.

Module SMPLNN := SimpleMappingProofs LNN10.
Import SMPLNN.

Lemma cast_same : forall {dim} (c : circ dim), cast c dim = c.
Proof. 
  intros dim c. 
  induction c. 
  reflexivity. 
  simpl. 
  destruct a; rewrite IHc; reflexivity.
Qed.

Lemma cast_layout_same : forall {dim} (la : layout dim), cast_layout la dim = la.
Proof. intros dim la. reflexivity. Qed.

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

Definition map_then_optimize (c : circ 10) :=
  let gr := make_lnn 10 in               (* 10-qubit LNN architecture *)
  let la := trivial_layout 10 in         (* trivial layout on 10 qubits *)
  if check_well_typed c 10               (* check that c is well-typed & uses <=10 qubits *)
  then 
    let (c', la') := swap_route c la gr in  (* map *)
    let c'' := optimize_nam c' in           (* optimization #1 *)
    let c''' := optimize_ibm c'' in         (* optimization #2 *)
    Some (c''', la') 
  else None.

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
