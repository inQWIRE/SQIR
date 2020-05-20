Require Import NotPropagation.
Require Import HadamardReduction.
Require Import GateCancellation.
Require Import RotationMerging.

(* 'optimize' function applies our optimizations in the following order:
   0, 1, 3, 2, 3, 1, 2, 4, 3, 2 
   
   0 - not propagation
   1 - hadamard reduction
   2 - single qubit gate cancellation
   3 - two qubit gate cancellation
   4 - rotation merging *) 

Definition optimize {dim} (l : RzQ_ucom_l dim) : RzQ_ucom_l dim :=
  cancel_single_qubit_gates 
    (cancel_two_qubit_gates 
      (merge_rotations
        (cancel_single_qubit_gates 
          (hadamard_reduction 
            (cancel_two_qubit_gates 
              (cancel_single_qubit_gates 
                (cancel_two_qubit_gates 
                  (hadamard_reduction 
                    (not_propagation l))))))))). 

(* LCR optimizer for multiple iterations. *)
Definition optimize_lcr {dim} (l : RzQ_ucom_l dim) :=
  LCR l optimize (fun n => @match_gate n).

(* Built-in well-typedness check. *)
Definition optimize_check_for_type_errors {dim} (l : RzQ_ucom_l dim) 
    : option (RzQ_ucom_l dim) :=
  if RzQ_ucom_l_well_typed_b dim l
  then Some (optimize l)
  else None.

Lemma cancel_single_qubit_gates_sound' : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> cancel_single_qubit_gates l ≅l≅ l.
Proof. intros. apply uc_equiv_cong_l. apply cancel_single_qubit_gates_sound. auto. Qed.

Lemma cancel_two_qubit_gates_sound' : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> cancel_two_qubit_gates l ≅l≅ l.
Proof. intros. apply uc_equiv_cong_l. apply cancel_two_qubit_gates_sound. auto. Qed.

Lemma merge_rotations_sound' : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> merge_rotations l ≅l≅ l.
Proof. intros. apply uc_equiv_cong_l. apply merge_rotations_sound. auto. Qed.

Lemma optimize_sound : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> optimize l ≅l≅ l.
Proof.
  intros.
  unfold optimize.
  repeat ((* soundness *)
          try rewrite not_propagation_sound;
          try rewrite hadamard_reduction_sound;
          try rewrite cancel_single_qubit_gates_sound';
          try rewrite cancel_two_qubit_gates_sound';
          try rewrite merge_rotations_sound';
          (* well-typedness *)
          try apply not_propagation_WT;
          try apply hadamard_reduction_WT;
          try apply cancel_single_qubit_gates_WT;
          try apply cancel_two_qubit_gates_WT;
          try apply merge_rotations_WT;
          try assumption).
  reflexivity.
Qed.

Lemma optimize_WT : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (optimize l).
Proof.
  intros.
  unfold optimize.
  repeat (try apply not_propagation_WT;
          try apply hadamard_reduction_WT;
          try apply cancel_single_qubit_gates_WT;
          try apply cancel_two_qubit_gates_WT;
          try apply merge_rotations_WT;
          auto).
Qed.

Lemma optimize_check_for_type_errors_sound : forall {dim} (l l' : RzQ_ucom_l dim),
  optimize_check_for_type_errors l = Some l' ->
  l' ≅l≅ l.
Proof.
  intros dim l l' H.
  unfold optimize_check_for_type_errors in H.
  destruct (RzQ_ucom_l_well_typed_b dim l) eqn:WTb; try discriminate.
  inversion H; subst.
  apply optimize_sound.
  apply uc_well_typed_l_b_equiv.
  apply WTb.
Qed.

Lemma optimize_lcr_sound : forall {dim} (p l c r : RzQ_ucom_l dim) n,
  (n > 2)%nat -> uc_well_typed_l p ->
  optimize_lcr p = Some (l, c, r) ->
  niter p n ≅l≅ (l ++ (niter c (n - 2)) ++ r).
Proof.
  intros dim p l c r n Hn WT H.
  eapply LCR_correct in H.
  apply H.
  all: try assumption.
  apply optimize_sound.
  apply optimize_WT.
Qed.
