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

(* Light version of the optimizer used for QFT-based adder programs (following Nam et al.). *)
Definition optimize_light {dim} (l : RzQ_ucom_l dim) : RzQ_ucom_l dim :=
  cancel_single_qubit_gates 
    (hadamard_reduction 
      (cancel_two_qubit_gates 
        (cancel_single_qubit_gates 
          (cancel_two_qubit_gates 
            (hadamard_reduction 
              (not_propagation l)))))). 
Definition optimize_light_lcr {dim} (l : RzQ_ucom_l dim) :=
  LCR l optimize_light (fun n => @match_gate n).

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

Lemma optimize_light_sound : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> optimize_light l ≅l≅ l.
Proof.
  intros.
  unfold optimize_light.
  repeat ((* soundness *)
          try rewrite not_propagation_sound;
          try rewrite hadamard_reduction_sound;
          try rewrite cancel_single_qubit_gates_sound';
          try rewrite cancel_two_qubit_gates_sound';
          (* well-typedness *)
          try apply not_propagation_WT;
          try apply hadamard_reduction_WT;
          try apply cancel_single_qubit_gates_WT;
          try apply cancel_two_qubit_gates_WT;
          try assumption).
  reflexivity.
Qed.

Lemma optimize_light_WT : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (optimize_light l).
Proof.
  intros.
  unfold optimize_light.
  repeat (try apply not_propagation_WT;
          try apply hadamard_reduction_WT;
          try apply cancel_single_qubit_gates_WT;
          try apply cancel_two_qubit_gates_WT;
          auto).
Qed.

Lemma optimize_light_lcr_sound : forall {dim} (p l c r : RzQ_ucom_l dim) n,
  (n > 2)%nat -> uc_well_typed_l p ->
  optimize_light_lcr p = Some (l, c, r) ->
  niter p n ≅l≅ (l ++ (niter c (n - 2)) ++ r).
Proof.
  intros dim p l c r n Hn WT H.
  eapply LCR_correct in H.
  apply H.
  all: try assumption.
  apply optimize_light_sound.
  apply optimize_light_WT.
Qed.


(** In progress... adding mapping **)

Require Import SimpleMappingWithLayout.

Definition only_map 
      (ldim pdim : nat) 
      (l : RzQ_ucom_l ldim)
      (m : qmap ldim pdim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph_b : nat -> nat -> bool)
  : option (RzQ_ucom_l pdim * qmap ldim pdim) :=
  (* we can check that the layout and input programs are sensible (making
     fewer assumptions for correctness), but we have to assume that get_path
     and is_in_graph_b are well-formed unless we use a proper Coq graph library. *)
  if layout_well_formed_b ldim pdim m && uc_well_typed_l_b ldim l
  then Some (simple_map_rzq l m get_path is_in_graph_b)
  else None.

Definition optimize_then_map 
      (ldim pdim : nat) 
      (l : RzQ_ucom_l ldim)
      (m : qmap ldim pdim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph_b : nat -> nat -> bool)
  : option (RzQ_ucom_l pdim * qmap ldim pdim) :=
  if layout_well_formed_b ldim pdim m && uc_well_typed_l_b ldim l
  then Some (simple_map_rzq (optimize l) m get_path is_in_graph_b)
  else None.

Definition map_then_optimize
      (ldim pdim : nat) 
      (l : RzQ_ucom_l ldim)
      (m : qmap ldim pdim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph_b : nat -> nat -> bool)
  : option (RzQ_ucom_l pdim * qmap ldim pdim) :=
  if layout_well_formed_b ldim pdim m && uc_well_typed_l_b ldim l
  then let (l',m') := simple_map_rzq l m get_path is_in_graph_b in
       Some (optimize l', m')
  else None.

(* In order for this ^ to be valid, the following must hold:

Lemma optimize_respects_contraints_undirected : forall {dim} (l : RzQ_ucom_l dim),
  respects_constraints_undirected is_in_graph_b l ->
  respects_constraints_undirected is_in_graph_b (optimize l).

Note that I'm using the "undirected" version of respects contraints -- meaning
that this only works for graphs that are undirected. The issue is that 
apply_H_equivalence3 (in HadamardReduction.v) does not preserve directionality.
You can prove respects_contraints_directed if you remove that step from
optimization. *)

Definition optimize_then_map_then_optimize
      (ldim pdim : nat) 
      (l : RzQ_ucom_l ldim)
      (m : qmap ldim pdim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph_b : nat -> nat -> bool)
  : option (RzQ_ucom_l pdim * qmap ldim pdim) :=
  if layout_well_formed_b ldim pdim m && uc_well_typed_l_b ldim l
  then let (l',m') := simple_map_rzq (optimize l) m get_path is_in_graph_b in
       Some (optimize l', m')
  else None.
