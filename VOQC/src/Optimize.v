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

Require Import SimpleMapping.

(* Definitions of mapping/optimizing in different orders (specialized to
   the RzQ gate set).

   Q: Why write these wrapper functions in Coq instead of OCaml?
   A: It would also be fine to write these functions in OCaml -- but then
      we can't prove anything about them. "Obviously" composing simple_map
      and optimize should be fine since they are both semantics-preserving,
      but it's still nice to have a formal proof of this fact.  *)

Definition simple_map_rzq {dim} 
      (l : RzQ_ucom_l dim)
      (m : qmap dim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph : nat -> nat -> bool)
  : RzQ_ucom_l dim * qmap dim
  := simple_map l m get_path is_in_graph RzQGateSet.CNOT RzQGateSet.SWAP RzQGateSet.H.

Definition only_map {dim}
      (l : RzQ_ucom_l dim)
      (m : qmap dim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph : nat -> nat -> bool)
  : option (RzQ_ucom_l dim * qmap dim) :=
  (* we can check that the layout and input programs are sensible (making
     fewer assumptions for correctness), but we have to assume that get_path
     and is_in_graph_b are well-formed unless we use a proper Coq graph library. *)
  if layout_well_formed_b dim m && uc_well_typed_l_b dim l
  then Some (simple_map_rzq l m get_path is_in_graph)
  else None.

Definition optimize_then_map {dim} 
      (l : RzQ_ucom_l dim)
      (m : qmap dim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph : nat -> nat -> bool)
  : option (RzQ_ucom_l dim * qmap dim) :=
  if layout_well_formed_b dim m && uc_well_typed_l_b dim l
  then Some (simple_map_rzq (optimize l) m get_path is_in_graph)
  else None.

Definition map_then_optimize {dim}
      (l : RzQ_ucom_l dim)
      (m : qmap dim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph : nat -> nat -> bool)
  : option (RzQ_ucom_l dim * qmap dim) :=
  if layout_well_formed_b dim m && uc_well_typed_l_b dim l
  then let (l',m') := simple_map_rzq l m get_path is_in_graph in
       Some (optimize l', m')
  else None.

Definition optimize_then_map_then_optimize {dim}
      (l : RzQ_ucom_l dim)
      (m : qmap dim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph : nat -> nat -> bool)
  : option (RzQ_ucom_l dim * qmap dim) :=
  if layout_well_formed_b dim m && uc_well_typed_l_b dim l
  then let (l',m') := simple_map_rzq (optimize l) m get_path is_in_graph in
       Some (optimize l', m')
  else None.

(* Assume the following is true: *)
Lemma optimize_respects_contraints_directed : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph l ->
  respects_constraints_directed is_in_graph (optimize l).
Proof.
Admitted.
(* To complete this proof, you should write a XX_respects_contraints_directed 
   lemma in each optimization file and then use those lemmas here. See the
   proof of optimize_sound above. 

   One small problem: this property isn't actually true :)

   The issue is that apply_H_equivalence3 (in HadamardReduction.v) doesn't 
   preserve directionality of CNOT interactions. I suggest removing this
   function from the optimizer -- it doesn't do much in our benchmarks anyways. *)


(* Now (given valid connectivity graph CG), we can prove correctness of our
   mapping/optimization functions. 

   --> so when we claim correctness of the OCaml code, we need to make sure 
   that we respect the assumptions made in ConnectivityGraph *)
Module OptimizeProofs (CG : ConnectivityGraph).

Module SMP := SimpleMappingProofs RzQGateSet MappableRzQ CG.
Export SMP.

Definition dim := CG.dim.

Lemma only_map_sound : forall (l : RzQ_ucom_l dim) (m : qmap dim) l' m',
  only_map l m CG.get_path CG.is_in_graph = Some (l', m') -> 
  l ≡ l' with (phys2log m) and (log2phys m').
Proof.
  intros l m l' m' H.
  unfold only_map in H.
  destruct (layout_well_formed_b dim m) eqn:WF.
  2: inversion H.
  destruct (uc_well_typed_l_b dim l) eqn:WT.
  2: inversion H.
  simpl in H.
  inversion H.
  apply layout_well_formed_b_equiv in WF.
  apply uc_well_typed_l_b_equiv in WT.
  apply simple_map_sound; auto.
Qed.

Lemma only_map_respects_constraints_directed : forall (l : RzQ_ucom_l dim) (m : qmap dim) l' m',
  only_map l m CG.get_path CG.is_in_graph = Some (l', m') -> 
  respects_constraints_directed CG.is_in_graph l'.
Proof.
  intros l m l' m' H.
  unfold only_map in H.
  destruct (layout_well_formed_b dim m) eqn:WF.
  2: inversion H.
  destruct (uc_well_typed_l_b dim l) eqn:WT.
  2: inversion H.
  simpl in H.
  inversion H.
  apply layout_well_formed_b_equiv in WF.
  apply uc_well_typed_l_b_equiv in WT.
  eapply simple_map_respects_constraints_directed; try apply H1; auto.
Qed.

Lemma optimize_then_map_sound : forall (l : RzQ_ucom_l dim) (m : qmap dim) l' m',
  optimize_then_map l m CG.get_path CG.is_in_graph = Some (l', m') -> 
  l ≅ l' with (phys2log m) and (log2phys m').
Proof.
  intros l m l' m' H.
  unfold optimize_then_map in H.
  destruct (layout_well_formed_b dim m) eqn:WF.
  2: inversion H.
  destruct (uc_well_typed_l_b dim l) eqn:WT.
  2: inversion H.
  simpl in H.
  inversion H.
  apply layout_well_formed_b_equiv in WF.
  apply uc_well_typed_l_b_equiv in WT.
  apply simple_map_sound in H1.
  apply uc_eq_perm_uc_cong_l with (l2:=optimize l).
  symmetry.
  apply optimize_sound.
  assumption.
  apply uc_eq_perm_implies_uc_cong_perm.
  apply H1.
  apply optimize_WT; auto.
  assumption.  
Qed.

Lemma optimize_then_map_respects_constraints_directed : forall (l : RzQ_ucom_l dim) (m : qmap dim) l' m',
  optimize_then_map l m CG.get_path CG.is_in_graph = Some (l', m') -> 
  respects_constraints_directed CG.is_in_graph l'.
Proof.
  intros l m l' m' H.
  unfold optimize_then_map in H.
  destruct (layout_well_formed_b dim m) eqn:WF.
  2: inversion H.
  destruct (uc_well_typed_l_b dim l) eqn:WT.
  2: inversion H.
  simpl in H.
  inversion H.
  apply layout_well_formed_b_equiv in WF.
  apply uc_well_typed_l_b_equiv in WT.
  eapply simple_map_respects_constraints_directed; try apply H1; auto.
  apply optimize_WT; auto.
Qed.

Lemma map_then_optimize_sound : forall (l : RzQ_ucom_l dim) (m : qmap dim) l' m',
  map_then_optimize l m CG.get_path CG.is_in_graph = Some (l', m') -> 
  l ≅ l' with (phys2log m) and (log2phys m').
Proof.
  intros l m l' m' H.
  unfold map_then_optimize in H.
  destruct (layout_well_formed_b dim m) eqn:WF.
  2: inversion H.
  destruct (uc_well_typed_l_b dim l) eqn:WT.
  2: inversion H.
  simpl in H.
  destruct (simple_map_rzq l m CG.get_path CG.is_in_graph) eqn:Hmap.
  inversion H; subst.
  apply layout_well_formed_b_equiv in WF.
  apply uc_well_typed_l_b_equiv in WT.
  assert (Hmap':=Hmap).
  apply simple_map_WT in Hmap'; auto.
  apply simple_map_sound in Hmap; auto.
  apply uc_eq_perm_uc_cong_l_alt with (l2:=r).
  apply uc_eq_perm_implies_uc_cong_perm.
  assumption.
  symmetry.
  apply optimize_sound.
  assumption.
Qed.

Lemma map_then_optimize_respects_constraints_directed : forall (l : RzQ_ucom_l dim) (m : qmap dim) l' m',
  map_then_optimize l m CG.get_path CG.is_in_graph = Some (l', m') -> 
  respects_constraints_directed CG.is_in_graph l'.
Proof.
  intros l m l' m' H.
  unfold map_then_optimize in H.
  destruct (layout_well_formed_b dim m) eqn:WF.
  2: inversion H.
  destruct (uc_well_typed_l_b dim l) eqn:WT.
  2: inversion H.
  simpl in H.
  destruct (simple_map_rzq l m CG.get_path CG.is_in_graph) eqn:Hmap.
  inversion H; subst.
  apply layout_well_formed_b_equiv in WF.
  apply uc_well_typed_l_b_equiv in WT.
  apply optimize_respects_contraints_directed.
  eapply simple_map_respects_constraints_directed in Hmap; auto.
Qed.

Lemma optimize_then_map_then_optimize_sound : forall (l : RzQ_ucom_l dim) (m : qmap dim) l' m',
  optimize_then_map_then_optimize l m CG.get_path CG.is_in_graph = Some (l', m') -> 
  l ≅ l' with (phys2log m) and (log2phys m').
Proof.
  intros l m l' m' H.
  unfold optimize_then_map_then_optimize in H.
  destruct (layout_well_formed_b dim m) eqn:WF.
  2: inversion H.
  destruct (uc_well_typed_l_b dim l) eqn:WT.
  2: inversion H.
  destruct (simple_map_rzq (optimize l) m CG.get_path CG.is_in_graph) eqn:Hmap.
  inversion H; subst.
  apply layout_well_formed_b_equiv in WF.
  apply uc_well_typed_l_b_equiv in WT.
  assert (Hmap':=Hmap).
  apply simple_map_WT in Hmap'; auto.
  apply simple_map_sound in Hmap; auto.
  apply uc_eq_perm_uc_cong_l_alt with (l2:=r).
  apply uc_eq_perm_uc_cong_l with (l2:=optimize l).
  symmetry.
  apply optimize_sound.
  assumption.
  apply uc_eq_perm_implies_uc_cong_perm.
  assumption.
  symmetry.
  apply optimize_sound.
  assumption.
  apply optimize_WT; assumption.
  apply optimize_WT; assumption.
Qed.

Lemma optimize_then_map_then_optimize_respects_constraints_directed : forall (l : RzQ_ucom_l dim) (m : qmap dim) l' m',
  optimize_then_map_then_optimize l m CG.get_path CG.is_in_graph = Some (l', m') -> 
  respects_constraints_directed CG.is_in_graph l'.
Proof.
  intros l m l' m' H.
  unfold optimize_then_map_then_optimize in H.
  destruct (layout_well_formed_b dim m) eqn:WF.
  2: inversion H.
  destruct (uc_well_typed_l_b dim l) eqn:WT.
  2: inversion H.
  destruct (simple_map_rzq (optimize l) m CG.get_path CG.is_in_graph) eqn:Hmap.
  inversion H; subst.
  apply layout_well_formed_b_equiv in WF.
  apply uc_well_typed_l_b_equiv in WT.
  apply optimize_respects_contraints_directed.
  eapply simple_map_respects_constraints_directed in Hmap; auto.
  apply optimize_WT; auto.
Qed.

End OptimizeProofs.


(* For example, we can specialize these proofs for the LNN graph: *)
Module OP := OptimizeProofs LNN.CG.
Export OP.

Definition only_map_lnn {dim} (l : RzQ_ucom_l dim) (m : qmap dim) :=
  only_map l m LNN.get_path (LNN.is_in_graph dim).

Lemma only_map_lnn_sound : forall (l : RzQ_ucom_l dim) (m : qmap dim) l' m',
  only_map_lnn l m = Some (l', m') -> 
  l ≡ l' with (phys2log m) and (log2phys m').
Proof. 
  intros. 
  apply only_map_sound. 
  assumption. 
Qed.

Lemma only_map_lnn_respects_constraints_directed : forall (l : RzQ_ucom_l dim) (m : qmap dim) l' m',
  only_map_lnn l m = Some (l', m') -> 
  respects_constraints_directed (LNN.is_in_graph dim) l'.
Proof. 
  intros l m l' m' H. 
  apply only_map_respects_constraints_directed in H.
  assumption.
Qed.

