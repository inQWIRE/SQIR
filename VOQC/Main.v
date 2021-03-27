Require Import RzQGateSet.
Require Import SimpleMapping.
Require Import StandardGateSet.
Import StdList.

Local Close Scope Q_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.

(* This is the "main" file that contains the versions of VOQC transformations
   that are extracted to OCaml (along with their correctness properties). The 
   definitions and proofs in this file are largely wrappers around / renamed 
   versions of other definitions and proofs.

   TODO: make names in repo consistent with names in VOQC user manual *)


Definition circ := standard_ucom_l.
Inductive gate_counts : Set :=
  | BuildCounts : nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> 
                  nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> gate_counts.
Definition layout := qmap.
Definition c_graph : Type := nat * (nat -> nat -> list nat) * (nat -> nat -> bool).
Definition get_dim (cg : c_graph) := fst (fst cg).
Definition get_get_path (cg : c_graph) := snd (fst cg).
Definition get_is_in_graph (cg : c_graph) := snd cg.

(** Utility functions **)

(* Cast changes the dependent type of a circuit --> will be extracted to a no-op *)
Fixpoint cast {dim} (c : circ dim) dim' : @circ dim' := 
  match c with 
  | [] => []
  | App1 g m :: t => App1 g m :: cast t dim'
  | App2 g m n :: t => App2 g m n :: cast t dim'
  | App3 g m n p :: t => App3 g m n p :: cast t dim'
  end.

Definition check_well_typed {dim} (n : nat) (c : circ dim) :=
  uc_well_typed_l_b n (cast c n).
Definition convert_to_ibm {dim} (c : circ dim) :=
  StandardGateSet.convert_to_ibm c.
Definition convert_to_rzq {dim} (c : circ dim) :=
  StandardGateSet.convert_to_rzq c.
Definition replace_rzq {dim} (c : circ dim) :=
  StandardGateSet.replace_rzq c.
Definition decompose_to_cnot {dim} (c : circ dim) :=
  StandardGateSet.decompose_to_cnot c.

Lemma check_well_typed_correct : forall {dim} n (c : circ dim),
  check_well_typed n c = true <-> uc_well_typed_l (cast c n).
Proof. intros. apply uc_well_typed_l_b_equiv. Qed.

Lemma convert_to_ibm_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (convert_to_ibm c =l= c)%ucom.
Proof. intros. apply StandardGateSet.convert_to_ibm_sound. assumption. Qed.

Lemma convert_to_ibm_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (convert_to_ibm c).
Proof.
  intros.
  eapply uc_equiv_l_implies_WT.
  symmetry.
  apply convert_to_ibm_preserves_semantics.
  assumption.
  assumption.
Qed.

Lemma convert_to_ibm_uses_ibm_gates : forall {dim} (c : circ dim),
  forall_gates only_ibm (convert_to_ibm c).
Proof. intros. apply StandardGateSet.convert_to_ibm_gates. Qed.

Lemma convert_to_rzq_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (convert_to_rzq c ≅l≅ c)%ucom.
Proof. intros. apply StandardGateSet.convert_to_rzq_sound. assumption. Qed.

Lemma convert_to_rzq_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (convert_to_rzq c).
Proof.
  intros.
  eapply uc_cong_l_implies_WT.
  symmetry.
  apply convert_to_rzq_preserves_semantics.
  assumption.
  assumption.
Qed.

Lemma convert_to_rzq_uses_rzq_gates : forall {dim} (c : circ dim),
  forall_gates only_rzq (convert_to_rzq c).
Proof. intros. apply StandardGateSet.convert_to_rzq_gates. Qed.

Lemma replace_rzq_preserves_semantics : forall {dim} (c : circ dim),
  (replace_rzq c =l= c)%ucom.
Proof. intros. apply StandardGateSet.replace_rzq_sound. Qed.

Lemma replace_rzq_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (replace_rzq c).
Proof.
  intros.
  eapply uc_equiv_l_implies_WT.
  symmetry.
  apply replace_rzq_preserves_semantics.
  assumption.
Qed.

Lemma replace_rzq_does_not_use_rzq_gates : forall {dim} (c : circ dim),
  forall_gates no_rzq (replace_rzq c).
Proof. intros. apply StandardGateSet.replace_rzq_gates. Qed.

Lemma decompose_to_cnot_preserves_semantics : forall {dim} (c : circ dim),
  (decompose_to_cnot c =l= c)%ucom.
Proof. intros. apply StandardGateSet.decompose_to_cnot_sound. Qed.

Lemma decompose_to_cnot_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (decompose_to_cnot c).
Proof.
  intros.
  eapply uc_equiv_l_implies_WT.
  symmetry.
  apply decompose_to_cnot_preserves_semantics.
  assumption.
Qed.

Lemma decompose_to_cnot_uses_cnot_gates : forall {dim} (c : circ dim),
  forall_gates only_cnots (decompose_to_cnot c).
Proof. intros. apply StandardGateSet.decompose_to_cnot_gates. Qed.

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
                 Qeq_bool q' Q_zero || Qeq_bool q' Q_half || 
                   Qeq_bool q' Q_three_halves || Qeq_bool q' Q_one
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
  destruct a; dependent destruction s; simpl length;
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
  scale_count (count_gates c) n = count_gates (StdList.niter c n).
Proof.
  intros dim c n.
  induction n.
  reflexivity.
  simpl.
  rewrite <- add_counts_correct, <- IHn.
  reflexivity.
Qed.

Lemma count_gates_lcr_correct : forall {dim} (l c r : circ dim) n,
  count_gates_lcr (l,c,r) n = count_gates (l ++ StdList.niter c (n - 2) ++ r).
Proof.
  intros.
  rewrite app_assoc.
  unfold count_gates_lcr.
  rewrite <- 2 add_counts_correct.
  rewrite <- scale_count_correct.
  reflexivity.
Qed.


(** IBM optimizations **)

Require Import Optimize1qGates.
Require Import CXCancellation.

Definition optimize_1q_gates {dim} (c : circ dim) : circ dim :=
  IBM_to_standard (Optimize1qGates.optimize_1q_gates (standard_to_IBM c)).

Definition cx_cancellation {dim} (c : circ dim) : circ dim :=
  IBM_to_standard (CXCancellation.cx_cancellation (standard_to_IBM c)).

Definition optimize_ibm {dim} (c : circ dim) : circ dim :=
  IBM_to_standard 
    (CXCancellation.cx_cancellation 
      (Optimize1qGates.optimize_1q_gates 
        (standard_to_IBM c))).

Lemma optimize_1q_gates_preserves_semantics : forall {dim} (c : circ dim),
  uc_well_typed_l c -> (optimize_1q_gates c ≅l≅ c)%ucom.
Proof.
  intros dim c WT.
  unfold optimize_1q_gates. 
  erewrite IBM_to_standard_cong.
  2: { apply Optimize1qGates.optimize_1q_gates_sound. 
       apply StandardGateSet.standard_to_IBM_WT.
       assumption. }
  apply uc_equiv_cong_l.
  apply IBM_to_standard_inv.
  assumption.
Qed.

Lemma optimize_1q_gates_preserves_WT : forall {dim} (c : circ dim),
  uc_well_typed_l c -> uc_well_typed_l (optimize_1q_gates c).
Proof.
  intros.
  eapply uc_cong_l_implies_WT.
  symmetry.
  apply optimize_1q_gates_preserves_semantics.
  assumption.
  assumption.
Qed.

Lemma optimize_1q_gates_preserves_mapping : forall {dim} (c : circ dim) (cg : c_graph),
  respects_constraints_directed (get_is_in_graph cg) c -> 
  respects_constraints_directed (get_is_in_graph cg) (optimize_1q_gates c).
Proof.
  intros dim c cg H.
  admit.
Qed.

Lemma optimize_sound : forall {dim} (l : IBM_ucom_l dim),
  uc_well_typed_l l -> optimize l ≅l≅ l.
Proof.
  intros.
  unfold optimize.
  eapply uc_cong_l_trans.
  apply uc_equiv_cong_l.
  apply cx_cancellation_sound.
  eapply uc_cong_l_implies_WT. 
  symmetry.
  apply optimize_1q_gates_sound.
  assumption.
  assumption.
  apply optimize_1q_gates_sound.
  assumption.
Qed.

Lemma optimize_WT : forall {dim} (l : IBM_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (optimize l).
Proof.
  intros.
  eapply uc_cong_l_implies_WT.
  symmetry.
  apply optimize_sound.
  assumption.
  assumption.
Qed.


(** Nam optimizations **)

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



Definition optimize_nam {dim} (c : circ dim) : circ dim :=
  RzQ_to_standard (OptimizeNam.optimize (standard_to_RzQ c)).

Lemma optimize_nam_preserves_semantics : forall {dim} (c : @circ dim),
  uc_well_typed_l c -> (optimize_nam c ≅l≅ c)%ucom.
Proof.
  intros dim c H.
  unfold optimize_nam. 
  erewrite RzQ_to_standard_cong.
  2: { apply OptimizeNam.optimize_sound. admit. }
  apply RzQ_to_standard_inv.
  assumption.
Qed.


Lemma optimize_preserves_mapping


Definition optimize_nam_lcr {dim} (l : RzQ_ucom_l dim) :=


Definition optimize_nam_light {dim} (l : RzQ_ucom_l dim) : RzQ_ucom_l dim :=

not_propagation
hadamard_reduction
cancel_single_qubit_gates
cancel_two_qubit_gates
merge_rotations

Lemma optimize_lcr_sound : forall {dim} (p l c r : RzQ_ucom_l dim) n,
  (n > 2)%nat -> uc_well_typed_l p ->
  optimize_lcr p = Some (l, c, r) ->
  niter p n ≅l≅ (l ++ (niter c (n - 2)) ++ r).





Definition optimize_ibm {dim} (l : IBM_ucom_l dim) :=

optimize_1q_gates
cx_cancellation


(** Mapping **)


Definition layout {dim} := qmap dim.
Definition c_graph := nat * (nat -> nat -> list nat) * (nat -> nat -> bool).

Definition cast_layout {dim} (la : @layout dim) dim' : @layout dim' := la.
  let (f, g) := la in (f, g).

check_layout : layout -> (n : int) -> bool
check_constraints : circ -> c_graph -> bool


Definition simple_map {cdim ldim} (c : @circ cdim) (la : @layout ldim) (cg : c_graph) :=
  let (n, get_path, is_in_graph) := cg in
  if check_well_typed c n && check_layout la n 
  then Some (SimpleMapping.simple_map (cast c n) (cast_layout la n) get_path is_in_graph) 
  else None

make_tenerife : unit -> c\_graph
make_lnn : (n : int) -> c\_graph
make_lnn_ring : (n : int) -> c\_graph
make_grid : (m : int) -> (n : int) -> c\_graph
trivial_layout : (n : int) -> layout
list_to_layout : list int -> layout
layout_to_list : layout -> list int



(** Example of composing transformations **)

Definition optimize_then_map c :=
  let gr := make_lnn 10 in         (* 10-qubit LNN architecture *)
  let la := trivial_layout 10 in   (* trivial layout on 10 qubits *)
  if check_well_typed c 10         (* check that c is well-typed & uses <=10 qubits *)
  then 
    let c' := optimize_nam c in    (* optimization #1 *)
    let c'' := optimize_ibm c' in  (* optimization #2 *)
    simple_map c'' la gr           (* map *)
  else None.

Definition map_then_optimize c :=
  let gr := make_lnn 10 in               (* 10-qubit LNN architecture *)
  let la := trivial_layout 10 in         (* trivial layout on 10 qubits *)
  if check_well_typed c 10               (* check that c is well-typed & uses <=10 qubits *)
  then 
    match simple_map c la gr with        (* map *)
    | Some (c', la') => 
        let c'' := optimize_nam c' in    (* optimization #1 *)
        let c''' := optimize_ibm c'' in  (* optimization #2 *)
        (c''', la') 
    | None => None
  else None.
