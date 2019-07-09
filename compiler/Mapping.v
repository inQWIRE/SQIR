Require Import Compose.
Require Import Equivalences.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.

(*************************)
(** LNN Mapping Example **)
(*************************)

(* Naive mapping algorithm. *)
Fixpoint move_target_left {dim} (base dist : nat) : ucom dim :=
  match dist with 
  | O => CNOT base (base + 1)
  | S n' => SWAP (base + dist) (base + dist + 1); 
           move_target_left base n'; 
           SWAP (base + dist) (base + dist + 1)
  end.

Fixpoint move_target_right {dim} (base dist : nat) : ucom dim :=
  match dist with 
  | O => CNOT (base + 1) base
  | S n' => SWAP (base - dist) (base - dist + 1); 
           move_target_right base n'; 
           SWAP (base - dist) (base - dist + 1)
  end.

Fixpoint map_to_lnn {dim} (c : ucom dim) : ucom dim :=
  match c with
  | c1; c2 => map_to_lnn c1; map_to_lnn c2
  | uapp2 U_CNOT n1 n2 =>
      if n1 <? n2
      then move_target_left n1 (n2 - n1 - 1)
      else if n2 <? n1
           then move_target_right (n1 - 1) (n1 - n2 - 1)
           else CNOT n1 n2 (* badly-typed case, n1=n2 *)
  | _ => c
  end.

(* Small test case. *)
Definition q0 : nat := 0.
Definition q1 : nat := 1.
Definition q2 : nat := 2.
Definition q3 : nat := 3.
Definition q4 : nat := 4.
Definition example3 : ucom 5 := CNOT q0 q3; CNOT q4 q1.
Compute (map_to_lnn example3).

(* There are many more interesting & general properties we can prove about SWAP, e.g.

       forall a b, SWAP a b; U b; SWAP a b ≡ U a

   but the properties below are sufficient for this problem.

   For reference, the general definition of the swap matrix for m < n is:

   @pad (1+(n-m-1)+1) m dim 
        ( ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨0∣ .+
          ∣0⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨0∣ .+
          ∣1⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨1∣ .+
          ∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨1∣ )
*)

(* TODO: clean up denote_swap_adjacent by adding the lemmas below to M_db. *)
Lemma swap_spec_general : forall (A B : Matrix 2 2),
  WF_Matrix A -> WF_Matrix B -> swap × (A ⊗ B) × swap = B ⊗ A.
Proof.
  intros A B WF_A WF_B.
  solve_matrix.
Qed.

Lemma rewrite_ket_prod00 : forall (q1 :  Matrix 2 1) (q2 : Matrix 1 2),
  WF_Matrix q1 -> WF_Matrix q2 -> (q1 × ⟨0∣) × (∣0⟩ × q2) = q1 × q2.
Proof. intros. solve_matrix. Qed.

Lemma rewrite_ket_prod01 : forall (q1 :  Matrix 2 1) (q2 : Matrix 1 2),
  (q1 × ⟨0∣) × (∣1⟩ × q2) = Zero.
Proof. intros. solve_matrix. Qed.

Lemma rewrite_ket_prod10 : forall (q1 :  Matrix 2 1) (q2 : Matrix 1 2),
  (q1 × ⟨1∣) × (∣0⟩ × q2) = Zero.
Proof. intros. solve_matrix. Qed.

Lemma rewrite_ket_prod11 : forall (q1 :  Matrix 2 1) (q2 : Matrix 1 2),
  WF_Matrix q1 -> WF_Matrix q2 -> (q1 × ⟨1∣) × (∣1⟩ × q2) = q1 × q2.
Proof. intros. solve_matrix. Qed.

(* Show that SWAP ≡ swap. *)
Lemma denote_SWAP_adjacent : forall {dim} n,
  @uc_well_typed dim (SWAP n (n + 1)) ->
  @uc_eval dim (SWAP n (n + 1)) = (I (2 ^ n)) ⊗ swap ⊗ (I (2 ^ (dim - 2 - n))).
Proof.
  intros dim n WT.
  assert (n + 1 < dim).
  { inversion WT; inversion H2. assumption. }
  clear WT.
  simpl; unfold ueval_cnot, pad.
  bdestruct (n <? n + 1); try lia.
  bdestruct (n + 1 <? n); try lia.
  replace (n + 1 - n) with 1 by lia; simpl.
  bdestruct (n + 2 <=? dim); try lia.
  clear - H.
  restore_dims_strong; Msimpl.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mmult_plus_distr_r. 
  restore_dims_strong; Msimpl.
  repeat rewrite Mmult_plus_distr_l.
  restore_dims_strong; Msimpl.
  replace (σx × ∣1⟩⟨1∣) with (∣0⟩⟨1∣) by (rewrite <- Mmult_assoc; Msimpl; reflexivity).
  replace (σx × ∣0⟩⟨0∣) with (∣1⟩⟨0∣) by (rewrite <- Mmult_assoc; Msimpl; reflexivity).
  replace (∣0⟩⟨0∣ × σx) with (∣0⟩⟨1∣) by (rewrite Mmult_assoc; Msimpl; reflexivity).
  replace (∣1⟩⟨1∣ × σx) with (∣1⟩⟨0∣) by (rewrite Mmult_assoc; Msimpl; reflexivity).
  repeat rewrite rewrite_ket_prod00; try auto with wf_db.
  repeat rewrite rewrite_ket_prod11; try auto with wf_db.
  repeat rewrite rewrite_ket_prod01.
  repeat rewrite rewrite_ket_prod10.
  repeat rewrite kron_0_l. 
  repeat rewrite Mplus_0_l, Mplus_0_r.
  replace (σx × ∣0⟩⟨1∣) with (∣1⟩⟨1∣) by (rewrite <- Mmult_assoc; Msimpl; reflexivity).
  repeat rewrite <- Mplus_assoc.
  assert (swap = ∣1⟩⟨1∣ ⊗ ∣1⟩⟨1∣ .+ ∣0⟩⟨1∣ ⊗ ∣1⟩⟨0∣ .+ ∣1⟩⟨0∣ ⊗ ∣0⟩⟨1∣ .+ ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣) by solve_matrix.
  rewrite H0.
  reflexivity.
Qed.

Lemma swap_adjacent_WT: forall b dim,
  b + 1 < dim -> @uc_well_typed dim (SWAP b (b + 1)).
Proof.
  intros b dim H.
  repeat apply WT_seq; apply WT_app2; lia.
Qed.

Lemma swap_adjacent_not_WT: forall b dim,
  b + 1 >= dim -> @uc_eval dim (SWAP b (b + 1)) = Zero.
Proof.
  intros b dim H.
  simpl; unfold ueval_cnot, pad.
  bdestruct (b <? b + 1); try lia.
  bdestruct (b + (1 + (b + 1 - b - 1) + 1) <=? dim); try lia.
  remove_zero_gates; trivial.
Qed.

Lemma swap_swap_id_adjacent: forall a dim,
  @uc_well_typed dim (SWAP a (a+1)) ->
  @uc_equiv dim (SWAP a (a+1); SWAP a (a+1)) uskip.
Proof.
  intros a dim WT.
  assert (a + 1 < dim).
  { inversion WT; inversion H2; assumption. }
  unfold uc_equiv.
  remember (SWAP a (a+1)) as s; simpl; subst.
  rewrite denote_SWAP_adjacent; try assumption.
  replace (2 ^ dim) with (2 ^ a * (2 ^ 1 * 2 ^ 1) * 2 ^ (dim - 2 - a)) by unify_pows_two.
  replace (2 ^ 1) with 2 by easy.
  repeat rewrite kron_mixed_product.
  rewrite swap_swap.
  Msimpl.
  reflexivity.
Qed.

Opaque SWAP.
Lemma swap_cnot_adjacent_left : forall {dim} a b,
  a < b ->
  @uc_equiv dim (SWAP b (b+1); CNOT a b; SWAP b (b+1)) (CNOT a (b+1)).
Proof.
  intros dim a b H.
  unfold uc_equiv.
  simpl; unfold ueval_cnot, pad.
  bdestruct (a <? b); try lia.
  bdestruct (a <? b + 1); try lia.
  remember (b - a - 1) as i.
  replace (b + 1 - a - 1) with (i + 1) by lia.
  bdestruct (a + (1 + (i + 1) + 1) <=? dim).
  2: { rewrite swap_adjacent_not_WT; try lia; remove_zero_gates; trivial. }
  bdestruct (a + (1 + i + 1) <=? dim); try lia.
  assert (b + 1 < dim) by lia.
  rewrite denote_SWAP_adjacent.
  2: { apply swap_adjacent_WT; assumption. }
  (* 1: rewrite identity matrices *)
  replace (2 ^ (dim - (1 + i + 1) - a)) with (2 * 2 ^ (dim - (1 + (i + 1) + 1) - a)) by unify_pows_two.
  replace (dim - (1 + (i + 1) + 1) - a) with (dim - 2 - b) by lia.
  replace (2 ^ (b - a)) with (2 ^ i * 2) by unify_pows_two.
  replace (2 ^ (i + 1)) with (2 ^ i * 2) by unify_pows_two.
  replace (2 ^ (b + 1 - a)) with (2 ^ i * 2 ^ 2) by unify_pows_two.
  replace (2 ^ b) with (2 ^ a * 2 * 2 ^ i) by unify_pows_two.  
  repeat rewrite <- id_kron.
  replace (2 ^ dim) with (2 ^ a * (2 ^ 1 * 2 ^ i * (2 ^ 2)) * 2 ^ (dim - 2 - b)) by unify_pows_two.
  replace (2 ^ 1) with 2 by easy.
  replace (2 ^ 2) with (2 * 2) by easy.
  clear.
  (* 2: manually mess with associativity *)
  rewrite (kron_assoc _ (I 2) _).
  restore_dims_strong.
  rewrite (kron_assoc _ _ swap).
  rewrite <- (kron_assoc ∣0⟩⟨0∣ _ (I 2)).
  rewrite <- (kron_assoc ∣0⟩⟨0∣ _ (I (2 ^ 2))).
  rewrite <- (kron_assoc ∣1⟩⟨1∣ _ (I 2)).
  restore_dims_strong.
  rewrite (kron_assoc _ (I 2) σx).
  rewrite <- (kron_assoc _ (I 2) (I (2 ^ (dim - 2 - b)))).
  rewrite (kron_assoc (I (2 ^ a)) _ (I 2)).
  rewrite kron_plus_distr_r.
  rewrite (kron_assoc _ σx (I 2)).
  rewrite (kron_assoc _ (I 2) (I 2)).
  (* 3: simplify *)
  replace (2 ^ a * (2 * 2 ^ i * 2) * 2) with (2 ^ a * (2 * 2 ^ i * (2 * 2))) by rewrite_assoc.
  replace (2 * 2 ^ i * 2 * 2) with (2 * 2 ^ i * (2 * 2)) by rewrite_assoc.
  Msimpl. 
  rewrite Mmult_plus_distr_r.
  rewrite Mmult_plus_distr_l.
  Msimpl. 
  repeat rewrite <- (Mmult_assoc swap _ swap).
  repeat rewrite swap_spec_general; try auto with wf_db.
  replace (2 ^ 2) with (2 * 2) by easy.
  replace (2 * (2 ^ i * 2) * 2) with (2 * 2 ^ i * (2 * 2)) by rewrite_assoc.
  reflexivity.
Qed.

Lemma swap_cnot_adjacent_right : forall {dim} a b,
  b + 1 < a ->
  @uc_equiv dim (SWAP b (b+1); CNOT a (b+1); SWAP b (b+1)) (CNOT a b).
Proof.
  intros dim a b H.
  unfold uc_equiv.
  simpl; unfold ueval_cnot, pad.
  bdestruct (b + 1 <? a); try lia.
  bdestruct (b <? a); try lia.
  bdestruct (a <? b + 1); try lia.
  bdestruct (a <? b); try lia.
  remember (a - b - 1) as i.
  remember (dim - (1 + i + 1) - b) as j.
  replace (a - (b + 1)) with i by lia.
  replace (dim - (1 + (i - 1) + 1) - (b + 1)) with j by lia.
  replace (b + 1 + (1 + (i - 1) + 1)) with (b + (1 + i + 1)) by lia.
  bdestruct (b + (1 + i + 1) <=? dim).
  2: { remove_zero_gates; trivial. }
  rewrite denote_SWAP_adjacent.
  2: { apply swap_adjacent_WT. lia. }
  (* 1: rewrite identity matrices *)
  replace (2 ^ (b + 1)) with (2 ^ b * 2) by unify_pows_two.
  replace (2 ^ i) with (2 * 2 ^ (i - 1)) by unify_pows_two.
  replace (2 ^ (a - b)) with ((2 ^ 2) * 2 ^ (i - 1)) by unify_pows_two.
  replace (2 ^ (dim - 2 - b)) with (2 ^ (i - 1) * 2 * 2 ^ j) by unify_pows_two.
  repeat rewrite <- id_kron.
  replace (2 ^ dim) with (2 ^ b * (2 ^ 2 * 2 ^ (i - 1) * 2) * 2 ^ j) by unify_pows_two.
  replace (2 ^ 2) with (2 * 2) by easy.
  replace (2 ^ (1 + i + 1)) with (2 ^ 1 * 2 ^ 1 * 2 ^ (i - 1) * 2 ^ 1) by unify_pows_two.
  replace (2 ^ 1) with 2 by easy.
  clear.
  (* 2: manually mess with associativity *)
  rewrite (kron_assoc _ swap _).
  rewrite <- (kron_assoc swap _ _).
  replace (2 * 2 * (2 ^ (i - 1) * 2 * 2 ^ j)) with (2 * 2 * 2 ^ (i - 1) * 2 * 2 ^ j) by rewrite_assoc.
  replace (2 * 2 * (2 ^ (i - 1) * 2)) with (2 * 2 * 2 ^ (i - 1) * 2) by rewrite_assoc.
  rewrite <- (kron_assoc (I (2 ^ b)) _ _).
  rewrite <- (kron_assoc swap _ _).
  rewrite <- (kron_assoc σx _ _).
  rewrite (kron_assoc (I (2 ^ b)) (I 2) _).
  restore_dims_strong.
  rewrite kron_plus_distr_l.
  repeat rewrite <- (kron_assoc (I 2) _ _).
  (* 3: simplify *)
  replace (2 ^ b * (2 * (2 * 2 ^ (i - 1) * 2))) with (2 ^ b * (2 * 2 * 2 ^ (i - 1) * 2)) by rewrite_assoc. 
  replace (2 * (2 * 2 ^ (i - 1) * 2)) with (2 * 2 * 2 ^ (i - 1) * 2) by rewrite_assoc.
  Msimpl.
  rewrite Mmult_plus_distr_r.
  rewrite Mmult_plus_distr_l.
  restore_dims_strong.
  Msimpl. 
  repeat rewrite <- (Mmult_assoc swap _ swap).
  repeat rewrite swap_spec_general; try auto with wf_db.
Qed.

Lemma move_target_left_equiv_cnot : forall {dim} base dist,
  @uc_equiv dim (move_target_left base dist) (CNOT base (base + dist + 1)).
Proof.
  intros dim base dist.
  induction dist.
  - replace (base + 0 + 1) with (base + 1) by lia; easy.
  - simpl.
    rewrite IHdist.
    replace (base + S dist) with (base + dist + 1) by lia.
    apply swap_cnot_adjacent_left.
    lia.
Qed. 

Lemma move_target_right_equiv_cnot : forall {dim} base dist,
   base >= dist -> @uc_equiv dim (move_target_right base dist) (CNOT (base + 1) (base - dist)).
Proof.
  intros dim base dist H.
  induction dist.
  - replace (base - 0) with base by lia; easy.
  - simpl.
    rewrite IHdist; try lia.
    replace (base - dist) with (base - S dist + 1) by lia.
    apply swap_cnot_adjacent_right.
    lia.
Qed.

(* map_to_lnn is semantics-preserving *)
Lemma map_to_lnn_sound : forall {dim} (c : ucom dim), c ≡ map_to_lnn c.
Proof.
  induction c; try easy.
  - simpl. rewrite <- IHc1. rewrite <- IHc2. reflexivity.
  - simpl. dependent destruction u.
    bdestruct (n <? n0).
    + rewrite (move_target_left_equiv_cnot n (n0 - n - 1)).
      replace (n + (n0 - n - 1) + 1) with n0 by lia.
      easy.
    + bdestruct (n0 <? n); try easy.
      rewrite (move_target_right_equiv_cnot (n - 1) (n - n0 - 1)) by lia.
      replace (n - 1 - (n - n0 - 1)) with n0 by lia.
      replace (n - 1 + 1) with n by lia.
      easy.
Qed.

(* linear nearest neighbor: 'all CNOTs are on adjacent qubits' *)
Inductive respects_LNN {dim} : ucom dim -> Prop :=
  | LNN_skip : respects_LNN uskip
  | LNN_seq : forall c1 c2, 
      respects_LNN c1 -> respects_LNN c2 -> respects_LNN (c1; c2)
  | LNN_app_u : forall (u : Unitary 1) n, respects_LNN (uapp1 u n)
  | LNN_app_cnot_left : forall n, respects_LNN (CNOT n (n+1))
  | LNN_app_cnot_right : forall n, respects_LNN (CNOT (n+1) n).

Transparent SWAP.
Lemma move_target_left_respects_lnn : forall {dim} base dist,
  @respects_LNN dim (move_target_left base dist).
Proof.
  intros dim base dist.
  induction dist.
  - simpl. apply LNN_app_cnot_left.
  - simpl. 
    repeat apply LNN_seq; 
    try apply LNN_app_cnot_left;
    try apply LNN_app_cnot_right.
    apply IHdist.
Qed. 

Lemma move_target_right_respects_lnn : forall {dim} base dist,
   base >= dist -> 
   @respects_LNN dim (move_target_right base dist).
Proof.
  intros dim base dist H.
  induction dist.
  - simpl. apply LNN_app_cnot_right.
  - simpl.
    repeat apply LNN_seq; 
    try apply LNN_app_cnot_left;
    try apply LNN_app_cnot_right.
    apply IHdist.
    lia.
Qed.

(* map_to_lnn produces programs that satisfy the LNN constraint. 

   The well-typedness constraint is necessary because gates applied
   to the incorrect number of arguments do not satisfy our LNN 
   property. (We can change this if we want). *)
Lemma map_to_lnn_correct : forall {dim} (c : ucom dim), 
  uc_well_typed c -> respects_LNN (map_to_lnn c).
Proof.
  intros dim c WT.
  induction WT.
  - apply LNN_skip.
  - simpl. apply LNN_seq; assumption.
  - dependent destruction u; apply LNN_app_u.
  - dependent destruction u; simpl.
    bdestruct (m <? n).
    apply move_target_left_respects_lnn.
    bdestruct (n <? m); try lia.
    apply move_target_right_respects_lnn; lia.
Qed.


(******************************)
(** Tenerife Mapping Example **)
(******************************)

(* Map to IBM's 5-qubit Tenerife machine. The connectivity graph for the 
   Tenerife machine is depicted here: https://github.com/Qiskit/ibmq-device-information/blob/master/backends/tenerife/V1/version_log.md 

   Ideally we would consider mapping to an arbitrary connectivity graph.
   But for now we'll be using a hardcoded graph because we haven't found an
   easy-to-use (and easy-to-extract) graph library for Coq. We've tried to
   keep the structure of the code general so we can use it as a guideline
   for future development. *)

(* CNOT connectivity between qubits. *)
Definition cnot_graph : list (nat * nat) := (1, 0) :: (2, 0) :: (2, 1) :: (3, 2) :: (3, 4) :: (4, 2) :: [].

(* Find a path to put the control adjacent to the target. This function 
   is (disgustingly) hardcoded for our harcoded graph, but should in general
   be a shortest path algorithm. *)
Definition find_path n1 n2 :=
  match n1, n2 with 
  | 0, 1 => 0 :: 1 :: []
  | 0, 2 => 0 :: 2 :: []
  | 0, 3 => 0 :: 2 :: 3 :: []
  | 0, 4 => 0 :: 2 :: 4 :: []
  | 1, 0 => 1 :: 0 :: []
  | 1, 2 => 1 :: 2 :: []
  | 1, 3 => 1 :: 2 :: 3 :: []
  | 1, 4 => 1 :: 2 :: 4 :: []
  | 2, 0 => 2 :: 0 :: []
  | 2, 1 => 2 :: 1 :: []
  | 2, 3 => 2 :: 3 :: []
  | 2, 4 => 2 :: 4 :: []
  | 3, 0 => 3 :: 2 :: 0 :: []
  | 3, 1 => 3 :: 2 :: 1 :: []
  | 3, 2 => 3 :: 2 :: []
  | 3, 4 => 3 :: 4 :: []
  | 4, 0 => 4 :: 2 :: 0 :: []
  | 4, 1 => 4 :: 2 :: 1 :: []
  | 4, 2 => 4 :: 2 :: []
  | 4, 3 => 4 :: 3 :: []
  | _, _ => [] (* bad input case *)
  end.

(* Loose formalism for describing paths (or rather walks) in a graph.
   A proper graph library would have more precise definitions. *)

Inductive begins_with : nat -> list nat -> Prop :=
  | begins_with_cons : forall h t, begins_with h (h :: t).

Inductive ends_with : nat -> list nat -> Prop :=
  | end_with_single_elmt : forall x, ends_with x [x]
  | ends_with_cons : forall x h t, ends_with x t -> ends_with x (h :: t).

Inductive valid_walk : list nat -> list (nat * nat) -> Prop :=
  | valid_walk_two_elmts : forall n1 n2 g, 
      In (n1, n2) g \/ In (n2, n1) g -> valid_walk (n1 :: n2 :: []) g
  | valid_walk_two_cons : forall n1 n2 t g, 
      In (n1, n2) g \/ In (n2, n1) g -> valid_walk (n2 :: t) g -> valid_walk (n1 :: n2 :: t) g.

Definition is_path p n1 n2 := 
  (begins_with n1 p) /\ (ends_with n2 p) /\ (valid_walk p cnot_graph).

(* This proof is ugly because of our hardcoded definition of find_path. *)
Lemma find_path_returns_path : forall n1 n2, 
  n1 <> n2 -> n1 < 5 -> n2 < 5 -> 
  is_path (find_path n1 n2) n1 n2.
Proof.
  intros.
  destruct n1.
  destruct n2; [| destruct n2; [| destruct n2 ; [| destruct n2; [| destruct n2]]]];
  try contradiction;
  try (contradict H1; lia);
  simpl; repeat split;
  try (left; repeat constructor; reflexivity);
  try (right; repeat constructor; reflexivity).
  destruct n1.
  destruct n2; [| destruct n2; [| destruct n2 ; [| destruct n2; [| destruct n2]]]];
  try contradiction;
  try (contradict H1; lia);
  simpl; repeat split;
  try (left; repeat constructor; reflexivity);
  try (right; repeat constructor; reflexivity).
  destruct n1.
  destruct n2; [| destruct n2; [| destruct n2 ; [| destruct n2; [| destruct n2]]]];
  try contradiction;
  try (contradict H1; lia);
  simpl; repeat split;
  try (left; repeat constructor; reflexivity);
  try (right; repeat constructor; reflexivity).
  destruct n1.
  destruct n2; [| destruct n2; [| destruct n2 ; [| destruct n2; [| destruct n2]]]];
  try contradiction;
  try (contradict H1; lia);
  simpl; repeat split;
  try (left; repeat constructor; reflexivity);
  try (right; repeat constructor; reflexivity).
  destruct n1.
  destruct n2; [| destruct n2; [| destruct n2 ; [| destruct n2; [| destruct n2]]]];
  try contradiction;
  try (contradict H1; lia);
  simpl; repeat split;
  try (left; repeat constructor; reflexivity);
  try (right; repeat constructor; reflexivity).
  contradict H0; lia.
Qed.

Definition beq_tup t t' := 
  match t, t' with
  | (n1, n2), (n1', n2') => (n1 =? n1') && (n2 =? n2')
  end.

Lemma beq_tup_refl : forall t t',
  beq_tup t t' = true <-> t = t'.
Proof.
  intros; unfold beq_tup.
  destruct t; destruct t'.
  split; intros.
  - apply andb_true_iff in H as [H1 H2].
    apply Nat.eqb_eq in H1; inversion H1; subst.
    apply Nat.eqb_eq in H2; inversion H2; subst.
    reflexivity.
  - apply andb_true_iff. 
    split; inversion H; subst; apply Nat.eqb_refl.
Qed.

Lemma tup_in_cnot_graph : forall n1 n2,
  existsb (beq_tup (n1, n2)) cnot_graph = true <-> In (n1, n2) cnot_graph.
Proof.
  intros.
  split; intros.
  - apply existsb_exists in H.
    destruct H; destruct x; destruct H as [H1 H2].
    apply beq_tup_refl in H2.
    inversion H2; subst.
    assumption.
  - apply existsb_exists.
    exists (n1, n2).
    split.
    assumption.
    apply beq_tup_refl; reflexivity.
Qed.

Inductive respects_tenerife_undirected : ucom 5 -> Prop :=
  | uTen_skip : respects_tenerife_undirected uskip
  | uTen_seq : forall c1 c2, 
      respects_tenerife_undirected c1 -> 
      respects_tenerife_undirected c2 -> 
      respects_tenerife_undirected (c1; c2)
  | uTen_app_u : forall (u : Unitary 1) n, respects_tenerife_undirected (uapp1 u n)
  | uTen_app_cnot : forall n1 n2, 
      (In (n1, n2) cnot_graph) \/ (In (n2, n1) cnot_graph) -> 
      respects_tenerife_undirected (CNOT n1 n2).

Inductive respects_tenerife : ucom 5 -> Prop :=
  | Ten_skip : respects_tenerife uskip
  | Ten_seq : forall c1 c2, 
      respects_tenerife c1 -> 
      respects_tenerife c2 -> 
      respects_tenerife (c1; c2)
  | Ten_app_u : forall (u : Unitary 1) n, respects_tenerife (uapp1 u n)
  | Ten_app_cnot : forall n1 n2, 
      In (n1, n2) cnot_graph -> respects_tenerife (CNOT n1 n2).


(** Version 1: Without logical <-> physical qubit mapping **)

Fixpoint do_cnot_along_path p : ucom 5 :=
  match p with
  | [] => uskip (* bad input case *)
  | n1 :: t => match t with 
             | [] => uskip (* bad input case *)
             | [n2] => CNOT n1 n2
             | n2 :: _ => SWAP n1 n2 ; do_cnot_along_path t ; SWAP n1 n2
             end
  end.

(* At this point all CNOTs should be between adjacent qubits, but
   they may not respect the direction of the edges in the connectivity
   graph. We can fix this by insert Hadamard gates before and after
   each offending CNOT. *)
Fixpoint fix_cnots (c : ucom 5) :=
  match c with
  | c1; c2 => fix_cnots c1; fix_cnots c2
  | uapp2 U_CNOT n1 n2 => 
      if existsb (beq_tup (n1, n2)) cnot_graph
      then CNOT n1 n2
      else H n1; H n2; CNOT n2 n1; H n1; H n2
  | _ => c
  end.

Fixpoint map_to_tenerife (c : ucom 5) :=
  match c with
  | c1; c2 => map_to_tenerife c1 ; map_to_tenerife c2
  | uapp2 U_CNOT n1 n2 => 
      let p := find_path n1 n2 in
      let c := do_cnot_along_path p in
      fix_cnots c
  | uapp1 u n => uapp1 u n
  | _ => c
  end.

(* Small examples *)
Definition test1 : ucom 5 := CNOT 0 2; X 3; CNOT 4 1; X 2; CNOT 3 2.
Definition test2 : ucom 5 := CNOT 4 1; CNOT 3 0; CNOT 3 2; CNOT 3 0; CNOT 2 1.
Compute (map_to_tenerife test1).
Compute (map_to_tenerife test2).
 
Lemma swap_cnot_general : forall {dim} a b c,
  (* well-typedness constraints *)
  a < dim -> b < dim -> c < dim ->
  a <> b -> b <> c -> a <> c ->
  (* main equivalence *)
  @uc_equiv dim (SWAP a b; CNOT b c; SWAP a b) (CNOT a c).
Proof. Admitted.

Lemma do_cnot_along_path_sound : forall n1 n2,
  n1 <> n2 -> n1 < 5 -> n2 < 5 ->
  CNOT n1 n2 ≡ do_cnot_along_path (find_path n1 n2).
Proof.
  intros.
  specialize (find_path_returns_path n1 n2 H H0 H1) as [H_l_begins [H_l_ends H_l_valid]].
  induction (find_path n1 n2); inversion H_l_begins; subst.
  clear H_l_begins.  
  destruct l.
  - inversion H_l_ends; subst. 
    contradict H; reflexivity.
    inversion H4.
  - simpl.
    destruct l.
    + inversion H_l_ends; subst.
      inversion H4; subst.
      reflexivity.
      inversion H5.
    +
 Admitted.

Lemma do_cnot_along_path_respects_undirected : forall n1 n2,
  respects_tenerife_undirected (do_cnot_along_path (find_path n1 n2)).
Proof.
Admitted.

Lemma H_swaps_CNOT : forall {dim} m n,
  @uc_equiv dim (CNOT m n) (H m; H n; CNOT n m; H m; H n).
Proof. Admitted.

Lemma fix_cnots_sound : forall c,
  c ≡ fix_cnots c.
Proof.
  intros.
  induction c; try reflexivity.
  - simpl. apply useq_congruence; assumption. 
  - unfold fix_cnots.
    destruct (existsb (beq_tup (n, n0)) cnot_graph);
    dependent destruction u.
    + reflexivity.
    + apply H_swaps_CNOT.
Qed.

Lemma fix_cnots_mapped : forall c,
  respects_tenerife_undirected c -> respects_tenerife (fix_cnots c).
Proof.
  intros.
  induction H.
  - constructor.
  - constructor. 
    apply IHrespects_tenerife_undirected1.
    apply IHrespects_tenerife_undirected2.
  - constructor.
  - destruct H. 
    + assert (existsb (beq_tup (n1, n2)) cnot_graph = true). 
      { apply tup_in_cnot_graph; assumption. }
      simpl; simpl in H0.
      rewrite H0.
      constructor; assumption.
    + remember (existsb (beq_tup (n1, n2)) cnot_graph) as e.
      symmetry in Heqe; destruct e. 
      assert (In (n1, n2) cnot_graph).
      { apply tup_in_cnot_graph; assumption. }
      simpl; simpl in Heqe.
      rewrite Heqe.
      constructor; assumption.
      simpl; simpl in Heqe.
      rewrite Heqe.
      repeat apply Ten_seq; try apply Ten_app_u.
      constructor.
      assumption.
Qed.

Lemma map_to_tenerife_sound : forall c, 
  uc_well_typed c -> c ≡ map_to_tenerife c.
Proof.
  intros.
  induction c; try reflexivity.
  - inversion H; subst. 
    simpl; apply useq_congruence. 
    apply IHc1; assumption.
    apply IHc2; assumption.
  - inversion H; subst. 
    dependent destruction u; simpl.
    rewrite <- fix_cnots_sound.
    rewrite <- do_cnot_along_path_sound; try assumption.
    reflexivity.
Qed.

Lemma map_to_tenerife_correct : forall c,
  respects_tenerife (map_to_tenerife c).
Proof.
  intros.
  induction c; try constructor; try assumption.
  dependent destruction u; simpl.
  apply fix_cnots_mapped.
  apply do_cnot_along_path_respects_undirected.
Qed.


(** Version 2: With logical <-> physical qubit mapping **)

(* Type for representing a logical <-> physical qubit mapping with dim 
   physical qubits. *)
Definition qmap (dim : nat) : Type := (nat -> nat) * (nat -> nat).

Definition l2p {dim} (m : qmap dim) q :=
  match m with
  | (m, _) => m q
  end.

Definition p2l {dim} (m : qmap dim) q :=
  match m with
  | (_, m) => m q
  end.

(* swap the logical qubits associated with physical qubits qphys1 and qphys2 *)
Definition swap_in_map {dim} (m : qmap dim) qphys1 qphys2 : qmap dim :=
  match m with
  | (m1, m2) => 
      let qlog1 := m2 qphys1 in
      let qlog2 := m2 qphys2 in
      let m1' q := if q =? qlog1 then qphys2
                   else if q =? qlog2 then qphys1 
                   else m1 q in
      let m2' q := if q =? qphys1 then qlog2 
                   else if q =? qphys2 then qlog1 
                   else m2 q in
      (m1', m2')
  end.

(* There may be a more elegant way to write this *)
Definition qmap_well_formed {dim} (m : qmap dim) := forall x y, 
  (x < dim /\ l2p m x = y) <-> (y < dim /\ p2l m y = x).

Lemma l2p_p2l_inverse : forall {dim} (m : qmap dim) q,
  qmap_well_formed m -> q < dim -> l2p m (p2l m q) = q.
Proof.
  unfold qmap_well_formed; intros.
  destruct m; simpl in *.
  specialize (H (n0 q) q) as [H1 H2].
  apply H2.
  split; try assumption; reflexivity.
Qed.

Lemma p2l_l2p_inverse : forall {dim} (m : qmap dim) q,
  qmap_well_formed m -> q < dim -> p2l m (l2p m q) = q.
Proof.
  unfold qmap_well_formed; intros.
  destruct m; simpl in *.
  specialize (H q (n q)) as [H1 H2].
  apply H1.
  split; try assumption; reflexivity.
Qed.    

Fixpoint path_to_swaps l (m : qmap 5) : (ucom 5 * qmap 5) :=
  match l with
  | [] => (uskip, m) (* bad input case *)
  | n1 :: t => match t with
             | [] => (uskip, m) (* bad input case *)
             | [n2] => (uskip, m) (* normal termination *)
             | n2 :: _ => let (c, m') := path_to_swaps t (swap_in_map m n1 n2) in
                        (SWAP n1 n2 ; c, m')
             end
  end.

(* Input:  program c and mapping m between logical and physical qubits
   Output: program c' that respects the Tenerife topology and resulting
           mapping m' between logical and physical qubits. 

   NOTE: The input program references logical qubits, and the output
   program references physical qubits. The soundness property says that
   the denotation of c is equivalent to the denotation of c', given 
   the reordering described by m' *)
Fixpoint map_to_tenerife_v2 (c : ucom 5) (m : qmap 5) :=
  match c with
  | c1; c2 => let (c1', m') := map_to_tenerife_v2 c1 m in
             let (c2', m'') := map_to_tenerife_v2 c2 m' in
             (c1'; c2', m'')
  | uapp2 U_CNOT n1 n2 => 
      let p := find_path (l2p m n1) (l2p m n2) in
      let (c, m') := path_to_swaps p m in
      let c' := fix_cnots (c; CNOT (l2p m' n1) (l2p m' n2)) in
      (c', m')
  | uapp1 u n => (uapp1 u (l2p m n), m)
  | _ => (c, m)
  end.

(* Small examples *)
Definition trivial_map : qmap 5 := (fun x => x, fun x => x).
Compute (map_to_tenerife_v2 test1 trivial_map).
Compute (map_to_tenerife_v2 test2 trivial_map).
Definition test_map : qmap 5 := 
  let l2p q := if q =? 0 then 4
               else if q =? 1 then 2
                    else if q =? 2 then 3
                         else if q =? 3 then 0
                              else 1 in
  let p2l q := if q =? 0 then 3
               else if q =? 1 then 4
                    else if q =? 2 then 1
                         else if q =? 3 then 2
                              else 0 in
  (l2p, p2l).
Compute (map_to_tenerife_v2 test1 test_map).
