Require Export ClassicalStates.

Local Open Scope ucom_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.

(** Some useful equivalences over unitary circuits. **)

Lemma ucom_id_l : forall {dim} n (c : base_ucom dim),
   uc_well_typed (@ID dim n) -> (ID n; c) ≡ c.
Proof.
  intros dim n c WT. 
  unfold uc_equiv.
  simpl; autorewrite with eval_db.
  apply uc_well_typed_ID in WT.
  bdestruct_all.
  repeat rewrite id_kron. 
  Msimpl_light; reflexivity.
Qed.

Lemma ucom_id_r : forall {dim} n (c : base_ucom dim),
   uc_well_typed (@ID dim n) -> (c ; ID n) ≡ c.
Proof.
  intros dim n c WT. 
  unfold uc_equiv.
  simpl; autorewrite with eval_db.
  apply uc_well_typed_ID in WT.
  bdestruct_all.
  repeat rewrite id_kron. 
  Msimpl_light; reflexivity.
Qed.

Lemma SKIP_id_l : forall {dim} (c : base_ucom dim),
   SKIP; c ≡ c.
Proof.
  intros dim c. 
  unfold uc_equiv.
  simpl. 
  destruct (uc_well_typed_b c) eqn:WT.
  - apply uc_well_typed_b_equiv in WT.
    apply uc_well_typed_implies_dim_nonzero in WT.
    autorewrite with eval_db; try assumption.
    Msimpl_light; reflexivity.
  - apply not_true_iff_false in WT. 
    rewrite uc_well_typed_b_equiv in WT.
    apply uc_eval_zero_iff in WT.
    rewrite WT.
    Msimpl_light; reflexivity.
Qed.

Lemma SKIP_id_r : forall {dim} (c : base_ucom dim),
   c; SKIP ≡ c.
Proof.
  intros dim c. 
  unfold uc_equiv.
  simpl. 
  destruct (uc_well_typed_b c) eqn:WT.
  - apply uc_well_typed_b_equiv in WT.
    apply uc_well_typed_implies_dim_nonzero in WT.
    autorewrite with eval_db; try assumption.
    Msimpl_light; reflexivity.
  - apply not_true_iff_false in WT. 
    rewrite uc_well_typed_b_equiv in WT.
    apply uc_eval_zero_iff in WT.
    rewrite WT.
    Msimpl_light; reflexivity.
Qed.

Lemma X_X_id : forall {dim} q, 
  X q; X q ≡ @ID dim q.
Proof. 
  intros dim q. 
  unfold uc_equiv.
  simpl; autorewrite with eval_db. 
  gridify.
  replace (σx × σx) with (I 2) by solve_matrix.
  reflexivity.
Qed.

Lemma X_CNOT_comm : forall {dim} c t, 
  @X dim t; CNOT c t ≡ CNOT c t ; X t.
Proof.
  intros dim c t.
  unfold uc_equiv.
  simpl; autorewrite with eval_db.
  gridify; reflexivity.
Qed.

Lemma H_H_id : forall {dim} q, 
  H q; H q ≡ @ID dim q.
Proof. 
  intros dim q. 
  unfold uc_equiv.
  simpl; autorewrite with eval_db. 
  gridify.
  replace (hadamard × hadamard) with (I 2) by solve_matrix.
  reflexivity.
Qed.

Lemma Rz_Rz_add : forall {dim} q θ θ', 
   @Rz dim θ q; Rz θ' q ≡ Rz (θ + θ') q.
Proof.
  intros.
  unfold uc_equiv.
  simpl; autorewrite with eval_db. 
  gridify. 
  rewrite phase_mul.
  rewrite Rplus_comm. 
  reflexivity.
Qed.

Lemma Rz_0_id : forall {dim} q, 
  Rz 0 q ≡ @ID dim q.
Proof.
  intros. 
  unfold uc_equiv.
  autorewrite with eval_db; simpl. 
  gridify.
  Qsimpl.
  reflexivity.
Qed.

Lemma U_V_comm : forall {dim} (m n : nat) (U V : base_Unitary 1),
  m <> n ->
  @uapp1 _ dim U m; uapp1 V n ≡ uapp1 V n ; uapp1 U m. 
Proof.
  intros.
  unfold uc_equiv; simpl.
  dependent destruction U; dependent destruction V.
  autorewrite with eval_db.
  gridify; reflexivity.
Qed.

(* A bit slow, due to six valid subcases *)
Lemma U_CNOT_comm : forall {dim} (q n1 n2 : nat) (U : base_Unitary 1),
  q <> n1 ->
  q <> n2 ->
  @uapp1 _ dim U q ; CNOT n1 n2 ≡ CNOT n1 n2 ; uapp1 U q. 
Proof.
  intros.
  unfold uc_equiv; simpl.
  dependent destruction U.
  autorewrite with eval_db.
  gridify; reflexivity.
Qed.

Lemma CNOT_CNOT_comm : forall {dim} (n1 n2 n1' n2' : nat),
  n1' <> n1 -> n1' <> n2 -> n2' <> n1 -> n2' <> n2 ->
  @CNOT dim n1 n2 ; CNOT n1' n2' ≡ CNOT n1' n2' ; CNOT n1 n2. 
Proof.
  intros.
  unfold uc_equiv; simpl.
  (* Works, but is painfully slow.
  autorewrite with eval_db.
  gridify; reflexivity. *) 
  specialize (bool_dec ((n1 <? dim) && (n2 <? dim) && negb (n1 =? n2) && (n1' <? dim) && (n2' <? dim) && negb (n1' =? n2')) true) as WT.
  destruct WT.
  repeat match goal with
  | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
  | H : _ <? _ = true |- _ => apply Nat.ltb_lt in H
  | H : _ =? _ = false |- _ => apply beq_nat_false in H 
  | H : negb _ = true |- _ => apply negb_true_iff in H
  end. 
  apply equal_on_basis_states_implies_equal; auto with wf_db.
  intro f.
  repeat rewrite Mmult_assoc.
  repeat rewrite f_to_vec_CNOT by auto.
  repeat rewrite update_index_neq by auto.
  rewrite update_twice_neq by auto.
  reflexivity.
  (* manual handling for badly typed cases *)
  autorewrite with eval_db.
  bdestruct_all.
  all: repeat rewrite Mmult_0_l; repeat rewrite Mmult_0_r; trivial. 
  (* hmm this is slow too. Just as bad as using gridify? *)
  all: bdestruct (n1 <? dim); try lia.
  all: bdestruct (n2 <? dim); try lia. 
  all: bdestruct (n1' <? dim); try lia.
  all: bdestruct (n2' <? dim); try lia.
  all: bdestruct (n1 =? n2); try lia.
  all: bdestruct (n1' =? n2'); try lia.
  all: contradict n; reflexivity.
Qed.

Lemma H_swaps_CNOT : forall {dim} m n,
  @H dim m; H n; CNOT n m; H m; H n ≡ CNOT m n.
Proof.
  intros.
  unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify; trivial. (* trivial shouldn't be necessary *)
  (* The trivial seems to be the result of autorewrite doing something weird.
     If you have 'repeat Msimpl_light' in gridify then you don't need the trivial. *)
  - rewrite <- 2 kron_plus_distr_r.
    apply f_equal2; trivial.
    repeat rewrite kron_assoc.
    restore_dims.
    rewrite <- 2 kron_plus_distr_l.
    apply f_equal2; trivial.
    replace (hadamard × hadamard) with (∣0⟩⟨0∣ .+ ∣1⟩⟨1∣) by solve_matrix.
    replace (hadamard × (σx × hadamard)) with (∣0⟩⟨0∣ .+ (- 1)%R .* ∣1⟩⟨1∣) by solve_matrix.
    distribute_plus.
    repeat rewrite <- Mplus_assoc.
    rewrite Mplus_swap_mid.    
    rewrite (Mplus_assoc _ _ _ (_ ⊗ (_ ⊗ ((-1)%R .* ∣1⟩⟨1∣)))).
    repeat rewrite Mscale_kron_dist_r.
    rewrite Mplus_comm.
    apply f_equal2.
    + rewrite <- Mscale_kron_dist_l.
      rewrite <- kron_plus_distr_r.
      apply f_equal2; trivial.
      solve_matrix.
    + rewrite <- kron_plus_distr_r.
      apply f_equal2; trivial.
      solve_matrix.
  - rewrite <- 2 kron_plus_distr_r.
    apply f_equal2; trivial.
    repeat rewrite kron_assoc.
    restore_dims.
    rewrite <- 2 kron_plus_distr_l.
    apply f_equal2; trivial.
    replace (hadamard × hadamard) with (∣0⟩⟨0∣ .+ ∣1⟩⟨1∣) by (Qsimpl; easy).
    replace (hadamard × (σx × hadamard)) with (∣0⟩⟨0∣ .+ (- 1)%R .* ∣1⟩⟨1∣) by solve_matrix.
    distribute_plus.
    repeat rewrite <- Mplus_assoc.
    rewrite Mplus_swap_mid.    
    rewrite (Mplus_assoc _ _ _ (((-1)%R .* ∣1⟩⟨1∣) ⊗ _)).
    rewrite Mplus_comm.
    apply f_equal2.
    + rewrite Mscale_kron_dist_l.
      rewrite <- Mscale_kron_dist_r.
      rewrite <- Mscale_kron_dist_r.
      repeat rewrite <- kron_assoc.
      restore_dims. 
      rewrite <- kron_plus_distr_l.
      apply f_equal2; trivial.
      solve_matrix.
    + rewrite <- 2 kron_plus_distr_l.
      apply f_equal2; trivial.
      apply f_equal2; trivial.
      solve_matrix.
Qed.
