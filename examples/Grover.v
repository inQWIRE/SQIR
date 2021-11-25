Require Import UnitaryOps.
Require Import Utilities.
Require Import QWIRE.Dirac.

(* Note: this file requires the version of Ratan in Coq >= 8.12.0 *)
Require Import Coq.Reals.Ratan. 

Local Open Scope ucom_scope.

(* Grover's search algorithm.

   Inputs:
   * n : number of input bits to f (must be at least 3)
   * f : nat -> bool function (must have both satisfying and falsifying solns)
   * Uf : SQIR program implementing f

   Grover's algorithm is a circuit with (n + 1) qubits that alternates between
   applying Uf and a "diffusion" operator. The last qubit in the circuit is
   an ancilla.

   The property we prove is that after i iterations, the probability 
   of measuring z where f z = true is sin^2((2i + 1) * θ) where
   θ = asin(√(k / 2^n)).

   The implementation of our diffusion operator is taken from "Grover’s 
   Algorithm: Quantum Database Search" by Lavor, Manssur, and Portugal.
   <https://arxiv.org/pdf/quant-ph/0301079.pdf>
*)

Section Grover.


(** Algorithm parameters **)

(* Number of input (qu)bits. *)
Variable n : nat.
Hypothesis n_ge_2 : (n >= 2)%nat.

(* Classical oracle function. *)
Variable f : nat -> bool.
Definition k := count f (2 ^ n).
Hypothesis f_has_both_good_and_bad_solutions : 0 < INR k < 2 ^ n. 

(* SQIR program implementing oracle. *)
Variable ancillae : nat.
Definition dim := (S n + ancillae)%nat.
Variable Uf : base_ucom dim.
Hypothesis Uf_implements_f : padded_boolean_oracle n Uf f.

Lemma dim_minus_Sn :
  (dim - S n)%nat = ancillae.
Proof.
  unfold dim. lia.
Qed.

Lemma pad_ancillae :
  forall v : Vector (2 ^ (S n)),
  pad_vector dim v = v ⊗ (kron_n ancillae ∣0⟩).
Proof.
  unfold padded_boolean_oracle, pad_vector. rewrite dim_minus_Sn. reflexivity.
Qed.

(** Program definition **)

(* Controlled-X with target (n-1) and controls 0, 1, ..., n-2 *)
Fixpoint generalized_Toffoli' n0 : base_ucom n :=
  match n0 with
  | O | S O => X (n - 1)
  | S n0' => UnitaryOps.control (n - n0) (generalized_Toffoli' n0')
  end.
Definition generalized_Toffoli := generalized_Toffoli' n.

(* Grover diffusion operator. *)
Definition diff : base_ucom n :=
  npar n U_H; npar n U_X ; 
  H (n - 1) ; generalized_Toffoli ; H (n - 1) ; 
  npar n U_X; npar n U_H.

(* Grover's algorithm (iterates applying Uf and diff). *)
Definition body := Uf ; cast diff dim.
Definition grover i := X n ; cast (npar (S n) U_H) dim ; niter i body.


(** Proof **)

(* Uniform superposition. *)
Definition ψ := 
  / √ (2 ^ n) .* vsum (2 ^ n) (fun k : nat => basis_vector (2 ^ n) k).

(* The "good" subspace satisfying f. *)
Definition ψg := 
  / (√ INR k) .*
  vsum (2 ^ n) 
       (fun k => if f k 
              then (basis_vector (2 ^ n) k)
              else Zero).

(* The "bad" subspace not satisfying f. *)
Definition ψb := 
  / (√ (2 ^ n - INR k)) .*
  vsum (2 ^ n) 
       (fun k => if f k 
              then Zero
              else (basis_vector (2 ^ n) k)).

Lemma WF_ψ : WF_Matrix ψ.
Proof.
  unfold ψ.
  auto with wf_db.
Qed.

Lemma WF_ψg : WF_Matrix ψg.
Proof.
  unfold ψg.
  apply WF_scale.
  apply vsum_WF.
  intros.
  destruct (f i); auto with wf_db.
Qed.

Lemma WF_ψb : WF_Matrix ψb.
Proof.
  unfold ψb.
  apply WF_scale.
  apply vsum_WF.
  intros.
  destruct (f i); auto with wf_db.
Qed.
Hint Resolve WF_ψ WF_ψg WF_ψb : wf_db.

(* ψ can be rewritten as a sum of ψg and ψb. *)

Definition θ := asin (√ (INR k / 2 ^ n)).

Lemma decompose_ψ : ψ = sin θ .* ψg .+ cos θ .* ψb.
Proof.
  specialize f_has_both_good_and_bad_solutions as H.
  assert (INR k / 2 ^ n < 1).
  { autorewrite with R_db.
    replace 1%R with (2 ^ n * / 2 ^ n)%R.
    apply Rmult_lt_compat_r; nonzero.
    apply Rinv_r. nonzero. }
  unfold θ, ψ, ψg, ψb.
  rewrite sin_asin, cos_asin.
  distribute_scale. 
  rewrite Rsqr_sqrt.
  autorewrite with RtoC_db.
  repeat rewrite inv_sqrt. 
  repeat rewrite <- sqrt_mult.
  field_simplify (INR k / 2 ^ n * / INR k)%R.
  field_simplify ((1 - INR k / 2 ^ n) * / (2 ^ n - INR k))%R.
  all: try lra; try nonzero.
  rewrite <- Mscale_plus_distr_r.
  apply f_equal2.
  autorewrite with R_db.
  reflexivity.
  rewrite <- vsum_plus.
  apply vsum_eq.
  intros.
  destruct (f i); lma.
  all: autorewrite with R_db.
  all: try (apply Rlt_le; nonzero).
  split.
  assert (0 <= √ (INR k * / 2 ^ n)).
  apply sqrt_pos.
  lra. 
  rewrite <- sqrt_1.
  apply sqrt_le_1; try lra.
  apply Rlt_le. nonzero.
  split.
  assert (0 <= √ (INR k * / 2 ^ n)).
  apply sqrt_pos.
  lra. 
  rewrite <- sqrt_1.
  apply sqrt_le_1; try lra.
  apply Rlt_le. nonzero.
Qed.

(* ψg and ψb are orthogonal. *)

Lemma ψg_ψb_orthogonal : ψg† × ψb = Zero.
Proof.
  unfold ψg, ψb.
  rewrite Mscale_adj.
  distribute_scale.
  rewrite Mmult_adj_vsum_distr_l.
  erewrite vsum_eq.
  2: { intros. rewrite Mmult_vsum_distr_l. reflexivity. }
  rewrite vsum_diagonal.
  rewrite vsum_0.
  lma.
  intros.
  destruct (f x); Msimpl; reflexivity.
  intros.
  destruct (f i); destruct (f j); Msimpl; try reflexivity.
  apply basis_vector_product_neq; assumption.
Qed.

Lemma ψb_ψg_orthogonal : ψb† × ψg = Zero.
Proof.
  rewrite <- (adjoint_involutive _ _ ψg).
  rewrite <- Mmult_adjoint.
  rewrite ψg_ψb_orthogonal.
  lma.
Qed.

Lemma ψg_ψg_unit : ψg† × ψg = I 1.
Proof.
  specialize f_has_both_good_and_bad_solutions as H.
  unfold ψg.
  rewrite Mscale_adj.
  distribute_scale.
  rewrite Mmult_adj_vsum_distr_l.
  erewrite vsum_eq.
  2: { intros. rewrite Mmult_vsum_distr_l. reflexivity. }
  rewrite vsum_diagonal.
  rewrite (vsum_eq _ _ (fun i => if f i then I 1 else Zero)).
  2: { intros. destruct (f i); Msimpl; auto.
       apply basis_vector_product_eq; auto. }
  rewrite vsum_count.
  replace (count f (2 ^ n)) with k by reflexivity.
  distribute_scale.
  rewrite <- RtoC_inv by nonzero.
  rewrite Cconj_R.
  autorewrite with RtoC_db.
  rewrite <- Rinv_mult_distr by nonzero.
  rewrite sqrt_def by lra.
  field_simplify (/ INR k * INR k)%R.
  lma.
  nonzero.
  intros.
  destruct (f i); destruct (f j); Msimpl; try reflexivity.
  apply basis_vector_product_neq; assumption.
Qed.

Lemma ψb_ψb_unit : ψb† × ψb = I 1.
Proof.
  specialize f_has_both_good_and_bad_solutions as H.
  unfold ψb.
  rewrite Mscale_adj.
  distribute_scale.
  rewrite Mmult_adj_vsum_distr_l.
  erewrite vsum_eq.
  2: { intros. rewrite Mmult_vsum_distr_l. reflexivity. }
  rewrite vsum_diagonal.
  rewrite (vsum_eq _ _ (fun i => if negf f i then I 1 else Zero)).
  2: { intros. unfold negf. destruct (f i); Msimpl; auto.
       apply basis_vector_product_eq; auto. }
  rewrite vsum_count.
  rewrite count_negf.
  replace (count f (2 ^ n)) with k by reflexivity.
  distribute_scale.
  rewrite <- RtoC_inv by nonzero.
  rewrite Cconj_R.
  autorewrite with RtoC_db.
  rewrite <- Rinv_mult_distr by nonzero.
  rewrite sqrt_def by lra.
  rewrite minus_INR.
  replace (INR (2 ^ n)) with (2 ^ n)%R.
  field_simplify (/ (2 ^ n - INR k) * (2 ^ n - INR k))%R.
  lma.
  nonzero. 
  rewrite pow_INR.
  reflexivity.
  apply INR_le.
  rewrite pow_INR.
  replace (INR 2) with 2%R by reflexivity. 
  lra.  
  intros.
  destruct (f i); destruct (f j); Msimpl; try reflexivity.
  apply basis_vector_product_neq; assumption.
Qed.

Lemma ψ_ψg_product : ψ† × ψg = sin θ .* I 1.
Proof.
  rewrite decompose_ψ.
  rewrite Mplus_adjoint, 2 Mscale_adj.
  distribute_plus.
  distribute_scale.
  rewrite ψg_ψg_unit, ψb_ψg_orthogonal.
  lma.
Qed.

Lemma ψ_ψb_product : ψ† × ψb = cos θ .* I 1.
Proof.
  rewrite decompose_ψ.
  rewrite Mplus_adjoint, 2 Mscale_adj.
  distribute_plus.
  distribute_scale.
  rewrite ψb_ψb_unit, ψg_ψb_orthogonal.
  lma.
Qed.

(* Facts about the diffusion operator (diff). *)

Lemma fresh_generalized_Toffoli' : forall m p, 
  (p > 0)%nat -> (m < n - p)%nat -> is_fresh m (generalized_Toffoli' p).
Proof.
  intros.
  induction p. lia.
  destruct p. simpl.
  apply fresh_X. lia.
  replace (generalized_Toffoli' (S (S p))) 
    with (UnitaryOps.control (n - (S (S p))) (generalized_Toffoli' (S p)))
    by reflexivity.
  apply fresh_control. 
  split. lia.
  apply IHp; lia.
Qed.

Lemma generalized_Toffoli'_WT : forall m, 
  (m <= n)%nat -> uc_well_typed (generalized_Toffoli' m).
Proof.
  specialize n_ge_2 as H.
  intros.
  induction m; simpl.
  apply uc_well_typed_X. lia.
  destruct m.
  apply uc_well_typed_X. lia.
  apply uc_well_typed_control. 
  repeat split.
  lia.
  apply fresh_generalized_Toffoli'; lia.
  apply IHm. lia.
Qed.

Lemma diff_WT : uc_well_typed diff.
Proof.  
  specialize n_ge_2 as H.
  repeat constructor.
  all: try apply npar_WT; try lia.
  all: try apply uc_well_typed_H; try lia.
  unfold generalized_Toffoli.
  apply generalized_Toffoli'_WT.
  lia.
Qed.

Lemma proj_split : forall q b,
  (q < n - 1)%nat -> proj q n b = proj q (n - 1) b ⊗ I 2.
Proof.
  intros.
  unfold proj, pad.
  bdestruct_all.
  repeat rewrite kron_assoc by auto with wf_db.
  restore_dims. 
  repeat rewrite kron_assoc by auto with wf_db.
  rewrite id_kron.
  replace (2 ^ (n - 1 - (q + 1)) * 2)%nat 
    with (2 ^ (n - (q + 1)))%nat by unify_pows_two.
  restore_dims.
  reflexivity.
Qed.

Lemma generalized_Toffoli_semantics_A : forall m (f : nat -> bool) (b : bool),
  (m <= n)%nat -> (forall i, (n - m <= i)%nat -> (i < n - 1)%nat -> f i = true) ->
  @Mmult _ _ 1 (uc_eval (generalized_Toffoli' m)) 
               (f_to_vec (n - 1) f ⊗ ∣ Nat.b2n b ⟩) = 
    f_to_vec (n - 1) f ⊗ ∣ Nat.b2n (negb b) ⟩.
Proof.
  specialize n_ge_2 as H.
  intros.
  induction m; [| destruct m].
  - simpl.
    autorewrite with eval_db.
    bdestruct_all.
    replace (n - (n - 1 + 1))%nat with O by lia.
    simpl. Msimpl.
    restore_dims.
    rewrite kron_mixed_product.
    Msimpl.
    destruct b; simpl; autorewrite with ket_db; reflexivity. 
  - simpl.
    autorewrite with eval_db.
    bdestruct_all.
    replace (n - (n - 1 + 1))%nat with O by lia.
    simpl. Msimpl.
    restore_dims.
    rewrite kron_mixed_product.
    Msimpl.
    destruct b; simpl; autorewrite with ket_db; reflexivity.
  - replace (generalized_Toffoli' (S (S m)))  
      with (UnitaryOps.control (n - (S (S m))) (generalized_Toffoli' (S m)))
      by reflexivity.
    rewrite control_correct.
    distribute_plus.
    rewrite Mmult_assoc.
    rewrite IHm.
    rewrite 2 proj_split by lia.
    restore_dims.
    repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite (f_to_vec_proj_eq _ _ _ true).
    rewrite (f_to_vec_proj_neq _ _ _ false).
    lma.
    all: try lia.
    1,2: rewrite H1 by lia; easy.
    intros. apply H1; lia.
    apply fresh_generalized_Toffoli'; lia.
    apply generalized_Toffoli'_WT; lia.
Qed.

Lemma generalized_Toffoli_semantics_B : forall m (f : nat -> bool) (b : bool),
  (m <= n)%nat -> (exists i, (n - m <= i)%nat /\ (i < n - 1)%nat /\ f i = false) ->
  @Mmult _ _ 1 (uc_eval (generalized_Toffoli' m)) 
               (f_to_vec (n - 1) f ⊗ ∣ Nat.b2n b ⟩) = 
    f_to_vec (n - 1) f ⊗ ∣ Nat.b2n b ⟩.
Proof.
  specialize n_ge_2 as H.
  intros.
  destruct H1 as [? [? [? ?]]].
  induction m; [| destruct m].
  - lia. (* first two cases contradict the "exists" assumption *)
  - lia.
  - replace (generalized_Toffoli' (S (S m)))  
      with (UnitaryOps.control (n - (S (S m))) (generalized_Toffoli' (S m)))
      by reflexivity.
    rewrite control_correct.
    distribute_plus.
    bdestruct (n - S (S m) =? x); subst.
    rewrite proj_fresh_commutes.
    rewrite 2 proj_split by lia.
    rewrite Mmult_assoc.
    restore_dims.
    repeat rewrite kron_mixed_product.
    rewrite (f_to_vec_proj_neq _ _ _ true).
    rewrite (f_to_vec_proj_eq _ _ _ false).
    do 2 Msimpl. lma.
    all: try lia.
    1,2: rewrite H3; easy.
    apply fresh_generalized_Toffoli'; lia.
    rewrite Mmult_assoc.
    rewrite IHm by lia.
    rewrite 2 proj_split by lia.
    restore_dims.
    repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite <- kron_plus_distr_r.
    rewrite <- Mmult_plus_distr_r.
    rewrite Mplus_comm.
    rewrite proj_sum.
    Msimpl. reflexivity.
    lia.
    apply fresh_generalized_Toffoli'; lia.
    apply generalized_Toffoli'_WT; lia.
Qed.

Lemma kron_n_σx : forall n f,
  n ⨂ σx × f_to_vec n f = f_to_vec n (negf f).
Proof.
  clear.
  intros n f.
  induction n; simpl.
  Msimpl. reflexivity.
  restore_dims. 
  rewrite kron_mixed_product.
  rewrite IHn0.
  unfold negf.
  destruct (f n0); simpl; autorewrite with ket_db; reflexivity.
Qed.

(* Notice the global phase of -1 compared to the standard definition. *)
Lemma diff_semantics : uc_eval diff = (-2) .* ψ × ψ† .+ I (2 ^ n).
Proof.
  specialize n_ge_2 as H.
  unfold diff.
  simpl.
  (* initial rewriting to get rid of H gates *)
  rewrite npar_H by lia.
  unfold ψ.
  rewrite <- H0_kron_n_spec_alt by lia.
  restore_dims.
  rewrite Mmult_adjoint.
  rewrite 2 kron_n_adjoint; auto with wf_db.
  rewrite hadamard_sa.
  replace (I (2 ^ n)) with (n ⨂ hadamard × I (2 ^ n) × n ⨂ hadamard).
  2: { Msimpl. rewrite kron_n_mult. 
       rewrite MmultHH. apply kron_n_I. }
  rewrite <- Mscale_mult_dist_r.
  repeat rewrite Mmult_assoc.
  rewrite <- Mmult_plus_distr_l.
  apply f_equal2; try reflexivity.
  repeat rewrite <- Mmult_assoc.
  rewrite <- Mmult_plus_distr_r.
  apply f_equal2; try reflexivity.
  (* switch to reasoning over basis vectors *)
  apply equal_on_basis_vectors_implies_equal; auto with wf_db.
  intros i Hi.
  rewrite npar_correct by lia.
  simpl.
  rewrite pauli_x_rotation.
  autorewrite with eval_db.
  bdestruct_all.
  clear - H Hi n_ge_2 f f_has_both_good_and_bad_solutions.
  replace (n - (n - 1 + 1))%nat with O by lia.
  simpl I.
  Msimpl.
  restore_dims.
  replace (n ⨂ σx) with ((n - 1) ⨂ σx ⊗ σx).
  2: { replace ((n - 1) ⨂ σx ⊗ σx) with ((S (n - 1)) ⨂ σx) by reflexivity.
       replace (S (n - 1)) with n by lia.
       reflexivity. }
  rewrite <- kron_n_adjoint; auto with wf_db.
  replace (n ⨂ ∣0⟩) with ((n - 1) ⨂ ∣0⟩ ⊗ ∣0⟩).
  2: { replace ((n - 1) ⨂ ∣0⟩ ⊗ ∣0⟩) with ((S (n - 1)) ⨂ ∣0⟩) by reflexivity.
       replace (S (n - 1)) with n by lia.
       reflexivity. }
  replace (I (2 ^ n)) with (I (2 ^ (n - 1)) ⊗ I 2).
  2: { rewrite id_kron. unify_pows_two.
       replace (n - 1 + 1)%nat with n by lia. 
       reflexivity. }
  rewrite basis_f_to_vec_alt by assumption.
  remember (nat_to_funbool n i) as fi; clear Heqfi.
  rewrite (f_to_vec_split 0 n (n - 1)) by lia.
  replace (n - 1 - (n - 1))%nat with O by lia.
  simpl f_to_vec.
  Msimpl.
  (* The on-paper argument destructs on whether the input vector is zero vs. 
     nonzero; in one case the program flips the sign, in the other case it 
     doesn't. We more or less follow that argument here, although it's a little
     messy due to matrix rewriting.  *)
  distribute_plus.
  repeat rewrite Mmult_assoc.
  restore_dims.
  distribute_scale.
  repeat rewrite kron_mixed_product.
  Msimpl.
  replace (σx × ∣ Nat.b2n (fi (n - 1)%nat) ⟩)
    with (∣ Nat.b2n (negb (fi (n - 1)%nat)) ⟩).
  2: { destruct (fi (n - 1)%nat); simpl; autorewrite with ket_db; reflexivity. }
  rewrite H_spec.
  distribute_scale.
  rewrite kron_plus_distr_l.
  distribute_plus.
  distribute_scale.
  rewrite kron_n_σx.
  rewrite kron_n_adjoint; auto with wf_db.
  repeat rewrite kron_mixed_product.
  rewrite kron_n_mult.
  Msimpl.
  replace ∣ 0 ⟩ with ∣ Nat.b2n false ⟩ by reflexivity.
  replace ∣ 1 ⟩ with ∣ Nat.b2n true ⟩ by reflexivity.
  unfold generalized_Toffoli.
  bdestruct (count fi (n - 1) =? 0)%nat.
  + specialize (count_zero _ _ H0) as Hf.
    rewrite 2 generalized_Toffoli_semantics_A; auto.
    2: { intros. unfold negf. 
         apply eq_true_not_negb, not_true_iff_false. 
         apply Hf. assumption. }
    2: { intros. unfold negf. 
         apply eq_true_not_negb, not_true_iff_false. 
         apply Hf. assumption. }
    simpl.
    Msimpl.
    autorewrite with ket_db.
    group_radicals.
    repeat rewrite Mplus_assoc.
    rewrite <- (Mplus_assoc _ _ (_ .* (_ ⊗ ∣ 0 ⟩))).
    rewrite (Mplus_comm _ _ (_ .* (_ ⊗ ∣ 0 ⟩))).
    repeat rewrite <- Mplus_assoc.
    rewrite <- Mscale_plus_distr_l.
    rewrite Mplus_assoc.
    rewrite <- Mscale_plus_distr_l.
    rewrite kron_n_σx.
    rewrite negf_involutive.
    assert (forall m f, (forall i, (i < m)%nat -> f i = false) ->
                 m ⨂ (∣ 0 ⟩ × (bra 0)) × f_to_vec m f = f_to_vec m f).
    { clear.
      intros m f Hf.
      induction m; simpl.
      Msimpl. reflexivity.
      restore_dims.
      rewrite kron_mixed_product, IHm.
      replace (f m) with false.
      simpl.
      autorewrite with ket_db; reflexivity.
      rewrite Hf; auto.
      intros.
      apply Hf; lia. }
    rewrite H1 by assumption; clear H1. 
    destruct (fi (n - 1)%nat); simpl; autorewrite with ket_db RtoC_db.
    field_simplify (/ 2 + / 2 * 1)%R.
    field_simplify (- / 2 + / 2 * 1)%R.
    autorewrite with R_db.
    Msimpl.
    reflexivity.
    field_simplify (/ 2 + / 2 * (-1 * 1))%R.
    field_simplify (- / 2 + / 2 * (-1 * 1))%R.
    autorewrite with R_db.
    Msimpl.
    replace (-2 * / 2)%R with (-2 + 1)%R by lra.
    rewrite RtoC_plus.
    rewrite Mscale_plus_distr_l.
    Msimpl.
    reflexivity.
  + specialize (count_nonzero _ _ H0) as Hf.
    destruct Hf as [x [? ?]].
    rewrite 2 generalized_Toffoli_semantics_B; auto.
    2: { exists x. repeat split; try lia. 
         unfold negf. apply negb_false_iff. 
         assumption. }
    2: { exists x. repeat split; try lia. 
         unfold negf. apply negb_false_iff. 
         assumption. }
    simpl.
    Msimpl.
    autorewrite with ket_db.
    group_radicals.
    repeat rewrite Mplus_assoc.
    rewrite <- (Mplus_assoc _ _ (_ .* (_ ⊗ ∣ 0 ⟩))).
    rewrite (Mplus_comm _ _ (_ .* (_ ⊗ ∣ 0 ⟩))).
    repeat rewrite <- Mplus_assoc.
    rewrite <- Mscale_plus_distr_l.
    rewrite Mplus_assoc.
    rewrite <- Mscale_plus_distr_l.
    rewrite kron_n_σx.
    rewrite negf_involutive.
    assert (forall m f, (exists i, (i < m)%nat /\ f i = true) ->
                 m ⨂ (∣ 0 ⟩ × (bra 0)) × f_to_vec m f = Zero).
    { clear.
      intros m f [i [? ?]].
      induction m; simpl.
      lia.
      restore_dims.
      rewrite kron_mixed_product. 
      bdestruct (i =? m); subst.
      rewrite H0.
      simpl.
      autorewrite with ket_db; reflexivity.
      rewrite IHm by lia.
      lma. }
    rewrite H3; clear H3.
    2: exists x; auto.
    destruct (fi (n - 1)%nat); simpl; autorewrite with ket_db RtoC_db.
    field_simplify (/ 2 + / 2 * 1)%R.
    field_simplify (/ 2 + - (/ 2 * 1))%R.
    autorewrite with R_db.
    Msimpl.
    reflexivity.
    field_simplify (/ 2 + / 2 * (-1 * 1))%R.
    field_simplify (/ 2 + - (/ 2 * (-1 * 1)))%R.
    autorewrite with R_db.
    Msimpl.
    reflexivity.
Qed.
Local Opaque diff.

(* Facts about the oracle (Uf). *)

Local Coercion Nat.b2n : bool >-> nat.
Lemma Uf_action_on_ψg : forall (b : bool),
  @Mmult _ _ 1 (uc_eval Uf) (@pad_vector (S n) dim (ψg ⊗ ∣ b ⟩)) =
    @pad_vector (S n) dim (ψg ⊗ ∣ negb b ⟩).
Proof.
  intros. repeat rewrite pad_ancillae.
  unfold ψg.
  restore_dims. distribute_scale.
  rewrite 2 kron_vsum_distr_r.
  replace (2 ^ n * 2)%nat with (2 ^ (S n))%nat by unify_pows_two.
  rewrite Nat.pow_1_l. repeat rewrite kron_vsum_distr_r.
  repeat rewrite Nat.mul_1_r.
  unify_pows_two.
  rewrite Mmult_vsum_distr_l.
  apply f_equal2; auto.
  apply vsum_eq.
  intros.
  destruct (f i) eqn:fi; Msimpl.
  specialize (Uf_implements_f i b H) as Hu.
  repeat rewrite pad_ancillae in Hu.
  rewrite fi, xorb_true_r in *.
  unify_pows_two. rewrite Nat.add_1_r.
  restore_dims.
  apply Hu.
  Msimpl. reflexivity.
Qed.

Lemma Uf_action_on_ψb : forall (b : bool),
  @Mmult _ _ 1 (uc_eval Uf) (@pad_vector (S n) dim (ψb ⊗ ∣ b ⟩)) =
    @pad_vector (S n) dim (ψb ⊗ ∣ b ⟩).
Proof.
  intros. rewrite pad_ancillae.
  unfold ψb.
  restore_dims. distribute_scale.
  rewrite kron_vsum_distr_r.
  replace (2 ^ n * 2)%nat with (2 ^ (S n))%nat by unify_pows_two.
  repeat rewrite Nat.mul_1_l. rewrite Nat.pow_1_l.
  repeat rewrite kron_vsum_distr_r.
  unify_pows_two. replace (S n + ancillae)%nat with dim by reflexivity.
  rewrite Mmult_vsum_distr_l.
  apply f_equal2; auto.
  apply vsum_eq.
  intros.
  destruct (f i) eqn:fi; Msimpl.
  Msimpl. reflexivity.
  specialize (Uf_implements_f i b H) as Hu.
  repeat rewrite pad_ancillae in Hu.
  rewrite fi, xorb_false_r in *.
  apply Hu.
Qed.

Lemma Uf_action_on_arbitrary_state : forall α β,
  @Mmult _ _ 1 (uc_eval Uf)
      (@pad_vector (S n) dim ((α .* ψg .+ β .* ψb) ⊗ ∣-⟩)) = 
    @pad_vector (S n) dim (((- α) .* ψg .+ β .* ψb) ⊗ ∣-⟩).
Proof.
  intros. repeat rewrite pad_ancillae.
  distribute_plus.
  restore_dims.
  rewrite kron_plus_distr_r.
  distribute_plus.
  distribute_scale.
  replace (∣ 0 ⟩) with (∣ false ⟩) by reflexivity.
  replace (∣ 1 ⟩) with (∣ true ⟩) by reflexivity.
  replace (2 ^ n * 2)%nat with (2 ^ S n)%nat by (simpl; lia).
  repeat rewrite <- pad_ancillae.
  restore_dims.
  repeat rewrite Uf_action_on_ψg.
  repeat rewrite Uf_action_on_ψb.
  lma.
Qed.

(* Main correctness property. *)

(* (-1)^i due to the global phase instroduced by diff; we could "fix" this
   by adding a global phase gate to SQIR, although it doesn't affect final
   measurement outcome. *)
Local Opaque Nat.mul.
Lemma loop_body_action_on_unif_superpos : forall i,
  @Mmult _ _ (1^n) (i ⨉ uc_eval body) (@pad_vector (S n) dim (ψ ⊗ ∣-⟩)) =
    @pad_vector (S n) dim ((-1)^i .* (sin (INR (2 * i + 1) * θ) .* ψg .+ 
                cos (INR (2 * i + 1) * θ) .* ψb) ⊗ ∣-⟩).
Proof.
  intros.
  repeat rewrite pad_ancillae.
  induction i.
  - replace (2 * 0 + 1)%nat with 1%nat by lia.
    simpl.
    autorewrite with R_db.
    Msimpl.
    rewrite decompose_ψ.  
    reflexivity.
  - simpl in *.
    rewrite Mmult_assoc.
    rewrite IHi; clear IHi.
    unfold dim.
    replace (uc_eval (cast diff (S n + ancillae)))
        with (uc_eval (cast diff (n + S ancillae))).
    2: { replace (S n + ancillae)%nat with (n + S ancillae)%nat by lia.
         reflexivity. }
    rewrite <- pad_dims_r.
    2: apply diff_WT.
    restore_dims.
    rewrite Mmult_assoc.
    restore_dims.
    distribute_scale.
    replace (2 ^ n * 2)%nat with (2 ^ (S n))%nat by unify_pows_two.
    rewrite <- pad_ancillae.
    restore_dims.
    rewrite Uf_action_on_arbitrary_state.
    rewrite pad_ancillae.
    restore_dims.
    rewrite kron_assoc; auto with wf_db.
    rewrite Nat.pow_1_l.
    rewrite kron_mixed_product.
    replace (2 ^ S ancillae)%nat with (2 * 2 ^ ancillae)%nat by reflexivity.
    rewrite <- id_kron.
    restore_dims.
    rewrite kron_mixed_product.
    Msimpl.
    rewrite <- kron_assoc; auto with wf_db.
    restore_dims.
    rewrite <- Mscale_kron_dist_l.
    unify_pows_two. restore_dims.
    rewrite <- Mscale_kron_dist_l.
    rewrite <- Mscale_kron_dist_l.
    rewrite Mscale_kron_dist_l.
    replace (2 ^ n * 2)%nat with (2 ^ S n)%nat by (simpl; lia).
    repeat rewrite <- pad_ancillae.
    apply f_equal.
    restore_dims.
    rewrite Cmult_comm.
    rewrite <- Mscale_assoc.
    rewrite <- (Mscale_kron_dist_l _ _ _ _ (-1)).
    do 2 (apply f_equal2; try reflexivity).
    rewrite diff_semantics.
    distribute_plus.
    distribute_scale.
    Msimpl.
    rewrite 2 Mmult_assoc.
    rewrite ψ_ψg_product, ψ_ψb_product.
    distribute_scale.
    Msimpl.
    rewrite decompose_ψ.
    repeat rewrite Mscale_plus_distr_r.
    distribute_scale.
    do 2 (rewrite <- Mplus_assoc;
          match goal with
          | |- context [?a .+ ?b .* ψg] => rewrite (Mplus_comm _ _ a (b .* ψg))
          end).
    repeat rewrite <- Mplus_assoc.
    rewrite <- 2 Mscale_plus_distr_l.
    repeat rewrite Mplus_assoc.
    rewrite <- 2 Mscale_plus_distr_l.
    apply f_equal2; apply f_equal2; auto.
    + autorewrite with RtoC_db R_db.
      replace (-2 * cos (INR (2 * i + 1) * θ) * cos θ * sin θ +
                 - sin (INR (2 * i + 1) * θ) + 
                 - (-2 * sin (INR (2 * i + 1) * θ) * sin θ * sin θ))%R 
         with (- (sin (INR (2 * i + 1) * θ) * (1 - 2 * sin θ * sin θ) +
                 cos (INR (2 * i + 1) * θ) * (2 * sin θ * cos θ)))%R 
         by lra.
      rewrite <- sin_2a.
      rewrite <- cos_2a_sin.
      rewrite <- sin_plus. 
      apply c_proj_eq; simpl; try reflexivity.
      field_simplify.
      do 2 apply f_equal.
      replace (S i) with (i + 1)%nat by lia.
      repeat (try rewrite plus_INR; try rewrite mult_INR).
      simpl.
      lra.
    + autorewrite with RtoC_db R_db.
      replace (- (-2 * sin (INR (2 * i + 1) * θ) * sin θ * cos θ) +
                 (-2 * cos (INR (2 * i + 1) * θ) * cos θ * cos θ +
                 cos (INR (2 * i + 1) * θ)))%R 
         with (- (cos (INR (2 * i + 1) * θ) * (2 * cos θ * cos θ - 1) -
                 sin (INR (2 * i + 1) * θ) * (2 * sin θ * cos θ)))%R
         by lra.
      rewrite <- sin_2a.
      rewrite <- cos_2a_cos.
      rewrite <- cos_plus. 
      apply c_proj_eq; simpl; try reflexivity.
      field_simplify.
      do 2 apply f_equal.
      replace (S i) with (i + 1)%nat by lia.
      repeat (try rewrite plus_INR; try rewrite mult_INR).
      simpl.
      lra.
Qed.

Lemma minus_norm_1 : ∣-⟩† × ∣-⟩ = I 1.
Proof. solve_matrix. Qed.

Lemma kron_n_add_dist :
  forall n1 n2 m1 m2 (A : Matrix m1 m2),
  WF_Matrix A ->
  kron_n (n1 + n2) A = kron_n n1 A ⊗ kron_n n2 A.
Proof.
  intros n1 n2 m1 m2 A H. induction n2 as [| n2 IH].
  - Msimpl. rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. cbn. rewrite IH.
    restore_dims. apply kron_assoc; auto with wf_db.
Qed.

(* After i iterations of Grover's, the probability of measuring z where 
   f z = true is sin^2((2i + 1) * θ) where θ = asin(√(k / 2^n)).

   Note that this implies that the "optimal" number of iterations is
   (PI / 4) * √ (2 ^ n / k). [TODO: prove this?] *)
Lemma grover_correct : forall i,
  (* sum over all "good" solutions *)
  Rsum
    (2 ^ n)
    (fun z => if f z 
              then @prob_partial_meas n (S ancillae)
                (basis_vector (2 ^ n) z)
                (uc_eval (grover i) × dim ⨂ ∣0⟩)
              else 0) = 
    ((sin ( INR (2 * i + 1) * θ)) ^ 2)%R.
Proof.
  intro i.
  specialize f_has_both_good_and_bad_solutions as H.
  rewrite (Rsum_eq_bounded _ _
             (fun j => if (f j) then (sin (INR (2 * i + 1) * θ) / √ INR k) ^ 2 else 0)%R).
  assert (forall m c, Rsum m (fun i => if f i then c else 0) = INR (count f m) * c)%R.
  { clear.
    intros.
    induction m; simpl.
    lra. 
    rewrite plus_INR, Rmult_plus_distr_r, <- IHm.
    destruct m; simpl.
    destruct (f 0); simpl; lra.
    destruct (f (S m)); simpl; try lra. }
  rewrite H0; clear H0.
  replace (count f (2 ^ n)) with k by reflexivity. 
  simpl.
  field_simplify_eq; try nonzero.
  rewrite pow2_sqrt by nonzero.
  lra.
  Local Opaque pow.
  intros x Hx.
  destruct (f x) eqn:fx; auto.
  unfold grover.
  Local Opaque npar.
  simpl.
  repeat rewrite Mmult_assoc.
  autorewrite with eval_db.
  bdestruct_all; try (unfold dim in *; lia).
  unfold dim at 3 4 5 6 7.
  replace (S n + ancillae - (n + 1))%nat with ancillae by lia.
  rewrite kron_n_add_dist, kron_assoc; auto with wf_db.
  restore_dims. rewrite kron_assoc; auto with wf_db.
  restore_dims.
  replace ((kron_n _ _) ⊗ ∣0⟩) with (kron_n (S (ancillae)) qubit0)
                                    by reflexivity.
  replace (S ancillae) with (1 + ancillae)%nat by reflexivity.
  rewrite kron_n_add_dist; auto with wf_db.
  restore_dims. rewrite kron_mixed_product, kron_mixed_product.
  Msimpl. restore_dims.
  rewrite <- pad_dims_r; try (apply npar_WT; lia).
  rewrite npar_correct by lia.
  simpl. rewrite hadamard_rotation.
  unfold pad. 
  bdestruct_all.
  replace (1 - (0 + 1))%nat with O by lia.
  simpl I. Msimpl.
  rewrite <- kron_assoc; auto with wf_db.
  restore_dims. repeat rewrite kron_mixed_product.
  Msimpl.
  replace (n ⨂ hadamard × n ⨂ ∣0⟩) with ψ.
  2: { rewrite H0_kron_n_spec_alt. reflexivity.
       specialize n_ge_2 as H2. lia. }
  replace (hadamard × (σx × ∣0⟩)) with ∣-⟩ by solve_matrix.
  rewrite niter_correct by lia.
  restore_dims.
  replace (2 ^ n * 2)%nat with (2 ^ S n)%nat by (simpl; lia).
  rewrite <- pad_ancillae.
  unify_pows_two.
  replace (n + 1)%nat with (S n) by lia.
  restore_dims.
  specialize (loop_body_action_on_unif_superpos i) as Hl.
  rewrite Nat.pow_1_l in Hl. Set Printing Implicit. rewrite Hl.
  rewrite pad_ancillae.
  restore_dims.
  rewrite kron_assoc; auto with wf_db.
  restore_dims.
  replace (2 * 2 ^ ancillae)%nat with (2 ^ S ancillae)%nat by reflexivity.
  rewrite Nat.pow_1_l.
  rewrite (@partial_meas_tensor n (S ancillae)); restore_dims.
  2: auto with wf_db.
  2: { rewrite kron_adjoint, kron_mixed_product, minus_norm_1, kron_n_adjoint;
       auto with wf_db.
       Msimpl. restore_dims. rewrite kron_n_mult, Mmult00.
       clear. induction ancillae; try reflexivity. simpl. Msimpl. assumption. }
  unfold probability_of_outcome.
  distribute_scale.
  distribute_plus.
  distribute_scale.
  assert ((basis_vector (2 ^ n) x) † × ψg = / √ INR k .* I 1).
  { unfold ψg.
    distribute_scale.
    rewrite Mmult_vsum_distr_l.
    erewrite vsum_unique.
    reflexivity.
    exists x.
    repeat split; auto.
    rewrite fx.
    apply basis_vector_product_eq; auto.
    intros.
    destruct (f j).
    apply basis_vector_product_neq; auto.
    Msimpl. reflexivity. }
  rewrite H2; clear H2.
  assert ((basis_vector (2 ^ n) x) † × ψb = Zero).
  { unfold ψb.
    distribute_scale.
    rewrite Mmult_vsum_distr_l.
    rewrite vsum_0.
    lma.
    intros.
    destruct (f x0) eqn:fx0.
    Msimpl. reflexivity.
    apply basis_vector_product_neq; auto.
    intro contra; subst.
    rewrite fx in fx0. 
    easy. } 
    rewrite H2; clear H2.
  Msimpl.
  unfold I, scale; simpl.
  autorewrite with R_db C_db.
  rewrite Cmod_mult, Cmod_pow.
  rewrite <- Cexp_PI, Cmod_Cexp.
  rewrite pow1, Rmult_1_l.
  apply RtoC_inj.
  rewrite <- RtoC_pow.
  rewrite Cmod_sqr.
  Local Transparent pow.
  simpl.
  autorewrite with RtoC_db.
  rewrite Cconj_R.
  autorewrite with RtoC_db R_db.
  reflexivity.
Qed.

End Grover.

