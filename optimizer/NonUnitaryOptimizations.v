Require Import SQIRE.
Require Import DensitySem.
Require Import Tactics.
Require Import Coq.Reals.ROrderedType.

Local Open Scope com.

(** Phase-meas optimization **)

Lemma Cexp_mul_neg_l : forall θ, Cexp (- θ) * Cexp θ = 1.
Proof.  
  unfold Cexp. intros R.
  eapply c_proj_eq; simpl.
  - rewrite cos_neg, sin_neg.
    field_simplify_eq.
    repeat rewrite <- Rsqr_pow2.
    rewrite Rplus_comm.
    apply sin2_cos2.
  - rewrite cos_neg, sin_neg. field.
Qed.

Lemma Cexp_mul_neg_r : forall θ, Cexp θ * Cexp (-θ) = 1.
Proof. intros. rewrite Cmult_comm. apply Cexp_mul_neg_l. Qed.

Local Transparent Rz.
Lemma R_mif : forall dim θ n c1 c2, 
  @Rz dim θ n ; mif n then c1 else c2 ≡ mif n then c1 else c2.
Proof.
  intros.
  unfold c_equiv.
  simpl.
  unfold compose_super, Splus, super.
  autorewrite with eval_db.
  rewrite <- phase_shift_rotation.
  apply functional_extensionality. intros ρ.

  gridify.
  apply f_equal2.
  - apply f_equal.
    repeat rewrite <- Mmult_assoc.
    Msimpl.
    restore_dims_fast.
    repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite (Mmult_assoc (∣1⟩)).
    replace (⟨1∣ × phase_shift θ) with (Cexp θ .* ⟨1∣) by solve_matrix.
    restore_dims_fast.
    repeat rewrite Mmult_assoc.
    restore_dims_fast.
    repeat rewrite kron_mixed_product.
    rewrite <- (Mmult_assoc _ (∣1⟩)).
    replace (phase_shift (- θ) × ∣1⟩) with (Cexp (- θ) .* ∣1⟩) by solve_matrix.                                            
    restore_dims_fast.
    Msimpl.
    repeat (try rewrite Mscale_mult_dist_r;
            try rewrite Mscale_mult_dist_l;
            try rewrite Mscale_kron_dist_l;
            try rewrite Mscale_kron_dist_r).
    repeat match goal with 
    | |- context[?A × (?c .* ?B)] => idtac c; rewrite (Mscale_mult_dist_r _ _ _ c A B)
    end. 
    rewrite Mscale_assoc.
    rewrite Cexp_mul_neg_r.
    rewrite Mscale_1_l.
    reflexivity.
  - apply f_equal.
    repeat rewrite <- Mmult_assoc.
    Msimpl.
    restore_dims_fast.
    repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite (Mmult_assoc (∣0⟩)).
    replace ((⟨0∣ × phase_shift θ)) with ⟨0∣ by solve_matrix.
    restore_dims_fast.
    repeat rewrite Mmult_assoc.
    restore_dims_fast.
    repeat rewrite kron_mixed_product.
    rewrite <- (Mmult_assoc _ (∣0⟩)).
    replace (phase_shift (- θ) × ∣0⟩) with ∣0⟩ by solve_matrix.
    restore_dims_fast.
    Msimpl.
    reflexivity.
Qed.

(* Cleaner old version: 
  bdestruct (n + 1 <=? dim).
  2: remove_zero_gates; reflexivity.
  remember (dim - 1 - n)%nat as m.
  assert (dim = n + 1 + m)%nat as E by lia.
  rewrite E in *.
  subst.
  clear.
  replace (2 ^ (n + 1 + m))%nat with (2^n * 2 * 2^m)%nat by unify_pows_two.
  restore_dims.
  Msimpl.
  repeat rewrite Mmult_assoc.
  repeat rewrite kron_mixed_product.  
  repeat (restore_dims; rewrite <- Mmult_assoc).
  repeat rewrite kron_mixed_product.  
  replace (phase_shift (- θ) × ∣0⟩) with ∣0⟩ by solve_matrix.
  replace (phase_shift (- θ) × ∣1⟩) with (Cexp (- θ) .* ∣1⟩) by solve_matrix.
  repeat (restore_dims; rewrite Mmult_assoc).
  replace ((⟨0∣ × phase_shift θ)) with ⟨0∣ by solve_matrix.
  replace (⟨1∣ × phase_shift θ) with (Cexp θ .* ⟨1∣) by solve_matrix.
  Msimpl.
  apply f_equal2; trivial.                                                              
  repeat (try rewrite Mscale_mult_dist_r;
          try rewrite Mscale_mult_dist_l;
          try rewrite Mscale_kron_dist_l;
          try rewrite Mscale_kron_dist_r).
  restore_dims_strong.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  rewrite Cexp_mul_neg_l.
  rewrite Mscale_1_l.
  reflexivity.
Qed.  
*)

Lemma R_measure : forall dim θ n, @Rz dim θ n ; measure n ≡ measure n.
Proof. intros. apply R_mif. Qed.

Lemma R_reset : forall dim θ n, @Rz dim θ n ; reset n ≡ reset n.
Proof. intros. apply R_mif. Qed.

(* Z is Rz PI, so the same lemmas apply. *)

Local Transparent SQIRE.Z.
Lemma Z_eq_Rz_PI : forall dim n, SQIRE.Z n ≡ @Rz dim PI n.
Proof.
  intros.
  unfold c_equiv, c_eval; simpl. 
  autorewrite with eval_db.
  rewrite <- pauli_z_rotation.  
  reflexivity.
Qed.

Lemma Z_mif : forall dim n c1 c2,
  @SQIRE.Z dim n ; mif n then c1 else c2 ≡ mif n then c1 else c2.
Proof.
  intros. 
  rewrite Z_eq_Rz_PI. 
  apply R_mif.
Qed.
  
Lemma Z_measure : forall dim n, @SQIRE.Z dim n ; measure n ≡ measure n.
Proof. intros. apply Z_mif. Qed.

Lemma Z_reset : forall dim n, @SQIRE.Z dim n ; reset n ≡ reset n.
Proof. intros. apply Z_mif. Qed.

(* T and P are Rz PI/4 and Rz PI/2, but those are explicit in SQIRE.v *) 

Fixpoint optimize_R_meas {dim} (c : com dim) : com dim :=
  match c with
  | app_R θ ϕ λ a ; meas b c1 c2 => 
      if Reqb θ 0 && Reqb ϕ 0 && (a =? b)
      then meas b (optimize_R_meas c1) (optimize_R_meas c2)  
      else app_R θ ϕ λ a ; meas b (optimize_R_meas c1) (optimize_R_meas c2) 
  | c1 ; c2 => (optimize_R_meas c1); (optimize_R_meas c2)
  | meas a c1 c2 => meas a (optimize_R_meas c1) (optimize_R_meas c2) 
  | _ => c
  end.

(* Not nice because of the Reqb:
   Compute (optimize_R_meas (skip; (SQIRE.Z O; reset O))). *)

Lemma optimize_R_meas_sound : forall dim (c : com dim),
  c ≡ optimize_R_meas c.
Proof.
  intros.
  induction c; simpl; try reflexivity.
  - destruct c1; simpl; try (rewrite <- IHc2; reflexivity).
    + rewrite IHc1, <- IHc2. simpl. reflexivity.
    + destruct c2; try (rewrite <- IHc2; reflexivity). 
      destruct (Reqb r 0 && Reqb r0 0 && (n =? n0)) eqn:H.
      repeat match goal with 
        | [ E : _ && _ = true |- _]   => apply andb_true_iff in E; destruct E
        | [ E : Reqb _ _ = true |- _] => apply Reqb_eq in E; subst
        | [ E : _ =? _ = true |- _] => apply Nat.eqb_eq in E; subst 
        end. 
      rewrite <- IHc2. 
      apply R_mif.
      rewrite <- IHc2; reflexivity.
    + rewrite <- IHc1, <- IHc2. reflexivity.
  - (* should be able to rewrite inside mif *)
    unfold c_equiv in *.
    simpl.
    rewrite <- IHc1, <- IHc2.
    reflexivity.
Qed.
      
(** Apply optimization **)


(** Resets optimization **)

Local Transparent X.
Lemma rm_resets_correct : forall (dim n : nat), 
  @meas dim n (X n) skip; @meas dim n (X n) skip ≡ @meas dim n (X n) skip.
Proof.
  intros.
  simpl.
  unfold c_equiv.
  simpl.
  unfold compose_super, Splus, super.
  autorewrite with eval_db.
  apply functional_extensionality.
  intros ρ.
  gridify.
  rewrite <- rotation_adjoint.
  rewrite <- pauli_x_rotation.
  repeat rewrite Mmult_assoc.
  repeat rewrite kron_mixed_product.  
  repeat (restore_dims_fast; rewrite <- Mmult_assoc).
  repeat rewrite kron_mixed_product.  
  repeat (restore_dims_fast; rewrite Mmult_assoc).
  Msimpl.
  repeat rewrite <- Mmult_assoc.
  Msimpl.
  replace (∣0⟩⟨1∣ × σx × ∣1⟩ × ⟨1∣) with (@Zero 2 2) by solve_matrix.
  replace ((∣0⟩⟨1∣ × ∣0⟩ × ⟨0∣)) with (@Zero 2 2) by solve_matrix.
  repeat remove_zero_gates.
  replace ((∣0⟩⟨0∣ × σx × ∣1⟩ × ⟨1∣)) with (∣0⟩⟨1∣) by solve_matrix.
  replace ((∣1⟩⟨1∣ × σx × ∣0⟩ × ⟨0∣)) with (∣1⟩⟨0∣) by solve_matrix.
  replace (∣0⟩⟨0∣ × ∣0⟩ × ⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
  repeat rewrite Mplus_0_l.
  reflexivity.
Qed.


