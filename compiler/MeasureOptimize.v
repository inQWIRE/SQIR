Require Import SQIRE.
Require Import DensitySem.

Local Open Scope com.

Definition R_ {dim} θ n : ucom dim := uapp1 (U_R θ) n.  

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

Lemma R_mif : forall dim θ n c1 c2, 
  @R_ dim θ n ; mif n then c1 else c2 ≡ mif n then c1 else c2.
Proof.
  intros.
  unfold c_equiv.
  simpl.
  unfold compose_super, Splus, super.
  unfold ueval1.
  apply functional_extensionality. intros ρ.
  unfold pad.
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

Lemma R_measure : forall dim θ n, @R_ dim θ n ; measure n ≡ measure n.
Proof. intros. apply R_mif. Qed.

Lemma R_reset : forall dim θ n, @R_ dim θ n ; reset n ≡ reset n.
Proof. intros. apply R_mif. Qed.

(* Z is R_ PI, so the same lemmas apply. *)

Lemma phase_pi : phase_shift PI = σz.
Proof.
  unfold phase_shift, σz.
  rewrite eulers_identity.
  replace (RtoC (-1)) with (Copp (RtoC 1)) by lca.
  reflexivity.
Qed.

Lemma ueval_R_pi : forall dim n, ueval1 dim n (U_R PI) = ueval1 dim n U_Z. 
Proof.
  intros.
  unfold ueval1; simpl.
  rewrite phase_pi.
  reflexivity.
Qed.

Lemma Z_mif : forall dim n c1 c2,
  @SQIRE.Z dim n ; mif n then c1 else c2 ≡ mif n then c1 else c2.
Proof.
  intros. unfold c_equiv. simpl.
  rewrite <- ueval_R_pi.
  apply R_mif.
Qed.
  
Lemma Z_measure : forall dim n, @SQIRE.Z dim n ; measure n ≡ measure n.
Proof. intros. apply Z_mif. Qed.

Lemma Z_reset : forall dim n, @SQIRE.Z dim n ; reset n ≡ reset n.
Proof. intros. apply Z_mif. Qed.

(* T and P are R_ PI/4 and R_ PI/2, but those are explicit in SQIRE.v *) 

Lemma rm_resets_correct : forall (dim n : nat), 
  @meas dim n (X n) skip; @meas dim n (X n) skip ≡ @meas dim n (X n) skip.
Proof.
  intros.
  simpl.
  unfold c_equiv.
  simpl.
  unfold compose_super, Splus, super.
  unfold ueval1.
  apply functional_extensionality.
  intros.
  unfold pad.
  bdestruct (n + 1 <=? dim).
  2 : remove_zero_gates; reflexivity.
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
  repeat (restore_dims; rewrite Mmult_assoc).
  Msimpl.
  repeat rewrite Mmult_plus_distr_r.
  repeat rewrite Mmult_assoc.
  Msimpl.
  replace (∣1⟩⟨0∣ × ∣1⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
  replace (∣0⟩⟨0∣ × ∣1⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
  replace (∣1⟩⟨0∣ × ∣0⟩⟨0∣) with (∣1⟩⟨0∣) by solve_matrix.
  replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
  repeat remove_zero_gates.
  rewrite Mplus_0_l.
  repeat remove_zero_gates.
  rewrite Mplus_0_l.
  repeat rewrite Mmult_plus_distr_l.
  rewrite <- Mmult_assoc.
  restore_dims.
  rewrite <- Mmult_assoc.
  repeat rewrite kron_mixed_product.
  replace (σx × ∣1⟩⟨1∣) with (∣0⟩⟨1∣) by solve_matrix.
  Msimpl.
  replace (∣0⟩⟨0∣ × ∣0⟩⟨1∣) with (∣0⟩⟨1∣) by solve_matrix.
  rewrite <- Mmult_assoc.
  restore_dims.
  rewrite <- Mmult_assoc.
  rewrite kron_mixed_product.
  Msimpl.
  replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
  reflexivity.
Qed.


