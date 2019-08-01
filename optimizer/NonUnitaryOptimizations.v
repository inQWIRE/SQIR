Require Import SQIRE.
Require Import DensitySem.
Require Import Tactics.

Local Open Scope com.

(** Phase-meas optimization **)

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
  unfold ueval1, ueval_unitary1.
  apply functional_extensionality. intros ρ.
  unfold pad.
  repad. subst. clear.
  Msimpl.
  repeat rewrite Mmult_assoc.
  Msimpl.
  repeat (restore_dims; rewrite <- Mmult_assoc).
  Msimpl.
  Search phase_shift.
  rewrite phase_adjoint.
  replace (phase_shift (- θ) × ∣0⟩) with ∣0⟩ by solve_matrix.
  replace (phase_shift (- θ) × ∣1⟩) with (Cexp (- θ) .* ∣1⟩) by solve_matrix.
  repeat (restore_dims; rewrite Mmult_assoc).
  replace ((⟨0∣ × phase_shift θ)) with ⟨0∣ by solve_matrix.
  replace (⟨1∣ × phase_shift θ) with (Cexp θ .* ⟨1∣) by solve_matrix.
  apply f_equal2; trivial.                                                              
  distribute_scale.  
  rewrite Cexp_mul_neg_r.
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

Definition is_rotation {dim} (c : com dim) : bool :=
  match c with
  | app1 U_Z _ | app1 (U_R _) _ => true
  | _                           => false 
  end.

Fixpoint optimize_R_meas {dim} (c : com dim) : com dim :=
  match c with
  | app1 U_Z a ; meas b c1 c2 => 
    if a =? b 
    then meas b (optimize_R_meas c1) (optimize_R_meas c2)  
    else app1 U_Z a; meas b (optimize_R_meas c1) (optimize_R_meas c2)
  | app1 (U_R θ) a ; meas b c1 c2 => 
    if a =? b 
    then meas b (optimize_R_meas c1) (optimize_R_meas c2) 
    else app1 (U_R θ) a; meas b (optimize_R_meas c1) (optimize_R_meas c2)
  | c1 ; c2 => (optimize_R_meas c1); (optimize_R_meas c2)
  | meas a c1 c2 => meas a (optimize_R_meas c1) (optimize_R_meas c2)
  | _      => c
  end.

Compute (optimize_R_meas (skip; (SQIRE.Z O; reset O))).

Lemma optimize_R_meas_sound : forall dim (c : com dim),
  c ≡ optimize_R_meas c.
Proof.
  intros.
  induction c; simpl; try reflexivity.
  - destruct c1; simpl; try (rewrite <- IHc2; reflexivity).
    + rewrite IHc1, <- IHc2. simpl. reflexivity.
    + dependent destruction u; try (rewrite <- IHc2; reflexivity).
      * destruct c2; try (rewrite <- IHc2; reflexivity).
        bdestruct (n =? n0); subst; try (rewrite <- IHc2; reflexivity).
        rewrite <- IHc2.
        apply Z_mif.
      * destruct c2; try (rewrite <- IHc2; reflexivity).
        bdestruct (n =? n0); subst; try (rewrite <- IHc2; reflexivity).
        rewrite <- IHc2.
        apply R_mif.
    + simpl in IHc1.
      rewrite <- IHc1.
      rewrite <- IHc2.
      reflexivity.
  - (* should be able to rewrite inside mif *)
    unfold c_equiv in *.
    simpl.
    rewrite <- IHc1, <- IHc2.
    reflexivity.
Qed.
      
(** Apply optimization **)


(** Resets optimization **)

Lemma rm_resets_correct : forall (dim n : nat), 
  @meas dim n (X n) skip; @meas dim n (X n) skip ≡ @meas dim n (X n) skip.
Proof.
  intros.
  simpl.
  unfold c_equiv.
  simpl.
  unfold compose_super, Splus, super.
  unfold ueval1, ueval_unitary1.
  apply functional_extensionality.
  intros ρ.
  unfold pad.
  gridify.
  repeat (restore_dims_fast; rewrite <- Mmult_assoc).
  repeat rewrite kron_mixed_product.  
  repeat (restore_dims_fast; rewrite Mmult_assoc).
  Msimpl.
  rewrite σx_sa.
  repeat rewrite <- Mmult_assoc.
  autorewrite with cnot_db.
  repeat rewrite (Mmult_assoc _ ⟨0∣).
  repeat rewrite (Mmult_assoc _ ⟨1∣).
  autorewrite with cnot_db.
  Msimpl.
  reflexivity.
Qed.


