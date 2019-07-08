Require Export QWIRE.Quantum.

(** Cexp lemmas **)

(* fix up names later *)
Definition Cexp_0 := eulers0.
Definition Cexp_PI := eulers_identity.
Definition Cexp_PI2 := eulers_identity2.

Lemma Cexp_2PI : Cexp (2 * PI) = 1.
Proof.
  unfold Cexp.
  rewrite sin_2PI, cos_2PI.
  reflexivity.
Qed.

Lemma Cexp_PI4 : Cexp (PI / 4) = /√2 + /√2 * Ci.
Proof.
  unfold Cexp.
  rewrite sin_PI4, cos_PI4.
  eapply c_proj_eq; simpl.
  field_simplify_eq; trivial; apply sqrt2_neq_0.
  field_simplify_eq; trivial; apply sqrt2_neq_0.
Qed.
  
Lemma Cexp_add: forall (x y : R), Cexp (x + y) = Cexp x * Cexp y.
Proof.
  intros.
  unfold Cexp.
  apply c_proj_eq; simpl.
  - apply cos_plus.
  - rewrite sin_plus. field.
Qed.

Lemma Cexp_neg : forall θ, Cexp (- θ) = / Cexp θ.
Proof.
  intros θ.
  unfold Cexp.
  rewrite sin_neg, cos_neg.
  apply c_proj_eq; simpl.
  - replace (cos θ * (cos θ * 1) + sin θ * (sin θ * 1))%R with 
        (cos θ ^ 2 + sin θ ^ 2)%R by reflexivity.
    repeat rewrite <- Rsqr_pow2.
    rewrite Rplus_comm.
    rewrite sin2_cos2.
    field.
  - replace ((cos θ * (cos θ * 1) + sin θ * (sin θ * 1)))%R with 
        (cos θ ^ 2 + sin θ ^ 2)%R by reflexivity.
    repeat rewrite <- Rsqr_pow2.
    rewrite Rplus_comm.
    rewrite sin2_cos2.
    field.
Qed.

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

(** Phase lemmas **)

Lemma phase_0 : phase_shift 0 = I 2.
Proof. 
  unfold phase_shift, I. 
  rewrite Cexp_0.
  solve_matrix.
Qed.

Lemma phase_2pi : phase_shift (2 * PI) = I 2.
  unfold phase_shift, I. 
  rewrite Cexp_2PI.
  solve_matrix.
Qed.

Lemma phase_pi : phase_shift PI = σz.
Proof.
  unfold phase_shift, σz.
  rewrite Cexp_PI.
  replace (RtoC (-1)) with (Copp (RtoC 1)) by lca.
  reflexivity.
Qed.

Lemma phase_neg_pi : phase_shift (-PI) = σz.
Proof.
  unfold phase_shift, σz.
  rewrite Cexp_neg.
  rewrite Cexp_PI.
  replace (/ -1) with (Copp (RtoC 1)) by lca.
  reflexivity.
Qed.

Lemma phase_mul : forall θ θ', phase_shift θ × phase_shift θ' = phase_shift (θ + θ').
Proof.
  intros. solve_matrix. rewrite Cexp_add. reflexivity.
Qed.  