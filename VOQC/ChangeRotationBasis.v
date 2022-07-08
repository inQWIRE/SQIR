Require Export Reals.ROrderedType.
Require Export Reals.Ratan.
Require Import QuantumLib.Quantum.
Require Import QuantumLib.Proportional.

Local Open Scope R_scope.

(* This file provides a function yzy_to_zyz that converts a YZY sequence of Euler
   rotations to a ZYZ sequence of Euler rotations.

   The main property proved is:

   Lemma yzy_to_zyz_correct : forall θ1 ξ θ2 ξ1 θ ξ2,
     yzy_to_zyz θ1 ξ θ2 = (ξ1, θ, ξ2) ->
     y_rotation θ2 × phase_shift ξ × y_rotation θ1
       ∝ phase_shift ξ2 × y_rotation θ × phase_shift ξ1.

   This code is effectively a specialization of Qiskit's 'Quaternion' class to
   the YZY -> ZYZ case; see https://qiskit.org/documentation/_modules/qiskit/quantum_info/operators/quaternion.html.

   For more info on Euler angles see https://en.wikipedia.org/wiki/Euler_angles. *)

(* We'll assert a Boolean comparison operation over Reals. *)
Parameter Rltb : R -> R -> bool.
Infix "<?" := Rltb : R_scope.
Axiom Rltb_lt : forall x y, Rltb x y = true <-> Rlt x y.

(* See: https://en.wikipedia.org/wiki/Atan2 *)
Definition atan2 (y x : R) : R :=
  if 0 <? x then atan (y/x)
  else if x <? 0 then
       if negb (y <? 0) then atan (y/x) + PI else atan (y/x) - PI
  else
       if 0 <? y then PI/2 else if y <? 0 then -PI/2 else 0.

(* Each "rm" term is an entry in the underlying rotation matrix. *)
Definition rm02 (x y z : R) : R := sin x * cos z + cos x * cos y * sin z.
Definition rm12 (x y z : R) : R := sin y * sin z.
Definition rm22 (x y z : R) : R := cos x * cos z - sin x * cos y * sin z.
Definition rm10 (x y z : R) : R := sin y * cos z. 
Definition rm11 (x y z: R) : R := cos y.
Definition rm20_minus (x y z : R) : R := cos x * sin z + sin x * cos y * cos z. 
Definition rm21 (x y z : R) : R := sin x * sin y.

Definition yzy_to_zyz (x y z : R) : R * R * R :=
  if rm22 x y z <? 1
  then if -1 <? rm22 x y z
       then (atan2 (rm12 x y z) (rm02 x y z),
             acos (rm22 x y z),
             atan2 (rm21 x y z) (rm20_minus x y z))
       else (- atan2 (rm10 x y z) (rm11 x y z), PI, 0)
  else (atan2 (rm10 x y z) (rm11 x y z), 0, 0).

(** Some simple automation **)

Lemma Rltb_reflect : forall (x y : R), reflect (x < y) (Rltb x y).
Proof.
  intros x y. apply iff_reflect. symmetry. apply Rltb_lt.
Qed.
#[export] Hint Resolve Rltb_reflect : bdestruct.

Lemma Reqb_reflect : forall (x y : R), reflect (x = y) (Reqb x y).
Proof.
  intros x y. apply iff_reflect. symmetry. apply Reqb_eq.
Qed.
#[export] Hint Resolve Reqb_reflect : bdestruct.

Lemma WF_y_rotation : forall θ, WF_Matrix (y_rotation θ).
Proof. intros. show_wf. Qed.
#[export] Hint Resolve WF_y_rotation : wf_db.

Ltac destruct_Rltb := 
  repeat match goal with
  | |- context[Rltb ?a ?b] => bdestruct (Rltb a b)
  end; 
  simpl;
  try lra. 

Ltac simplify_assumptions :=
  repeat match goal with
  | H1 : not (Rlt ?a 0), H2 : not (Rlt 0 ?a) |- _ => assert (a = 0) by lra; clear H1 H2
  | H1 : not (Rlt 0 ?a), H2 : Rlt ?a 0 |- _ => clear H1
  | H1 : not (Rlt ?a 0), H2 : Rlt 0 ?a |- _ => clear H1
  end.

(** Useful trig facts **)

Lemma cos_1_sin: forall (θ:R), cos θ = 1 -> sin θ = 0.
Proof. 
  intros.
  specialize (sin2_cos2 θ) as eq1.
  rewrite H in eq1.
  assert ((sin θ)² = 0).
  unfold Rsqr in eq1. unfold Rsqr. lra.
  apply Rsqr_0_uniq in H0. assumption.
Qed.

Lemma cos_neg_1_sin: forall (θ:R), cos θ = -1 -> sin θ = 0.
Proof. 
  intros.
  specialize (sin2_cos2 θ) as eq1.
  rewrite H in eq1.
  assert ((sin θ)² = 0).
  unfold Rsqr in eq1. unfold Rsqr. lra.
  apply Rsqr_0_uniq in H0. assumption.
Qed.

Lemma sin_1_cos: forall (θ:R), sin θ = 1 -> cos θ = 0.
Proof. 
  intros.
  specialize (sin2_cos2 θ) as eq1.
  rewrite H in eq1.
  assert ((cos θ)² = 0).
  unfold Rsqr in eq1. unfold Rsqr. lra.
  apply Rsqr_0_uniq in H0. assumption.
Qed.

Lemma cos_0_sin: forall (θ:R), cos θ = 0 -> sin θ = 1 \/ sin θ = -1.
Proof. 
  intros.
  specialize (sin2_cos2 θ) as eq1.
  rewrite H in eq1.
  assert ((sin θ)² = Rsqr 1).
  unfold Rsqr in eq1. unfold Rsqr. lra.
  apply Rsqr_eq in H0. assumption.
Qed.

Lemma sin_0_cos: forall (θ:R), sin θ = 0 -> cos θ = 1 \/ cos θ = -1.
Proof. 
  intros.
  specialize (sin2_cos2 θ) as eq1.
  rewrite H in eq1.
  assert ((cos θ)² = Rsqr 1).
  unfold Rsqr in eq1. unfold Rsqr. lra.
  apply Rsqr_eq in H0. assumption.
Qed.

Lemma sin_half_squared : forall x, (sin (x/2))² = /2 * (1 - cos x).
Proof.
  intros x.
  replace x with (2 * (x / 2)) at 2 by lra.
  rewrite cos_2a_sin.
  unfold Rsqr.
  lra.
Qed.

Lemma cos_half_squared : forall x, (cos (x/2))² = /2 * (1 + cos x).
Proof.
  intros x.
  replace x with (2 * (x / 2)) at 2 by lra.
  rewrite cos_2a_cos.
  unfold Rsqr.
  lra.
Qed.

Lemma sin_half_zero : forall x, sin (x/2) = 0 -> cos x = 1.
Proof.
  intros x Hx. 
  assert (H: (sin (x/2))² = 0²).
  rewrite Hx; auto.
  rewrite Rsqr_0 in H.
  rewrite sin_half_squared in H.
  lra.
Qed.

Lemma cos_half_zero : forall x, cos (x/2) = 0 -> cos x = -1.
Proof.
  intros x Hx. 
  assert (H: (cos (x/2))² = 0²).
  rewrite Hx; auto.
  rewrite Rsqr_0 in H.
  rewrite cos_half_squared in H.
  lra.
Qed.

Lemma cos_x_y_zero : forall x y,
  cos (x + y) = 0 ->
  cos (x - y) = 0 ->
  (cos x = 0 /\ sin y = 0) \/ (sin x = 0 /\ cos y = 0).
Proof.
  intros x y H1 H2.
  rewrite cos_plus in H1.
  rewrite cos_minus in H2.
  assert (H3: cos x * cos y = 0) by lra.
  assert (H4: sin x * sin y = 0) by lra.
  apply Rmult_integral in H3 as [H3 | H3];
  apply Rmult_integral in H4 as [H4 | H4].
  - specialize (cos_sin_0 x) as H.
    contradict H; auto.
  - left; auto.
  - right; auto.
  - specialize (cos_sin_0 y) as H.
    contradict H; auto.
Qed.

Lemma sin_x_y_zero : forall x y,
  sin (x + y) = 0 ->
  sin (x - y) = 0 ->
  (sin x = 0 /\ sin y = 0) \/ (cos x = 0 /\ cos y = 0).
Proof.
  intros x y H1 H2.
  rewrite sin_plus in H1.
  rewrite sin_minus in H2.
  assert (H3: sin x * cos y = 0) by lra.
  assert (H4: cos x * sin y = 0) by lra.
  apply Rmult_integral in H3 as [H3 | H3];
  apply Rmult_integral in H4 as [H4 | H4].
  - specialize (cos_sin_0 x) as H.
    contradict H; auto.
  - left; auto.
  - right; auto.
  - specialize (cos_sin_0 y) as H.
    contradict H; auto.
Qed.

(* cos (acos x / 2) and sin (acos x / 2) have the same sign *)
Lemma cos_sin_acos_same_sign : forall x,
  -1 < x < 1 ->
  (cos (acos x / 2) = √ ((x + 1) / 2) /\ sin (acos x / 2) = √ ((1 - x) / 2))
   \/ (cos (acos x / 2) = - √ ((x + 1) / 2) /\ sin (acos x / 2) = - √ ((1 - x) / 2)).
Proof.
  intros x Hx.
  remember (cos (acos x / 2)) as c.
  remember (sin (acos x / 2)) as s.
  assert (H1: sin (acos x) = 2 * s * c).
  subst.
  replace (acos x) with (2 * (acos x / 2)) at 1 by lra.
  apply sin_2a.
  assert (H2: sin (acos x) >= 0).
  rewrite sin_acos by lra.
  apply Rle_ge.
  apply sqrt_pos.
  assert (H3: c = √ ((x + 1) / 2) \/ c = - √ ((x + 1) / 2)).
  apply Rsqr_eq.
  rewrite Rsqr_sqrt by lra.
  subst.
  rewrite cos_half_squared.
  rewrite cos_acos by lra.
  lra.
  assert (H4: s = √ ((1 - x) / 2) \/ s = - √ ((1 - x) / 2)).
  apply Rsqr_eq.
  rewrite Rsqr_sqrt by lra.
  subst.
  rewrite sin_half_squared.
  rewrite cos_acos by lra.
  lra.
  destruct H3 as [H3 | H3]; destruct H4 as [H4 | H4]; auto.
  - assert (c > 0).
    subst.
    rewrite H3.
    apply sqrt_lt_R0.
    lra.
    assert (s < 0).
    subst.
    rewrite H4.
    apply Ropp_lt_gt_0_contravar.
    apply sqrt_lt_R0.
    lra.
    assert (c * s < 0).
    rewrite <- (Rmult_0_r c).
    apply Rmult_lt_compat_l; auto.
    lra. (* contradiction *)
  - assert (c < 0).
    subst.
    rewrite H3.
    apply Ropp_lt_gt_0_contravar.
    apply sqrt_lt_R0.
    lra.
    assert (s > 0).
    subst.
    rewrite H4.
    apply sqrt_lt_R0.
    lra.
    assert (s * c < 0).
    rewrite <- (Rmult_0_r s).
    apply Rmult_lt_compat_l; auto.
    lra. (* contradiction *)
Qed.

(** Useful Cexp facts **)

Lemma Cexp_atan : forall x y,
  0 < x ->
  Cexp (atan (y/x)) = (/ √ (x² + y²) * (x,y))%C.
Proof.
  intros x y Hx.
  unfold Cexp.  
  rewrite cos_atan, sin_atan.
  assert (√ (x² + y²) <> 0).
  { apply sqrt_neq_0_compat.
    apply Rplus_lt_le_0_compat.
    apply Rsqr_pos_lt.
    lra.
    apply Rle_0_sqr. }  
  replace (1 + (y / x)²) with ((/ x)² * (x² + y²)).
  rewrite sqrt_mult_alt.
  rewrite sqrt_Rsqr. 
  apply c_proj_eq; simpl; field_simplify_eq; trivial.
  1,2: split; try lra.
  left.
  apply Rinv_0_lt_compat.
  assumption.
  apply Rle_0_sqr.
  unfold Rsqr.
  R_field_simplify; trivial.
  lra.
Qed.

Lemma Cexp_atan_neg : forall x y,
  x < 0 ->
  Cexp (atan (y/x)) = (- / √ (x² + y²) * (x,y))%C.
Proof.
  intros x y Hx.
  unfold Cexp.  
  rewrite cos_atan, sin_atan.
  assert (√ (x² + y²) <> 0).
  { apply sqrt_neq_0_compat.
    apply Rplus_lt_le_0_compat.
    apply Rsqr_pos_lt.
    lra.
    apply Rle_0_sqr. }  
  replace (1 + (y / x)²) with ((- / x)² * (x² + y²)).
  rewrite sqrt_mult_alt.
  rewrite sqrt_Rsqr. 
  apply c_proj_eq; simpl; field_simplify_eq; trivial.
  1,2: split; try lra.
  apply Ropp_0_ge_le_contravar.
  left.
  apply Rinv_lt_0_compat.
  assumption.
  apply Rle_0_sqr.
  unfold Rsqr.
  R_field_simplify; trivial.
  lra.
Qed.

Lemma Cexp_PI2_minus : Cexp (- PI / 2) = (- Ci)%C.
Proof.
  rewrite Ropp_div.
  unfold Cexp.
  rewrite cos_neg, sin_neg.  
  rewrite cos_PI2, sin_PI2.
  lca.
Qed.

Lemma Cexp_cos_1 : forall x, cos x = 1 -> Cexp x = 1.
Proof.
  intros x H.
  unfold Cexp.
  rewrite H.
  rewrite cos_1_sin by assumption.
  reflexivity.
Qed.

Lemma Cexp_cos_minus_1 : forall x, cos x = -1 -> Cexp x = -1.
Proof.
  intros x H.
  unfold Cexp.
  rewrite H.
  rewrite cos_neg_1_sin by assumption.
  reflexivity.
Qed.

Lemma Cexp_atan_tan : forall x, cos x > 0 -> Cexp (atan (sin x * / cos x)) = Cexp x.
Proof.
  intros x Hx.
  unfold Cexp.
  apply f_equal2.
  rewrite cos_atan.
  replace (1 + (sin x * / cos x)²) with (((sin x)² + (cos x)²) * (/ cos x)²).
  rewrite sin2_cos2.
  autorewrite with R_db.
  rewrite sqrt_Rsqr.
  field_simplify_eq; nonzero.
  left.
  apply Rinv_0_lt_compat.
  assumption.
  unfold Rsqr.
  field_simplify_eq; nonzero.
  rewrite sin_atan.
  replace (1 + (sin x * / cos x)²) with (((sin x)² + (cos x)²) * (/ cos x)²).
  rewrite sin2_cos2.
  autorewrite with R_db.
  rewrite sqrt_Rsqr.
  field_simplify_eq; nonzero.
  left.
  apply Rinv_0_lt_compat.
  assumption.
  unfold Rsqr.
  field_simplify_eq; nonzero.
Qed.

Lemma Cexp_atan_tan_neg : forall x, cos x < 0 -> Cexp (atan (sin x * / cos x)) = (- Cexp x)%C.
Proof.
  intros x Hx.

  unfold Cexp.
  apply f_equal2; simpl.
  rewrite cos_atan.
  replace (1 + (sin x * / cos x)²) with (((sin x)² + (cos x)²) * (/ cos x)²).
  rewrite sin2_cos2.
  autorewrite with R_db.
  rewrite Rsqr_neg.
  rewrite sqrt_Rsqr.
  field_simplify_eq; nonzero.
  left.
  rewrite Ropp_inv_permute by lra.
  apply Rinv_0_lt_compat.
  lra.
  unfold Rsqr.
  field_simplify_eq; nonzero.
  rewrite sin_atan.
  replace (1 + (sin x * / cos x)²) with (((sin x)² + (cos x)²) * (/ cos x)²).
  rewrite sin2_cos2.
  autorewrite with R_db.
  rewrite Rsqr_neg.
  rewrite sqrt_Rsqr.
  field_simplify_eq; nonzero.
  left.
  rewrite Ropp_inv_permute by lra.
  apply Rinv_0_lt_compat.
  lra.
  unfold Rsqr.
  field_simplify_eq; nonzero.
Qed.

Lemma Cexp_acos_pos : forall x y,
  0 <= y -> x² + y² = 1 -> Cexp (- acos x) = (x, (-y)%R)%C.
Proof.
  intros x y H0 H1.
  unfold Cexp.
  assert (H2: 0 <= x²). 
  apply Rle_0_sqr.
  assert (H3: 0 <= y²).
  apply Rle_0_sqr.
  assert (H4: x² <= 1) by lra.
  replace 1 with 1² in H4.
  assert (H5:=H4).
  apply Rsqr_neg_pos_le_0 in H4.
  apply Rsqr_incr_0_var in H5.
  rewrite cos_neg, sin_neg.
  rewrite cos_acos by lra.
  rewrite sin_acos by lra.
  rewrite <- H1.
  replace (x² + y² - x²) with y² by lra.
  rewrite sqrt_Rsqr by assumption.
  reflexivity.
  lra.
  lra.
  unfold Rsqr; lra.
Qed.

Lemma Cexp_acos_neg : forall x y,
  y < 0 -> x² + y² = 1 -> Cexp (acos x) = (x, (-y)%R)%C.
Proof.
  intros x y H0 H1.
  unfold Cexp.
  assert (H2: 0 <= x²). 
  apply Rle_0_sqr.
  assert (H3: 0 <= y²).
  apply Rle_0_sqr.
  assert (H4: x² <= 1) by lra.
  replace 1 with 1² in H4.
  assert (H5:=H4).
  apply Rsqr_neg_pos_le_0 in H4.
  apply Rsqr_incr_0_var in H5.
  rewrite cos_acos by lra.
  rewrite sin_acos by lra.
  rewrite <- H1.
  replace (x² + y² - x²) with (-y)².
  rewrite sqrt_Rsqr.
  reflexivity. 
  lra.
  unfold Rsqr; lra.
  lra.
  lra.
  unfold Rsqr; lra.
Qed.

(* Although the atan2 defn has 6 branches, there are only 5 outcomes when
   considering Cexp (atan2 ...). *)
Lemma Cexp_atan2_case_1 : forall y x, 
  x > 0 ->
  Cexp (atan2 y x) = Cexp (atan (y/x)).
Proof. intros. unfold atan2. destruct_Rltb. reflexivity. Qed.

Lemma Cexp_atan2_case_2 : forall y x, 
  x < 0 ->
  Cexp (atan2 y x) = (- Cexp (atan (y/x)))%C.
Proof.
  intros. unfold atan2.
  destruct_Rltb; autorewrite with Cexp_db; lca.
Qed.

Lemma Cexp_atan2_case_3 : forall y x, 
  x = 0 -> y > 0 -> Cexp (atan2 y x) = Ci.
Proof.
  intros. unfold atan2.
  destruct_Rltb. 
  apply Cexp_PI2.
Qed.

Lemma Cexp_atan2_case_4 : forall y x, 
  x = 0 -> y < 0 -> Cexp (atan2 y x) = (-Ci)%C.
Proof.
  intros. unfold atan2.
  destruct_Rltb. 
  rewrite Ropp_div.
  autorewrite with Cexp_db.
  lca.
Qed.

Lemma Cexp_atan2_case_5 : forall y x, 
  x = 0 -> y = 0 -> Cexp (atan2 y x) = C1.
Proof.
  intros. unfold atan2.
  destruct_Rltb. 
  apply Cexp_0.
Qed.

(** Constants used in the main proof **)

(* k1, k2 are normalizing contants *)
Definition k1 θ1 ξ θ2 := /2 * (1 + cos θ1 * cos θ2 - sin θ1 * cos ξ * sin θ2).
Definition k2 θ1 ξ θ2 := /2 * (1 - cos θ1 * cos θ2 + sin θ1 * cos ξ * sin θ2).

(*  mij is entry (i,j) in the matrix (y_rotation θ2 × phase_shift ξ × y_rotation θ1) *)
Definition m00 θ1 ξ θ2 : C :=
  cos (θ2 / 2) * cos (θ1 / 2) + - (sin (θ2 / 2) * Cexp ξ * sin (θ1 / 2)).
Definition m01 θ1 ξ θ2 : C :=
  - (cos (θ2 / 2) * sin (θ1 / 2)) + - (sin (θ2 / 2) * Cexp ξ * cos (θ1 / 2)).
Definition m10 θ1 ξ θ2 : C :=
  sin (θ2 / 2) * cos (θ1 / 2) + cos (θ2 / 2) * Cexp ξ * sin (θ1 / 2).
Definition m11 θ1 ξ θ2 : C :=
  - (sin (θ2 / 2) * sin (θ1 / 2)) + cos (θ2 / 2) * Cexp ξ * cos (θ1 / 2).

(* Real and imaginary parts of m00 *)
Definition m00_R θ1 ξ θ2 := cos (θ1 / 2) * cos (θ2 / 2) + - (cos ξ * sin (θ1 / 2) * sin (θ2 / 2)).
Definition m00_I θ1 ξ θ2 := (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)).

(* Different way of writing k1, k2 *)
Lemma k1_rewrite : forall θ1 ξ θ2,
  k1 θ1 ξ θ2 = 
  (sin (ξ / 2) * cos (θ1 / 2  - θ2 / 2))² + (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))².
Proof.
  intros.
  unfold k1.
  repeat rewrite Rsqr_mult.
  replace (θ1 / 2 - θ2 / 2) with ((θ1 - θ2) / 2) by lra.
  replace (θ1 / 2 + θ2 / 2) with ((θ1 + θ2) / 2) by lra.
  repeat rewrite sin_half_squared.
  repeat rewrite cos_half_squared.
  rewrite cos_plus, cos_minus.
  lra. 
Qed.

Lemma k2_rewrite : forall θ1 ξ θ2,
  k2 θ1 ξ θ2 = 
  (sin (ξ / 2) * sin (θ1 / 2  - θ2 / 2))² + (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))².
Proof.
  intros.
  unfold k2.
  repeat rewrite Rsqr_mult.
  replace (θ1 / 2 - θ2 / 2) with ((θ1 - θ2) / 2) by lra.
  replace (θ1 / 2 + θ2 / 2) with ((θ1 + θ2) / 2) by lra.
  repeat rewrite sin_half_squared.
  repeat rewrite cos_half_squared.
  rewrite cos_plus, cos_minus.
  lra. 
Qed.

(* Different way of writing mij, consistent with the alternate forms of k1, k2 *)
Lemma m00_rewrite : forall θ1 ξ θ2,
  m00 θ1 ξ θ2 = 
  (/2 * ((1 - Cexp ξ) * cos (θ1/2 - θ2/2) + (1 + Cexp ξ) * cos (θ1/2 + θ2/2)))%C.
Proof. intros. unfold m00. rewrite cos_plus, cos_minus. lca. Qed.

Lemma m01_rewrite : forall θ1 ξ θ2,
  m01 θ1 ξ θ2 = 
  (-/2 * ((1 - Cexp ξ) * sin (θ1/2 - θ2/2) + (1 + Cexp ξ) * sin (θ1/2 + θ2/2)))%C.
Proof. intros. unfold m01. rewrite sin_plus, sin_minus. lca. Qed.

Lemma m10_rewrite : forall θ1 ξ θ2,
  m10 θ1 ξ θ2 = 
  (/2 * ((-1 + Cexp ξ) * sin (θ1/2 - θ2/2) + (1 + Cexp ξ) * sin (θ1/2 + θ2/2)))%C.
Proof. intros. unfold m10. rewrite sin_plus, sin_minus. lca. Qed.

Lemma m11_rewrite : forall θ1 ξ θ2,
  m11 θ1 ξ θ2 = 
  (/2 * ((-1 + Cexp ξ) * cos (θ1/2 - θ2/2) + (1 + Cexp ξ) * cos (θ1/2 + θ2/2)))%C.
Proof. intros. unfold m11. rewrite cos_plus, cos_minus. lca. Qed.

(* Try applying all mij_rewrite rules *)
Ltac rewrite_mij θ1 ξ θ2 :=
  let Hm00 := fresh in
  let Hm01 := fresh in
  let Hm10 := fresh in 
  let Hm11 := fresh in
  specialize (m00_rewrite θ1 ξ θ2) as Hm00;
  specialize (m01_rewrite θ1 ξ θ2) as Hm01;
  specialize (m10_rewrite θ1 ξ θ2) as Hm10;
  specialize (m11_rewrite θ1 ξ θ2) as Hm11;
  unfold m00, m01, m10, m11 in *;
  try rewrite Hm00;
  try rewrite Hm01;
  try rewrite Hm10;
  try rewrite Hm11;
  clear Hm00 Hm01 Hm10 Hm11.

Lemma k1_geq_0 : forall θ1 ξ θ2, 0 <= k1 θ1 ξ θ2.
Proof.
  intros.
  rewrite k1_rewrite.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Lemma k2_geq_0 : forall θ1 ξ θ2, 0 <= k2 θ1 ξ θ2.
Proof.
  intros.
  rewrite k2_rewrite.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Lemma k1_plus_k2 : forall θ1 ξ θ2, k1 θ1 ξ θ2 + k2 θ1 ξ θ2 = 1.
Proof. intros. unfold k1, k2. lra. Qed.

Lemma rm22_rewrite : forall θ1 ξ θ2, rm22 θ1 ξ θ2 = 2 * k1 θ1 ξ θ2 - 1.
Proof. intros. unfold rm22, k1. lra. Qed.

Lemma rm22_bounds : forall θ1 ξ θ2, -1 <= rm22 θ1 ξ θ2 <= 1.
Proof.
  intros θ1 ξ θ2.
  rewrite rm22_rewrite.
  specialize (k1_plus_k2 θ1 ξ θ2) as H1.
  specialize (k1_geq_0 θ1 ξ θ2) as H2.
  specialize (k2_geq_0 θ1 ξ θ2) as H3.
  lra.
Qed.

Lemma rm22_one : forall θ1 ξ θ2, 
  rm22 θ1 ξ θ2 = 1 ->
  k1 θ1 ξ θ2 = 1 /\ k2 θ1 ξ θ2 = 0.
Proof.
  intros.
  rewrite rm22_rewrite in H.
  specialize (k1_plus_k2 θ1 ξ θ2) as ?.
  split; lra.  
Qed.

Lemma rm22_minus_one : forall θ1 ξ θ2, 
  rm22 θ1 ξ θ2 = -1 ->
  k1 θ1 ξ θ2 = 0 /\ k2 θ1 ξ θ2 = 1.
Proof.
  intros.
  rewrite rm22_rewrite in H.
  specialize (k1_plus_k2 θ1 ξ θ2) as ?.
  split; lra.  
Qed.

Lemma k1_zero : forall θ1 ξ θ2, 
  k1 θ1 ξ θ2 = 0 ->
  (cos ξ = 1 /\ cos (θ1 / 2 + θ2 / 2) = 0) \/
  (cos ξ = -1 /\ cos (θ1 / 2 - θ2 / 2) = 0) \/
  (cos (θ1 / 2 + θ2 / 2) = 0 /\ cos (θ1 / 2 - θ2 / 2) = 0).
Proof.
  intros θ1 ξ θ2 H.
  rewrite k1_rewrite in H.
  apply Rplus_sqr_eq_0 in H as [H1 H2].
  apply Rmult_integral in H1 as [H1 | H1];
  apply Rmult_integral in H2 as [H2 | H2].
  - specialize (cos_sin_0 (ξ / 2)) as H.
    contradict H; auto.
  - left.
    split; auto.
    apply sin_half_zero; auto.
  - right; left.
    split; auto.
    apply cos_half_zero; auto.
  - right; right.
    split; auto.
Qed.

Lemma k2_zero : forall θ1 ξ θ2, 
  k2 θ1 ξ θ2 = 0 ->
  (cos ξ = 1 /\ sin (θ1/2 + θ2/2) = 0) \/
  (cos ξ = -1 /\ sin (θ1/2 - θ2/2) = 0) \/
  (sin (θ1/2 + θ2/2) = 0 /\ sin (θ1/2 - θ2/2) = 0).
Proof.
  intros θ1 ξ θ2 H.
  rewrite k2_rewrite in H.
  apply Rplus_sqr_eq_0 in H as [H1 H2].
  apply Rmult_integral in H1 as [H1 | H1];
  apply Rmult_integral in H2 as [H2 | H2].
  - specialize (cos_sin_0 (ξ / 2)) as H.
    contradict H; auto.
  - left.
    split; auto.
    apply sin_half_zero; auto.
  - right; left.
    split; auto.
    apply cos_half_zero; auto.
  - right; right.
    split; auto.
Qed.

(* Given a goal of the form (w + ... + x = y + ... + z), produce
   a goal of the form (a + ... + b = 0). This tactic tends to be slow due
   to the repeated calls to field_simplify_eq. *)
Ltac move_terms_to_lhs :=
  repeat match goal with 
  | |- _ = _ + ?a => apply Rplus_eq_reg_r with (r:=-a); field_simplify_eq
  | |- _ = _ - ?a => apply Rplus_eq_reg_r with (r:=a); field_simplify_eq
  | |- _ = 0 => idtac
  | |- _ = ?a => apply Rplus_eq_reg_r with (r:=-a); field_simplify_eq
  end.

(* Switch to using Rsqr rather than pow when possible *)
Ltac change_to_sqr :=
  repeat match goal with
  | |- context[?a ^ 3] => replace (a ^ 3) with (a ^ 2 * a) by lra
  | |- context[?a ^ 4] => replace (a ^ 4) with (a ^ 2 * a ^ 2) by lra
  | |- context[?a ^ 5] => replace (a ^ 5) with (a ^ 2 * a ^ 2 * a) by lra
  end;
  repeat rewrite <- Rsqr_pow2;
  repeat rewrite <- Rmult_assoc.

(* Undo some of the simplifications done by field_simpify_eq *)
Ltac undo_field_simpl :=
  repeat match goal with 
  | |- context[?a - ?b] => replace (a - b) with (a + - b) by lra
  | |- context[?a ^ 2] => replace (a ^ 2) with (a * a) by lra
  end;
  repeat rewrite Ropp_mult_distr_l;
  repeat rewrite <- Rmult_assoc.

(* Apply Rmult_plus_distr_r and Rmult_plus_distr_l *)
Ltac group_like_terms :=
  repeat rewrite <- Rmult_plus_distr_r;
  repeat rewrite Rmult_assoc;
  repeat rewrite <- Rmult_plus_distr_l;
  repeat rewrite <- Rmult_assoc.

(* Apply the sin2_cos2 rule *)
Ltac apply_sin2_cos2 :=
  group_like_terms;
  try rewrite (Rplus_comm ((cos _)²));
  rewrite sin2_cos2;
  field_simplify_eq;
  undo_field_simpl.

Lemma reorder_prod : forall a b c, a * b * c = a * c * b.
Proof. intros. lra. Qed.

Lemma reorder_sum : forall a b c, a + b + c = a + c + b.
Proof. intros. lra. Qed.

Lemma rm02_squared_plus_rm12_squared : forall θ1 ξ θ2,
  (rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)² = 4 * k1 θ1 ξ θ2 * k2 θ1 ξ θ2.
Proof.
  intros.
  unfold rm02, rm12, k1, k2.
  unfold Rsqr.
  field_simplify_eq.
  move_terms_to_lhs.
  change_to_sqr.
  rewrite (reorder_sum (_ * ((cos θ2)²))).
  rewrite (reorder_prod _ ((sin θ1)²) ((cos θ2)²)).
  apply_sin2_cos2.
  assert (tmp : forall a b c d e, a + b + c + d + e = a + (b + c) + d + e).
  { intros. lra. }
  rewrite tmp.
  clear tmp.
  rewrite (reorder_prod _ ((sin θ1)²) ((cos ξ)²)).
  rewrite (reorder_prod _ ((sin θ1)²) ((sin θ2)²)).
  apply_sin2_cos2.
  rewrite (reorder_prod _ ((cos ξ)²) ((sin θ2)²)).
  apply_sin2_cos2.
  apply_sin2_cos2.
  reflexivity.
Qed.

Lemma k1_args_swapped : forall θ1 ξ θ2, k1 θ1 ξ θ2 = k1 θ2 ξ θ1.
Proof. intros. unfold k1. lra. Qed.

Lemma k2_args_swapped : forall θ1 ξ θ2, k2 θ1 ξ θ2 = k2 θ2 ξ θ1.
Proof. intros. unfold k2. lra. Qed.

Lemma rm20m_squared_plus_rm21_squared : forall θ1 ξ θ2,
  (rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)² = 4 * k1 θ1 ξ θ2 * k2 θ1 ξ θ2.
Proof.
  intros.
  replace ((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²)
    with ((rm02 θ2 ξ θ1)² + (rm12 θ2 ξ θ1)²).
  rewrite rm02_squared_plus_rm12_squared.
  rewrite k1_args_swapped, k2_args_swapped.
  reflexivity.
  unfold rm02, rm12, rm20_minus, rm21.
  unfold Rsqr.
  lra.
Qed.

Lemma Cexp_atan_rm02 : forall θ1 ξ θ2,
  0 < rm02 θ1 ξ θ2 ->
  (Cexp (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2)) =
    / (√ (4 * k1 θ1 ξ θ2 * k2 θ1 ξ θ2)) * (rm02 θ1 ξ θ2, rm12 θ1 ξ θ2))%C.
Proof.
  intros.
  rewrite Cexp_atan by assumption.  
  rewrite rm02_squared_plus_rm12_squared.
  reflexivity.
Qed.

Lemma Cexp_atan_neg_rm02 : forall θ1 ξ θ2,
  rm02 θ1 ξ θ2 < 0 ->
  (Cexp (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2)) =
    - / (√ (4 * k1 θ1 ξ θ2 * k2 θ1 ξ θ2)) * (rm02 θ1 ξ θ2, rm12 θ1 ξ θ2))%C.
Proof.
  intros.
  rewrite Cexp_atan_neg by assumption.  
  rewrite rm02_squared_plus_rm12_squared.
  reflexivity.
Qed.

Lemma acos_rm22 : forall θ1 ξ θ2,
  -1 < rm22 θ1 ξ θ2 < 1 ->
  (cos (acos (rm22 θ1 ξ θ2) / 2) = √ (k1 θ1 ξ θ2) /\ 
     sin (acos (rm22 θ1 ξ θ2) / 2) = √ (k2 θ1 ξ θ2)) \/ 
  (cos (acos (rm22 θ1 ξ θ2) / 2) = - √ (k1 θ1 ξ θ2) /\ 
     sin (acos (rm22 θ1 ξ θ2) / 2) = - √ (k2 θ1 ξ θ2)).
Proof. 
  intros θ1 ξ θ2 Hrm22.
  specialize (k1_plus_k2 θ1 ξ θ2) as Hk.
  destruct (cos_sin_acos_same_sign (rm22 θ1 ξ θ2) Hrm22) as [[H1 H2] | [H1 H2]].
  left; split.
  rewrite H1, rm22_rewrite.
  apply f_equal.
  lra.
  rewrite H2, rm22_rewrite.
  apply f_equal.
  lra.
  right; split.
  rewrite H1, rm22_rewrite.
  do 2 apply f_equal.
  lra.
  rewrite H2, rm22_rewrite.
  do 2 apply f_equal.
  lra.
Qed.

Lemma m00_R_m00_I_sum : forall θ1 ξ θ2,
  k1 θ1 ξ θ2 > 0 ->
  (m00_R θ1 ξ θ2 / √ k1 θ1 ξ θ2)² + (m00_I θ1 ξ θ2 / √ k1 θ1 ξ θ2)² = 1.
Proof.
  intros θ1 ξ θ2 H.
  repeat rewrite Rsqr_div; try nonzero.
  rewrite Rsqr_sqrt by lra.
  field_simplify_eq; try nonzero.
  rewrite k1_rewrite.
  repeat rewrite Rsqr_mult.
  rewrite sin_half_squared, cos_half_squared.
  rewrite cos_plus, cos_minus.
  unfold m00_R, m00_I, Rsqr.
  field_simplify_eq.
  move_terms_to_lhs.
  change_to_sqr.
  undo_field_simpl.
  rewrite 2 (reorder_prod _ ((cos ξ)²)).
  apply_sin2_cos2.
  reflexivity.
Qed.

Lemma Cexp_acos_m00_R_pos : forall θ1 ξ θ2,
  0 < k1 θ1 ξ θ2 ->
  0 <= m00_I θ1 ξ θ2 / √ k1 θ1 ξ θ2 ->
  Cexp (- acos (m00_R θ1 ξ θ2 / √ k1 θ1 ξ θ2)) = (m00 θ1 ξ θ2 / √ k1 θ1 ξ θ2)%C.
Proof.
  intros θ1 ξ θ2 Hk1 H.
  erewrite Cexp_acos_pos; try apply H.
  unfold m00_R, m00_I, m00.
  apply c_proj_eq; simpl; field_simplify_eq; nonzero.
  apply m00_R_m00_I_sum.
  assumption.
Qed.

Lemma Cexp_acos_m00_R_neg : forall θ1 ξ θ2,
  0 < k1 θ1 ξ θ2 ->
  m00_I θ1 ξ θ2 / √ k1 θ1 ξ θ2 < 0 ->
  Cexp (acos (m00_R θ1 ξ θ2 / √ k1 θ1 ξ θ2)) = (m00 θ1 ξ θ2 / √ k1 θ1 ξ θ2)%C.
Proof.
  intros θ1 ξ θ2 Hk1 H.
  erewrite Cexp_acos_neg; try apply H.
  unfold m00_R, m00_I, m00.
  apply c_proj_eq; simpl; field_simplify_eq; nonzero.
  apply m00_R_m00_I_sum.
  assumption.
Qed.

(* First auxiliary lemma used in m01_rewrite_alt *)
Lemma m01_rewrite_alt_aux1 : forall θ1 ξ θ2,
  0 < k1 θ1 ξ θ2 ->  
  0 < k2 θ1 ξ θ2 ->
  m01 θ1 ξ θ2 =
  (- (m00 θ1 ξ θ2 * / √ k1 θ1 ξ θ2 * (√ k2 θ1 ξ θ2 *
    (/ √ (4 * k1 θ1 ξ θ2 * k2 θ1 ξ θ2) * (rm02 θ1 ξ θ2, rm12 θ1 ξ θ2)))))%C.
Proof.
  intros θ1 ξ θ2 Hk1 Hk2.
  assert (tmp : forall a b c d e, (a * b * (c * (d * e)))%C = (c * b * d * a * e)%C).
  { intros. lca. }
  rewrite tmp.
  clear tmp.
  rewrite 2 Copp_mult_distr_l.
  replace (- (√ k2 θ1 ξ θ2 * / √ k1 θ1 ξ θ2 * / √ (4 * k1 θ1 ξ θ2 * k2 θ1 ξ θ2)))%C 
    with (- / (2 * k1 θ1 ξ θ2))%C.
  2: { repeat rewrite sqrt_mult by lra.
       autorewrite with RtoC_db.
       repeat rewrite Rinv_mult_distr by nonzero.
       apply c_proj_eq; simpl;
       field_simplify_eq; try nonzero.
       replace 4 with (2²) by reflexivity. 
       rewrite sqrt_Rsqr by lra.
       rewrite <- Rsqr_pow2.
       rewrite Rsqr_sqrt by lra.
       lra. }
  unfold rm02, rm12.
  replace θ1 with (2 * (θ1 / 2)) by lra.
  replace θ2 with (2 * (θ2 / 2)) by lra.
  repeat rewrite sin_2a.
  repeat rewrite cos_2a.
  replace (2 * (θ1 / 2)) with θ1 by lra.
  replace (2 * (θ2 / 2)) with θ2 by lra.
  unfold m00, m01.
  field_simplify_eq; try nonzero.
  rewrite k1_rewrite.
  repeat rewrite Rsqr_mult.
  repeat rewrite sin_half_squared.
  repeat rewrite cos_half_squared.
  rewrite cos_plus, cos_minus.
  unfold Rsqr.
  apply c_proj_eq; simpl; field_simplify_eq.
  - move_terms_to_lhs.
    change_to_sqr. 
    undo_field_simpl.
    rewrite (reorder_sum (_ * ((sin (θ2 / 2))²))).
    rewrite (reorder_prod _ ((sin (θ1 / 2))²) (sin (θ1 / 2))).
    apply_sin2_cos2.
    assert (tmp: forall a b c d, a + b + c + d = a + d + b + c).
    { intros. lra. }
    rewrite tmp.
    clear tmp.
    rewrite (reorder_prod _ ((cos ξ)²) ((sin (θ2 / 2))²)).
    apply_sin2_cos2.
    replace (-2) with (- (2)) by lra.
    apply_sin2_cos2.
    reflexivity.
  - move_terms_to_lhs.
    change_to_sqr. 
    undo_field_simpl.
    replace (-4) with (- (4)) by lra.
    rewrite (reorder_prod _ ((cos (θ1 / 2))²) (cos (θ1 / 2))).
    rewrite (reorder_prod _ ((cos (θ1 / 2))²) (sin (θ2 / 2))).
    rewrite (reorder_prod _ ((cos (θ1 / 2))²) (sin ξ)).
    apply_sin2_cos2.
    rewrite (reorder_prod _ ((cos (θ1 / 2))²) ((sin (θ2 / 2))²)).
    rewrite (reorder_prod _ ((cos (θ1 / 2))²) (sin (θ1 / 2))).
    rewrite (reorder_prod _ ((cos (θ1 / 2))²) (cos ξ)).
    apply_sin2_cos2.
    reflexivity.
Qed.

Ltac move_term_left X :=
  repeat match goal with
  | |- _ => try rewrite (Rmult_comm _ X); repeat rewrite <- Rmult_assoc
  end.

Lemma sin_half_sin : forall x,
  sin (x / 2) * sin x + - cos (x / 2) = - cos (x / 2) * cos x.
Proof.
  intro x.
  replace x with (2 * (x / 2)) at 2 by lra.
  rewrite sin_2a.
  rewrite <- (Rmult_1_r (- cos _)).
  rewrite <- Ropp_mult_distr_l.
  rewrite Ropp_mult_distr_r.
  move_term_left (cos (x / 2)).
  group_like_terms.
  replace (sin (x / 2) * 2 * sin (x / 2) + - (1))
    with (- (1 - 2 * sin (x / 2) * sin (x / 2))) by lra.
  rewrite <- cos_2a_sin.
  replace (2 * (x / 2)) with x by lra.
  lra.
Qed.

Lemma sin_half_cos : forall x,
  sin (x / 2) * (1 + cos x) = cos (x / 2) * sin x.
Proof.
  intro x.
  replace x with (2 * (x / 2)) at 2 4 by lra.
  rewrite sin_2a.
  rewrite cos_2a_cos.
  lra.
Qed.

Lemma cos_half_cos : forall x,
  cos (x / 2) * (1 - cos x) = sin (x / 2) * sin x.
Proof.
  intro x.
  replace x with (2 * (x / 2)) at 2 4 by lra.
  rewrite sin_2a.
  rewrite cos_2a_sin.
  lra.
Qed.

(* Second auxiliary lemma used in m01_rewrite_alt
   TODO: this is still pretty manual; need to think about how to automate better -KHH *)
Lemma m01_rewrite_alt_aux2 : forall θ1 ξ θ2,
  rm02 θ1 ξ θ2 = 0 ->
  (m01 θ1 ξ θ2 * rm12 θ1 ξ θ2)%C = (- m00 θ1 ξ θ2 * (2 * (k2 θ1 ξ θ2 * Ci)))%C.
Proof.
  intros θ1 ξ θ2 Hrm02.
  unfold m00, m01, k2, rm12, rm02 in *.
  apply c_proj_eq; simpl; field_simplify_eq; move_terms_to_lhs;
  change_to_sqr; undo_field_simpl.
  - move_term_left (sin ξ).
    group_like_terms.
    apply Rmult_eq_0_compat_l.
    assert (tmp: forall a b c d e, a + b + c + d + e = (a + c + d) + (b + e)).
    { intros. lra. }
    rewrite tmp. clear tmp.
    replace θ2 with (2 * (θ2 / 2)) at 2 by lra.
    rewrite sin_2a.
    replace (-2) with (- (2)) by lra.
    rewrite <- Ropp_mult_distr_l.
    rewrite Ropp_mult_distr_r.
    rewrite <- 3 Ropp_mult_distr_l.
    rewrite Ropp_mult_distr_r.
    move_term_left (sin (θ1 / 2)).
    move_term_left (sin (θ2 / 2)).
    rewrite <- (Rmult_1_r 2) at 12.
    group_like_terms.
    replace (- cos (θ2 / 2) * 2 * cos (θ2 / 2) + - cos θ1 * cos θ2 + 1) 
      with (- (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1) + - cos θ1 * cos θ2) by lra.
    rewrite <- cos_2a_cos.
    replace (2 * (θ2 / 2)) with θ2 by lra.
    replace (- cos θ2 + - cos θ1 * cos θ2) 
      with (- cos θ2 * (1 + cos θ1)) by lra.
    rewrite <- 4 Ropp_mult_distr_l.
    rewrite (Ropp_mult_distr_r _ (cos _)).
    move_term_left (sin θ2).
    move_term_left (cos ξ).
    move_term_left 2.
    group_like_terms.
    rewrite sin_half_sin.
    rewrite Ropp_mult_distr_l.
    rewrite (Rmult_comm (- _)).
    rewrite <- Rmult_assoc.
    rewrite sin_half_cos.
    rewrite <- Rmult_assoc.
    rewrite <- Ropp_mult_distr_r.
    rewrite 2 Ropp_mult_distr_l.
    move_term_left (- cos (θ1 / 2)).
    group_like_terms.
    replace (cos ξ * sin θ2 * cos θ1) with (cos θ1 * cos ξ * sin θ2) by lra.
    rewrite Hrm02.
    lra.
 - rewrite sin2.
   field_simplify_eq.
   undo_field_simpl.
   rewrite <- 4 Ropp_mult_distr_l at 1.
   rewrite Ropp_mult_distr_r.
   move_term_left (sin θ2).
   group_like_terms.
   replace (cos (θ1 / 2) + - sin (θ1 / 2) * sin θ1)
     with (- (sin (θ1 / 2) * sin θ1 + - cos (θ1 / 2))) by lra.
   rewrite sin_half_sin.
   field_simplify_eq.
   undo_field_simpl.
   assert (tmp: forall a b c, a + b + c = c + a + b).
   { intros. lra. }
   rewrite (tmp (_ * _)). clear tmp.
   replace θ2 with (2 * (θ2 / 2)) at 1 by lra.
   rewrite sin_2a.
   unfold Rsqr.
   repeat rewrite <- Rmult_assoc.
   move_term_left (cos ξ).
   move_term_left (sin (θ2 / 2)).
   move_term_left (cos (θ1 / 2)).
   rewrite (Rmult_assoc _ 2).
   remember (2 * cos (θ2 / 2)) as x.
   move_term_left 2.
   subst x.
   group_like_terms.
   replace (2 * cos (θ2 / 2) * sin θ1 * cos (θ2 / 2))
     with (2 * sin θ1 * (cos (θ2 / 2))²) by (unfold Rsqr; lra).
   rewrite cos_half_squared.
   replace (2 * sin θ1 * (/ 2 * (1 + cos θ2)) + cos ξ * sin θ2 * cos θ1)
     with (sin θ1 * cos θ2 + cos θ1 * cos ξ * sin θ2 + sin θ1) by lra.
   rewrite Hrm02.
   field_simplify_eq.
   undo_field_simpl.
   assert (tmp: forall a b c d e f, a + b + c + d + e + f = (b + c + d) + (a + e + f)).
   { intros. lra. }
   rewrite tmp. clear tmp.
   rewrite <- 2 Ropp_mult_distr_l at 1.
   rewrite Ropp_mult_distr_r.
   rewrite <- 2 Ropp_mult_distr_l at 1.
   rewrite Ropp_mult_distr_r.
   replace θ2 with (2 * (θ2 / 2)) at 2 by lra.
   rewrite sin_2a.
   rewrite <- (Rmult_1_r (cos (θ1 / 2))) at 3.
   repeat rewrite <- Rmult_assoc.
   move_term_left (cos (θ2 / 2)).
   rewrite <- (Rmult_1_r (sin (θ1 / 2))) at 2.
   repeat rewrite <- Rmult_assoc.
   rewrite <- 4 Ropp_mult_distr_l.
   rewrite Ropp_mult_distr_r.
   group_like_terms.
   replace (- sin (θ2 / 2) * 2 * sin (θ2 / 2) + - cos θ1 * cos θ2 + 1)
     with (1 - 2 * sin (θ2 / 2) * sin (θ2 / 2) + - cos θ1 * cos θ2) by lra.
   rewrite <- cos_2a_sin.
   replace (2 * (θ2 / 2)) with θ2 by lra.
   replace (cos θ2 + - cos θ1 * cos θ2) with (cos θ2 * (1 - cos θ1)) by lra.
   rewrite <- Rmult_assoc.
   rewrite (reorder_prod _ (cos (θ1 / 2))).
   repeat rewrite Rmult_assoc.
   rewrite cos_half_cos.
   replace θ1 with (2 * (θ1 / 2)) at 4 by lra.
   rewrite sin_2a.
   move_term_left (sin (θ2 / 2)).
   move_term_left (cos ξ).
   move_term_left (sin (θ1 / 2)).
   group_like_terms.
   replace (cos (θ1 / 2) * 2 * cos (θ1 / 2) + cos θ1 * cos θ2 + - (1)) 
     with (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1 + cos θ1 * cos θ2) by lra.
   rewrite <- cos_2a_cos.
   replace (2 * (θ1 / 2)) with θ1 by lra.
   replace (cos θ1 + cos θ1 * cos θ2) with (cos θ1 * (1 + cos θ2)) by lra.
   rewrite <- Rmult_assoc.
   rewrite (reorder_prod _ (sin (θ2 / 2))).
   repeat rewrite Rmult_assoc.
   rewrite sin_half_cos.
   repeat rewrite <- Rmult_assoc.
   move_term_left (sin (θ1 / 2)).
   move_term_left (cos (θ2 / 2)).
   group_like_terms.
   replace (cos θ2 * sin θ1 + cos ξ * cos θ1 * sin θ2)
     with (sin θ1 * cos θ2 + cos θ1 * cos ξ * sin θ2) by lra.
   rewrite Hrm02.
   lra.
Qed.

Ltac try_rewrites :=
  repeat match goal with
  | H : ?x = _ |- context[?x] => rewrite H
  end.

Ltac simplify := 
  try_rewrites;
  try rewrite Cexp_cos_1 by assumption;
  try rewrite Cexp_cos_minus_1 by assumption;
  try rewrite Cexp_atan2_case_1 by lra;
  try rewrite Cexp_atan2_case_2 by lra;
  try rewrite Cexp_atan2_case_3 by lra;
  try rewrite Cexp_atan2_case_4 by lra;
  try rewrite Cexp_atan2_case_5 by lra;
  autorewrite with Cexp_db trig_db C_db RtoC_db R_db;
  try rewrite Cexp_atan_tan by assumption;
  try rewrite Cexp_atan_tan_neg by assumption.

Ltac try_solve :=
  try lca;
  try (eapply c_proj_eq; simpl; R_field); (* if lca doesn't work *)
  try (C_field_simplify; try lca;  (* if R_field doesn't work *) 
       try (replace (Ropp R0) with R0 by lra); (* Ropp R0 breaks nonzero *)
       nonzero).

Ltac simplify_and_solve := simplify; try_solve.

Lemma m01_rewrite_alt : forall θ1 ξ θ2,
  0 < k1 θ1 ξ θ2 -> 
  0 < k2 θ1 ξ θ2 -> 
  m01 θ1 ξ θ2 = 
    (- (m00 θ1 ξ θ2 * / √ k1 θ1 ξ θ2 *
      (√ k2 θ1 ξ θ2 * Cexp (atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2)))))%C.
Proof. 
  intros θ1 ξ θ2 Hk1 Hk2.
  unfold atan2.
  destruct_Rltb; simplify_assumptions.
  - rewrite Cexp_atan_rm02 by assumption. 
    autorewrite with C_db.
    apply m01_rewrite_alt_aux1; assumption.
  - rewrite Cexp_minus_PI.
    rewrite Cexp_atan_neg_rm02 by assumption.
    autorewrite with C_db.
    apply m01_rewrite_alt_aux1; assumption.
  - rewrite Cexp_plus_PI.
    rewrite Cexp_atan_neg_rm02 by assumption.
    autorewrite with C_db.
    apply m01_rewrite_alt_aux1; assumption.
  - rewrite Cexp_PI2.
    replace (/ √ k1 θ1 ξ θ2)%C with (2 * √ k2 θ1 ξ θ2 / rm12 θ1 ξ θ2)%C.
    2: { specialize (rm02_squared_plus_rm12_squared θ1 ξ θ2) as H3.
         rewrite H2 in H3.
         rewrite Rsqr_0, Rplus_0_l in H3.
         apply c_proj_eq; simpl; field_simplify_eq; try nonzero.
         replace 2 with (√ 4).
         rewrite (reorder_prod _ (rm12 _ _ _)).
         repeat rewrite <- sqrt_mult; try lra.
         rewrite (reorder_prod 4).
         rewrite <- H3.
         rewrite sqrt_Rsqr by lra.
         lra.
         replace 4 with (2²) by (unfold Rsqr; lra).
         rewrite sqrt_Rsqr; lra. }
    field_simplify_eq; try nonzero.
    repeat rewrite <- Cmult_assoc.
    rewrite (Cmult_assoc (√ _)).
    autorewrite with RtoC_db.
    rewrite sqrt_def by lra.
    apply m01_rewrite_alt_aux2; assumption.
  - rewrite Cexp_PI2_minus.
    autorewrite with C_db.
    replace (/ √ k1 θ1 ξ θ2)%C with (- (2) * √ k2 θ1 ξ θ2 / rm12 θ1 ξ θ2)%C.
    2: { specialize (rm02_squared_plus_rm12_squared θ1 ξ θ2) as H4.
         rewrite H3 in H4.
         rewrite Rsqr_0, Rplus_0_l in H4.
         apply c_proj_eq; simpl; field_simplify_eq; try nonzero.
         replace (-2) with (- √ 4).
         rewrite (reorder_prod _ (rm12 _ _ _)).
         rewrite <- 2 Ropp_mult_distr_l.
         repeat rewrite <- sqrt_mult; try lra.
         rewrite (reorder_prod 4).
         rewrite <- H4.
         rewrite Rsqr_neg.
         rewrite sqrt_Rsqr by lra.
         lra.
         replace 4 with (2²) by (unfold Rsqr; lra).
         rewrite sqrt_Rsqr; lra. }
    field_simplify_eq; try nonzero.
    repeat rewrite <- Cmult_assoc.
    rewrite (Cmult_assoc (√ _)).
    autorewrite with RtoC_db.
    rewrite sqrt_def by lra.
    apply m01_rewrite_alt_aux2; assumption.
  - (* rm12 = 0 and rm02 = 0 forces k2 = 0, which is a contradiction *)
    assert (H: k2 θ1 ξ θ2 = 0). 
    { specialize (rm02_squared_plus_rm12_squared θ1 ξ θ2) as H.
      rewrite H1, H3 in H.
      rewrite Rsqr_0 in H.
      rewrite Rplus_0_l in H.
      symmetry in H.
      apply Rmult_integral in H as [H | H]; try assumption.
      apply Rmult_integral in H as [H | H]; lra. }
    lra.
Qed.

Lemma m10_rewrite_alt : forall θ1 ξ θ2,
  0 < k1 θ1 ξ θ2 -> 
  0 < k2 θ1 ξ θ2 -> 
  m10 θ1 ξ θ2 = 
    (m00 θ1 ξ θ2 * / √ k1 θ1 ξ θ2 *
      (Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)) * √ k2 θ1 ξ θ2))%C.
Proof. 
  intros θ1 ξ θ2 Hk1 Hk2.
  specialize (m01_rewrite_alt θ2 ξ θ1) as Hm01.
  unfold m00, m01, m10, rm02, rm12, rm20_minus, rm21 in *.
  rewrite <- Copp_plus_distr in Hm01.
  rewrite <- (Copp_involutive (_ + _)%C).
  rewrite (Cmult_comm (sin (θ2 / 2)) (cos (θ1 / 2))). 
  replace (cos (θ2 / 2) * Cexp ξ * sin (θ1 / 2))%C
    with (sin (θ1 / 2) * Cexp ξ * cos (θ2 / 2))%C by lca.
  rewrite Hm01.
  clear Hm01.
  rewrite (k1_args_swapped θ2 ξ θ1), (k2_args_swapped θ2 ξ θ1).
  rewrite (Rmult_comm (sin θ1) (sin ξ)). 
  rewrite (Rmult_comm (cos θ1) (sin θ2)). 
  replace (sin θ1 * cos ξ * cos θ2) with (cos θ2 * cos ξ * sin θ1) by lra.
  lca. 
  rewrite k1_args_swapped.
  assumption.
  rewrite k2_args_swapped.
  assumption.
Qed.

Lemma C0_imp: forall c : C, c = 0 -> fst c = 0 /\ snd c = 0.
Proof. intros c H. inversion H. auto. Qed.

Lemma m00_zero_implies_m11_zero : forall θ1 ξ θ2,
  m00 θ1 ξ θ2 = 0 -> m11 θ1 ξ θ2 = 0.
Proof.
  intros θ1 ξ θ2 H.
  unfold m00, m11 in *.
  apply C0_imp in H as [H1 H2].
  simpl in *.
  autorewrite with R_db in *.
  apply Ropp_eq_0_compat in H2.
  rewrite Ropp_involutive in H2.
  apply Rmult_integral in H2 as [H2 | H2].
  apply Rmult_integral in H2 as [H2 | H2].
  - rewrite H2 in *.
    autorewrite with C_db R_db in *.
    apply Rmult_integral in H1 as [H1 | H1].
    specialize (cos_sin_0 (θ2 * / 2)) as H.
    contradict H; auto.
    rewrite H1.
    lca.
  - apply sin_0_cos in H2 as [H2 | H2].
    rewrite H2 in *.
    rewrite Cexp_cos_1 by assumption.
    lca.
    rewrite H2 in *.
    rewrite Cexp_cos_minus_1 by assumption.
    lca.
  - rewrite H2 in *.
    autorewrite with C_db R_db in *.
    apply Rmult_integral in H1 as [H1 | H1].
    rewrite H1. lca.
    specialize (cos_sin_0 (θ1 * / 2)) as H.
    contradict H; auto.
Qed.

Lemma m11_rewrite_alt_aux : forall θ1 ξ θ2,
  (m11 θ1 ξ θ2 * m00 θ1 ξ θ2 * k2 θ1 ξ θ2)%C =  
    (- m01 θ1 ξ θ2 * m10 θ1 ξ θ2 * k1 θ1 ξ θ2)%C.
Proof. 
  intros.
  unfold m11, m00, k2, m01, m10, k1.
  apply c_proj_eq; simpl; field_simplify_eq; move_terms_to_lhs.
  change_to_sqr.
  repeat rewrite sin_half_squared.
  repeat rewrite cos_half_squared.
  rewrite sin2.
  field_simplify_eq.
  replace (16 * (cos ξ)² * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)) 
    with (4 * (cos ξ)² * sin θ2 * sin θ1).
  lra.
  replace θ1 with (2 * (θ1 / 2)) at 1 by lra.
  replace θ2 with (2 * (θ2 / 2)) at 1 by lra.
  rewrite 2 sin_2a.
  lra.
  change_to_sqr.
  repeat rewrite sin_half_squared.
  repeat rewrite cos_half_squared.
  field_simplify_eq.
  replace (16 * cos ξ * sin ξ * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)) 
    with (4 * cos ξ * sin ξ * sin θ2 * sin θ1).
  lra.
  replace θ1 with (2 * (θ1 / 2)) at 1 by lra.
  replace θ2 with (2 * (θ2 / 2)) at 1 by lra.
  rewrite 2 sin_2a.
  lra.
Qed.

Lemma m11_rewrite_alt : forall θ1 ξ θ2,
  0 < k1 θ1 ξ θ2 -> 
  0 < k2 θ1 ξ θ2 -> 
  m11 θ1 ξ θ2 = 
    (m00 θ1 ξ θ2 * / √ k1 θ1 ξ θ2 *
      (Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)) * √ k1 θ1 ξ θ2 *
         Cexp (atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2))))%C.
Proof. 
  intros θ1 ξ θ2 Hk1 Hk2.
  (* first, solve the case where m00 = 0 (which implies m11 = 0) *)
  specialize (Ceq_dec (m00 θ1 ξ θ2) 0) as m00_zero. 
  destruct m00_zero.
  rewrite e.
  apply m00_zero_implies_m11_zero in e.
  rewrite e.
  lca.
  (* otherwise, we can use m11_rewrite_alt_aux *)
  field_simplify_eq; try nonzero.
  (* too lazy to do the rewriting manually, but in general this is not good form -KH *)
  replace (m00 θ1 ξ θ2 * Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)) * Cexp (atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2)))%C
  with (- (- (m00 θ1 ξ θ2 * / √ k1 θ1 ξ θ2 * (√ k2 θ1 ξ θ2 * Cexp (atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2))))) * (m00 θ1 ξ θ2 * / √ k1 θ1 ξ θ2 * (Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)) * √ k2 θ1 ξ θ2)) * / m00 θ1 ξ θ2 * / k2 θ1 ξ θ2 * k1 θ1 ξ θ2)%C.
  rewrite <- m01_rewrite_alt by assumption.
  rewrite <- m10_rewrite_alt by assumption.
  field_simplify_eq.
  apply m11_rewrite_alt_aux.
  split; try assumption; nonzero.
  field_simplify_eq.
  rewrite <- (Cmult_assoc (m00 _ _ _) (√ k2 _ _ _)).
  rewrite <- (Cmult_assoc (m00 _ _ _) (√ k1 _ _ _)).
  autorewrite with RtoC_db.
  rewrite 2 sqrt_def by lra.
  lca.
  repeat split; try assumption; nonzero.
Qed.

Ltac rewrite_mij_alt θ1 ξ θ2 :=
  let Hm01 := fresh in
  let Hm10 := fresh in 
  let Hm11 := fresh in
  specialize (m01_rewrite_alt θ1 ξ θ2) as Hm01;
  specialize (m10_rewrite_alt θ1 ξ θ2) as Hm10;
  specialize (m11_rewrite_alt θ1 ξ θ2) as Hm11;
  unfold m00, m01, m10, m11 in *;
  try rewrite Hm01 by assumption;
  try rewrite Hm10 by assumption;
  try rewrite Hm11 by assumption;
  clear Hm01 Hm10 Hm11.

Lemma minus_1_plus_1 : -1 + 1 = 0.
Proof. lra. Qed.
Lemma one_plus_minus_1 : 1 + -1 = 0.
Proof. lra. Qed.
Hint Rewrite minus_1_plus_1 one_plus_minus_1 : R_db.
Hint Rewrite atan_0 atan_opp : trig_db.

(* The proof is split into 3 main cases, each with various subcases, depending 
   on the values of θ1 ξ θ2. In general, different parameters lead to different
   global phases. You can find the global phases used by searching for the 
   keyword "exists". *)
Lemma yzy_to_zyz_correct : forall θ1 ξ θ2 ξ1 θ ξ2,
  yzy_to_zyz θ1 ξ θ2 = (ξ1, θ, ξ2) ->
  y_rotation θ2 × phase_shift ξ × y_rotation θ1
    ∝ phase_shift ξ2 × y_rotation θ × phase_shift ξ1.
Proof.
  intros θ1 ξ θ2 ξ1 θ ξ2 H.
  unfold yzy_to_zyz in H.
  bdestruct (rm22 θ1 ξ θ2 <? 1).
  bdestruct (-1 <? rm22 θ1 ξ θ2).
  all: inversion H; subst; clear H.
  - (* CASE 1: -1 < rm22 < 1 *)
    assert (Hk1: 0 < k1 θ1 ξ θ2).
    { rewrite rm22_rewrite in H0, H1. lra. }
    assert (Hk2: 0 < k2 θ1 ξ θ2).
    { rewrite rm22_rewrite in H0, H1.  specialize (k1_plus_k2 θ1 ξ θ2) as ?. lra. }
    specialize (acos_rm22 θ1 ξ θ2) as [[H2 H3] | [H2 H3]];
    bdestruct (m00_I θ1 ξ θ2 / √ k1 θ1 ξ θ2 <? 0).
    1,2: lra.
    * exists (acos (m00_R θ1 ξ θ2 / √ k1 θ1 ξ θ2)).
      rewrite Cexp_acos_m00_R_neg by assumption.
      solve_matrix; try_rewrites; rewrite_mij_alt θ1 ξ θ2; try_solve. 
    * exists (- acos (m00_R θ1 ξ θ2 / √ k1 θ1 ξ θ2)).
      apply ROrder.not_gt_le in H.
      rewrite Cexp_acos_m00_R_pos by assumption.
      solve_matrix; try_rewrites; rewrite_mij_alt θ1 ξ θ2; try_solve. 
    * exists (PI + acos (m00_R θ1 ξ θ2 / √ k1 θ1 ξ θ2)).
      rewrite Cexp_add, Cexp_PI.
      rewrite Cexp_acos_m00_R_neg by assumption.
      solve_matrix; try_rewrites; rewrite_mij_alt θ1 ξ θ2; try_solve. 
    * exists (PI + - acos (m00_R θ1 ξ θ2 / √ k1 θ1 ξ θ2)).
      rewrite Cexp_add, Cexp_PI.
      apply ROrder.not_gt_le in H.
      rewrite Cexp_acos_m00_R_pos by assumption.
      solve_matrix; try_rewrites; rewrite_mij_alt θ1 ξ θ2; try_solve. 
  - (* CASE 2: rm22 = -1 *)
    assert (rm22 θ1 ξ θ2 = -1).
    specialize (rm22_bounds θ1 ξ θ2) as [? _].
    lra.
    clear H0 H1.
    apply rm22_minus_one in H as [H _].
    apply k1_zero in H as [H | [H | H]]; destruct H as [H1 H2].
    + destruct (cos_0_sin (θ1 / 2 + θ2 / 2) H2) as [H3 | H3].
      * exists 0.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11, atan2.
        destruct_Rltb.
        assert (Hs : sin ξ = 0).
        apply cos_1_sin; auto.
        simplify_and_solve.
      * exists PI.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11, atan2.
        destruct_Rltb.
        assert (Hs : sin ξ = 0).
        apply cos_1_sin; auto.
        simplify_and_solve.
    + destruct (cos_0_sin (θ1 / 2 - θ2 / 2) H2) as [H3 | H3].
      * exists PI.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11, atan2.
        assert (Hs : sin ξ = 0).
        apply cos_neg_1_sin; auto.
        destruct_Rltb; simplify_and_solve.
      * exists 0.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11, atan2.
        assert (Hs : sin ξ = 0).
        apply cos_neg_1_sin; auto.
        destruct_Rltb; simplify_and_solve.
    + destruct (cos_x_y_zero _ _ H1 H2) as [[H3 H4] | [H3 H4]];
      destruct (cos_0_sin (θ1/2 + θ2/2) H1) as [H5 | H5];
      destruct (cos_0_sin (θ1/2 - θ2/2) H2) as [H6 | H6].
      * apply sin_half_zero in H4.
        exists ξ.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11.
        bdestruct (0 <? cos ξ); bdestruct (cos ξ <? 0); simplify_and_solve. 
        simplify_assumptions.
        destruct (cos_0_sin _ H7) as [H8 | H8]; simplify_and_solve.
      * (* contradiction - impossible case *)
        rewrite sin_plus, sin_minus in *.
        rewrite H3 in *.
        lra. 
      * (* contradiction *)
        rewrite sin_plus, sin_minus in *.
        rewrite H3 in *.
        lra.
      * apply sin_half_zero in H4.
        exists (PI + ξ).
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11.
        bdestruct (0 <? cos ξ); bdestruct (cos ξ <? 0); simplify_and_solve. 
        simplify_assumptions.
        destruct (cos_0_sin _ H7) as [H8 | H8]; simplify_and_solve.
      * (* contradiction *)
        rewrite sin_plus, sin_minus, cos_plus, cos_minus in *.
        rewrite H3, H4 in *.
        lra. 
      * specialize (cos_half_zero _ H4) as H7.
        exists 0.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11.
        bdestruct (0 <? cos ξ); bdestruct (cos ξ <? 0); simplify_and_solve.
        1,2: replace (sin ξ * -1 * / cos ξ) with (- (sin ξ / cos ξ)) by lra;
             simplify_and_solve.
        simplify_assumptions.
        destruct (cos_0_sin _ H8) as [H9 | H9]; simplify_and_solve.
      * specialize (cos_half_zero _ H4) as H7.
        exists PI.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11.
        bdestruct (0 <? cos ξ); bdestruct (cos ξ <? 0); simplify_and_solve.
        1,2: replace (sin ξ * -1 * / cos ξ) with (- (sin ξ / cos ξ)) by lra;
             simplify_and_solve.
        simplify_assumptions.
        destruct (cos_0_sin _ H8) as [H9 | H9]; simplify_and_solve.
      * (* contradiction *)
        rewrite sin_plus, sin_minus, cos_plus, cos_minus in *.
        rewrite H3, H4 in *.
        lra.
  - (* CASE 3: rm22 = 1 *)
    assert (rm22 θ1 ξ θ2 = 1).
    specialize (rm22_bounds θ1 ξ θ2) as [_ ?].
    lra.
    clear H0.
    apply rm22_one in H as [_ H].
    apply k2_zero in H as [H | [H | H]]; destruct H as [H1 H2].
    + destruct (sin_0_cos (θ1 / 2 + θ2 / 2) H2) as [H3 | H3].
      * exists 0.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11, atan2.
        destruct_Rltb.
        assert (Hs : sin ξ = 0).
        apply cos_1_sin; auto.
        simplify_and_solve.
      * exists PI.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11, atan2.
        destruct_Rltb.
        assert (Hs : sin ξ = 0).
        apply cos_1_sin; auto.
        simplify_and_solve.
    + destruct (sin_0_cos (θ1 / 2 - θ2 / 2) H2) as [H3 | H3].
      * exists 0.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11, atan2.
        assert (Hs : sin ξ = 0).
        apply cos_neg_1_sin; auto.
        destruct_Rltb; simplify_and_solve.
      * exists PI.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11, atan2.
        assert (Hs : sin ξ = 0).
        apply cos_neg_1_sin; auto.
        destruct_Rltb; simplify_and_solve.
    + destruct (sin_x_y_zero _ _ H1 H2) as [[H3 H4] | [H3 H4]];
      destruct (sin_0_cos (θ1/2 + θ2/2) H1) as [H5 | H5];
      destruct (sin_0_cos (θ1/2 - θ2/2) H2) as [H6 | H6].
      * apply sin_half_zero in H4.
        exists 0.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11.
        bdestruct (0 <? cos ξ); bdestruct (cos ξ <? 0); simplify_and_solve.
        simplify_assumptions.
        destruct (cos_0_sin _ H7) as [H8 | H8]; simplify_and_solve.
      * (* contradiction - impossible case *)
        rewrite cos_plus, cos_minus in *.
        rewrite H3 in *.
        lra. 
      * (* contradiction *)
        rewrite cos_plus, cos_minus in *.
        rewrite H3 in *.
        lra. 
      * apply sin_half_zero in H4.
        exists PI.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11.
        bdestruct (0 <? cos ξ); bdestruct (cos ξ <? 0); simplify_and_solve.
        simplify_assumptions.
        destruct (cos_0_sin _ H7) as [H8 | H8]; simplify_and_solve.
      * (* contradiction *)
        rewrite sin_plus, sin_minus, cos_plus, cos_minus in *.
        rewrite H3, H4 in *.
        lra. 
      * specialize (cos_half_zero _ H4) as H7.
        exists ξ.
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11.
        bdestruct (0 <? cos ξ); bdestruct (cos ξ <? 0); simplify_and_solve.
        1,2: replace (sin ξ * -1 * / cos ξ) with (- (sin ξ / cos ξ)) by lra;
             simplify_and_solve.
        simplify_assumptions.
        destruct (cos_0_sin _ H8) as [H9 | H9]; simplify_and_solve.
      * specialize (cos_half_zero _ H4) as H7.
        exists (PI + ξ).
        solve_matrix; rewrite_mij θ1 ξ θ2; simplify_and_solve.
        unfold rm10, rm11.
        bdestruct (0 <? cos ξ); bdestruct (cos ξ <? 0); simplify_and_solve.
        1,2: replace (sin ξ * -1 * / cos ξ) with (- (sin ξ / cos ξ)) by lra;
             simplify_and_solve.
        simplify_assumptions.
        destruct (cos_0_sin _ H8) as [H9 | H9]; simplify_and_solve.
      * (* contradiction *)
        rewrite sin_plus, sin_minus, cos_plus, cos_minus in *.
        rewrite H3, H4 in *.
        lra.
Qed.
