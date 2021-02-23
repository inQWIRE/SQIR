Require Export UnitarySem.
Require Export Reals.ROrderedType.
Require Export Reals.Ratan.

Local Open Scope ucom_scope.
Local Open Scope R_scope.

(* Boolean comparison is not defined over Reals - for now we'll assert
   that such an operator exists. *)
Parameter Rleb : R -> R -> bool. 
Parameter Rltb : R -> R -> bool.
Infix "<=?" := Rleb : R_scope.
Infix "<?" := Rltb : R_scope.
Axiom Rleb_le : forall x y, Rleb x y = true <-> Rle x y.
Axiom Rltb_lt : forall x y, Rltb x y = true <-> Rlt x y.

Lemma Rleb_lt_false: forall x y, Rleb x y = false <-> Rlt y x.
Proof.
intros.
split.
intros H.
apply Rnot_le_lt.
intros R.
apply Rleb_le in R. rewrite R in H.
inversion H.
intros.
apply not_true_is_false.
intros R.
apply Rleb_le in R. lra.
Qed.

Lemma Rltb_le_false: forall x y, Rltb x y = false <-> Rle y x.
Proof.
intros.
split.
intros H.
apply Rnot_lt_le.
intros R.
apply Rltb_lt in R. rewrite R in H.
inversion H.
intros.
apply not_true_is_false.
intros R.
apply Rltb_lt in R. lra.
Qed.

(* See: https://en.wikipedia.org/wiki/Atan2 *)
Definition atan2 (y x : R) : R :=
  if 0 <? x then atan (y/x)
  else if x <? 0 then
       if 0 <=? y then atan (y/x) + PI else atan (y/x) - PI
  else
       if 0 <? y then PI/2 else if y <? 0 then -PI/2 else 0.

(* The code below is fairly direct translation of Qiskit's 'Quaternion' class.
   https://qiskit.org/documentation/_modules/qiskit/quantum_info/operators/quaternion.html *)

(* Note: we should be using a matrix library instead, but since everything 
   is fixed size tuples are fine for now. *)
Definition quaternion : Type := R * R * R * R.
Definition rotation_matrix : Type := (R * R * R) * (R * R * R) * (R * R * R).

(* Multiply two quaternions. *)
Definition mult (q p : quaternion) : quaternion :=
  match q with (qw, qx, qy, qz) =>
  match p with (pw, px, py, pz) =>
  (qw * pw - qx * px - qy * py - qz * pz,
   qw * px + qx * pw + qy * pz - qz * py,
   qw * py - qx * pz + qy * pw + qz * px,
   qw * pz + qx * py - qy * px + qz * pw)
  end end.

(* Normalize a quaternion. *)
Definition norm (q : quaternion) : R :=
  match q with (qw, qx, qy, qz) =>
  sqrt (qw * qw + qx * qx + qy * qy + qz * qz)
  end.

Definition normalize (q : quaternion) : quaternion :=
  match q with (qw, qx, qy, qz) =>
  (qw / norm q, qx / norm q, qy / norm q, qz / norm q)
  end.

(* First, we need to talk about if the norm of a quaternion is zero.
    It is impossible in the case of the q1, q2 and a3 in from_yzy.
    norm of the q1 * q2 * q3 is one. *)
Lemma from_yzy_norm_one :    forall (θ1 ξ θ2 : R),
      let q1 : quaternion := (cos (θ1 / 2), 0, sin (θ1 / 2), 0) in
  let q2 : quaternion := (cos (ξ / 2), 0, 0, sin (ξ / 2)) in
  let q3 : quaternion := (cos (θ2 / 2), 0, sin (θ2 / 2), 0) in
         norm (mult (mult q1 q2) q3) = 1.
Proof.
intros.
unfold q1,q2,q3, mult,norm.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((cos (θ1 * / 2) * cos (ξ * / 2) * cos (θ2 * / 2) +
    - (sin (θ1 * / 2) * cos (ξ * / 2) * sin (θ2 * / 2)))
   = cos (ξ * / 2) * (cos (θ1 * / 2) * cos (θ2 * / 2) - sin (θ1 * / 2) * sin (θ2 * / 2))) by lra.
rewrite H. clear H.
rewrite <- cos_plus.
assert (cos (ξ * / 2) * cos (θ1 * / 2 + θ2 * / 2) * (cos (ξ * / 2) * cos (θ1 * / 2 + θ2 * / 2))
       = ( Rsqr (cos (ξ * / 2)) * Rsqr (cos (θ1 * / 2 + θ2 * / 2)))).
unfold Rsqr. lra.
rewrite H. clear H.
assert ((sin (θ1 * / 2) * sin (ξ * / 2) * cos (θ2 * / 2) +
    - (cos (θ1 * / 2) * sin (ξ * / 2) * sin (θ2 * / 2)))
   = sin (ξ * / 2) * (sin (θ1 * / 2) * cos (θ2 * / 2) - cos (θ1 * / 2) * sin (θ2 * / 2))) by lra.
rewrite H. clear H.
rewrite <- sin_minus.
assert (sin (ξ * / 2) * sin (θ1 * / 2 - θ2 * / 2) * (sin (ξ * / 2) * sin (θ1 * / 2 - θ2 * / 2))
       = ( Rsqr (sin (ξ * / 2)) * Rsqr (sin (θ1 * / 2 - θ2 * / 2)))).
unfold Rsqr. lra.
rewrite H. clear H.
assert ((cos (θ1 * / 2) * cos (ξ * / 2) * sin (θ2 * / 2) +
    sin (θ1 * / 2) * cos (ξ * / 2) * cos (θ2 * / 2))
   = cos (ξ * / 2) * (sin (θ1 * / 2) * cos (θ2 * / 2) + cos (θ1 * / 2) * sin (θ2 * / 2))) by lra.
rewrite H. clear H.
rewrite <- sin_plus.
assert (cos (ξ * / 2) * sin (θ1 * / 2 + θ2 * / 2) * (cos (ξ * / 2) * sin (θ1 * / 2 + θ2 * / 2))
       = ( Rsqr (cos (ξ * / 2)) * Rsqr (sin (θ1 * / 2 + θ2 * / 2)))).
unfold Rsqr. lra.
rewrite H. clear H.
assert ((sin (θ1 * / 2) * sin (ξ * / 2) * sin (θ2 * / 2) +
    cos (θ1 * / 2) * sin (ξ * / 2) * cos (θ2 * / 2))
   = sin (ξ * / 2) * (cos (θ1 * / 2) * cos (θ2 * / 2) + sin (θ1 * / 2) * sin (θ2 * / 2))) by lra.
rewrite H. clear H.
rewrite <- cos_minus.
assert (sin (ξ * / 2) * cos (θ1 * / 2 - θ2 * / 2) * (sin (ξ * / 2) * cos (θ1 * / 2 - θ2 * / 2))
       = ( Rsqr (sin (ξ * / 2)) * Rsqr (cos (θ1 * / 2 - θ2 * / 2)))).
unfold Rsqr. lra.
rewrite H. clear H.
assert (((cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))² + (sin (ξ * / 2))² * (sin (θ1 * / 2 - θ2 * / 2))² +
   (cos (ξ * / 2))² * (sin (θ1 * / 2 + θ2 * / 2))² + (sin (ξ * / 2))² * (cos (θ1 * / 2 - θ2 * / 2))²)
   = (cos (ξ * / 2))² * ((sin (θ1 * / 2 + θ2 * / 2))² + (cos (θ1 * / 2 + θ2 * / 2))²)
    + (sin (ξ * / 2))² * ((sin (θ1 * / 2 - θ2 * / 2))² + (cos (θ1 * / 2 - θ2 * / 2))²)) by lra.
rewrite H. clear H.
rewrite sin2_cos2. rewrite sin2_cos2.
autorewrite with R_db.
rewrite Rplus_comm.
rewrite sin2_cos2.
rewrite sqrt_1.
reflexivity.
Qed.


Lemma from_yzy_normalize_eq :    forall (θ1 ξ θ2 : R),
      let q1 : quaternion := (cos (θ1 / 2), 0, sin (θ1 / 2), 0) in
  let q2 : quaternion := (cos (ξ / 2), 0, 0, sin (ξ / 2)) in
  let q3 : quaternion := (cos (θ2 / 2), 0, sin (θ2 / 2), 0) in
         normalize (mult (mult q1 q2) q3) = (mult (mult q1 q2) q3).
Proof.
intros.
unfold q1,q2,q3,normalize.
rewrite from_yzy_norm_one.
unfold mult.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite  Rinv_1.
 autorewrite with R_db C_db Cexp_db trig_db.
reflexivity.
Qed.


Lemma norm_bound : forall (q: quaternion), 0 <= norm q.
Proof.
intros.
unfold norm.
destruct q.
destruct p. destruct p.
assert (0 <= (r1 * r1 + r2 * r2 + r0 * r0 + r * r)).
specialize ( Rle_0_sqr r1) as H1.
unfold Rsqr in H1. 
specialize ( Rle_0_sqr r2) as H2.
unfold Rsqr in H2. 
specialize ( Rle_0_sqr r0) as H3.
unfold Rsqr in H3. 
specialize ( Rle_0_sqr r) as H4.
unfold Rsqr in H4.
lra. 
apply sqrt_positivity.
assumption.
Qed.


(* Convert a unit-length quaternion to a rotation matrix. *)
Definition to_matrix (q : quaternion) : rotation_matrix :=
  match q with
  (w, x, y, z) =>
    ((1 - 2*y*y - 2*z*z, 2*x*y - 2*z*w, 2*x*z + 2*y*w), 
     (2*x*y + 2*z*w, 1 - 2*x*x - 2*z*z, 2*y*z - 2*x*w), 
     (2*x*z - 2*y*w, 2*y*z + 2*x*w, 1 - 2*x*x - 2*y*y))
  end.


Definition rw (θ1 ξ θ2 : R) : R := 
   cos (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)).
   
Definition rx (θ1 ξ θ2 : R) : R := 
   sin (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)).

Definition ry (θ1 ξ θ2 : R) : R := 
   cos (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2)).

Definition rz (θ1 ξ θ2 : R) : R := 
   sin (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)).

Definition rm02 (θ1 ξ θ2 : R) : R :=
  2 * (rx θ1 ξ θ2) * (rz θ1 ξ θ2) + 2 * (ry θ1 ξ θ2) * (rw θ1 ξ θ2). 

Definition rm12 (θ1 ξ θ2 : R) : R :=
  2 * (ry θ1 ξ θ2) * (rz θ1 ξ θ2) - 2 * (rx θ1 ξ θ2) * (rw θ1 ξ θ2). 

Definition rm22 (θ1 ξ θ2 : R) : R :=
  1 - 2 * (rx θ1 ξ θ2) * (rx θ1 ξ θ2) - 2 * (ry θ1 ξ θ2) * (ry θ1 ξ θ2).

Definition rm10 (θ1 ξ θ2 : R) : R :=
  2 * (rx θ1 ξ θ2) * (ry θ1 ξ θ2) + 2 * (rz θ1 ξ θ2) * (rw θ1 ξ θ2). 

Definition rm11 (θ1 ξ θ2 : R) : R :=
  1 - 2 * (rx θ1 ξ θ2) * (rx θ1 ξ θ2) - 2 * (rz θ1 ξ θ2) * (rz θ1 ξ θ2). 

Definition rm20_minus (θ1 ξ θ2 : R) : R :=
  - 2 * (rx θ1 ξ θ2) * (rz θ1 ξ θ2) + 2 * (ry θ1 ξ θ2) * (rw θ1 ξ θ2). 

Definition rm21 (θ1 ξ θ2 : R) : R :=
  2 * (ry θ1 ξ θ2) * (rz θ1 ξ θ2) + 2 * (rx θ1 ξ θ2) * (rw θ1 ξ θ2). 

(* Convert a quaternion to a sequence of ZYZ Euler angles.
   We extract the formula for phi, theta and lambda directly. *)
Definition to_zyz_theta (θ1 ξ θ2 : R) : R :=
  if rm22 θ1 ξ θ2 <? 1
  then if -1 <? rm22 θ1 ξ θ2 
       then acos (rm22 θ1 ξ θ2)
       else PI else 0.

Definition to_zyz_phi (θ1 ξ θ2 : R) : R :=
  if rm22 θ1 ξ θ2 <? 1
  then if -1 <? rm22 θ1 ξ θ2 
       then atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2)
       else - atan2 (rm10 θ1 ξ θ2) (rm11 θ1 ξ θ2) 
  else atan2 (rm10 θ1 ξ θ2) (rm11 θ1 ξ θ2).

Definition to_zyz_lambda (θ1 ξ θ2 : R) : R :=
  if rm22 θ1 ξ θ2 <? 1
  then if -1 <? rm22 θ1 ξ θ2 
       then atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)
       else 0 
  else 0.

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

Lemma cos_1_half_cos: forall (θ:R), cos θ = 1 -> cos (θ/2) = 1 \/ cos (θ/2) = -1.
Proof.
  intros.
  assert (θ = 2 * (θ / 2)) by lra.
  rewrite H0 in H.
  rewrite cos_2a_cos in H.
  assert (Rsqr (cos (θ / 2)) = Rsqr 1).
  unfold Rsqr. lra.
  apply Rsqr_eq in H1. assumption.
Qed.

Lemma cos_neg_1_half_cos: forall (θ:R), cos θ = -1 -> cos (θ/2) = 0.
Proof.
  intros.
  assert (θ = 2 * (θ / 2)) by lra.
  rewrite H0 in H.
  rewrite cos_2a_cos in H.
  assert (Rsqr (cos (θ / 2)) = 0).
  unfold Rsqr. lra.
  apply Rsqr_0_uniq in H1. assumption.
Qed.

Lemma cos_1_half_sin: forall (θ:R), cos θ = 1 -> sin (θ/2) = 0.
Proof.
  intros.
  assert (θ = 2 * (θ / 2)) by lra.
  rewrite H0 in H.
  rewrite cos_2a_sin in H.
  assert (Rsqr (sin (θ / 2)) = 0).
  unfold Rsqr. lra.
  apply Rsqr_0_uniq in H1. assumption.
Qed.

Lemma cos_neg_1_half_sin: forall (θ:R), cos θ = - 1 -> sin (θ/2) = 1 \/ sin (θ/2) = -1.
Proof.
  intros.
  assert (θ = 2 * (θ / 2)) by lra.
  rewrite H0 in H.
  rewrite cos_2a_sin in H.
  assert (Rsqr (sin (θ / 2)) = Rsqr 1).
  unfold Rsqr. lra.
  apply Rsqr_eq in H1. assumption.
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

Lemma cos2_cos2a : forall (x:R), Rsqr (cos x) = (1 + cos (2 * x)) / 2.
Proof.
  intros.
  rewrite cos_2a_cos.
  unfold Rsqr. lra.
Qed.
 
Lemma sin2_cos2a : forall (x:R), Rsqr (sin x) = (1 - cos (2 * x)) / 2.
Proof.
  intros.
  rewrite cos_2a_sin.
  unfold Rsqr. lra.
Qed.

Hint Rewrite sin2_cos2 sin_plus cos_plus sin_minus cos_minus : trig_db.

Lemma sqr_angle_four_1 : forall (x y z: R),
   (Rsqr (sin x)) * (Rsqr (sin y)) + (Rsqr (sin x)) * (Rsqr (cos y))
   + (Rsqr (cos x)) * (Rsqr (sin z)) + (Rsqr (cos x)) * (Rsqr (cos z)) = 1.
Proof.
  intros.
  rewrite <- Rmult_plus_distr_l.
  rewrite Rplus_assoc.
  rewrite <- Rmult_plus_distr_l.
  autorewrite with R_db trig_db.
  reflexivity.
Qed.

Hint Rewrite Rsqr_sqrt Rsqr_mult Rsqr_div Rsqr_plus Rsqr_minus : sqr_db.
Hint Rewrite <- Rsqr_neg : sqr_db.

Search (0 <= Rsqr _)%R.
Ltac prove_geq_0 :=
  repeat match goal with 
  | |- 0 <= _ + _ => apply Rplus_le_le_0_compat
  | |- 0 <= _ * _ => apply Rmult_le_pos
  | |- 0 <= Rsqr _ => apply Rle_0_sqr
  | _ => try lra
  end.

Lemma Rmult_to_div : forall r1 r2, r2 <> 0 -> r1 = r2 -> r1 * / r2 = 1.
Proof.
  intros r1 r2 H1 H2.
  subst. 
  rewrite Rinv_r; auto.
Qed.

Lemma delta_cos_sin: forall (x y z :R),
   (sqrt (Rsqr (sin (z / 2)) * Rsqr (cos (x - y)) +  Rsqr (cos (z / 2)) * Rsqr (cos (x + y))) <> 0)%R
  -> 
    Rsqr ((cos x * cos y - (cos z * sin x * sin y)) / 
        (sqrt (Rsqr (sin (z / 2)) * Rsqr (cos (x - y)) +  Rsqr (cos (z / 2)) * Rsqr (cos (x + y)))))
   + Rsqr ((- sin z * sin x * sin y)
   / (sqrt (Rsqr (sin (z / 2)) * Rsqr (cos (x - y)) +  Rsqr (cos (z / 2)) * Rsqr (cos (x + y))))) = 1.
Proof.
  intros.
  remember (√ ((sin (z / 2))² * (cos (x - y))² + (cos (z / 2))² * (cos (x + y))²)) as t.
  autorewrite with sqr_db R_db; try assumption.
  rewrite Ropp_mult_distr_l.
  repeat rewrite <- Rmult_plus_distr_r.
  apply Rmult_to_div.
  apply Rsqr_pos_lt in H.
  lra.
  subst. 
  autorewrite with sqr_db R_db trig_db. 
  assert (aux : forall (a b c d : R), (a + b + c) + d = a + (d + b) + c). 
  intros. lra.  
  rewrite aux. clear aux.
  repeat rewrite Rmult_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite sin2_cos2.
  rewrite Rmult_1_l.
  repeat rewrite Rmult_plus_distr_l.
  assert (aux : forall (a b c d e : R), 
    a * b + a * c + a * d + (e * b + e * c + e * - d) = 
      (a + e) * (b + c) + - (e - a) * d). 
  intros. lra.  
  rewrite aux. clear aux.
  rewrite sin2_cos2.
  rewrite Rmult_1_l.
  unfold Rsqr.
  rewrite <- cos_2a.
  replace (2 * (z * / 2)) with z by lra.
  lra.
  prove_geq_0.
Qed.

Require Import Interval.Tactic.
Lemma delta_cos_bound : forall (x y z :R),
   (sqrt (Rsqr (sin (z / 2)) * Rsqr (cos (x - y)) +  Rsqr (cos (z / 2)) * Rsqr (cos (x + y))) <> 0)%R
  -> 
    -1 <= ((cos x * cos y - (cos z * sin x * sin y)) / 
        (sqrt (Rsqr (sin (z / 2)) * Rsqr (cos (x - y)) +  Rsqr (cos (z / 2)) * Rsqr (cos (x + y)))))
       <= 1.
Proof.
intros.
specialize (delta_cos_sin x y z H) as H1.
specialize (Rle_0_sqr ((cos x * cos y - cos z * sin x * sin y) /
      √ ((sin (z / 2))² * (cos (x - y))² + (cos (z / 2))² * (cos (x + y))²))) as H2.
specialize (Rle_0_sqr (- sin z * sin x * sin y /
      √ ((sin (z / 2))² * (cos (x - y))² + (cos (z / 2))² * (cos (x + y))²))) as H3.
assert (0 <= ((cos x * cos y - cos z * sin x * sin y) /
      √ ((sin (z / 2))² * (cos (x - y))² + (cos (z / 2))² * (cos (x + y))²))²) by lra.
assert (((cos x * cos y - cos z * sin x * sin y) /
      √ ((sin (z / 2))² * (cos (x - y))² + (cos (z / 2))² * (cos (x + y))²))² <= 1) by lra.
assert (1 = Rsqr 1).
unfold Rsqr. lra.
rewrite H5 in H4.
split.
apply Rsqr_neg_pos_le_0 in H4.
assumption.
lra.
apply Rsqr_incr_0_var in H4.
assumption.
lra.
Qed.



Lemma cos_2a_cos_half : forall x:R, cos x = sqrt ((cos (2 * x) + 1) / 2)
           \/ cos x = - sqrt ((cos (2 * x) + 1) / 2).
Proof.
intros.
specialize (cos_2a_cos x) as H.
assert (Rsqr (cos x) = (cos (2 * x) + 1) / 2).
unfold Rsqr. lra.
rewrite <- Rsqr_sqrt in H0.
apply Rsqr_eq in H0.
assumption.
specialize (COS_bound (2 * x)) as H1.
destruct H1.
lra.
Qed.

Lemma sin_2a_cos_half : forall x:R, sin x = sqrt ((1 - cos (2 * x)) / 2)
           \/ sin x = - sqrt ((1 - cos (2 * x)) / 2).
Proof.
intros.
specialize (cos_2a_sin x) as H.
assert (Rsqr (sin x) = (1 - cos (2 * x)) / 2).
unfold Rsqr. lra.
rewrite <- Rsqr_sqrt in H0.
apply Rsqr_eq in H0.
assumption.
specialize (COS_bound (2 * x)) as H1.
destruct H1.
lra.
Qed.

Lemma rm02_eq : forall (x y z:R), 
   rm02 x y z = (sin x * cos z + (cos y * cos x * sin z)).
Proof.
intros.
unfold rm02,rx,ry,rw,rz.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite <- cos_plus.
rewrite <- cos_minus.
assert (2 * (sin (y / 2) * sin (x / 2 - z / 2)) * (sin (y / 2) * cos (x / 2 - z / 2))
   = (sin (y / 2) * sin (y / 2)) * (2 * sin (x / 2 - z / 2) * cos (x / 2 - z / 2))) by lra.
rewrite H. clear H. 
assert (2 * (cos (y / 2) * sin (x / 2 + z / 2)) * (cos (y / 2) * cos (x / 2 + z / 2))
   = (cos (y / 2) * cos (y / 2)) * (2 * sin (x / 2 + z / 2) * cos (x / 2 + z / 2))) by lra.
rewrite H. clear H. 
rewrite <- sin_2a.
rewrite <- sin_2a.
assert ((2 * (x / 2 - z / 2)) = x - z) by lra.
rewrite H. clear H. 
assert ((2 * (x / 2 + z / 2)) = x + z) by lra.
rewrite H. clear H. 
rewrite sin_minus.
rewrite sin_plus.
assert ((sin (y / 2) * sin (y / 2) * (sin x * cos z - cos x * sin z) +
     cos (y / 2) * cos (y / 2) * (sin x * cos z + cos x * sin z))
  = (Rsqr (sin (y / 2)) +  Rsqr (cos (y / 2))) * (sin x * cos z)
       + ((cos (y / 2) * cos (y / 2) - sin (y / 2) * sin (y / 2)) * cos x * sin z)).
unfold Rsqr. lra.
rewrite H. clear H. 
rewrite sin2_cos2.
rewrite <- cos_2a.
assert (2 * (y/2) = y) by lra.
rewrite H. clear H. 
lra.
Qed.

Lemma rm02_diff:  forall (θ1 ξ θ2:R), 
   rm02 θ1 ξ θ2 = 2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
                  2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
                  2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
                  2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2).
Proof.
intros.
unfold rm02,rx,ry,rw,rz.
assert (2 * (sin (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))) *
    (sin (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))) +
    2 * (cos (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))) *
    (cos (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
  = 2 * sin (θ1 / 2) * cos (θ1 / 2) * Rsqr (cos (θ2 / 2))
   - 2 * sin (θ1 / 2) * cos (θ1 / 2) * Rsqr (sin (θ2 / 2))
   + 2 * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * Rsqr (sin (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2)).
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = (2 * (ξ/2))) by lra.
rewrite <- H. reflexivity.
rewrite H. rewrite cos_2a.
assert (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² 
 = (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² ) * (Rsqr (sin (ξ / 2)) + Rsqr (cos (ξ / 2)))).
rewrite sin2_cos2. lra.
rewrite H0.
unfold Rsqr. lra.
rewrite H. reflexivity.
Qed.

Lemma rm10_eq: forall (θ1 ξ θ2:R), rm10 θ1 ξ θ2 = sin ξ * cos θ2.
Proof.
intros.
unfold rm10,rx,ry,rz,rw.
rewrite <- sin_plus. rewrite <- sin_minus.
rewrite <- cos_plus. rewrite <- cos_minus.
assert (2 * (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2)) *
(cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2)) +
2 * (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2)) *
(cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))
 = (2 * sin (ξ / 2) * cos (ξ / 2)) * 
     (cos (θ1 / 2 + θ2 / 2) * cos (θ1 / 2 - θ2 / 2) + sin (θ1 / 2 + θ2 / 2) * sin (θ1 / 2 - θ2 / 2))) by lra.
rewrite H. rewrite <- sin_2a. rewrite <- cos_minus.
assert (2 * (ξ / 2) = ξ) by lra. rewrite H0.
assert ((θ1 / 2 + θ2 / 2 - (θ1 / 2 - θ2 / 2)) = θ2) by lra.
rewrite H1. reflexivity.
Qed.

Lemma rm11_eq: forall (θ1 ξ θ2:R), rm11 θ1 ξ θ2 = cos ξ.
Proof.
intros.
unfold rm11,rx,ry,rz,rw.
rewrite <- sin_minus. rewrite <- cos_minus.
assert (1 -
2 * (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2)) *
(sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2)) -
2 * (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2)) *
(sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))
  = 1 - 2 * sin (ξ / 2) * sin (ξ / 2) * (Rsqr (sin (θ1 / 2 - θ2 / 2)) + Rsqr (cos (θ1 / 2 - θ2 / 2)))).
unfold Rsqr. lra.
rewrite H. rewrite sin2_cos2.
rewrite  Rmult_1_r.
rewrite <- cos_2a_sin.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H0. reflexivity.
Qed.


Lemma rm12_eq : forall (x y z:R), 
   rm12 x y z = sin y * sin z.
Proof.
intros.
unfold rm12,rx,ry,rw,rz.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite <- cos_plus.
rewrite <- cos_minus.
assert (2 * (cos (y / 2) * sin (x / 2 + z / 2)) * (sin (y / 2) * cos (x / 2 - z / 2)) -
  2 * (sin (y / 2) * sin (x / 2 - z / 2)) * (cos (y / 2) * cos (x / 2 + z / 2))
  = (2 * sin (y/2) * cos (y/2)) * (sin (x / 2 + z / 2) *
           cos (x / 2 - z / 2) - cos (x / 2 + z / 2) * sin (x / 2 - z / 2))) by lra.
rewrite H. clear H.
rewrite <- sin_2a.
rewrite <- sin_minus.
assert ((x / 2 + z / 2 - (x / 2 - z / 2))  = z) by lra.
rewrite H. clear H.
assert ((2 * (y / 2)) = y) by lra.
rewrite H. clear H.
reflexivity.
Qed.

Lemma rm20_eq : forall (x y z:R), 
   rm20_minus x y z = (cos x * sin z) + cos y * sin x * cos z.
Proof.
intros.
unfold rm20_minus,rx,ry,rw,rz.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite <- cos_plus.
rewrite <- cos_minus.
assert (-2 * (sin (y / 2) * sin (x / 2 - z / 2)) * (sin (y / 2) * cos (x / 2 - z / 2))
   = - ((sin (y / 2) * sin (y / 2)) * (2 * sin (x / 2 - z / 2) * cos (x / 2 - z / 2)))) by lra.
rewrite H. clear H. 
assert (2 * (cos (y / 2) * sin (x / 2 + z / 2)) * (cos (y / 2) * cos (x / 2 + z / 2))
   = (cos (y / 2) * cos (y / 2)) * (2 * sin (x / 2 + z / 2) * cos (x / 2 + z / 2))) by lra.
rewrite H. clear H. 
rewrite <- sin_2a.
rewrite <- sin_2a.
assert ((2 * (x / 2 - z / 2)) = x - z) by lra.
rewrite H. clear H. 
assert ((2 * (x / 2 + z / 2)) = x + z) by lra.
rewrite H. clear H. 
rewrite sin_minus.
rewrite sin_plus.
assert (- (sin (y / 2) * sin (y / 2) * (sin x * cos z - cos x * sin z)) +
cos (y / 2) * cos (y / 2) * (sin x * cos z + cos x * sin z)
  = (Rsqr (sin (y / 2)) +  Rsqr (cos (y / 2))) * (cos x * sin z)
       + ((cos (y / 2) * cos (y / 2) - sin (y / 2) * sin (y / 2)) * sin x * cos z)).
unfold Rsqr. lra.
rewrite H. clear H. 
rewrite sin2_cos2.
rewrite <- cos_2a.
assert (2 * (y/2) = y) by lra.
rewrite H. clear H. 
lra.
Qed.


Lemma rm20_diff:  forall (θ1 ξ θ2:R), 
   rm20_minus θ1 ξ θ2 = 2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)
                      - 2 * (sin (θ1 / 2))² *  sin (θ2 / 2) * cos (θ2 / 2)
                      + 2 * cos ξ *  sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²
                      - 2 * cos ξ *  sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))².
Proof.
intros.
unfold rm20_minus,rx,ry,rw,rz.
assert (-2 * (sin (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))) *
(sin (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))) +
2 * (cos (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))) *
(cos (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
   = - 2 * ((sin (ξ / 2))² + (cos (ξ / 2))²) * (sin (θ1 / 2))² *  sin (θ2 / 2) * cos (θ2 / 2)
     + 2 * ((sin (ξ / 2))² + (cos (ξ / 2))²) *  (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)
     + 2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) *  sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²
     - 2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) *  sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite sin2_cos2.
unfold Rsqr.
rewrite <- cos_2a.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H. lra.
Qed.

Lemma rm21_eq : forall (x y z:R), 
   rm21 x y z = sin y * sin x.
Proof.
intros.
unfold rm21,rx,ry,rw,rz.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite <- cos_plus.
rewrite <- cos_minus.
assert (2 * (cos (y / 2) * sin (x / 2 + z / 2)) * (sin (y / 2) * cos (x / 2 - z / 2)) +
  2 * (sin (y / 2) * sin (x / 2 - z / 2)) * (cos (y / 2) * cos (x / 2 + z / 2))
  = (2 * sin (y/2) * cos (y/2)) * (sin (x / 2 + z / 2) *
           cos (x / 2 - z / 2) + cos (x / 2 + z / 2) * sin (x / 2 - z / 2))) by lra.
rewrite H. clear H.
rewrite <- sin_2a.
rewrite <- sin_plus.
assert ((x / 2 + z / 2 + (x / 2 - z / 2))  = x) by lra.
rewrite H. clear H.
assert ((2 * (y / 2)) = y) by lra.
rewrite H. clear H.
reflexivity.
Qed.


Lemma rm12_sin: forall (x y z:R), 0 < (rm02 x y z) ->
    sin (atan ((rm12 x y z) / (rm02 x y z))) =
      (sin y * sin z)
           / sqrt (Rsqr (sin x * cos z + (cos y * cos x * sin z)) + Rsqr(sin y) * Rsqr (sin z)).
Proof.
intros.
rewrite sin_atan.
specialize (rm02_eq x y z) as H0.
specialize (rm12_eq x y z) as H1.
rewrite H0. rewrite H1.
rewrite Rsqr_div.
assert (1 + (sin y * sin z)² / (sin x * cos z + cos y * cos x * sin z)²
    = ((sin x * cos z + cos y * cos x * sin z)² + (Rsqr (sin y) * Rsqr (sin z)))
      / (sin x * cos z + cos y * cos x * sin z)²).
unfold Rsqr.
assert (((sin x * cos z + cos y * cos x * sin z) * (sin x * cos z + cos y * cos x * sin z))
    * / ((sin x * cos z + cos y * cos x * sin z) * (sin x * cos z + cos y * cos x * sin z)) = 1).
rewrite  Rinv_r.
reflexivity.
rewrite H0 in H. 
assert (0 < Rsqr (sin x * cos z + cos y * cos x * sin z)).
apply Rsqr_pos_lt. lra.
unfold Rsqr in H2.
lra.
rewrite <- H2. lra.
rewrite H2.
rewrite sqrt_div_alt.
rewrite sqrt_Rsqr.
autorewrite with R_db.
rewrite  Rinv_mult_distr.
rewrite Rinv_involutive.
assert (sin y * sin z * / (sin x * cos z + cos y * cos x * sin z) *
(/ √ ((sin x * cos z + cos y * cos x * sin z)² + (sin y)² * (sin z)²) *
 (sin x * cos z + cos y * cos x * sin z))
 = (sin y * sin z * / √ ((sin x * cos z + cos y * cos x * sin z)² + (sin y)² * (sin z)²))
     * ((sin x * cos z + cos y * cos x * sin z) * / (sin x * cos z + cos y * cos x * sin z))) by lra.
rewrite H3. clear H3.
rewrite Rinv_r. lra.
rewrite H0 in H. lra.
rewrite H0 in H. lra.
assert (0 < ((sin x * cos z + cos y * cos x * sin z)² + (sin y)² * (sin z)²)).
rewrite <- Rsqr_mult.
assert ( 0 < (sin x * cos z + cos y * cos x * sin z)²).
rewrite H0 in H.
apply Rsqr_pos_lt. lra.
assert (0 <= (sin y * sin z)²).
apply Rle_0_sqr.
lra.
apply sqrt_lt_R0  in H3.
lra.
rewrite H0 in H.
assert (0 < / (sin x * cos z + cos y * cos x * sin z)).
apply Rinv_0_lt_compat. lra.
lra. lra.
rewrite H0 in H.
apply Rsqr_pos_lt. lra.
lra.
Qed.


Lemma rm12_sin_neg: forall (x y z:R), (rm02 x y z) < 0 ->
    sin (atan ((rm12 x y z) / (rm02 x y z))) =
      (-(sin y * sin z))
           / sqrt (Rsqr (- (sin x * cos z + (cos y * cos x * sin z))) + Rsqr(sin y) * Rsqr (sin z)).
Proof.
intros.
rewrite sin_atan.
specialize (rm02_eq x y z) as H0.
specialize (rm12_eq x y z) as H1.
rewrite H0. rewrite H1.
rewrite Rsqr_div.
assert (1 + (sin y * sin z)² / ((sin x * cos z + cos y * cos x * sin z))²
    = ((-(sin x * cos z + cos y * cos x * sin z))² + (Rsqr (sin y) * Rsqr (sin z)))
      / (-(sin x * cos z + cos y * cos x * sin z))²).
rewrite <- Rsqr_neg.
unfold Rsqr.
assert ((((sin x * cos z + cos y * cos x * sin z)) * ((sin x * cos z + cos y * cos x * sin z)))
    * / (((sin x * cos z + cos y * cos x * sin z)) * ((sin x * cos z + cos y * cos x * sin z))) = 1).
rewrite  Rinv_r.
reflexivity.
rewrite H0 in H. 
assert (0 < Rsqr ((sin x * cos z + cos y * cos x * sin z))).
apply Rsqr_pos_lt. lra.
unfold Rsqr in H2.
lra.
rewrite <- H2. lra.
rewrite H2.
rewrite sqrt_div_alt.
rewrite sqrt_Rsqr.
autorewrite with R_db.
rewrite  Rinv_mult_distr.
rewrite Rinv_involutive.
assert (sin y * sin z * / (sin x * cos z + cos y * cos x * sin z) *
(/ √ ((- (sin x * cos z + cos y * cos x * sin z))² + (sin y)² * (sin z)²) *
 - (sin x * cos z + cos y * cos x * sin z))
 = ((-(sin y * sin z)) * / √ ((-(sin x * cos z + cos y * cos x * sin z))² + (sin y)² * (sin z)²))
     * (-(sin x * cos z + cos y * cos x * sin z) * / -(sin x * cos z + cos y * cos x * sin z))).
rewrite <- Ropp_inv_permute.
lra.
lra.
rewrite H3. clear H3.
rewrite Rinv_r. lra.
rewrite H0 in H. lra.
rewrite H0 in H. lra.
assert (0 < ((-(sin x * cos z + cos y * cos x * sin z))² + (sin y)² * (sin z)²)).
rewrite <- Rsqr_mult.
assert ( 0 < (-(sin x * cos z + cos y * cos x * sin z))²).
rewrite H0 in H.
apply Rsqr_pos_lt. lra.
assert (0 <= (sin y * sin z)²).
apply Rle_0_sqr.
lra.
apply sqrt_lt_R0  in H3.
lra.
rewrite H0 in H.
assert (0 < / -(sin x * cos z + cos y * cos x * sin z)).
apply Rinv_0_lt_compat. lra.
lra. lra.
rewrite H0 in H.
apply Rsqr_pos_lt. lra.
lra.
Qed.

Lemma rm12_cos: forall (x y z:R), 0 < (rm02 x y z) ->
    cos (atan ((rm12 x y z) / (rm02 x y z))) =
      (sin x * cos z + (cos y * cos x * sin z))
           / sqrt (Rsqr (sin x * cos z + (cos y * cos x * sin z)) + Rsqr(sin y) * Rsqr (sin z)).
Proof.
intros.
rewrite cos_atan.
specialize (rm02_eq x y z) as H0.
specialize (rm12_eq x y z) as H1.
rewrite H0. rewrite H1.
rewrite Rsqr_div.
assert (1 + (sin y * sin z)² / (sin x * cos z + cos y * cos x * sin z)²
    = ((sin x * cos z + cos y * cos x * sin z)² + (Rsqr (sin y) * Rsqr (sin z)))
      / (sin x * cos z + cos y * cos x * sin z)²).
unfold Rsqr.
assert (((sin x * cos z + cos y * cos x * sin z) * (sin x * cos z + cos y * cos x * sin z))
    * / ((sin x * cos z + cos y * cos x * sin z) * (sin x * cos z + cos y * cos x * sin z)) = 1).
rewrite  Rinv_r.
reflexivity.
rewrite H0 in H. 
assert (0 < Rsqr (sin x * cos z + cos y * cos x * sin z)).
apply Rsqr_pos_lt. lra.
unfold Rsqr in H2.
lra.
rewrite <- H2. lra.
rewrite H2.
autorewrite with R_db.
rewrite sqrt_mult_alt.
rewrite <- inv_sqrt.
rewrite  Rinv_mult_distr.
rewrite Rinv_involutive.
rewrite sqrt_Rsqr.
lra.
lra.
assert (0 < (sin x * cos z + cos y * cos x * sin z)²).
apply Rsqr_pos_lt. lra.
assert (0 < √ (sin x * cos z + cos y * cos x * sin z)²).
apply sqrt_lt_R0. assumption.
lra.
assert (0 < ((sin x * cos z + cos y * cos x * sin z)² + (sin y)² * (sin z)²)).
assert (0 < (sin x * cos z + cos y * cos x * sin z)²).
apply Rsqr_pos_lt. lra.
rewrite <- Rsqr_mult.
assert (0 <= (sin y * sin z)²).
apply Rle_0_sqr.
lra.
assert (0 < √ ((sin x * cos z + cos y * cos x * sin z)² + (sin y)² * (sin z)²)).
apply sqrt_lt_R0. assumption.
lra.
assert (0 < / √ (sin x * cos z + cos y * cos x * sin z)² ).
apply Rinv_0_lt_compat. 
apply sqrt_lt_R0.
apply Rsqr_pos_lt. lra.
lra.
apply Rsqr_pos_lt. lra.
rewrite <- Rsqr_mult.
assert (0 < (sin x * cos z + cos y * cos x * sin z)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (sin y * sin z)²).
apply Rle_0_sqr.
lra.
lra.
Qed.

Lemma rm12_cos_neg: forall (x y z:R), (rm02 x y z) < 0 ->
    cos (atan ((rm12 x y z) / (rm02 x y z))) =
      (-(sin x * cos z + (cos y * cos x * sin z)))
           / sqrt (Rsqr (-(sin x * cos z + (cos y * cos x * sin z))) + Rsqr(sin y) * Rsqr (sin z)).
Proof.
intros.
rewrite cos_atan.
rewrite rm02_eq.
specialize (rm12_eq x y z) as H0.
rewrite H0.
rewrite Rsqr_div.
assert (1 + (sin y * sin z)² / (sin x * cos z + cos y * cos x * sin z)²
    = ((-(sin x * cos z + cos y * cos x * sin z))² + (Rsqr (sin y) * Rsqr (sin z)))
      / (-(sin x * cos z + cos y * cos x * sin z))²).
rewrite <- Rsqr_neg.
unfold Rsqr.
assert (((sin x * cos z + cos y * cos x * sin z) * (sin x * cos z + cos y * cos x * sin z))
    * / ((sin x * cos z + cos y * cos x * sin z) * (sin x * cos z + cos y * cos x * sin z)) = 1).
rewrite  Rinv_r.
reflexivity.
rewrite rm02_eq in H.
assert (0 < Rsqr (sin x * cos z + cos y * cos x * sin z)).
apply Rsqr_pos_lt. lra.
unfold Rsqr in H1.
lra.
rewrite <- H1. lra.
rewrite H1.
autorewrite with R_db.
rewrite sqrt_mult_alt.
rewrite <- inv_sqrt.
rewrite  Rinv_mult_distr.
rewrite Rinv_involutive.
rewrite sqrt_Rsqr.
lra.
rewrite rm02_eq in H.
lra.
assert (0 < (-(sin x * cos z + cos y * cos x * sin z))²).
apply Rsqr_pos_lt. rewrite rm02_eq in H. lra.
assert (0 < √ (-(sin x * cos z + cos y * cos x * sin z))²).
apply sqrt_lt_R0. assumption.
lra.
assert (0 < ((- (sin x * cos z + cos y * cos x * sin z))² + (sin y)² * (sin z)²)).
assert (0 < (-(sin x * cos z + cos y * cos x * sin z))²).
apply Rsqr_pos_lt. rewrite rm02_eq in H. lra.
rewrite <- Rsqr_mult.
assert (0 <= (sin y * sin z)²).
apply Rle_0_sqr.
lra.
assert (0 < √ ((- (sin x * cos z + cos y * cos x * sin z))² + (sin y)² * (sin z)²)).
apply sqrt_lt_R0. assumption.
lra.
assert (0 < / √ (- (sin x * cos z + cos y * cos x * sin z))² ).
apply Rinv_0_lt_compat. 
apply sqrt_lt_R0.
apply Rsqr_pos_lt. rewrite rm02_eq in H. lra.
lra.
apply Rsqr_pos_lt. rewrite rm02_eq in H. lra.
rewrite <- Rsqr_mult.
assert (0 < (- (sin x * cos z + cos y * cos x * sin z))²).
apply Rsqr_pos_lt. rewrite rm02_eq in H. lra.
assert (0 <= (sin y * sin z)²).
apply Rle_0_sqr.
lra.
rewrite rm02_eq in H. lra.
Qed.

Lemma rm21_sin: forall (x y z:R), 0 < (rm20_minus x y z) ->
    sin (atan ((rm21 x y z) / (rm20_minus x y z))) =
      (sin y * sin x)
           / √ ((cos x * sin z + cos y * sin x * cos z)² + (sin y)² * (sin x)²).
Proof.
intros.
rewrite sin_atan.
specialize (rm20_eq x y z) as eq1.
specialize (rm21_eq x y z) as eq2.
rewrite eq1. rewrite eq2.
rewrite Rsqr_div.
assert ((1 + (sin y * sin x)² / (cos x * sin z + cos y * sin x * cos z)²)
    = ((cos x * sin z + cos y * sin x * cos z)² + (Rsqr (sin y) * Rsqr (sin x)))
      / (cos x * sin z + cos y * sin x * cos z)²).
unfold Rsqr.
assert (((cos x * sin z + cos y * sin x * cos z) * (cos x * sin z + cos y * sin x * cos z))
    * / ((cos x * sin z + cos y * sin x * cos z) * (cos x * sin z + cos y * sin x * cos z)) = 1).
rewrite  Rinv_r.
reflexivity.
rewrite eq1 in H. 
assert (0 < Rsqr (cos x * sin z + cos y * sin x * cos z)).
apply Rsqr_pos_lt. lra.
unfold Rsqr in H0.
lra.
rewrite <- H0. lra.
rewrite H0.
rewrite sqrt_div_alt.
rewrite sqrt_Rsqr.
autorewrite with R_db.
rewrite  Rinv_mult_distr.
rewrite Rinv_involutive.
assert (sin y * sin x * / (cos x * sin z + cos y * sin x * cos z) *
(/ √ ((cos x * sin z + cos y * sin x * cos z)² + (sin y)² * (sin x)²) *
 (cos x * sin z + cos y * sin x * cos z))
 = (sin y * sin x * / √ ((cos x * sin z + cos y * sin x * cos z)² + (sin y)² * (sin x)²))
     * ((cos x * sin z + cos y * sin x * cos z) * / (cos x * sin z + cos y * sin x * cos z))) by lra.
rewrite H1. clear H1.
rewrite Rinv_r. lra.
rewrite eq1 in H. lra.
rewrite eq1 in H. lra.
assert (0 < ((cos x * sin z + cos y * sin x * cos z)² + (sin y)² * (sin x)²)).
rewrite <- Rsqr_mult.
assert ( 0 < (cos x * sin z + cos y * sin x * cos z)²).
rewrite eq1 in H.
apply Rsqr_pos_lt. lra.
assert (0 <= (sin y * sin x)²).
apply Rle_0_sqr.
lra.
apply sqrt_lt_R0  in H1.
lra.
rewrite eq1 in H.
assert (0 < / (cos x * sin z + cos y * sin x * cos z)).
apply Rinv_0_lt_compat. lra.
lra. lra.
rewrite eq1 in H.
apply Rsqr_pos_lt. lra.
lra.
Qed.

Lemma rm21_sin_neg: forall (x y z:R), (rm20_minus x y z) < 0 ->
    sin (atan ((rm21 x y z) / (rm20_minus x y z))) =
      (-(sin y * sin x))
           / √ ((-(cos x * sin z + cos y * sin x * cos z))² + (sin y)² * (sin x)²).
Proof.
intros.
rewrite sin_atan.
specialize (rm20_eq x y z) as eq1.
specialize (rm21_eq x y z) as eq2.
rewrite eq1. rewrite eq2.
rewrite Rsqr_div.
assert ((1 + (sin y * sin x)² / (cos x * sin z + cos y * sin x * cos z)²)
    = ((-(cos x * sin z + cos y * sin x * cos z))² + (Rsqr (sin y) * Rsqr (sin x)))
      / (-(cos x * sin z + cos y * sin x * cos z))²).
rewrite <- Rsqr_neg.
unfold Rsqr.
assert ((((cos x * sin z + cos y * sin x * cos z)) * ((cos x * sin z + cos y * sin x * cos z)))
    * / (((cos x * sin z + cos y * sin x * cos z)) * ((cos x * sin z + cos y * sin x * cos z))) = 1).
rewrite  Rinv_r.
reflexivity.
rewrite eq1 in H. 
assert (0 < Rsqr ((cos x * sin z + cos y * sin x * cos z))).
apply Rsqr_pos_lt. lra.
unfold Rsqr in H0.
lra.
rewrite <- H0. lra.
rewrite H0.
rewrite sqrt_div_alt.
rewrite sqrt_Rsqr.
autorewrite with R_db.
rewrite  Rinv_mult_distr.
rewrite Rinv_involutive.
assert (sin y * sin x * / (cos x * sin z + cos y * sin x * cos z) *
(/ √ ((- (cos x * sin z + cos y * sin x * cos z))² + (sin y)² * (sin x)²) *
 - (cos x * sin z + cos y * sin x * cos z))
 = ((-(sin y * sin x)) * / √ ((-(cos x * sin z + cos y * sin x * cos z))² + (sin y)² * (sin x)²))
     * (-(cos x * sin z + cos y * sin x * cos z) * / -(cos x * sin z + cos y * sin x * cos z))).
rewrite <- Ropp_inv_permute.
lra.
lra.
rewrite H1. clear H1.
rewrite Rinv_r. lra.
rewrite eq1 in H. lra.
rewrite eq1 in H. lra.
assert (0 < ((- (cos x * sin z + cos y * sin x * cos z))² + (sin y)² * (sin x)²)).
rewrite <- Rsqr_mult.
assert ( 0 < (- (cos x * sin z + cos y * sin x * cos z))²).
rewrite eq1 in H.
apply Rsqr_pos_lt. lra.
assert (0 <= (sin y * sin x)²).
apply Rle_0_sqr.
lra.
apply sqrt_lt_R0 in H1.
lra.
rewrite eq1 in H.
assert (0 < / (- (cos x * sin z + cos y * sin x * cos z))).
apply Rinv_0_lt_compat. lra.
lra. lra.
rewrite eq1 in H.
apply Rsqr_pos_lt. lra.
lra.
Qed.

Lemma rm21_cos: forall (x y z:R), 0 < (rm20_minus x y z) ->
    cos (atan ((rm21 x y z) / (rm20_minus x y z))) =
      (cos x * sin z + cos y * sin x * cos z)
           / √ ((cos x * sin z + cos y * sin x * cos z)² + (sin y)² * (sin x)²).
Proof.
intros.
rewrite cos_atan.
specialize (rm20_eq x y z) as H0.
specialize (rm21_eq x y z) as H1.
rewrite H0. rewrite H1.
rewrite Rsqr_div.
assert ((1 + (sin y * sin x)² / (cos x * sin z + cos y * sin x * cos z)²)
    = ((cos x * sin z + cos y * sin x * cos z)² + (sin y)² * (sin x)²)
      / (cos x * sin z + cos y * sin x * cos z)²).
unfold Rsqr.
assert (((cos x * sin z + cos y * sin x * cos z) * (cos x * sin z + cos y * sin x * cos z))
    * / ((cos x * sin z + cos y * sin x * cos z) * (cos x * sin z + cos y * sin x * cos z)) = 1).
rewrite  Rinv_r.
reflexivity.
rewrite H0 in H. 
assert (0 < Rsqr (cos x * sin z + cos y * sin x * cos z)).
apply Rsqr_pos_lt. lra.
unfold Rsqr in H2.
lra.
rewrite <- H2. lra.
rewrite H2.
autorewrite with R_db.
rewrite sqrt_mult_alt.
rewrite <- inv_sqrt.
rewrite  Rinv_mult_distr.
rewrite Rinv_involutive.
rewrite sqrt_Rsqr.
lra.
lra.
assert (0 < (cos x * sin z + cos y * sin x * cos z)²).
apply Rsqr_pos_lt. lra.
assert (0 < √ (cos x * sin z + cos y * sin x * cos z)²).
apply sqrt_lt_R0. assumption.
lra.
assert (0 < ((cos x * sin z + cos y * sin x * cos z)² + (sin y)² * (sin x)²)).
assert (0 < (cos x * sin z + cos y * sin x * cos z)²).
apply Rsqr_pos_lt. lra.
rewrite <- Rsqr_mult.
assert (0 <= (sin y * sin x)²).
apply Rle_0_sqr.
lra.
assert (0 < √ ((cos x * sin z + cos y * sin x * cos z)² + (sin y)² * (sin x)²)).
apply sqrt_lt_R0. assumption.
lra.
assert (0 < / √ (cos x * sin z + cos y * sin x * cos z)² ).
apply Rinv_0_lt_compat. 
apply sqrt_lt_R0.
apply Rsqr_pos_lt. lra.
lra.
apply Rsqr_pos_lt. lra.
rewrite <- Rsqr_mult.
assert (0 < (cos x * sin z + cos y * sin x * cos z)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (sin y * sin x)²).
apply Rle_0_sqr.
lra.
lra.
Qed.

Lemma rm21_cos_neg: forall (x y z:R), (rm20_minus x y z) < 0 ->
     cos (atan ((rm21 x y z) / (rm20_minus x y z))) =
      (-(cos x * sin z + cos y * sin x * cos z))
           / √ ((-(cos x * sin z + cos y * sin x * cos z))² + (sin y)² * (sin x)²).
Proof.
intros.
rewrite cos_atan.
rewrite rm20_eq.
specialize (rm21_eq x y z) as H0.
rewrite H0.
rewrite Rsqr_div.
assert ((1 + (sin y * sin x)² / (cos x * sin z + cos y * sin x * cos z)²)
    = ((- (cos x * sin z + cos y * sin x * cos z))² + (sin y)² * (sin x)²)
      / (-(cos x * sin z + cos y * sin x * cos z))²).
rewrite <- Rsqr_neg.
unfold Rsqr.
assert (((cos x * sin z + cos y * sin x * cos z) * (cos x * sin z + cos y * sin x * cos z))
    * / ((cos x * sin z + cos y * sin x * cos z) * (cos x * sin z + cos y * sin x * cos z)) = 1).
rewrite  Rinv_r.
reflexivity.
rewrite rm20_eq in H.
assert (0 < Rsqr (cos x * sin z + cos y * sin x * cos z)).
apply Rsqr_pos_lt. lra.
unfold Rsqr in H1.
lra.
rewrite <- H1. lra.
rewrite H1.
autorewrite with R_db.
rewrite sqrt_mult_alt.
rewrite <- inv_sqrt.
rewrite  Rinv_mult_distr.
rewrite Rinv_involutive.
rewrite sqrt_Rsqr.
lra.
rewrite rm20_eq in H.
lra.
assert (0 < (-(cos x * sin z + cos y * sin x * cos z))²).
apply Rsqr_pos_lt. rewrite rm20_eq in H. lra.
assert (0 < √ (-(cos x * sin z + cos y * sin x * cos z))²).
apply sqrt_lt_R0. assumption.
lra.
assert (0 < ((- (cos x * sin z + cos y * sin x * cos z))² + (sin y)² * (sin x)²)).
assert (0 < (-(cos x * sin z + cos y * sin x * cos z))²).
apply Rsqr_pos_lt. rewrite rm20_eq in H. lra.
rewrite <- Rsqr_mult.
assert (0 <= (sin y * sin x)²).
apply Rle_0_sqr.
lra.
assert (0 < √ ((-(cos x * sin z + cos y * sin x * cos z))² + (sin y)² * (sin x)²)).
apply sqrt_lt_R0. assumption.
lra.
assert (0 < / √ (- (cos x * sin z + cos y * sin x * cos z))² ).
apply Rinv_0_lt_compat. 
apply sqrt_lt_R0.
apply Rsqr_pos_lt. rewrite rm20_eq in H. lra.
lra.
apply Rsqr_pos_lt. rewrite rm20_eq in H. lra.
rewrite <- Rsqr_mult.
assert (0 < (-(cos x * sin z + cos y * sin x * cos z))²).
apply Rsqr_pos_lt. rewrite rm20_eq in H. lra.
assert (0 <= (sin y * sin x)²).
apply Rle_0_sqr.
lra.
rewrite rm20_eq in H. lra.
Qed.

Lemma sin_cos_q: forall (θ1 ξ θ2:R), 
 (Rsqr (sin θ1 * cos θ2 + (cos ξ * cos θ1 * sin θ2)) + Rsqr(sin ξ) * Rsqr (sin θ2))
  = 4 *
    ((Rsqr (sin (ξ / 2)) * Rsqr (cos (θ1 / 2  - θ2 / 2))
         +  Rsqr (cos (ξ / 2)) * Rsqr (cos (θ1 / 2 + θ2 / 2)))
    * ((Rsqr (sin (ξ / 2)) * Rsqr (sin (θ1 / 2  - θ2 / 2))
         +  Rsqr (cos (ξ / 2)) * Rsqr (sin (θ1 / 2 + θ2 / 2))))).
Proof.
intros.
rewrite cos_plus.
rewrite cos_minus.
rewrite sin_plus.
rewrite sin_minus.
rewrite (Rsqr_plus (cos (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rsqr_minus (cos (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rsqr_plus (sin (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rsqr_minus (sin (θ1 / 2) * cos (θ2 / 2))).
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rsqr_mult. rewrite Rsqr_mult.
remember ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) as p.
remember ((sin (θ1 / 2))² * (cos (θ2 / 2))² + (cos (θ1 / 2))² * (sin (θ2 / 2))²) as q.
assert (2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))
    = (2 * sin (θ1 / 2) * cos (θ1 / 2)) * (sin (θ2 / 2) * cos (θ2 / 2))) by lra.
rewrite H. clear H.
assert (2 * (sin (θ1 / 2) * cos (θ2 / 2)) * (cos (θ1 / 2) * sin (θ2 / 2))
    = (2 * sin (θ1 / 2) * cos (θ1 / 2)) * (sin (θ2 / 2) * cos (θ2 / 2))) by lra.
rewrite H. clear H.
assert (4 *
(((sin (ξ / 2))² * (p + 2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2) * cos (θ2 / 2))) +
 (cos (ξ / 2))² * (p - 2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2) * cos (θ2 / 2)))) *
((sin (ξ / 2))² * (q - 2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2) * cos (θ2 / 2))) +
 (cos (ξ / 2))² * (q + 2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2) * cos (θ2 / 2)))))
 = (2 * ((sin (ξ / 2))² * (p + 2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2) * cos (θ2 / 2))) +
 (cos (ξ / 2))² * (p - 2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2) * cos (θ2 / 2)))))
* (2 * ((sin (ξ / 2))² * (q - 2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2) * cos (θ2 / 2))) +
 (cos (ξ / 2))² * (q + 2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2) * cos (θ2 / 2)))))) by lra.
rewrite H. clear H.
assert (2 *
((sin (ξ / 2))² * (p + 2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2) * cos (θ2 / 2))) +
 (cos (ξ / 2))² * (p - 2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2) * cos (θ2 / 2))))
= (2 * ((sin (ξ / 2))² + (cos (ξ / 2))²) * p
     - (((cos (ξ / 2))² - (sin (ξ / 2))²) * (2 * sin (θ1 / 2) * cos (θ1 / 2))
                    * (2 * sin (θ2 / 2) * cos (θ2 / 2))))) by lra.
rewrite H. clear H.
assert ((2 *
 ((sin (ξ / 2))² * (q - 2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2) * cos (θ2 / 2))) +
  (cos (ξ / 2))² * (q + 2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2) * cos (θ2 / 2)))))
= (2 * ((sin (ξ / 2))² + (cos (ξ / 2))²) * q
     + (((cos (ξ / 2))² - (sin (ξ / 2))²) * (2 * sin (θ1 / 2) * cos (θ1 / 2))
                    * (2 * sin (θ2 / 2) * cos (θ2 / 2))))) by lra.
rewrite H. clear H.
rewrite <- sin_2a.
rewrite <- sin_2a.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H. reflexivity.
rewrite H.
rewrite sin2_cos2.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H0. clear H0.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H0. clear H0.
assert ((2 * 1 * p - cos ξ * sin θ1 * sin θ2) * (2 * 1 * q + cos ξ * sin θ1 * sin θ2)
 = 4 * p * q + 2 * p * cos ξ * sin θ1 * sin θ2 - 2 * q
   * cos ξ * sin θ1 * sin θ2 - (cos ξ)² * (sin θ1)² * (sin θ2)²).
unfold Rsqr. lra.
rewrite H0. clear H0.
rewrite Heqp. rewrite Heqq.
assert (4 * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) *
((sin (θ1 / 2))² * (cos (θ2 / 2))² + (cos (θ1 / 2))² * (sin (θ2 / 2))²)
= (2 * sin (θ1 / 2) * cos (θ1 / 2))² * (cos (θ2 / 2) * cos (θ2 / 2))² 
+ (2 * sin (θ1 / 2) * cos (θ1 / 2))² * (sin (θ2 / 2) * sin (θ2 / 2))² 
+ (2 * sin (θ2 / 2) * cos (θ2 / 2))² * (sin (θ1 / 2) * sin (θ1 / 2))²
+ (2 * sin (θ2 / 2) * cos (θ2 / 2))² * (cos (θ1 / 2) * cos (θ1 / 2))²).
unfold Rsqr. lra.
rewrite H0. clear H0.
rewrite <- sin_2a.
rewrite <- sin_2a.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H0. clear H0.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H0. clear H0.
assert ((sin θ1)² * (cos (θ2 / 2) * cos (θ2 / 2))² + (sin θ1)² * (sin (θ2 / 2) * sin (θ2 / 2))² +
(sin θ2)² * (sin (θ1 / 2) * sin (θ1 / 2))² + (sin θ2)² * (cos (θ1 / 2) * cos (θ1 / 2))² +
2 * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) * cos ξ * sin θ1 * sin θ2 -
2 * ((sin (θ1 / 2))² * (cos (θ2 / 2))² + (cos (θ1 / 2))² * (sin (θ2 / 2))²) * cos ξ * sin θ1 * sin θ2 -
(cos ξ)² * (sin θ1)² * (sin θ2)²
= (sin θ1)² * (((sin (θ2 / 2))²)² + ((cos (θ2 / 2))²)²) + 
  (sin θ2)² * (((sin (θ1 / 2))²)² + ((cos (θ1 / 2))²)²) + 
2 * cos ξ * sin θ1 * sin θ2 * 
   ((cos (θ2 / 2))² * ((cos (θ1 / 2))² - (sin (θ1 / 2))²)
    - (sin (θ2 / 2))² * ((cos (θ1 / 2))² - (sin (θ1 / 2))²))
 - (cos ξ)² * (sin θ1)² * (sin θ2)²).
unfold Rsqr. lra.
rewrite H0. clear H0.
assert (((cos (θ1 / 2))² - (sin (θ1 / 2))²) = cos θ1).
unfold Rsqr. rewrite <- cos_2a.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H0. reflexivity.
rewrite H0.
assert (((cos (θ2 / 2))² * cos θ1 - (sin (θ2 / 2))² * cos θ1)
   =  cos θ1 * ((cos (θ2 / 2))² - (sin (θ2 / 2))²)) by lra.
rewrite H1. clear H1.
assert (((cos (θ2 / 2))² - (sin (θ2 / 2))²) = cos θ2).
unfold Rsqr. rewrite <- cos_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H1. reflexivity.
rewrite H1.
rewrite (cos2_cos2a ((θ2 / 2))). rewrite (cos2_cos2a ((θ1 / 2))).
rewrite (sin2_cos2a ((θ2 / 2))). rewrite (sin2_cos2a ((θ1 / 2))).
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H2. clear H2.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H2. clear H2.
rewrite 4 Rsqr_div.
rewrite (Rsqr_plus 1). rewrite (Rsqr_plus 1).
rewrite (Rsqr_minus 1). rewrite (Rsqr_minus 1).
assert (((1² + (cos θ2)² - 2 * 1 * cos θ2) / 2² + (1² + (cos θ2)² + 2 * 1 * cos θ2) / 2²)
    = (1 + 1 * (cos θ2)²) / 2).
unfold Rsqr. lra.
rewrite H2. clear H2.
assert (((1² + (cos θ1)² - 2 * 1 * cos θ1) / 2² + (1² + (cos θ1)² + 2 * 1 * cos θ1) / 2²) 
  = (1 + 1 * (cos θ1)²) / 2).
unfold Rsqr. lra.
rewrite H2. clear H2.
assert (- (cos ξ)² * (sin θ1)² * (sin θ2)² 
   = (cos ξ)² * (cos θ1)² * (sin θ2)² - (cos ξ)² * (sin θ2)²).
assert ((sin θ1)² = 1 - (cos θ1)²).
rewrite <- (sin2_cos2 (θ1)). lra. rewrite H2. lra.
assert ((sin θ1)² * ((1 + 1 * (cos θ2)²) / 2) + (sin θ2)² * ((1 + 1 * (cos θ1)²) / 2) +
2 * cos ξ * sin θ1 * sin θ2 * (cos θ1 * cos θ2) - (cos ξ)² * (sin θ1)² * (sin θ2)² =
((sin θ1)² * ((1 + 1 * (cos θ2)²) / 2) + (sin θ2)² * ((1 + 1 * (cos θ1)²) / 2) +
2 * cos ξ * sin θ1 * sin θ2 * (cos θ1 * cos θ2)) + (- (cos ξ)² * (sin θ1)² * (sin θ2)²)) by lra.
rewrite H3. clear H3. rewrite H2. clear H2.
assert ((sin θ1)² * ((1 + 1 * (cos θ2)²) / 2) + (sin θ2)² * ((1 + 1 * (cos θ1)²) / 2)
= (sin θ2)² + (sin θ1)² * (cos θ2)²).
assert ((sin θ2)² = 1 - (cos θ2)²).
rewrite <- (sin2_cos2 (θ2)). lra.
rewrite H2. clear H2.
assert ((cos θ1)² = 1 - (sin θ1)²).
rewrite <- (sin2_cos2 (θ1)). lra.
rewrite H2. clear H2.
lra.
rewrite H2.
assert ((sin θ2)² + (sin θ1)² * (cos θ2)² + 2 * cos ξ * sin θ1 * sin θ2 * (cos θ1 * cos θ2) +
((cos ξ)² * (cos θ1)² * (sin θ2)² - (cos ξ)² * (sin θ2)²)
 = ((sin θ1)² * (cos θ2)² + 2 * cos ξ * sin θ1 * sin θ2 * (cos θ1 * cos θ2) +
      (cos ξ)² * (cos θ1)² * (sin θ2)²) + ((sin θ2)² * (1 - (cos ξ)²))) by lra.
rewrite H3. clear H3.
assert ((1 - (cos ξ)²) = (sin ξ)²).
rewrite <- (sin2_cos2 (ξ)). lra.
rewrite H3. clear H3.
rewrite Rsqr_plus.
rewrite 3 Rsqr_mult. lra.
lra. lra. lra. lra.
Qed.

Lemma sin_cos_q_rm20: forall (θ1 ξ θ2:R), 
 (Rsqr (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) + Rsqr(sin ξ) * Rsqr (sin θ1))
  = 4 *
    ((Rsqr (sin (ξ / 2)) * Rsqr (cos (θ1 / 2  - θ2 / 2))
         +  Rsqr (cos (ξ / 2)) * Rsqr (cos (θ1 / 2 + θ2 / 2)))
    * ((Rsqr (sin (ξ / 2)) * Rsqr (sin (θ1 / 2  - θ2 / 2))
         +  Rsqr (cos (ξ / 2)) * Rsqr (sin (θ1 / 2 + θ2 / 2))))).
Proof.
intros.
assert ((sin ξ)² * (sin θ1)² = (sin ξ * sin θ1)²).
rewrite Rsqr_mult.
reflexivity.
rewrite H.
rewrite <- rm20_eq.
rewrite <- (rm21_eq θ1 ξ θ2).
assert ((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²
       = (rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²).
unfold rm02,rm20_minus,rm12,rm21.
assert ((-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2)²
= (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2)²).
rewrite Rsqr_neg.
unfold Rsqr. lra.
rewrite H0.
rewrite Rsqr_plus.
rewrite Rsqr_minus.
rewrite Rsqr_plus.
rewrite Rsqr_minus. lra.
rewrite H0.
rewrite rm02_eq.
rewrite rm12_eq.
rewrite Rsqr_mult.
rewrite sin_cos_q.
reflexivity.
Qed.

Lemma sqrt_term_neq_0: forall (θ1 ξ θ2:R),
 0 < rm02 θ1 ξ θ2 ->
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
 ->
√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) <> 0.
Proof.
intros.
assert (√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
   * √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
apply sqrt_mult_alt.
assert (0 <= ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
assert (0 <= (sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² ).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
lra.
assert (0 <= ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
assert (0 <= (sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
lra.
apply  Rmult_le_pos. assumption.
assumption.
rewrite H1.
apply Rmult_integral_contrapositive.
split.
assert (0 < √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
apply sqrt_lt_R0.
specialize (sin_cos_q θ1 ξ θ2) as eq4.
assert (((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²) * / 4
 = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
rewrite eq4.
lra. rewrite <- H2.
apply Rmult_lt_0_compat.
rewrite <- Rsqr_mult.
rewrite rm02_eq in H.
assert (0 < (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (sin ξ * sin θ2)²).
apply Rle_0_sqr.
lra. lra. lra. assumption.
Qed.

Lemma sqrt_term_neq_0_rm20: forall (θ1 ξ θ2:R),
 0 < rm20_minus θ1 ξ θ2 ->
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
 ->
√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) <> 0.
Proof.
intros.
assert (√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
   * √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
apply sqrt_mult_alt.
assert (0 <= ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
assert (0 <= (sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² ).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
lra.
assert (0 <= ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
assert (0 <= (sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
lra.
apply  Rmult_le_pos. assumption.
assumption.
rewrite H1.
apply Rmult_integral_contrapositive.
split.
assert (0 < √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
apply sqrt_lt_R0.
specialize (sin_cos_q θ1 ξ θ2) as eq4.
assert (((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²) * / 4
 = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
rewrite eq4.
lra. rewrite <- H2.
apply Rmult_lt_0_compat.
rewrite <- Rsqr_mult.
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
assert ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)² =  (rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H3.
assert (0 <= (rm21 θ1 ξ θ2)²).
apply Rle_0_sqr.
assert ((0 < (rm20_minus θ1 ξ θ2)²)).
apply Rsqr_pos_lt. lra. lra. lra.
lra. assumption.
Qed.

Lemma sqrt_term_neq_0_neg: forall (θ1 ξ θ2:R),
  rm02 θ1 ξ θ2 < 0 ->
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
 ->
√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) <> 0.
Proof.
intros.
assert (√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
   * √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
apply sqrt_mult_alt.
assert (0 <= ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
assert (0 <= (sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² ).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
lra.
assert (0 <= ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
assert (0 <= (sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
lra.
apply  Rmult_le_pos. assumption.
assumption.
rewrite H1.
apply Rmult_integral_contrapositive.
split.
assert (0 < √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
apply sqrt_lt_R0.
specialize (sin_cos_q θ1 ξ θ2) as eq4.
specialize (Rsqr_neg ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))) as eq1.
rewrite eq1 in eq4.
assert (((-(sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))² + (sin ξ)² * (sin θ2)²) * / 4
 = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
rewrite eq4.
lra. rewrite <- H2.
apply Rmult_lt_0_compat.
rewrite <- Rsqr_mult.
rewrite rm02_eq in H.
assert (0 < (-(sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))²).
apply Rsqr_pos_lt. lra.
assert (0 <= (sin ξ * sin θ2)²).
apply Rle_0_sqr.
lra. lra. lra. assumption.
Qed.

Lemma sqrt_term_neq_0_neg_rm20: forall (θ1 ξ θ2:R),
  rm20_minus θ1 ξ θ2 < 0 ->
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
 ->
√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) <> 0.
Proof.
intros.
assert (√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
   * √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
apply sqrt_mult_alt.
assert (0 <= ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
assert (0 <= (sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² ).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
lra.
assert (0 <= ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
assert (0 <= (sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
lra.
apply  Rmult_le_pos. assumption.
assumption.
rewrite H1.
apply Rmult_integral_contrapositive.
split.
assert (0 < √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
apply sqrt_lt_R0.
specialize (sin_cos_q θ1 ξ θ2) as eq4.
assert ((((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))² + (sin ξ)² * (sin θ2)²) * / 4
 = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
rewrite eq4.
lra. rewrite <- H2.
rewrite <- rm02_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm12_eq θ1 ξ θ2).
apply Rmult_lt_0_compat.
assert ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)² =  (rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H3.
specialize (Rsqr_neg (rm20_minus θ1 ξ θ2)) as eq1.
rewrite eq1.
assert (0 < (- rm20_minus θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
rewrite rm21_eq.
assert (0 <= (sin ξ * sin θ1)²).
apply Rle_0_sqr.
lra. lra. lra. assumption.
Qed.

Lemma sqrt_term_neq_0_a: forall (θ1 ξ θ2:R), 
 0 < rm02 θ1 ξ θ2 ->
√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) <> 0.
Proof.
intros.
assert (0 < √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
apply sqrt_lt_R0.
specialize (sin_cos_q θ1 ξ θ2) as eq4.
assert (((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²) * / 4
 = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
rewrite eq4.
lra. rewrite <- H0.
apply Rmult_lt_0_compat.
rewrite <- Rsqr_mult.
rewrite rm02_eq in H.
assert (0 < (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (sin ξ * sin θ2)²).
apply Rle_0_sqr.
lra. lra. lra.
Qed.

Lemma sqrt_term_neq_0_a_rm20: forall (θ1 ξ θ2:R), 
 0 < rm20_minus θ1 ξ θ2 ->
√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) <> 0.
Proof.
intros.
assert (0 < √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
apply sqrt_lt_R0.
specialize (sin_cos_q θ1 ξ θ2) as eq4.
assert (((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²) * / 4
 = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
rewrite eq4.
lra. rewrite <- H0.
apply Rmult_lt_0_compat.
rewrite <- Rsqr_mult.
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
assert ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)² =  (rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H1.
assert (0 <= (rm21 θ1 ξ θ2)²).
apply Rle_0_sqr.
assert ((0 < (rm20_minus θ1 ξ θ2)²)).
apply Rsqr_pos_lt. lra. lra. lra. lra.
Qed.

Lemma sqrt_term_neq_0_a_neg: forall (θ1 ξ θ2:R), 
 rm02 θ1 ξ θ2 < 0 ->
√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) <> 0.
Proof.
intros.
assert (0 < √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
apply sqrt_lt_R0.
specialize (sin_cos_q θ1 ξ θ2) as eq4.
specialize (Rsqr_neg (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)) as eq1.
rewrite eq1 in eq4.
assert (((-(sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))² + (sin ξ)² * (sin θ2)²) * / 4
 = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
rewrite eq4.
lra. rewrite <- H0.
apply Rmult_lt_0_compat.
rewrite <- Rsqr_mult.
rewrite rm02_eq in H.
assert (0 < (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (sin ξ * sin θ2)²).
apply Rle_0_sqr.
lra. lra. lra.
Qed.

Lemma sqrt_term_neq_0_a_neg_rm20: forall (θ1 ξ θ2:R), 
 rm20_minus θ1 ξ θ2 < 0 ->
√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) <> 0.
Proof.
intros.
assert (0 < √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
apply sqrt_lt_R0.
specialize (sin_cos_q θ1 ξ θ2) as eq4.
assert ((((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))² + (sin ξ)² * (sin θ2)²) * / 4
 = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
rewrite eq4.
lra. rewrite <- H0.
apply Rmult_lt_0_compat.
rewrite <- rm02_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm12_eq θ1 ξ θ2).
assert ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)² =  (rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H1.
assert (0 <= (rm21 θ1 ξ θ2)²).
apply Rle_0_sqr.
assert ((0 < (rm20_minus θ1 ξ θ2)²)).
apply Rsqr_pos_lt. lra. lra. lra. lra.
Qed.

Lemma C_smult_l: forall (x y z:R), ((RtoC x) * (y,z))%C = ((x * y)%R, (x * z)%R)%C.
Proof.
intros. lca.
Qed.

Lemma C_smult_r: forall (x y z:R), ((y,z)*(RtoC x))%C = ((y * x)%R, (z * x)%R)%C.
Proof.
intros. lca.
Qed.

Lemma Cmult_c: forall (x y w z:R), ((x%R,y%R)%C*(w%R,z%R)%C)%C = ((x * w - y * z)%R, (x * z + y * w)%R)%C.
Proof.
intros. lca.
Qed.

Lemma C_splus_l: forall (x y z:R), ((RtoC x) + (y,z))%C = ((x + y)%R, z%R)%C.
Proof.
intros. lca.
Qed.

Lemma C_splus_r: forall (x y z:R), ((y,z) + (RtoC x))%C = ((y + x)%R, z%R)%C.
Proof.
intros. lca.
Qed.



Lemma cos_sin_mult_q_l: forall (θ1 ξ θ2: R),
  sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2 = 0 ->
   (sin (θ1 / 2) * cos (θ2 / 2) + cos ξ * cos (θ1 / 2) * sin (θ2 / 2)) *
   (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) = 
    (2 * sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
Proof.
intros.
rewrite cos_minus.
rewrite cos_plus. 
rewrite Rsqr_plus.
rewrite Rsqr_minus.
rewrite <- rm02_eq in H.
unfold rm02,rx,ry,rw,rz in H.
assert (2 * (sin (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))) *
    (sin (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))) +
    2 * (cos (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))) *
    (cos (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
  = 2 * sin (θ1 / 2) * cos (θ1 / 2) * Rsqr (cos (θ2 / 2))
   - 2 * sin (θ1 / 2) * cos (θ1 / 2) * Rsqr (sin (θ2 / 2))
   + 2 * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * Rsqr (sin (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2)).
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = (2 * (ξ/2))) by lra.
rewrite <- H0. reflexivity.
rewrite H0. rewrite cos_2a.
assert (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² 
 = (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² ) * (Rsqr (sin (ξ / 2)) + Rsqr (cos (ξ / 2)))).
rewrite sin2_cos2. lra.
rewrite H1.
unfold Rsqr. lra.
rewrite H0 in H. clear H0.
assert (
((sin (ξ / 2))² *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
  (cos (ξ / 2))² *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
= ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
- ((cos (ξ / 2))² - (sin (ξ / 2))²) *
 (2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2)))) by lra.
rewrite H0. clear H0.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H0. reflexivity.
rewrite H0. clear H0.
rewrite Rmult_1_l.
rewrite  Rmult_minus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite  Rmult_plus_distr_r.
rewrite  Rmult_minus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite  Rmult_minus_distr_l.
rewrite Rmult_plus_distr_l.
assert (sin (θ1 / 2) * cos (θ2 / 2) * (2 * (cos (θ1 / 2) * cos (θ2 / 2))²)
  = 2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H0. clear H0.
assert (sin (θ1 / 2) * cos (θ2 / 2) * (2 * (sin (θ1 / 2) * sin (θ2 / 2))²)
 = 2 * sin (θ1 / 2) * (sin (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H0. clear H0.
assert (sin (θ1 / 2) * cos (θ2 / 2) *
(2 * (cos ξ * (2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2)))))
= 4 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H0. clear H0.
assert ((cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (2 * (cos (θ1 / 2) * cos (θ2 / 2))²)
= 2 * cos ξ * cos (θ1 / 2) * (cos (θ1 / 2))² * sin (θ2 / 2) * (cos (θ2 / 2))²)).
unfold Rsqr. lra.
rewrite H0. clear H0.
assert (cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (2 * (sin (θ1 / 2) * sin (θ2 / 2))²)
= 2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H0. clear H0.
assert (cos ξ * cos (θ1 / 2) * sin (θ2 / 2) *
 (2 * (cos ξ * (2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2)))))
= 4 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H0. clear H0.
assert (2 * sin (θ1 / 2) * (sin (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)
 = 2 * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)
   - 2 * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq1.
rewrite <- eq1. lra. rewrite H0. lra.
rewrite H0. clear H0.
assert (2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))² 
 = 2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
   - 2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq1.
rewrite <- eq1. lra. rewrite H0. lra.
rewrite H0. clear H0.
assert (2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))² +
(2 * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
 2 * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)) -
4 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² +
(2 * cos ξ * cos (θ1 / 2) * (cos (θ1 / 2))² * sin (θ2 / 2) * (cos (θ2 / 2))² +
 (2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
  2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) -
 4 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)) 
 = cos (θ1 / 2) * cos (θ2 / 2) * (
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  + 2 * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)
  + 2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
  - 4 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
  - 4 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H0. clear H0.
rewrite H.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert (4 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
= 2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
+ 2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
- 2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - ((cos (θ2 / 2))²)).
specialize (sin2_cos2 (θ2 / 2)) as eq1.
rewrite <- eq1. lra. rewrite H0. lra.
rewrite H0. clear H0.
assert (4 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)
 = 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)
  + 2  * (cos ξ)² * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) 
  - 2 * (cos ξ)² * sin (θ1 / 2) * (sin (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq1.
rewrite <- eq1. lra. rewrite H0. lra.
rewrite H0. clear H0.
assert (2 * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) +
2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
(2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² +
 2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
 2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²) -
(2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2) +
 2 * (cos ξ)² * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
 2 * (cos ξ)² * sin (θ1 / 2) * (sin (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2))
=
- cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (
2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
+ 2 * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)
+ 2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
- 2 * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) 
- 2 * (cos ξ)² * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H0. clear H0. rewrite H.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert (2 * (cos ξ)² * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)
 = 2 * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
2 * (sin ξ)² * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)).
assert ((sin ξ)² = 1 - ((cos ξ)²)).
specialize (sin2_cos2 ξ) as eq1.
rewrite <- eq1. lra. rewrite H0. lra.
rewrite H0. clear H0.
unfold Rsqr. lra.
Qed.

Lemma cos_sin_mult_q_l_rm20: forall (θ1 ξ θ2: R),
   cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2 = 0 ->
   (cos (θ1 / 2) * sin (θ2 / 2) + cos ξ * sin (θ1 / 2) * cos (θ2 / 2)) *
   (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) = 
    (2 * sin ξ * sin ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)).
Proof.
intros.
rewrite cos_minus.
rewrite cos_plus. 
rewrite Rsqr_plus.
rewrite Rsqr_minus.
rewrite <- rm20_eq in H.
unfold rm20_minus,rx,ry,rw,rz in H.
assert (-2 * (sin (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))) *
    (sin (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))) +
    2 * (cos (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))) *
    (cos (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
  = 2 * Rsqr (cos (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2) 
   - 2 * Rsqr (sin (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * Rsqr (cos (θ2 / 2))
   - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * Rsqr (sin (θ2 / 2))).
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = (2 * (ξ/2))) by lra.
rewrite <- H0. reflexivity.
rewrite H0. rewrite cos_2a.
assert (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)
 = (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) * (Rsqr (sin (ξ / 2)) + Rsqr (cos (ξ / 2)))).
rewrite sin2_cos2. lra.
rewrite H1.
unfold Rsqr. lra.
rewrite H0 in H. clear H0.
assert (
((sin (ξ / 2))² *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
  (cos (ξ / 2))² *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
= ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
- ((cos (ξ / 2))² - (sin (ξ / 2))²) *
 (2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2)))) by lra.
rewrite H0. clear H0.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H0. reflexivity.
rewrite H0. clear H0.
rewrite Rmult_1_l.
rewrite  Rmult_minus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite  Rmult_plus_distr_r.
rewrite  Rmult_minus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite  Rmult_minus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rsqr_mult. rewrite Rsqr_mult.
assert (cos (θ1 / 2) * sin (θ2 / 2) * (2 * ((sin (θ1 / 2))² * (sin (θ2 / 2))²))
 = cos (θ1 / 2) * sin (θ2 / 2) * 2 * (sin (θ1 / 2))²
  - cos (θ1 / 2) * sin (θ2 / 2) * (2 * ((sin (θ1 / 2))² * (cos (θ2 / 2))²))).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq1.
rewrite <- eq1. lra. rewrite H0. lra.
rewrite H0. clear H0.
assert (cos (θ1 / 2) * sin (θ2 / 2) *
(2 * (cos ξ * (2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2)))))
 = 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² * cos (θ2 / 2)
  + 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq1.
rewrite <- eq1. lra. rewrite H0. unfold Rsqr. lra.
rewrite H0. clear H0.
assert (cos (θ1 / 2) * sin (θ2 / 2) * (2 * ((cos (θ1 / 2))² * (cos (θ2 / 2))²)) +
(cos (θ1 / 2) * sin (θ2 / 2) * 2 * (sin (θ1 / 2))² -
 cos (θ1 / 2) * sin (θ2 / 2) * (2 * ((sin (θ1 / 2))² * (cos (θ2 / 2))²))) -
(2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) *
 cos (θ2 / 2) -
 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² * cos (θ2 / 2) +
 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2))
= cos (θ1 / 2) * cos (θ2 / 2) *
   (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
   + cos (θ1 / 2) * sin (θ2 / 2) * 2 * (sin (θ1 / 2))²
   - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H0. clear H0.
rewrite H.
assert (cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * (2 * ((cos (θ1 / 2))² * (cos (θ2 / 2))²))
  = cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * 2 * (cos (θ1 / 2))²
   - (cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * (2 * ((cos (θ1 / 2))² * (sin (θ2 / 2))²)))).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq1.
rewrite <- eq1. lra. rewrite H0. unfold Rsqr. lra.
rewrite H0. clear H0.
assert (cos ξ * sin (θ1 / 2) * cos (θ2 / 2) *
 (2 * (cos ξ * (2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2)))))
 = 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)
  - 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq1.
rewrite <- eq1. lra. rewrite H0. unfold Rsqr. lra.
rewrite H0. clear H0.
assert ((cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * 2 * (cos (θ1 / 2))² -
 cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * (2 * ((cos (θ1 / 2))² * (sin (θ2 / 2))²)) +
 cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * (2 * ((sin (θ1 / 2))² * (sin (θ2 / 2))²)) -
 (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) *
  cos (θ2 / 2) + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) -
  2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) *
  (sin (θ2 / 2))²))
= - cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * 
   (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
 + cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * 2 * (cos (θ1 / 2))²
 - 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)).
unfold Rsqr. lra.
rewrite H0. clear H0. rewrite H.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)
= 2 * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)
 - 2 * (sin ξ)² * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)).
assert ((sin ξ)² = 1 - ((cos ξ)²)).
specialize (sin2_cos2 ξ) as eq1.
rewrite <- eq1. lra. rewrite H0. unfold Rsqr. lra.
rewrite H0. clear H0.
unfold Rsqr. lra.
Qed.

Lemma cos_sin_mult_q_r: forall (θ1 ξ θ2: R),
  sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2 = 0 ->
   (sin ξ * cos (θ1 / 2) * sin (θ2 / 2)) *
   (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) = 
    (2 * sin ξ * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * sin ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
Proof.
intros.
rewrite cos_minus.
rewrite cos_plus. 
rewrite Rsqr_plus.
rewrite Rsqr_minus.
rewrite <- rm02_eq in H.
unfold rm02,rx,ry,rw,rz in H.
assert (2 * (sin (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))) *
    (sin (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))) +
    2 * (cos (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))) *
    (cos (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
  = 2 * sin (θ1 / 2) * cos (θ1 / 2) * Rsqr (cos (θ2 / 2))
   - 2 * sin (θ1 / 2) * cos (θ1 / 2) * Rsqr (sin (θ2 / 2))
   + 2 * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * Rsqr (sin (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2)).
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = (2 * (ξ/2))) by lra.
rewrite <- H0. reflexivity.
rewrite H0. rewrite cos_2a.
assert (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² 
 = (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² ) * (Rsqr (sin (ξ / 2)) + Rsqr (cos (ξ / 2)))).
rewrite sin2_cos2. lra.
rewrite H1.
unfold Rsqr. lra.
rewrite H0 in H. clear H0.
assert (
((sin (ξ / 2))² *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
  (cos (ξ / 2))² *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
= ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
- ((cos (ξ / 2))² - (sin (ξ / 2))²) *
 (2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2)))) by lra.
rewrite H0. clear H0.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H0. reflexivity.
rewrite H0. clear H0.
rewrite Rmult_1_l.
rewrite  Rmult_minus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite  Rmult_minus_distr_l.
rewrite Rmult_plus_distr_l.
assert (sin ξ * cos (θ1 / 2) * sin (θ2 / 2) * (2 * (cos (θ1 / 2) * cos (θ2 / 2))²) 
 = 2 * sin ξ *  cos (θ1 / 2) * (cos (θ1 / 2))² * sin (θ2 / 2) * (cos (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H0. clear H0.
assert (sin ξ * cos (θ1 / 2) * sin (θ2 / 2) * (2 * (sin (θ1 / 2) * sin (θ2 / 2))²)
= 2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H0. clear H0.
assert (sin ξ * cos (θ1 / 2) * sin (θ2 / 2) *
(2 * (cos ξ * (2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2)))))
= 4 * sin ξ * cos ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H0. clear H0.
assert (2 * sin ξ * cos (θ1 / 2) * (cos (θ1 / 2))² * sin (θ2 / 2) * (cos (θ2 / 2))²
= 2 * sin ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
   - 2 * sin ξ * cos (θ1 / 2) * (sin (θ1 / 2))² * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq1.
rewrite <- eq1. lra. rewrite H0. lra.
rewrite H0. clear H0.
assert (4 * sin ξ * cos ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)
= 2 * sin ξ * cos ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)
 + 2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)
 - 2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq1.
rewrite <- eq1. lra. rewrite H0. lra.
rewrite H0. clear H0.
assert (2 * sin ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
2 * sin ξ * cos (θ1 / 2) * (sin (θ1 / 2))² * sin (θ2 / 2) * (cos (θ2 / 2))² +
2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))² -
(2 * sin ξ * cos ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2) +
 2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
 2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2))
= - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (
 2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
+ 2 * sin ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
- 2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) ).
unfold Rsqr. lra.
rewrite H0. clear H0. rewrite H.
unfold Rsqr. lra.
Qed.

Lemma cos_sin_mult_q_r_rm20: forall (θ1 ξ θ2: R),
   cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2 = 0 ->
   (sin ξ * sin (θ1 / 2) * cos (θ2 / 2)) *
   (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) = 
    2 * sin ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
      2 * sin ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2).
Proof.
intros.
rewrite cos_minus.
rewrite cos_plus. 
rewrite Rsqr_plus.
rewrite Rsqr_minus.
rewrite <- rm20_eq in H.
unfold rm20_minus,rx,ry,rw,rz in H.
assert (-2 * (sin (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))) *
    (sin (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))) +
    2 * (cos (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))) *
    (cos (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
  = 2 * Rsqr (cos (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2) 
   - 2 * Rsqr (sin (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * Rsqr (cos (θ2 / 2))
   - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * Rsqr (sin (θ2 / 2))).
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = (2 * (ξ/2))) by lra.
rewrite <- H0. reflexivity.
rewrite H0. rewrite cos_2a.
assert (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)
 = (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) * (Rsqr (sin (ξ / 2)) + Rsqr (cos (ξ / 2)))).
rewrite sin2_cos2. lra.
rewrite H1.
unfold Rsqr. lra.
rewrite H0 in H. clear H0.
assert (
((sin (ξ / 2))² *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
  (cos (ξ / 2))² *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
= ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
- ((cos (ξ / 2))² - (sin (ξ / 2))²) *
 (2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2)))) by lra.
rewrite H0. clear H0.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H0. reflexivity.
rewrite H0. clear H0.
rewrite Rmult_1_l.
rewrite  Rmult_minus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite  Rmult_minus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rsqr_mult. rewrite Rsqr_mult.
assert (sin ξ * sin (θ1 / 2) * cos (θ2 / 2) * (2 * ((cos (θ1 / 2))² * (cos (θ2 / 2))²))
  = sin ξ * sin (θ1 / 2) * cos (θ2 / 2) * 2 * (cos (θ1 / 2))²
  - sin ξ * sin (θ1 / 2) * cos (θ2 / 2) * (2 * ((cos (θ1 / 2))² * (sin (θ2 / 2))²))).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq1.
rewrite <- eq1. lra. rewrite H0. lra.
rewrite H0. clear H0.
assert (sin ξ * sin (θ1 / 2) * cos (θ2 / 2) *
(2 * (cos ξ * (2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2)))))
= 2 * sin ξ * cos ξ *  sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
 + 2 * sin ξ * cos ξ *  sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)
  - 2 * sin ξ * cos ξ *  sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq1.
rewrite <- eq1. lra. rewrite H0. unfold Rsqr. lra.
rewrite H0. clear H0.
assert (sin ξ * sin (θ1 / 2) * cos (θ2 / 2) * 2 * (cos (θ1 / 2))² -
sin ξ * sin (θ1 / 2) * cos (θ2 / 2) * (2 * ((cos (θ1 / 2))² * (sin (θ2 / 2))²)) +
sin ξ * sin (θ1 / 2) * cos (θ2 / 2) * (2 * ((sin (θ1 / 2))² * (sin (θ2 / 2))²)) -
(2 * sin ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) *
 cos (θ2 / 2) + 2 * sin ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) -
 2 * sin ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) *
 (sin (θ2 / 2))²)
= - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
    (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
  + 2 * sin ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
2 * sin ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)).
unfold Rsqr. lra.
rewrite H0. clear H0. rewrite H.
lra.
Qed.

Lemma rm22_rewrite_case_1:
  forall (θ1 ξ θ2:R),
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
        (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
  -> (-
 (cos (θ2 / 2) * sin (θ1 / 2) +
  sin (θ2 / 2) *
  ((cos ξ * cos (θ1 / 2))%R, (sin ξ * cos (θ1 / 2))%R)))%C =
(-
 (((cos
      (acos
         ((cos (θ1 / 2) * cos (θ2 / 2) -
           cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
          √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
             (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
    cos (atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2)) -
    -
    (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
        (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
    sin (atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2))) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
      (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))%R,
 ((-
   (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
       (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
   cos (atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2)) +
   cos
     (acos
        ((cos (θ1 / 2) * cos (θ2 / 2) -
          cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
         √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
            (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
   sin (atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2))) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))%R))%C.
Proof.
intros.
rename H into H0.
assert (θ1=θ1) as H1 by lra .
assert (0 <= √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
        (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) as H2.
apply sqrt_pos.
assert (θ2=θ2) as H3 by lra.
assert (ξ=ξ) as H4 by lra.
assert (ξ=ξ) as H5 by lra.
rewrite cos_acos.
unfold atan2.
destruct (0 <? rm02 θ1 ξ θ2) eqn:eq3.
{
apply Rltb_lt in eq3.
rewrite rm12_cos.
rewrite rm12_sin.
rewrite  Rmult_plus_distr_r.
remember (√ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²)) as p.
rewrite sin_cos_q in Heqp.
assert ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)
   = (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2/2) * cos (θ2/2) - sin (θ2/2) * sin (θ2/2))
       + 2 * cos ξ * (cos (θ1/2) * cos (θ1/2) - sin (θ1/2) * sin (θ1/2)) * sin (θ2 / 2) * cos (θ2 / 2))).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (θ2 = 2 * (θ2/2)) by lra.
assert (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2
  = sin (2 * (θ1/2)) * cos (2 * (θ2/2)) + cos ξ * cos (2 * (θ1/2)) * sin (2 * (θ2/2))).
rewrite <- H. rewrite <- H6. reflexivity.
rewrite H7.
rewrite sin_2a.
rewrite sin_2a.
rewrite cos_2a.
rewrite cos_2a.
lra.
rewrite H. clear H.
assert (sin θ2 = 2 * sin (θ2/2) * cos (θ2/2)).
assert (θ2 = 2 * (θ2/2)) by lra.
assert (sin θ2 = sin (2 * (θ2/2))).
rewrite <- H. reflexivity.
rewrite H6.
rewrite sin_2a. reflexivity.
rewrite H. 
assert ((-
  (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
  ((2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
    2 * cos ξ * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
    cos (θ2 / 2)) / p) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) +
  (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
  (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)) / p) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))%R
=
((((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
    2 * cos ξ * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
    cos (θ2 / 2))
+ (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)))
* 
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
* / (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))

* / p)%R) by lra.
rewrite H6. clear H6.
assert ((cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2))
   = (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1)).
rewrite <- cos_2a. rewrite -> cos_2a_cos. reflexivity.
rewrite H6. clear H6.
assert ((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) *
    (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
    2 * cos ξ * (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1) * sin (θ2 / 2) * cos (θ2 / 2)) +
   (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
   (2 * sin (θ2 / 2) * cos (θ2 / 2)))
=
(sin ξ * sin (θ2 / 2) * cos (θ1 / 2)) *
 (2 * ((Rsqr (cos (θ2 / 2))) * (1 - (Rsqr (sin (θ1 / 2)))) + (Rsqr (sin (θ1 / 2))) * (Rsqr (sin (θ2 / 2))))
  - 4 * (cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)))).
assert ((cos (θ2 / 2))² * (1 - (sin (θ1 / 2))²)
    = (cos (θ2 / 2))² - (cos (θ2 / 2))² * (sin (θ1 / 2))²).
unfold Rsqr. lra.
rewrite H6.
unfold Rsqr.
lra.
assert ((1 - (sin (θ1 / 2))²) = (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as H7.
rewrite <- H7. lra.
rewrite H7 in H6. rewrite H6.
clear H7. clear H6.
assert ((2 * ((cos (θ2 / 2))² * (cos (θ1 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   4 * (cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)))
   = 2 * Rsqr (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite Rsqr_sqrt.
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus.
rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
  = ((sin (ξ / 2))² + (cos (ξ / 2))²) *
    ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
  - 2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))
       * (sin (θ1 / 2) * sin (θ2 / 2)))) by lra.
rewrite H6. clear H6.

rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra. rewrite H6. reflexivity.
rewrite H6.
unfold Rsqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²) by apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²) by apply Rle_0_sqr.
lra.
rewrite H6. clear H6.
rewrite  sqrt_mult_alt in Heqp.
assert (√ 4 = 2). assert (4 = Rsqr 2). unfold Rsqr. lra.
rewrite H6. rewrite sqrt_Rsqr. reflexivity. lra.
rewrite H6 in Heqp. clear H6.
assert ((√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))²
 = (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
unfold Rsqr. lra.
rewrite H6. clear H6.
assert ((sin ξ * sin (θ2 / 2) * cos (θ1 / 2) *
  (2 *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
  / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) * 
  / p)
= 
(sin ξ * sin (θ2 / 2) * cos (θ1 / 2) *
  ((2 *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
   * / p) *
  (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))) by lra.
rewrite H6. clear H6.
rewrite <- sqrt_mult.
rewrite Heqp.
rewrite Rinv_r. rewrite Rinv_r. 
assert ((((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    ((2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
      2 * cos ξ * (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1) * sin (θ2 / 2) * cos (θ2 / 2)) /
     (2 *
      √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
         ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))) -
    -
    (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
    (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)) /
     (2 *
      √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
         ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))%R
= 
((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
(2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
      2 * cos ξ * (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1) * sin (θ2 / 2) * cos (θ2 / 2))
+ (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2))))
* (√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
* (/ (2 *
      √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
         ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
* / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite H6. clear H6.
rewrite <- Rinv_mult_distr.
rewrite (Rmult_assoc 2 (√ (((sin (ξ / 2))² 
       * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) )).
rewrite <- sqrt_mult_alt.
assert (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
    (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
     2 * cos ξ * (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1) * sin (θ2 / 2) * cos (θ2 / 2)) +
    sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2))))
 = (cos (θ2 / 2) * sin (θ1 / 2) + cos ξ * sin (θ2 / 2) * cos (θ1 / 2))
   * (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite cos_plus.
rewrite cos_minus.
rewrite (Rsqr_plus (cos (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rsqr_minus (cos (θ1 / 2) * cos (θ2 / 2))).
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
= ((sin (ξ / 2))² + (cos (ξ / 2))²) *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
  - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H6. clear H6.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H6. reflexivity.
rewrite H6.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite <- cos_2a.
rewrite <- cos_2a_cos.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * cos (2 * (θ2 / 2)))
 = 2 * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
+ 2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
- 2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)).
rewrite cos_2a.
assert (2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
 = 2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   * (Rsqr (sin (θ1 / 2)) + Rsqr (cos (θ1 / 2)))).
rewrite sin2_cos2. lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * cos (2 * (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2))
 = 2 * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
+ 2 * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
- 2 * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2)
    * (Rsqr (sin (θ2 / 2)) + Rsqr (cos (θ2 / 2)))).
rewrite cos_2a.
unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)))
 = 2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
  - (Rsqr (cos ξ)) * sin (θ1 / 2) * sin (θ2 / 2) * 
   (2 * sin (θ2 / 2) * cos (θ2 / 2)) * ((Rsqr (sin (θ1 / 2))) + (Rsqr (cos (θ1 / 2))))).
rewrite sin2_cos2.
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite cos_2a. rewrite cos_2a.
unfold Rsqr. lra.
rewrite H6. clear H6.
assert ((2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
 = (2 * √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²))).
rewrite sqrt_Rsqr. reflexivity.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite H6. clear H6.
assert (((cos (θ2 / 2) * sin (θ1 / 2) + cos ξ * sin (θ2 / 2) * cos (θ1 / 2)) *
   (2 * √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))
 = (cos (θ2 / 2) * sin (θ1 / 2) + cos ξ * sin (θ2 / 2) * cos (θ1 / 2)) *
  ((2 * (√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
         * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
     * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
  * /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
unfold Rsqr. lra.
rewrite H6. clear H6.
rewrite <- sqrt_mult_alt.
assert ((((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
  = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
        ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
        ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite H6. clear H6.
rewrite Rinv_r. lca.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0. assumption. assumption.
apply  Rmult_le_pos.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
apply  Rmult_le_pos.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_a. assumption.
assumption. assumption.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_a. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
lra. assumption. assumption.
}
destruct (rm02 θ1 ξ θ2 <? 0) eqn:eq4.
apply Rltb_lt in eq4.
destruct (0 <=? rm12 θ1 ξ θ2) eqn:eq5.
apply Rleb_le in eq5.
{
assert ((atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2) + PI) = PI + atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2)) by lra.
rewrite H. clear H.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite rm12_cos_neg.
rewrite rm12_sin_neg.
rewrite  Rmult_plus_distr_r.
remember (√ ((-(sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))² + (sin ξ)² * (sin θ2)²)) as p.
specialize (sin_cos_q θ1 ξ θ2) as eq6.
rewrite (Rsqr_neg (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)) in eq6.
rewrite eq6 in Heqp.
assert ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)
   = (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2/2) * cos (θ2/2) - sin (θ2/2) * sin (θ2/2))
       + 2 * cos ξ * (cos (θ1/2) * cos (θ1/2) - sin (θ1/2) * sin (θ1/2)) * sin (θ2 / 2) * cos (θ2 / 2))).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (θ2 = 2 * (θ2/2)) by lra.
assert (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2
  = sin (2 * (θ1/2)) * cos (2 * (θ2/2)) + cos ξ * cos (2 * (θ1/2)) * sin (2 * (θ2/2))).
rewrite <- H. rewrite <- H6. reflexivity.
rewrite H7.
rewrite sin_2a.
rewrite sin_2a.
rewrite cos_2a.
rewrite cos_2a.
lra.
rewrite H. clear H.
assert (- (- (sin ξ * sin θ2) / p) = (sin ξ * sin θ2) / p) by lra.
rewrite H. clear H.
assert (-
    (-
     (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
      2 * cos ξ * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
      cos (θ2 / 2)) / p)
 = ((2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
      2 * cos ξ * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
      cos (θ2 / 2)) / p)) by lra.
rewrite H. clear H.
assert (sin θ2 = 2 * sin (θ2/2) * cos (θ2/2)).
assert (θ2 = 2 * (θ2/2)) by lra.
assert (sin θ2 = sin (2 * (θ2/2))).
rewrite <- H. reflexivity.
rewrite H6.
rewrite sin_2a. reflexivity.
rewrite H. 
assert ((-
  (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
  ((2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
    2 * cos ξ * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
    cos (θ2 / 2)) / p) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) +
  (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
  (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)) / p) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))%R
=
((((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
    2 * cos ξ * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
    cos (θ2 / 2))
+ (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)))
* 
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
* / (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))

* / p)%R) by lra.
rewrite H6. clear H6.
assert ((cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2))
   = (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1)).
rewrite <- cos_2a. rewrite -> cos_2a_cos. reflexivity.
rewrite H6. clear H6.
assert ((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) *
    (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
    2 * cos ξ * (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1) * sin (θ2 / 2) * cos (θ2 / 2)) +
   (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
   (2 * sin (θ2 / 2) * cos (θ2 / 2)))
=
(sin ξ * sin (θ2 / 2) * cos (θ1 / 2)) *
 (2 * ((Rsqr (cos (θ2 / 2))) * (1 - (Rsqr (sin (θ1 / 2)))) + (Rsqr (sin (θ1 / 2))) * (Rsqr (sin (θ2 / 2))))
  - 4 * (cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)))).
assert ((cos (θ2 / 2))² * (1 - (sin (θ1 / 2))²)
    = (cos (θ2 / 2))² - (cos (θ2 / 2))² * (sin (θ1 / 2))²).
unfold Rsqr. lra.
rewrite H6.
unfold Rsqr.
lra.
assert ((1 - (sin (θ1 / 2))²) = (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as H7.
rewrite <- H7. lra.
rewrite H7 in H6. rewrite H6.
clear H7. clear H6.
assert ((2 * ((cos (θ2 / 2))² * (cos (θ1 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   4 * (cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)))
   = 2 * Rsqr (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite Rsqr_sqrt.
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus.
rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
  = ((sin (ξ / 2))² + (cos (ξ / 2))²) *
    ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
  - 2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))
       * (sin (θ1 / 2) * sin (θ2 / 2)))) by lra.
rewrite H6. clear H6.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra. rewrite H6. reflexivity.
rewrite H6.
unfold Rsqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²) by apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²) by apply Rle_0_sqr.
lra.
rewrite H6. clear H6.
rewrite  sqrt_mult_alt in Heqp.
assert (√ 4 = 2). assert (4 = Rsqr 2). unfold Rsqr. lra.
rewrite H6. rewrite sqrt_Rsqr. reflexivity. lra.
rewrite H6 in Heqp. clear H6.
assert ((√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))²
 = (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
unfold Rsqr. lra.
rewrite H6. clear H6.
assert ((sin ξ * sin (θ2 / 2) * cos (θ1 / 2) *
  (2 *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
  / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) * 
  / p)
= 
(sin ξ * sin (θ2 / 2) * cos (θ1 / 2) *
  ((2 *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
   * / p) *
  (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))) by lra.
rewrite H6. clear H6.
rewrite <- sqrt_mult.
rewrite Heqp.
rewrite Rinv_r. rewrite Rinv_r. 
assert ((((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    ((2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
      2 * cos ξ * (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1) * sin (θ2 / 2) * cos (θ2 / 2)) /
     (2 *
      √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
         ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))) -
    -
    (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
    (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)) /
     (2 *
      √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
         ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))%R
= 
((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
(2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
      2 * cos ξ * (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1) * sin (θ2 / 2) * cos (θ2 / 2))
+ (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2))))
* (√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
* (/ (2 *
      √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
         ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
* / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite H6. clear H6.
rewrite <- Rinv_mult_distr.
rewrite (Rmult_assoc 2 (√ (((sin (ξ / 2))² 
       * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) )).
rewrite <- sqrt_mult_alt.
assert (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
    (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
     2 * cos ξ * (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1) * sin (θ2 / 2) * cos (θ2 / 2)) +
    sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2))))
 = (cos (θ2 / 2) * sin (θ1 / 2) + cos ξ * sin (θ2 / 2) * cos (θ1 / 2))
   * (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite cos_plus.
rewrite cos_minus.
rewrite (Rsqr_plus (cos (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rsqr_minus (cos (θ1 / 2) * cos (θ2 / 2))).
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
= ((sin (ξ / 2))² + (cos (ξ / 2))²) *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
  - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H6. clear H6.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H6. reflexivity.
rewrite H6.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite <- cos_2a.
rewrite <- cos_2a_cos.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * cos (2 * (θ2 / 2)))
 = 2 * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
+ 2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
- 2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)).
rewrite cos_2a.
assert (2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
 = 2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   * (Rsqr (sin (θ1 / 2)) + Rsqr (cos (θ1 / 2)))).
rewrite sin2_cos2. lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * cos (2 * (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2))
 = 2 * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
+ 2 * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
- 2 * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2)
    * (Rsqr (sin (θ2 / 2)) + Rsqr (cos (θ2 / 2)))).
rewrite cos_2a.
unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)))
 = 2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
  - (Rsqr (cos ξ)) * sin (θ1 / 2) * sin (θ2 / 2) * 
   (2 * sin (θ2 / 2) * cos (θ2 / 2)) * ((Rsqr (sin (θ1 / 2))) + (Rsqr (cos (θ1 / 2))))).
rewrite sin2_cos2.
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite cos_2a. rewrite cos_2a.
unfold Rsqr. lra.
rewrite H6. clear H6.
assert ((2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
 = (2 * √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²))).
rewrite sqrt_Rsqr. reflexivity.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite H6. clear H6.
assert (((cos (θ2 / 2) * sin (θ1 / 2) + cos ξ * sin (θ2 / 2) * cos (θ1 / 2)) *
   (2 * √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))
 = (cos (θ2 / 2) * sin (θ1 / 2) + cos ξ * sin (θ2 / 2) * cos (θ1 / 2)) *
  ((2 * (√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
         * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
     * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
  * /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
unfold Rsqr. lra.
rewrite H6. clear H6.
rewrite <- sqrt_mult_alt.
assert ((((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
  = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
        ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
        ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite H6. clear H6.
rewrite Rinv_r. lca.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_neg. assumption. assumption.
apply  Rmult_le_pos.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
apply  Rmult_le_pos.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_a_neg. assumption.
assumption. assumption.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_a_neg. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
lra. assumption. assumption.
}

{
assert ((atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2) - PI) = - (PI - atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2))) by lra.
rewrite H. clear H.
rewrite sin_neg.
rewrite cos_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite rm12_cos_neg.
rewrite rm12_sin_neg.
rewrite  Rmult_plus_distr_r.
remember (√ ((-(sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))² + (sin ξ)² * (sin θ2)²)) as p.
specialize (sin_cos_q θ1 ξ θ2) as eq6.
rewrite (Rsqr_neg (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)) in eq6.
rewrite eq6 in Heqp.
assert ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)
   = (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2/2) * cos (θ2/2) - sin (θ2/2) * sin (θ2/2))
       + 2 * cos ξ * (cos (θ1/2) * cos (θ1/2) - sin (θ1/2) * sin (θ1/2)) * sin (θ2 / 2) * cos (θ2 / 2))).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (θ2 = 2 * (θ2/2)) by lra.
assert (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2
  = sin (2 * (θ1/2)) * cos (2 * (θ2/2)) + cos ξ * cos (2 * (θ1/2)) * sin (2 * (θ2/2))).
rewrite <- H. rewrite <- H6. reflexivity.
rewrite H7.
rewrite sin_2a.
rewrite sin_2a.
rewrite cos_2a.
rewrite cos_2a.
lra.
rewrite H. clear H.
assert (- (- (sin ξ * sin θ2) / p) = (sin ξ * sin θ2) / p) by lra.
rewrite H. clear H.
assert (-
    (-
     (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
      2 * cos ξ * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
      cos (θ2 / 2)) / p)
 = ((2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
      2 * cos ξ * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
      cos (θ2 / 2)) / p)) by lra.
rewrite H. clear H.
assert (sin θ2 = 2 * sin (θ2/2) * cos (θ2/2)).
assert (θ2 = 2 * (θ2/2)) by lra.
assert (sin θ2 = sin (2 * (θ2/2))).
rewrite <- H. reflexivity.
rewrite H6.
rewrite sin_2a. reflexivity.
rewrite H. 
assert ((-
  (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
  ((2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
    2 * cos ξ * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
    cos (θ2 / 2)) / p) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) +
  (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
  (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)) / p) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))%R
=
((((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
    2 * cos ξ * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
    cos (θ2 / 2))
+ (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)))
* 
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
* / (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))

* / p)%R) by lra.
rewrite H6. clear H6.
assert ((cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2))
   = (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1)).
rewrite <- cos_2a. rewrite -> cos_2a_cos. reflexivity.
rewrite H6. clear H6.
assert ((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) *
    (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
    2 * cos ξ * (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1) * sin (θ2 / 2) * cos (θ2 / 2)) +
   (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
   (2 * sin (θ2 / 2) * cos (θ2 / 2)))
=
(sin ξ * sin (θ2 / 2) * cos (θ1 / 2)) *
 (2 * ((Rsqr (cos (θ2 / 2))) * (1 - (Rsqr (sin (θ1 / 2)))) + (Rsqr (sin (θ1 / 2))) * (Rsqr (sin (θ2 / 2))))
  - 4 * (cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)))).
assert ((cos (θ2 / 2))² * (1 - (sin (θ1 / 2))²)
    = (cos (θ2 / 2))² - (cos (θ2 / 2))² * (sin (θ1 / 2))²).
unfold Rsqr. lra.
rewrite H6.
unfold Rsqr.
lra.
assert ((1 - (sin (θ1 / 2))²) = (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as H7.
rewrite <- H7. lra.
rewrite H7 in H6. rewrite H6.
clear H7. clear H6.
assert ((2 * ((cos (θ2 / 2))² * (cos (θ1 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   4 * (cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)))
   = 2 * Rsqr (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite Rsqr_sqrt.
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus.
rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
  = ((sin (ξ / 2))² + (cos (ξ / 2))²) *
    ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
  - 2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))
       * (sin (θ1 / 2) * sin (θ2 / 2)))) by lra.
rewrite H6. clear H6.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra. rewrite H6. reflexivity.
rewrite H6.
unfold Rsqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²) by apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²) by apply Rle_0_sqr.
lra.
rewrite H6. clear H6.
rewrite  sqrt_mult_alt in Heqp.
assert (√ 4 = 2). assert (4 = Rsqr 2). unfold Rsqr. lra.
rewrite H6. rewrite sqrt_Rsqr. reflexivity. lra.
rewrite H6 in Heqp. clear H6.
assert ((√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))²
 = (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
unfold Rsqr. lra.
rewrite H6. clear H6.
assert ((sin ξ * sin (θ2 / 2) * cos (θ1 / 2) *
  (2 *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
  / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) * 
  / p)
= 
(sin ξ * sin (θ2 / 2) * cos (θ1 / 2) *
  ((2 *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
   * / p) *
  (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))) by lra.
rewrite H6. clear H6.
rewrite <- sqrt_mult.
rewrite Heqp.
rewrite Rinv_r. rewrite Rinv_r. 
assert ((((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    ((2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
      2 * cos ξ * (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1) * sin (θ2 / 2) * cos (θ2 / 2)) /
     (2 *
      √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
         ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))) -
    -
    (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
    (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)) /
     (2 *
      √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
         ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))%R
= 
((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
(2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
      2 * cos ξ * (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1) * sin (θ2 / 2) * cos (θ2 / 2))
+ (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2))))
* (√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
* (/ (2 *
      √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
         ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
* / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite H6. clear H6.
rewrite <- Rinv_mult_distr.
rewrite (Rmult_assoc 2 (√ (((sin (ξ / 2))² 
       * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) )).
rewrite <- sqrt_mult_alt.
assert (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
    (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)) +
     2 * cos ξ * (2 * cos (θ1 / 2) * cos (θ1 / 2) - 1) * sin (θ2 / 2) * cos (θ2 / 2)) +
    sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2))))
 = (cos (θ2 / 2) * sin (θ1 / 2) + cos ξ * sin (θ2 / 2) * cos (θ1 / 2))
   * (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite cos_plus.
rewrite cos_minus.
rewrite (Rsqr_plus (cos (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rsqr_minus (cos (θ1 / 2) * cos (θ2 / 2))).
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
= ((sin (ξ / 2))² + (cos (ξ / 2))²) *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
  - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H6. clear H6.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H6. reflexivity.
rewrite H6.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite <- cos_2a.
rewrite <- cos_2a_cos.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * cos (2 * (θ2 / 2)))
 = 2 * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
+ 2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
- 2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)).
rewrite cos_2a.
assert (2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
 = 2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   * (Rsqr (sin (θ1 / 2)) + Rsqr (cos (θ1 / 2)))).
rewrite sin2_cos2. lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * cos (2 * (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2))
 = 2 * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
+ 2 * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
- 2 * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2)
    * (Rsqr (sin (θ2 / 2)) + Rsqr (cos (θ2 / 2)))).
rewrite cos_2a.
unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)))
 = 2 * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
  - (Rsqr (cos ξ)) * sin (θ1 / 2) * sin (θ2 / 2) * 
   (2 * sin (θ2 / 2) * cos (θ2 / 2)) * ((Rsqr (sin (θ1 / 2))) + (Rsqr (cos (θ1 / 2))))).
rewrite sin2_cos2.
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite cos_2a. rewrite cos_2a.
unfold Rsqr. lra.
rewrite H6. clear H6.
assert ((2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
 = (2 * √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²))).
rewrite sqrt_Rsqr. reflexivity.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite H6. clear H6.
assert (((cos (θ2 / 2) * sin (θ1 / 2) + cos ξ * sin (θ2 / 2) * cos (θ1 / 2)) *
   (2 * √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))
 = (cos (θ2 / 2) * sin (θ1 / 2) + cos ξ * sin (θ2 / 2) * cos (θ1 / 2)) *
  ((2 * (√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
         * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
     * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
  * /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
unfold Rsqr. lra.
rewrite H6. clear H6.
rewrite <- sqrt_mult_alt.
assert ((((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
  = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
        ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
        ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite H6. clear H6.
rewrite Rinv_r. lca.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_neg. assumption. assumption.
apply  Rmult_le_pos.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
apply  Rmult_le_pos.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_a_neg. assumption.
assumption. assumption.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_a_neg. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
lra. assumption. assumption.
}

{
destruct (0 <? rm12 θ1 ξ θ2) eqn:eq5.
rewrite sin_PI2. rewrite cos_PI2.
assert ((((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    0 -
    -
    (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
    1) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))

= (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
  (/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
   * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))).
rewrite Rinv_r. lra.
assumption.
rewrite H. clear H.
assert (((-
   (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
   0 +
   (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   1) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
=
(cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
 (/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
  * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
  * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) ))).
rewrite Rinv_r. lra.
assumption.
rewrite H. clear H.
assert ((/
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
    (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))
 = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) *

/ √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²)).
assert (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²
 = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
     * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite sqrt_mult_alt.
rewrite sqrt_mult_alt.
rewrite Rinv_mult_distr. lra.
assumption. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite H. clear H.
rewrite sqrt_Rsqr.
specialize (sin_cos_q θ1 ξ θ2) as eq6.
assert (((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²) * / 4
     = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite <- H. clear H.
apply Rltb_le_false in eq3.
apply Rltb_le_false in eq4.
assert (rm02 θ1 ξ θ2 = 0) by lra.
rewrite rm02_eq in H.
rewrite H.
apply Rltb_lt in eq5.
assert (√ ((0² + (sin ξ)² * (sin θ2)²) * / 4) = sin ξ * sin θ2 * / 2).
rewrite <- Rsqr_mult.
assert (Rsqr 0 = 0). unfold Rsqr. lra.
rewrite H6.
autorewrite with R_db.
rewrite sqrt_mult_alt.
rewrite  sqrt_Rsqr.
rewrite <- inv_sqrt.
assert (4 = Rsqr 2). unfold Rsqr. lra.
rewrite H7. 
rewrite  sqrt_Rsqr. reflexivity.
lra. lra. 
rewrite rm12_eq in eq5.
lra.
apply Rle_0_sqr.
rewrite H6. clear H6.
rewrite <- (Rmult_assoc (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite <- (Rmult_assoc (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * sin θ2 * / 2)
   = ((2 * sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) * /2)).
assert (θ2 = 2 * (θ2/2)) by lra.
assert (sin θ2 = sin (2 * (θ2/2))). rewrite <- H6. reflexivity.
rewrite H7. rewrite sin_2a. lra.
rewrite H6. clear H6.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * (sin ξ * sin θ2 * / 2)
 = (2 * sin ξ * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) * / 2).
assert (θ2 = 2 * (θ2/2)) by lra.
assert (sin θ2 = sin (2 * (θ2/2))). rewrite <- H6. reflexivity.
rewrite H7. rewrite sin_2a. lra.
rewrite H6. clear H6.
rewrite <- cos_sin_mult_q_l.
rewrite <- cos_sin_mult_q_r.
rewrite (Rmult_assoc ((sin (θ1 / 2) * cos (θ2 / 2) + cos ξ * cos (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc ((sin (θ1 / 2) * cos (θ2 / 2) + cos ξ * cos (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc (2 *
    ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite <- Rinv_mult_distr.
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * cos (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_assoc (sin ξ * cos (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_assoc (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite <- Rinv_mult_distr.
rewrite Rinv_r. lca.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra. assumption. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
destruct (rm12 θ1 ξ θ2 <? 0) eqn:eq6.

assert ((- PI / 2) = - (PI / 2)) by lra.
rewrite H. clear H.
rewrite sin_neg. rewrite cos_neg.
rewrite sin_PI2. rewrite cos_PI2.
assert ((((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    0 -
    -
    (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
    - (1)) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))

= (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
  (/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
   * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))).
rewrite Rinv_r. lra.
assumption.
rewrite H. clear H.
assert (((-
   (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
   0 +
   (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   - (1)) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
=
(-(cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
 (/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
  * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
  * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) )))).
rewrite Rinv_r. lra.
assumption.
rewrite H. clear H.
assert ((/
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
    (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))
 = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) *

/ √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²)).
assert (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²
 = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
     * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite sqrt_mult_alt.
rewrite sqrt_mult_alt.
rewrite Rinv_mult_distr. lra.
assumption. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite H. clear H.
rewrite sqrt_Rsqr.
specialize (sin_cos_q θ1 ξ θ2) as eq7.
assert (((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²) * / 4
     = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite <- H. clear H.
apply Rltb_le_false in eq3.
apply Rltb_le_false in eq4.
assert (rm02 θ1 ξ θ2 = 0) by lra.
rewrite rm02_eq in H.
rewrite H.
apply Rltb_lt in eq6.
assert (√ ((0² + (sin ξ)² * (sin θ2)²) * / 4) = (-(sin ξ * sin θ2)) * / 2).
rewrite <- Rsqr_mult.
assert (Rsqr 0 = 0). unfold Rsqr. lra.
rewrite H6.
autorewrite with R_db.
rewrite sqrt_mult_alt.
rewrite Rsqr_neg.
rewrite  sqrt_Rsqr.
rewrite <- inv_sqrt.
assert (4 = Rsqr 2). unfold Rsqr. lra.
rewrite H7. 
rewrite  sqrt_Rsqr. lra.
lra. lra. 
rewrite rm12_eq in eq6.
lra.
apply Rle_0_sqr.
rewrite H6. clear H6.
rewrite <- (Rmult_assoc (-sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite <- (Rmult_assoc (-(cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
assert (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (- (sin ξ * sin θ2) * / 2)
   = ((2 * sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) * /2)).
assert (θ2 = 2 * (θ2/2)) by lra.
assert (sin θ2 = sin (2 * (θ2/2))). rewrite <- H6. reflexivity.
rewrite H7. rewrite sin_2a. lra.
rewrite H6. clear H6.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
  (- (sin ξ * sin θ2) * / 2))
 = (2 * sin ξ * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) * / 2).
assert (θ2 = 2 * (θ2/2)) by lra.
assert (sin θ2 = sin (2 * (θ2/2))). rewrite <- H6. reflexivity.
rewrite H7. rewrite sin_2a. lra.
rewrite H6. clear H6.
rewrite <- cos_sin_mult_q_l.
rewrite <- cos_sin_mult_q_r.
rewrite (Rmult_assoc ((sin (θ1 / 2) * cos (θ2 / 2) + cos ξ * cos (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc ((sin (θ1 / 2) * cos (θ2 / 2) + cos ξ * cos (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc (2 *
    ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite <- Rinv_mult_distr.
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * cos (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_assoc (sin ξ * cos (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_assoc (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite <- Rinv_mult_distr.
rewrite Rinv_r. lca.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra. assumption. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite sin_0. rewrite cos_0.
assert ((((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    1 -
    -
    (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
    0) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
= (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
  (/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
   * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))).
rewrite Rinv_r. lra.
assumption.
rewrite H. clear H.
assert (((-
   (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
   1 +
   (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   0) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
=
(-(sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * 
 (/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
  * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
  * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) ))))).
rewrite Rinv_r. lra.
assumption.
rewrite H. clear H.
assert ((/
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
    (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))
 = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) *

/ √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²)).
assert (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²
 = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
     * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite sqrt_mult_alt.
rewrite sqrt_mult_alt.
rewrite Rinv_mult_distr. lra.
assumption. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite H. clear H.
rewrite sqrt_Rsqr.
specialize (sin_cos_q θ1 ξ θ2) as eq7.
assert (((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²) * / 4
     = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite <- H. clear H.
apply Rltb_le_false in eq3.
apply Rltb_le_false in eq4.
assert (rm02 θ1 ξ θ2 = 0) by lra.
rewrite rm02_eq in H.
rewrite H.
apply Rltb_le_false in eq5.
apply Rltb_le_false in eq6.
assert (rm12 θ1 ξ θ2 = 0) by lra.
rewrite rm12_eq in H6.
assert ((sin ξ)² * (sin θ2)² = (sin ξ * sin θ2)²).
rewrite Rsqr_mult. reflexivity.
rewrite H7. clear H7.
rewrite H6.
assert (√ ((0² + 0²) * / 4) = 0). 
unfold Rsqr. rewrite sqrt_mult_alt.
assert ((0 * 0 + 0 * 0) = 0) by lra.
rewrite H7.  rewrite sqrt_0. lra. lra.
assert ((-
 (cos (θ2 / 2) * sin (θ1 / 2) +
  sin (θ2 / 2) * ((cos ξ * cos (θ1 / 2))%R, (sin ξ * cos (θ1 / 2))%R)))%C
 = (- ((sin (θ1 / 2) * cos (θ2 / 2) + cos ξ * cos (θ1 / 2) * sin (θ2 / 2))%R,
         (sin ξ * cos (θ1 / 2) * sin (θ2 / 2))%R))%C) by lca.
rewrite H8.
specialize (cos_sin_mult_q_l θ1 ξ θ2 H) as eq8.
apply (Rmult_eq_compat_r (/ (2 *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))) in eq8.
rewrite Rmult_assoc in eq8.
rewrite Rinv_r in eq8.
rewrite Rmult_1_r in eq8.
rewrite eq8.
specialize (cos_sin_mult_q_r θ1 ξ θ2 H) as eq9.
apply (Rmult_eq_compat_r (/ (2 *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))) in eq9.
rewrite Rmult_assoc in eq9.
rewrite Rinv_r in eq9.
rewrite Rmult_1_r in eq9.
rewrite eq9.
assert (2 * sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = (sin ξ * sin θ2) * sin ξ * sin (θ1 / 2) * sin (θ2 / 2)).
assert (θ2 = 2 * (θ2/2)) by lra.
assert (sin θ2 = sin (2 * (θ2/2))). rewrite <- H9. reflexivity.
rewrite H10. rewrite sin_2a. lra.
rewrite H9.
rewrite H6.
assert ((2 * sin ξ * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * sin ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2))
 = (sin ξ * sin θ2) * (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2) )).
assert (θ2 = 2 * (θ2/2)) by lra.
assert (sin θ2 = sin (2 * (θ2/2))). rewrite <- H10. reflexivity.
rewrite H11. rewrite sin_2a. lra.
rewrite H10.
rewrite H6.
rewrite H7. lca.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
}
apply delta_cos_bound.
assumption.
Qed.

Lemma rm22_rewrite_case_2:
  forall (θ1 ξ θ2 :R),
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
        (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0 ->
(sin (θ2 / 2) * cos (θ1 / 2) +
 cos (θ2 / 2) * ((cos ξ * sin (θ1 / 2))%R, (sin ξ * sin (θ1 / 2))%R))%C =
((cos
    (acos
       ((cos (θ1 / 2) * cos (θ2 / 2) -
         cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
        √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
           (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
  cos (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)) -
  -
  (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
      (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
  sin (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2))) *
 √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²),
(-
 (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
 cos (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)) +
 cos
   (acos
      ((cos (θ1 / 2) * cos (θ2 / 2) -
        cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
 sin (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2))) *
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
   (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
Proof.
intros.
rename H into H0.
assert (θ1=θ1) as H1 by lra .
assert (0 <= √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
        (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) as H2.
apply sqrt_pos.
assert (θ2=θ2) as H3 by lra.
assert (ξ=ξ) as H4 by lra.
assert (ξ=ξ) as H5 by lra.
rewrite cos_acos.
unfold atan2.
destruct (0 <? rm20_minus θ1 ξ θ2) eqn:eq3.
{
apply Rltb_lt in eq3.
rewrite rm21_cos.
rewrite rm21_sin.
rewrite  Rmult_plus_distr_r.
remember (√ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)) as p.
rewrite sin_cos_q_rm20 in Heqp.
assert ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)
   = (2 * (cos (θ1/2) * cos (θ1/2) - sin (θ1/2) * sin (θ1/2)) * sin (θ2 / 2) * cos (θ2 / 2)
       + 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2/2) * cos (θ2/2) - sin (θ2/2) * sin (θ2/2)))).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (θ2 = 2 * (θ2/2)) by lra.
assert ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)
  = cos (2 * (θ1/2)) * sin (2 * (θ2/2)) + cos ξ * sin (2 * (θ1/2)) * cos (2 * (θ2/2))).
rewrite <- H. rewrite <- H6. reflexivity.
rewrite H7.
rewrite sin_2a.
rewrite sin_2a.
rewrite cos_2a.
rewrite cos_2a.
lra.
rewrite H. clear H.
assert (sin θ1 = 2 * sin (θ1/2) * cos (θ1/2)).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (sin θ1 = sin (2 * (θ1/2))).
rewrite <- H. reflexivity.
rewrite H6.
rewrite sin_2a. reflexivity.
rewrite H. 
assert ((-
(sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
((2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) *
  sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) *
  (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2))) / p) *
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
   (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) +
(cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
   (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
(sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)) / p) *
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
   (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))%R
=
((((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) *
  sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) *
  (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)))
+ (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))))
* 
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
* / (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
* / p)%R) by lra.
rewrite H6. clear H6.
assert ((cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2))
   = (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)).
rewrite <- cos_2a. rewrite -> cos_2a_cos. reflexivity.
rewrite H6. clear H6.
assert ((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
  cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)) +
 (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))))
=
sin ξ * sin (θ1 / 2) * cos (θ2 / 2) *
 (2 * ((Rsqr (cos (θ1 / 2))) * (1 - (Rsqr (sin (θ2 / 2)))) + (Rsqr (sin (θ1 / 2))) * (Rsqr (sin (θ2 / 2))))
  - 4 * (cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)))).
assert ((cos (θ1 / 2))² * (1 - (sin (θ2 / 2))²)
    = (cos (θ1 / 2))² - (cos (θ1 / 2))² * (sin (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H6.
unfold Rsqr.
lra.
assert ((1 - (sin (θ2 / 2))²) = (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as H7.
rewrite <- H7. lra.
rewrite H7 in H6. rewrite H6.
clear H7. clear H6.
assert ((2 * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
 4 * (cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2))) 
   = 2 * Rsqr (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite Rsqr_sqrt.
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus.
rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
  = ((sin (ξ / 2))² + (cos (ξ / 2))²) *
    ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
  - 2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))
       * (sin (θ1 / 2) * sin (θ2 / 2)))) by lra.
rewrite H6. clear H6.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra. rewrite H6. reflexivity.
rewrite H6.
unfold Rsqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²) by apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²) by apply Rle_0_sqr.
lra.
rewrite H6. clear H6.
rewrite  sqrt_mult_alt in Heqp.
assert (√ 4 = 2). assert (4 = Rsqr 2). unfold Rsqr. lra.
rewrite H6. rewrite sqrt_Rsqr. reflexivity. lra.
rewrite H6 in Heqp. clear H6.
assert ((√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))²
 = (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
unfold Rsqr. lra.
rewrite H6. clear H6.
assert ((sin ξ * sin (θ1 / 2) * cos (θ2 / 2) *
(2 *
 (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) * / p)
= 
(sin ξ * sin (θ1 / 2) * cos (θ2 / 2) *
  ((2 *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
   * / p) *
  (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))) by lra.
rewrite H6. clear H6.
rewrite <- sqrt_mult.
rewrite Heqp.
rewrite Rinv_r. rewrite Rinv_r. 
assert (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
  ((2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)) /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))) -
  -
  (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
  (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)) /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))) *
 √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
= 
 (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
 * (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)))
 + (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))))
 * (√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
* (/ (2 *
      √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
         ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
* / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite H6. clear H6.
rewrite <- Rinv_mult_distr.
rewrite (Rmult_assoc 2 (√ (((sin (ξ / 2))² 
       * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))).
rewrite <- sqrt_mult_alt.
assert (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
  (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
   cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)) +
  sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))))
 = (sin (θ2 / 2) * cos (θ1 / 2) + cos ξ * cos (θ2 / 2) * sin (θ1 / 2))
   * (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite cos_plus.
rewrite cos_minus.
rewrite (Rsqr_plus (cos (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rsqr_minus (cos (θ1 / 2) * cos (θ2 / 2))).
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
= ((sin (ξ / 2))² + (cos (ξ / 2))²) *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
  - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H6. clear H6.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H6. reflexivity.
rewrite H6.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite <- cos_2a.
rewrite <- cos_2a_cos.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_1_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_r.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos (2 * (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
rewrite cos_2a. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
  = - 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²
    + 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)).
assert ((cos  (θ2 / 2))² = 1 - (sin  (θ2 / 2))²).
specialize (sin2_cos2 ( (θ2 / 2))). lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (2 * (θ2 / 2)))
 = 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
rewrite cos_2a. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²
  = -2 * cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² * (sin (θ1 / 2))²
+2 * cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin  (θ1 / 2))² = 1 - (cos  (θ1 / 2))²).
specialize (sin2_cos2 ( (θ1 / 2))). lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (- (cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * (2 * cos (2 * (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2))
 = - 4 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
+ 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
rewrite cos_2a_cos. lra.
rewrite H7. clear H7.
assert (- (cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (2 * (θ2 / 2)))
= - 4 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
+ 2 * (cos ξ)² * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)).
rewrite cos_2a_cos. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)
 = 2 * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)
   - 2 * (sin ξ) * (sin ξ) * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
unfold Rsqr. lra.
rewrite H6. clear H6.
assert ((2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
 = (2 * √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²))).
rewrite sqrt_Rsqr. reflexivity.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite H6. clear H6.
assert (((sin (θ2 / 2) * cos (θ1 / 2) + cos ξ * cos (θ2 / 2) * sin (θ1 / 2)) *
   (2 * √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))
 = (sin (θ2 / 2) * cos (θ1 / 2) + cos ξ * cos (θ2 / 2) * sin (θ1 / 2)) *
  ((2 * (√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
         * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
     * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
  * /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
unfold Rsqr. lra.
rewrite H6. clear H6.
rewrite <- sqrt_mult_alt.
assert ((((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
  = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
        ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
        ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite H6. clear H6.
rewrite Rinv_r. lca.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_rm20. assumption. assumption.
apply  Rmult_le_pos.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
apply  Rmult_le_pos.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_a_rm20. assumption.
assumption. assumption.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_a_rm20. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
lra. assumption. assumption.
}
destruct (rm20_minus θ1 ξ θ2 <? 0) eqn:eq4.
apply Rltb_lt in eq4.
destruct (0 <=? rm21 θ1 ξ θ2) eqn:eq5.
apply Rleb_le in eq5.
{
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + PI) = PI + atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2)) by lra.
rewrite H. clear H.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite rm21_cos_neg.
rewrite rm21_sin_neg.
rewrite  Rmult_plus_distr_r.
remember (√ ((-(cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2))² + (sin ξ)² * (sin θ1)²)) as p.
specialize (sin_cos_q_rm20 θ1 ξ θ2) as eq6.
rewrite (Rsqr_neg (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)) in eq6.
rewrite eq6 in Heqp.
assert ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)
   = (2 * (cos (θ1/2) * cos (θ1/2) - sin (θ1/2) * sin (θ1/2)) * sin (θ2 / 2) * cos (θ2 / 2)
       + 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2/2) * cos (θ2/2) - sin (θ2/2) * sin (θ2/2)))).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (θ2 = 2 * (θ2/2)) by lra.
assert ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)
  = cos (2 * (θ1/2)) * sin (2 * (θ2/2)) + cos ξ * sin (2 * (θ1/2)) * cos (2 * (θ2/2))).
rewrite <- H. rewrite <- H6. reflexivity.
rewrite H7.
rewrite sin_2a.
rewrite sin_2a.
rewrite cos_2a.
rewrite cos_2a.
lra.
rewrite H. clear H.
assert (- (- (sin ξ * sin θ1) / p) = (sin ξ * sin θ1) / p) by lra.
rewrite H. clear H.
assert (- (-
   (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
    cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) *
    (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2))) / p) 
 = (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
    cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) *
    (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2))) / p) by lra.
rewrite H. clear H.
assert (sin θ1 = 2 * sin (θ1/2) * cos (θ1/2)).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (sin θ1 = sin (2 * (θ1/2))).
rewrite <- H. reflexivity.
rewrite H6.
rewrite sin_2a. reflexivity.
rewrite H. 
assert ((-
(sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
((2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) *
  sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) *
  (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2))) / p) *
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
   (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) +
(cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
   (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
(sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)) / p) *
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
   (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))%R
=
((((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) *
  sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) *
  (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)))
+ (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))))
* 
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
* / (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
* / p)%R) by lra.
rewrite H6. clear H6.
assert ((cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2))
   = (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)).
rewrite <- cos_2a. rewrite -> cos_2a_cos. reflexivity.
rewrite H6. clear H6.
assert ((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
  cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)) +
 (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))))
=
sin ξ * sin (θ1 / 2) * cos (θ2 / 2) *
 (2 * ((Rsqr (cos (θ1 / 2))) * (1 - (Rsqr (sin (θ2 / 2)))) + (Rsqr (sin (θ1 / 2))) * (Rsqr (sin (θ2 / 2))))
  - 4 * (cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)))).
assert ((cos (θ1 / 2))² * (1 - (sin (θ2 / 2))²)
    = (cos (θ1 / 2))² - (cos (θ1 / 2))² * (sin (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H6.
unfold Rsqr.
lra.
assert ((1 - (sin (θ2 / 2))²) = (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as H7.
rewrite <- H7. lra.
rewrite H7 in H6. rewrite H6.
clear H7. clear H6.
assert ((2 * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
 4 * (cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2))) 
   = 2 * Rsqr (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite Rsqr_sqrt.
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus.
rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
  = ((sin (ξ / 2))² + (cos (ξ / 2))²) *
    ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
  - 2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))
       * (sin (θ1 / 2) * sin (θ2 / 2)))) by lra.
rewrite H6. clear H6.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra. rewrite H6. reflexivity.
rewrite H6.
unfold Rsqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²) by apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²) by apply Rle_0_sqr.
lra.
rewrite H6. clear H6.
rewrite  sqrt_mult_alt in Heqp.
assert (√ 4 = 2). assert (4 = Rsqr 2). unfold Rsqr. lra.
rewrite H6. rewrite sqrt_Rsqr. reflexivity. lra.
rewrite H6 in Heqp. clear H6.
assert ((√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))²
 = (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
unfold Rsqr. lra.
rewrite H6. clear H6.
assert ((sin ξ * sin (θ1 / 2) * cos (θ2 / 2) *
(2 *
 (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) * / p)
= 
(sin ξ * sin (θ1 / 2) * cos (θ2 / 2) *
  ((2 *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
   * / p) *
  (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))) by lra.
rewrite H6. clear H6.
rewrite <- sqrt_mult.
rewrite Heqp.
rewrite Rinv_r. rewrite Rinv_r. 
assert (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
  ((2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)) /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))) -
  -
  (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
  (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)) /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))) *
 √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
= 
 (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
 * (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)))
 + (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))))
 * (√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
* (/ (2 *
      √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
         ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
* / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite H6. clear H6.
rewrite <- Rinv_mult_distr.
rewrite (Rmult_assoc 2 (√ (((sin (ξ / 2))² 
       * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))).
rewrite <- sqrt_mult_alt.
assert (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
  (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
   cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)) +
  sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))))
 = (sin (θ2 / 2) * cos (θ1 / 2) + cos ξ * cos (θ2 / 2) * sin (θ1 / 2))
   * (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite cos_plus.
rewrite cos_minus.
rewrite (Rsqr_plus (cos (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rsqr_minus (cos (θ1 / 2) * cos (θ2 / 2))).
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
= ((sin (ξ / 2))² + (cos (ξ / 2))²) *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
  - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H6. clear H6.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H6. reflexivity.
rewrite H6.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite <- cos_2a.
rewrite <- cos_2a_cos.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_1_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_r.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos (2 * (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
rewrite cos_2a. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
  = - 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²
    + 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)).
assert ((cos  (θ2 / 2))² = 1 - (sin  (θ2 / 2))²).
specialize (sin2_cos2 ( (θ2 / 2))). lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (2 * (θ2 / 2)))
 = 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
rewrite cos_2a. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²
  = -2 * cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² * (sin (θ1 / 2))²
+2 * cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin  (θ1 / 2))² = 1 - (cos  (θ1 / 2))²).
specialize (sin2_cos2 ( (θ1 / 2))). lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (- (cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * (2 * cos (2 * (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2))
 = - 4 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
+ 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
rewrite cos_2a_cos. lra.
rewrite H7. clear H7.
assert (- (cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (2 * (θ2 / 2)))
= - 4 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
+ 2 * (cos ξ)² * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)).
rewrite cos_2a_cos. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)
 = 2 * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)
   - 2 * (sin ξ) * (sin ξ) * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
unfold Rsqr. lra.
rewrite H6. clear H6.
assert ((2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
 = (2 * √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²))).
rewrite sqrt_Rsqr. reflexivity.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite H6. clear H6.
assert (((sin (θ2 / 2) * cos (θ1 / 2) + cos ξ * cos (θ2 / 2) * sin (θ1 / 2)) *
   (2 * √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))
 = (sin (θ2 / 2) * cos (θ1 / 2) + cos ξ * cos (θ2 / 2) * sin (θ1 / 2)) *
  ((2 * (√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
         * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
     * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
  * /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
unfold Rsqr. lra.
rewrite H6. clear H6.
rewrite <- sqrt_mult_alt.
assert ((((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
  = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
        ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
        ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite H6. clear H6.
rewrite Rinv_r. lca.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_neg_rm20. assumption. assumption.
apply  Rmult_le_pos.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
apply  Rmult_le_pos.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_a_neg_rm20. assumption.
assumption. assumption.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_a_neg_rm20. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
lra. assumption. assumption.
}

{
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) - PI) = -(PI - atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2))) by lra.
rewrite H. clear H.
rewrite sin_neg.
rewrite cos_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite rm21_cos_neg.
rewrite rm21_sin_neg.
rewrite  Rmult_plus_distr_r.
remember (√ ((-(cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2))² + (sin ξ)² * (sin θ1)²)) as p.
specialize (sin_cos_q_rm20 θ1 ξ θ2) as eq6.
rewrite (Rsqr_neg (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)) in eq6.
rewrite eq6 in Heqp.
assert ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)
   = (2 * (cos (θ1/2) * cos (θ1/2) - sin (θ1/2) * sin (θ1/2)) * sin (θ2 / 2) * cos (θ2 / 2)
       + 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2/2) * cos (θ2/2) - sin (θ2/2) * sin (θ2/2)))).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (θ2 = 2 * (θ2/2)) by lra.
assert ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)
  = cos (2 * (θ1/2)) * sin (2 * (θ2/2)) + cos ξ * sin (2 * (θ1/2)) * cos (2 * (θ2/2))).
rewrite <- H. rewrite <- H6. reflexivity.
rewrite H7.
rewrite sin_2a.
rewrite sin_2a.
rewrite cos_2a.
rewrite cos_2a.
lra.
rewrite H. clear H.
assert (- (- (sin ξ * sin θ1) / p) = (sin ξ * sin θ1) / p) by lra.
rewrite H. clear H.
assert (- (-
   (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
    cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) *
    (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2))) / p) 
 = (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
    cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) *
    (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2))) / p) by lra.
rewrite H. clear H.
assert (sin θ1 = 2 * sin (θ1/2) * cos (θ1/2)).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (sin θ1 = sin (2 * (θ1/2))).
rewrite <- H. reflexivity.
rewrite H6.
rewrite sin_2a. reflexivity.
rewrite H. 
assert ((-
(sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
((2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) *
  sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) *
  (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2))) / p) *
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
   (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) +
(cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
   (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
(sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)) / p) *
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
   (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))%R
=
((((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) *
  sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) *
  (cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2)))
+ (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))))
* 
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
* / (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
* / p)%R) by lra.
rewrite H6. clear H6.
assert ((cos (θ2 / 2) * cos (θ2 / 2) - sin (θ2 / 2) * sin (θ2 / 2))
   = (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)).
rewrite <- cos_2a. rewrite -> cos_2a_cos. reflexivity.
rewrite H6. clear H6.
assert ((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
  cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)) +
 (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))))
=
sin ξ * sin (θ1 / 2) * cos (θ2 / 2) *
 (2 * ((Rsqr (cos (θ1 / 2))) * (1 - (Rsqr (sin (θ2 / 2)))) + (Rsqr (sin (θ1 / 2))) * (Rsqr (sin (θ2 / 2))))
  - 4 * (cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)))).
assert ((cos (θ1 / 2))² * (1 - (sin (θ2 / 2))²)
    = (cos (θ1 / 2))² - (cos (θ1 / 2))² * (sin (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H6.
unfold Rsqr.
lra.
assert ((1 - (sin (θ2 / 2))²) = (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as H7.
rewrite <- H7. lra.
rewrite H7 in H6. rewrite H6.
clear H7. clear H6.
assert ((2 * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
 4 * (cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2))) 
   = 2 * Rsqr (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite Rsqr_sqrt.
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus.
rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
  = ((sin (ξ / 2))² + (cos (ξ / 2))²) *
    ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
  - 2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))
       * (sin (θ1 / 2) * sin (θ2 / 2)))) by lra.
rewrite H6. clear H6.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra. rewrite H6. reflexivity.
rewrite H6.
unfold Rsqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²) by apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²) by apply Rle_0_sqr.
lra.
rewrite H6. clear H6.
rewrite  sqrt_mult_alt in Heqp.
assert (√ 4 = 2). assert (4 = Rsqr 2). unfold Rsqr. lra.
rewrite H6. rewrite sqrt_Rsqr. reflexivity. lra.
rewrite H6 in Heqp. clear H6.
assert ((√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))²
 = (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
unfold Rsqr. lra.
rewrite H6. clear H6.
assert ((sin ξ * sin (θ1 / 2) * cos (θ2 / 2) *
(2 *
 (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) * / p)
= 
(sin ξ * sin (θ1 / 2) * cos (θ2 / 2) *
  ((2 *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
   * / p) *
  (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))) by lra.
rewrite H6. clear H6.
rewrite <- sqrt_mult.
rewrite Heqp.
rewrite Rinv_r. rewrite Rinv_r. 
assert (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
  ((2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)) /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))) -
  -
  (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
  (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)) /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))) *
 √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
= 
 (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
 * (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)))
 + (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))))
 * (√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
* (/ (2 *
      √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
         ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
* / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite H6. clear H6.
rewrite <- Rinv_mult_distr.
rewrite (Rmult_assoc 2 (√ (((sin (ξ / 2))² 
       * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))).
rewrite <- sqrt_mult_alt.
assert (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
  (2 * (cos (θ1 / 2) * cos (θ1 / 2) - sin (θ1 / 2) * sin (θ1 / 2)) * sin (θ2 / 2) *
   cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (2 * cos (θ2 / 2) * cos (θ2 / 2) - 1)) +
  sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))))
 = (sin (θ2 / 2) * cos (θ1 / 2) + cos ξ * cos (θ2 / 2) * sin (θ1 / 2))
   * (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite cos_plus.
rewrite cos_minus.
rewrite (Rsqr_plus (cos (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rsqr_minus (cos (θ1 / 2) * cos (θ2 / 2))).
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
= ((sin (ξ / 2))² + (cos (ξ / 2))²) *
  ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
  - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 
   2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H6. clear H6.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H6. reflexivity.
rewrite H6.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite <- cos_2a.
rewrite <- cos_2a_cos.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_1_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_r.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_l.
rewrite Rmult_plus_distr_r.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos (2 * (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
rewrite cos_2a. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
  = - 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²
    + 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)).
assert ((cos  (θ2 / 2))² = 1 - (sin  (θ2 / 2))²).
specialize (sin2_cos2 ( (θ2 / 2))). lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (2 * (θ2 / 2)))
 = 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
rewrite cos_2a. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²
  = -2 * cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² * (sin (θ1 / 2))²
+2 * cos ξ * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin  (θ1 / 2))² = 1 - (cos  (θ1 / 2))²).
specialize (sin2_cos2 ( (θ1 / 2))). lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (- (cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * (2 * cos (2 * (θ1 / 2)) * sin (θ2 / 2) * cos (θ2 / 2))
 = - 4 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
+ 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
rewrite cos_2a_cos. lra.
rewrite H7. clear H7.
assert (- (cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (2 * (θ2 / 2)))
= - 4 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
+ 2 * (cos ξ)² * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)).
rewrite cos_2a_cos. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)
 = 2 * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)
   - 2 * (sin ξ) * (sin ξ) * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
unfold Rsqr. lra.
rewrite H6. clear H6.
assert ((2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
 = (2 * √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²))).
rewrite sqrt_Rsqr. reflexivity.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite H6. clear H6.
assert (((sin (θ2 / 2) * cos (θ1 / 2) + cos ξ * cos (θ2 / 2) * sin (θ1 / 2)) *
   (2 * √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
   /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))
 = (sin (θ2 / 2) * cos (θ1 / 2) + cos ξ * cos (θ2 / 2) * sin (θ1 / 2)) *
  ((2 * (√ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
         * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
     * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))
  * /
   (2 *
    √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
unfold Rsqr. lra.
rewrite H6. clear H6.
rewrite <- sqrt_mult_alt.
assert ((((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
  = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
        ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
        ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite H6. clear H6.
rewrite Rinv_r. lca.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_neg_rm20. assumption. assumption.
apply  Rmult_le_pos.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
apply  Rmult_le_pos.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_a_neg_rm20. assumption.
assumption. assumption.
apply  Rmult_integral_contrapositive.
split. lra.
apply sqrt_term_neq_0_a_neg_rm20. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
lra. assumption. assumption.
}

{
destruct (0 <? rm21 θ1 ξ θ2) eqn:eq5.
rewrite sin_PI2. rewrite cos_PI2.
assert (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) * 0 -
  -
  (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
  1) *
 √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)

= (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
  (/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
   * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))).
rewrite Rinv_r. lra.
assumption.
rewrite H. clear H.
assert ((-
 (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
 0 +
 (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) * 1) *
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
=
(cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
 (/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
  * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
  * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) ))).
rewrite Rinv_r. lra.
assumption.
rewrite H. clear H.
assert ((/
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
    (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))
 = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) *

/ √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²)).
assert (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²
 = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
     * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite sqrt_mult_alt.
rewrite sqrt_mult_alt.
rewrite Rinv_mult_distr. lra.
assumption. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite H. clear H.
rewrite sqrt_Rsqr.
specialize (sin_cos_q θ1 ξ θ2) as eq6.
assert (((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²) * / 4
     = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite <- H. clear H.
apply Rltb_le_false in eq3.
apply Rltb_le_false in eq4.
assert (rm20_minus θ1 ξ θ2 = 0) by lra.
rewrite <- rm02_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm12_eq θ1 ξ θ2).
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²).
unfold rm02,rm20_minus,rm12,rm21.
unfold Rsqr. lra.
rewrite H6.
rewrite Rltb_lt in eq5.
rewrite H.
rewrite rm21_eq.
rewrite Rsqr_mult.
assert (√ ((0² + (sin ξ)² * (sin θ1)²) * / 4) = sin ξ * sin θ1 * / 2).
rewrite <- Rsqr_mult.
assert (Rsqr 0 = 0). unfold Rsqr. lra.
rewrite H7.
autorewrite with R_db.
rewrite sqrt_mult_alt.
rewrite  sqrt_Rsqr.
rewrite <- inv_sqrt.
assert (4 = Rsqr 2). unfold Rsqr. lra.
rewrite H8. 
rewrite  sqrt_Rsqr. reflexivity.
lra. lra. 
rewrite rm21_eq in eq5.
lra.
apply Rle_0_sqr.
rewrite H7. clear H7.
rewrite <- (Rmult_assoc (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite <- (Rmult_assoc (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin ξ * sin θ1 * / 2)
   = ((2 * sin ξ * sin ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)) * /2)).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (sin θ1 = sin (2 * (θ1/2))). rewrite <- H7. reflexivity.
rewrite H8. rewrite sin_2a. lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * (sin ξ * sin θ1 * / 2)
 = (2 * sin ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)) * / 2).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (sin θ1 = sin (2 * (θ1/2))). rewrite <- H7. reflexivity.
rewrite H8. rewrite sin_2a. lra.
rewrite H7. clear H7.
rewrite <- cos_sin_mult_q_l_rm20.
rewrite <- cos_sin_mult_q_r_rm20.
rewrite (Rmult_assoc ((cos (θ1 / 2) * sin (θ2 / 2) + cos ξ * sin (θ1 / 2) * cos (θ2 / 2)))).
rewrite (Rmult_assoc ((cos (θ1 / 2) * sin (θ2 / 2) + cos ξ * sin (θ1 / 2) * cos (θ2 / 2)))).
rewrite (Rmult_assoc (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite <- Rinv_mult_distr.
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * sin (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rmult_assoc (sin ξ * sin (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rmult_assoc (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite <- Rinv_mult_distr.
rewrite Rinv_r. lca.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra. 
rewrite rm20_eq in H.
assumption. 
rewrite rm20_eq in H.
assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.

destruct (rm21 θ1 ξ θ2 <? 0) eqn:eq6.
assert ((- PI / 2) = - (PI / 2)) by lra.
rewrite H. clear H.
rewrite sin_neg. rewrite cos_neg.
rewrite sin_PI2. rewrite cos_PI2.
assert (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) * 0 -
  -
  (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
  - (1)) *
 √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)

= (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
  (/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
   * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))).
rewrite Rinv_r. lra.
assumption.
rewrite H. clear H.
assert ((-
 (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
 0 +
 (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
 - (1)) *
√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
=
(-(cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
 (/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
  * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
  * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) )))).
rewrite Rinv_r. lra.
assumption.
rewrite H. clear H.
assert ((/
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
    (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))
 = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) *

/ √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²)).
assert (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²
 = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
     * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite sqrt_mult_alt.
rewrite sqrt_mult_alt.
rewrite Rinv_mult_distr. lra.
assumption. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite H. clear H.
rewrite sqrt_Rsqr.
specialize (sin_cos_q θ1 ξ θ2) as eq7.
assert (((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²) * / 4
     = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))) by lra.
apply Rltb_le_false in eq3.
apply Rltb_le_false in eq4.
assert (rm20_minus θ1 ξ θ2 = 0) by lra.
rewrite <- rm02_eq in H.
rewrite <- Rsqr_mult in H.
rewrite <- (rm12_eq θ1 ξ θ2) in H.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = ((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H7 in H.
rewrite rm20_eq in H.
rewrite rm21_eq in H.
rewrite Rsqr_mult in H.
rewrite rm20_eq in H6.
rewrite <- H. clear H.
apply Rltb_lt in eq6.
assert (√ ((0² + (sin ξ)² * (sin θ1)²) * / 4) = (-(sin ξ * sin θ1)) * / 2).
rewrite <- Rsqr_mult.
assert (Rsqr 0 = 0). unfold Rsqr. lra.
rewrite H.
autorewrite with R_db.
rewrite sqrt_mult_alt.
rewrite Rsqr_neg.
rewrite  sqrt_Rsqr.
rewrite <- inv_sqrt.
assert (4 = Rsqr 2). unfold Rsqr. lra.
rewrite H8. 
rewrite  sqrt_Rsqr. lra.
lra. lra. 
rewrite rm21_eq in eq6.
lra.
apply Rle_0_sqr.
rewrite H6. rewrite H. clear H.
rewrite <- (Rmult_assoc (-sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite <- (Rmult_assoc (-(cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
assert (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (- (sin ξ * sin θ1) * / 2)
   = ((2 * sin ξ * sin ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)) * /2)).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (sin θ1 = sin (2 * (θ1/2))). rewrite <- H. reflexivity.
rewrite H8. rewrite sin_2a. lra.
rewrite H. clear H.
assert (- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * (- (sin ξ * sin θ1) * / 2)
 = (2 * sin ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
      2 * sin ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)) * / 2).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (sin θ1 = sin (2 * (θ1/2))). rewrite <- H. reflexivity.
rewrite H8. rewrite sin_2a. lra.
rewrite H. clear H.
rewrite <- cos_sin_mult_q_l_rm20.
rewrite <- cos_sin_mult_q_r_rm20.
rewrite (Rmult_assoc ((cos (θ1 / 2) * sin (θ2 / 2) + cos ξ * sin (θ1 / 2) * cos (θ2 / 2)))).
rewrite (Rmult_assoc ((cos (θ1 / 2) * sin (θ2 / 2) + cos ξ * sin (θ1 / 2) * cos (θ2 / 2)))).
rewrite (Rmult_assoc (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite <- Rinv_mult_distr.
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * sin (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rmult_assoc (sin ξ * sin (θ1 / 2) * cos (θ2 / 2))).
rewrite (Rmult_assoc (2 * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
rewrite <- Rinv_mult_distr.
rewrite Rinv_r. lca.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra. assumption. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite sin_0. rewrite cos_0.
assert ((((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    1 -
    -
    (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
    0) *
   √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
= (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
  (/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
   * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))).
rewrite Rinv_r. lra.
assumption.
rewrite H. clear H.
assert (((-
   (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) *
   1 +
   (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   0) *
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))
=
(-(sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * 
 (/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
  * √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
  * (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) ))))).
rewrite Rinv_r. lra.
assumption.
rewrite H. clear H.
assert ((/
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *
    (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     /
     √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))
 = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) *

/ √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²)).
assert (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)²
 = √ (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
     * ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite sqrt_mult_alt.
rewrite sqrt_mult_alt.
rewrite Rinv_mult_distr. lra.
assumption. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite H. clear H.
rewrite sqrt_Rsqr.
specialize (sin_cos_q θ1 ξ θ2) as eq7.
assert (((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²) * / 4
     = (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
       ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))) by lra.
rewrite <- rm02_eq in H.
rewrite <- Rsqr_mult in H.
rewrite <- (rm12_eq θ1 ξ θ2) in H.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = ((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21,Rsqr.
lra.
rewrite H6 in H. clear H6.
rewrite rm20_eq in H. rewrite rm21_eq in H.
rewrite <- H. clear H.
apply Rltb_le_false in eq3.
apply Rltb_le_false in eq4.
assert (rm20_minus θ1 ξ θ2 = 0) by lra.
rewrite rm20_eq in H.
rewrite H.
apply Rltb_le_false in eq5.
apply Rltb_le_false in eq6.
assert (rm21 θ1 ξ θ2 = 0) by lra.
rewrite rm21_eq in H6.
rewrite H6.
assert (√ ((0² + 0²) * / 4) = 0). 
unfold Rsqr. rewrite sqrt_mult_alt.
assert ((0 * 0 + 0 * 0) = 0) by lra.
rewrite H7.  rewrite sqrt_0. lra. lra.
assert ((sin (θ2 / 2) * cos (θ1 / 2) +
 cos (θ2 / 2) * ((cos ξ * sin (θ1 / 2))%R, (sin ξ * sin (θ1 / 2))%R))%C
 = (((cos (θ1 / 2) * sin (θ2 / 2) + cos ξ * sin (θ1 / 2) * cos (θ2 / 2))%R,
         (sin ξ * sin (θ1 / 2) * cos (θ2 / 2))%R))%C) by lca.
rewrite H8.
specialize (cos_sin_mult_q_l_rm20 θ1 ξ θ2 H) as eq8.
apply (Rmult_eq_compat_r (/ (2 *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))) in eq8.
rewrite Rmult_assoc in eq8.
rewrite Rinv_r in eq8.
rewrite Rmult_1_r in eq8.
rewrite eq8. clear eq8.
specialize (cos_sin_mult_q_r_rm20 θ1 ξ θ2 H) as eq9.
apply (Rmult_eq_compat_r (/ (2 *
       ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))) in eq9.
rewrite Rmult_assoc in eq9.
rewrite Rinv_r in eq9.
rewrite Rmult_1_r in eq9.
rewrite eq9.
assert (2 * sin ξ * sin ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2)
  = (sin ξ * sin θ1) * sin ξ * sin (θ1 / 2) * sin (θ2 / 2)).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (sin θ1 = sin (2 * (θ1/2))). rewrite <- H9. reflexivity.
rewrite H10. rewrite sin_2a. lra.
rewrite H9.
rewrite H6.
assert ((2 * sin ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
 2 * sin ξ * cos ξ * sin (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2))
 = (sin ξ * sin θ1) * (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2) )).
assert (θ1 = 2 * (θ1/2)) by lra.
assert (sin θ1 = sin (2 * (θ1/2))). rewrite <- H10. reflexivity.
rewrite H11. rewrite sin_2a. lra.
rewrite H10.
rewrite H6.
rewrite H7. lca.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra.
assert (0 < ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite <- (Rsqr_sqrt (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
       + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))).
apply Rlt_0_sqr. assumption.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
}
apply delta_cos_bound.
assumption.
Qed.

Lemma rm22_rewrite_case_3: forall (θ1 ξ θ2 : R),
   (rm22 θ1 ξ θ2 <? 1) = true -> (-1 <? rm22 θ1 ξ θ2) = true ->
(- (sin (θ2 / 2) * sin (θ1 / 2)) +
 cos (θ2 / 2) * (Cexp ξ * cos (θ1 / 2)))%C =
(((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))%R,
 (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2))%R) *
 (Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)) *
  Cexp (atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2))))%C.
Proof.
intros.
rename H into eq1.
rename H0 into eq2.
assert (θ1=θ1) as H0 by lra .
assert (θ1=θ1) as H1 by lra .
assert (0 <= √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
        (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) as H2.
apply sqrt_pos.
assert (θ2=θ2) as H3 by lra.
assert (ξ=ξ) as H4 by lra.
assert (ξ=ξ) as H5 by lra.
rewrite <- Cexp_add.
unfold Cexp,atan2.
destruct (0 <? rm20_minus θ1 ξ θ2) eqn:eq3.
destruct (0 <? rm02 θ1 ξ θ2) eqn:eq4.
{
apply Rltb_lt in eq3.
apply Rltb_lt in eq4.
rewrite cos_plus.
rewrite sin_plus.
rewrite rm12_sin.
rewrite rm12_cos.
rewrite rm21_sin.
rewrite rm21_cos.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
rewrite <- (rm20_eq θ1 ξ θ2).
rewrite <- (rm02_eq θ1 ξ θ2).
rewrite <- (rm12_eq θ1 ξ θ2).
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H.
assert ((rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) -
   rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))%R
 = ((rm20_minus θ1 ξ θ2) * (rm02 θ1 ξ θ2) - (rm21 θ1 ξ θ2)
               * (rm12 θ1 ξ θ2)) / ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
assert ((rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) +
  rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))
  =
(rm21 θ1 ξ θ2 * rm02 θ1 ξ θ2 + rm20_minus θ1 ξ θ2 * rm12 θ1 ξ θ2)
       /((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
rewrite rm02_eq. rewrite rm12_eq.
rewrite Rsqr_mult.
rewrite sin_cos_q.
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
unfold rm02,rm12,rm21,rm20_minus.

assert (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
     /\ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) <> 0).
assert ((Rsqr (sin θ1 * cos θ2 + (cos ξ * cos θ1 * sin θ2)) + Rsqr(sin ξ) * Rsqr (sin θ2)) <> 0).
assert (0 < (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²).
rewrite <- rm02_eq.
rewrite <- Rsqr_mult.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt.
lra.
assert (0 <= (sin ξ * sin θ2)²) by apply Rle_0_sqr.
lra. lra.
rewrite sin_cos_q in H6.
apply Rmult_neq_0_reg in H6.
destruct H6.
apply Rmult_neq_0_reg in H7.
lra.
destruct H6.
assert (((-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) -
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (((rw θ1 ξ θ2))² - (rz θ1 ξ θ2 )²) * (((rx θ1 ξ θ2))² + (ry θ1 ξ θ2 )²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) =
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) /
   (4 *
    (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) / 
         ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite Rinv_mult_distr.
rewrite (Rmult_assoc (4 * ((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite (Rmult_comm (((sin (ξ * / 2))² * (sin (θ1 * / 2 + - (θ2 * / 2)))² +
  (cos (ξ * / 2))² * (sin (θ1 * / 2 + θ2 * / 2))²))).
rewrite (Rmult_assoc (/ 4)).
rewrite (Rmult_assoc (/ ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²))).
rewrite <- Rinv_l_sym.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite <- (Rmult_assoc 4).
rewrite Rinv_r.
lra. lra.
assumption. assumption. assumption.
lra.
apply Rmult_integral_contrapositive.
split.
assumption. assumption.
rewrite H8. clear H8.
assert (((2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) +
   (-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (2 * (rw θ1 ξ θ2) * (rz θ1 ξ θ2)) * ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) *
  ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) /
  (4 *
   (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) / 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite (Rmult_comm ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²)).
rewrite <- (Rmult_assoc 4).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite <- Rmult_assoc.
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rinv_r. lra.
apply Rmult_integral_contrapositive.
split. lra. assumption.
apply Rmult_integral_contrapositive.
split. lra. assumption.
assumption.
rewrite H8. clear H8.
assert (((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) =
    cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²)
           - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)).
unfold rw,rz.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = 2 * (ξ/2)) by lra.
rewrite <- H8. reflexivity.
rewrite H8. clear H8.
rewrite cos_2a.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) 
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * ((sin (ξ / 2))² + (cos (ξ / 2))²)).
rewrite sin2_cos2.
lra.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2 = sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
unfold rw,rz.
rewrite (Rmult_assoc 2).
rewrite (Rmult_comm (cos (ξ / 2) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_comm ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc 2). rewrite <- (Rmult_assoc 2).
rewrite <- (Rmult_assoc 2). rewrite <- sin_2a.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * ((cos (θ1 / 2))² * 
                  (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²))
   / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
          ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   = (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * 
       ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H8. unfold Rsqr. lra.
rewrite <- H8. clear H8.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
(sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
   = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) 
  * sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)
  - (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)))
  / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H8. clear H8.
assert (sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
 ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) ).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite <- H8. clear H8.
autorewrite with R_db.
rewrite (Rmult_assoc (- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
assumption. assumption. assumption.
assumption. assumption. assumption.
}
destruct (rm02 θ1 ξ θ2 <? 0) eqn:eq5.
destruct (0 <=? rm12 θ1 ξ θ2) eqn:eq6.
{
apply Rltb_lt in eq3.
apply Rltb_lt in eq5.
apply Rleb_le in eq6.
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2) + PI))
    = (PI + ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2)))))) by lra.
rewrite H. clear H.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_plus.
rewrite sin_plus.
rewrite rm12_sin_neg.
rewrite rm12_cos_neg.
rewrite rm21_sin.
rewrite rm21_cos.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
rewrite <- (rm20_eq θ1 ξ θ2).
rewrite <- (rm02_eq θ1 ξ θ2).
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- Rsqr_neg.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H.
assert ((-
   (rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
    (- rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) -
    rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
    (- rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))))%R
 = ((rm20_minus θ1 ξ θ2) * (rm02 θ1 ξ θ2) - (rm21 θ1 ξ θ2)
               * (rm12 θ1 ξ θ2)) / ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
assert ((-
  (rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (- rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) +
   rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (- rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))))%R
  =
(rm21 θ1 ξ θ2 * rm02 θ1 ξ θ2 + rm20_minus θ1 ξ θ2 * rm12 θ1 ξ θ2)
       /((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
rewrite rm02_eq. rewrite rm12_eq.
rewrite Rsqr_mult.
rewrite sin_cos_q.
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
unfold rm02,rm12,rm21,rm20_minus.
assert (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
     /\ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) <> 0).
assert ((Rsqr (sin θ1 * cos θ2 + (cos ξ * cos θ1 * sin θ2)) + Rsqr(sin ξ) * Rsqr (sin θ2)) <> 0).
assert (0 < (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²).
rewrite <- rm02_eq.
rewrite <- Rsqr_mult.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt.
lra.
assert (0 <= (sin ξ * sin θ2)²) by apply Rle_0_sqr.
lra. lra.
rewrite sin_cos_q in H6.
apply Rmult_neq_0_reg in H6.
destruct H6.
apply Rmult_neq_0_reg in H7.
lra.
destruct H6.
assert (((-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) -
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (((rw θ1 ξ θ2))² - (rz θ1 ξ θ2 )²) * (((rx θ1 ξ θ2))² + (ry θ1 ξ θ2 )²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) =
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) /
   (4 *
    (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) / 
         ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite Rinv_mult_distr.
rewrite (Rmult_assoc (4 * ((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite (Rmult_comm (((sin (ξ * / 2))² * (sin (θ1 * / 2 + - (θ2 * / 2)))² +
  (cos (ξ * / 2))² * (sin (θ1 * / 2 + θ2 * / 2))²))).
rewrite (Rmult_assoc (/ 4)).
rewrite (Rmult_assoc (/ ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²))).
rewrite <- Rinv_l_sym.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite <- (Rmult_assoc 4).
rewrite Rinv_r.
lra. lra.
assumption. assumption. assumption.
lra.
apply Rmult_integral_contrapositive.
split.
assumption. assumption.
rewrite H8. clear H8.
assert (((2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) +
   (-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (2 * (rw θ1 ξ θ2) * (rz θ1 ξ θ2)) * ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) *
  ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) /
  (4 *
   (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) / 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite (Rmult_comm ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²)).
rewrite <- (Rmult_assoc 4).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite <- Rmult_assoc.
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rinv_r. lra.
apply Rmult_integral_contrapositive.
split. lra. assumption.
apply Rmult_integral_contrapositive.
split. lra. assumption.
assumption.
rewrite H8. clear H8.
assert (((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) =
    cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²)
           - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)).
unfold rw,rz.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = 2 * (ξ/2)) by lra.
rewrite <- H8. reflexivity.
rewrite H8. clear H8.
rewrite cos_2a.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) 
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * ((sin (ξ / 2))² + (cos (ξ / 2))²)).
rewrite sin2_cos2.
lra.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2 = sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
unfold rw,rz.
rewrite (Rmult_assoc 2).
rewrite (Rmult_comm (cos (ξ / 2) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_comm ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc 2). rewrite <- (Rmult_assoc 2).
rewrite <- (Rmult_assoc 2). rewrite <- sin_2a.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * ((cos (θ1 / 2))² * 
                  (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²))
   / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
          ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   = (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * 
       ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H8. unfold Rsqr. lra.
rewrite <- H8. clear H8.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
(sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
   = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) 
  * sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)
  - (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)))
  / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H8. clear H8.
assert (sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
 ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) ).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite <- H8. clear H8.
autorewrite with R_db.
rewrite (Rmult_assoc (- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
assumption. assumption. assumption.
assumption. assumption. assumption.
}

{
apply Rltb_lt in eq3.
apply Rltb_lt in eq5.
apply Rleb_lt_false in eq6.
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2) - PI))
    = (-(PI - ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2))))))) by lra.
rewrite H. clear H.
rewrite cos_neg.
rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite cos_plus.
rewrite sin_plus.
rewrite rm12_sin_neg.
rewrite rm12_cos_neg.
rewrite rm21_sin.
rewrite rm21_cos.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
rewrite <- (rm20_eq θ1 ξ θ2).
rewrite <- (rm02_eq θ1 ξ θ2).
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- Rsqr_neg.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H.
assert ((-
   (rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
    (- rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) -
    rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
    (- rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))))%R
 = ((rm20_minus θ1 ξ θ2) * (rm02 θ1 ξ θ2) - (rm21 θ1 ξ θ2)
               * (rm12 θ1 ξ θ2)) / ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
assert ((-
  (rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (- rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) +
   rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (- rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))))%R
  =
(rm21 θ1 ξ θ2 * rm02 θ1 ξ θ2 + rm20_minus θ1 ξ θ2 * rm12 θ1 ξ θ2)
       /((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
rewrite rm02_eq. rewrite rm12_eq.
rewrite Rsqr_mult.
rewrite sin_cos_q.
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
unfold rm02,rm12,rm21,rm20_minus.
assert (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
     /\ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) <> 0).
assert ((Rsqr (sin θ1 * cos θ2 + (cos ξ * cos θ1 * sin θ2)) + Rsqr(sin ξ) * Rsqr (sin θ2)) <> 0).
assert (0 < (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²).
rewrite <- rm02_eq.
rewrite <- Rsqr_mult.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt.
lra.
assert (0 <= (sin ξ * sin θ2)²) by apply Rle_0_sqr.
lra. lra.
rewrite sin_cos_q in H6.
apply Rmult_neq_0_reg in H6.
destruct H6.
apply Rmult_neq_0_reg in H7.
lra.
destruct H6.
assert (((-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) -
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (((rw θ1 ξ θ2))² - (rz θ1 ξ θ2 )²) * (((rx θ1 ξ θ2))² + (ry θ1 ξ θ2 )²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) =
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) /
   (4 *
    (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) / 
         ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite Rinv_mult_distr.
rewrite (Rmult_assoc (4 * ((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite (Rmult_comm (((sin (ξ * / 2))² * (sin (θ1 * / 2 + - (θ2 * / 2)))² +
  (cos (ξ * / 2))² * (sin (θ1 * / 2 + θ2 * / 2))²))).
rewrite (Rmult_assoc (/ 4)).
rewrite (Rmult_assoc (/ ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²))).
rewrite <- Rinv_l_sym.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite <- (Rmult_assoc 4).
rewrite Rinv_r.
lra. lra.
assumption. assumption. assumption.
lra.
apply Rmult_integral_contrapositive.
split.
assumption. assumption.
rewrite H8. clear H8.
assert (((2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) +
   (-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (2 * (rw θ1 ξ θ2) * (rz θ1 ξ θ2)) * ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) *
  ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) /
  (4 *
   (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) / 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite (Rmult_comm ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²)).
rewrite <- (Rmult_assoc 4).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite <- Rmult_assoc.
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rinv_r. lra.
apply Rmult_integral_contrapositive.
split. lra. assumption.
apply Rmult_integral_contrapositive.
split. lra. assumption.
assumption.
rewrite H8. clear H8.
assert (((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) =
    cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²)
           - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)).
unfold rw,rz.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = 2 * (ξ/2)) by lra.
rewrite <- H8. reflexivity.
rewrite H8. clear H8.
rewrite cos_2a.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) 
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * ((sin (ξ / 2))² + (cos (ξ / 2))²)).
rewrite sin2_cos2.
lra.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2 = sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
unfold rw,rz.
rewrite (Rmult_assoc 2).
rewrite (Rmult_comm (cos (ξ / 2) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_comm ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc 2). rewrite <- (Rmult_assoc 2).
rewrite <- (Rmult_assoc 2). rewrite <- sin_2a.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * ((cos (θ1 / 2))² * 
                  (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²))
   / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
          ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   = (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * 
       ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H8. unfold Rsqr. lra.
rewrite <- H8. clear H8.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
(sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
   = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) 
  * sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)
  - (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)))
  / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H8. clear H8.
assert (sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
 ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) ).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite <- H8. clear H8.
autorewrite with R_db.
rewrite (Rmult_assoc (- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
assumption. assumption. assumption.
assumption. assumption. assumption.
}
(* when rm02 = 0, rm20 > 0 *)
{
apply Rltb_lt in eq3.
apply Rltb_le_false in eq4. 
apply Rltb_le_false in eq5.
assert (rm02 θ1 ξ θ2 = 0) by lra.
destruct (0 <? rm12 θ1 ξ θ2) eqn:eq6.
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + PI / 2)
   = PI / 2 + atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2)) by lra.
rewrite H6. clear H6.
rewrite <- cos_sin.
assert (cos (PI / 2 + atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2))
  = - sin (atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2))).
rewrite -> sin_cos. lra.
rewrite H6. clear H6.
rewrite rm21_sin.
rewrite rm21_cos.
rewrite rm02_eq in H.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H6.
rewrite H.
assert (√ (0² + (sin ξ * sin θ2)²) = sin ξ * sin θ2).
assert (0² = 0).
unfold Rsqr. lra.
rewrite H7.
autorewrite with R_db.
rewrite  sqrt_Rsqr.
reflexivity.
apply Rltb_lt in eq6. rewrite rm12_eq in eq6.
lra.
rewrite H7. clear H7.
rewrite Cmult_c.
rewrite <- rm20_eq.
assert (rm20_minus θ1 ξ θ2 =
       2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
     - 2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
     + 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
     - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)).
unfold rm20_minus, rx,ry,rz,rw.
rewrite <- sin_plus. rewrite <- sin_minus.
rewrite <- cos_plus. rewrite <- cos_minus.
assert (-2 * (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2)) * (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))
  = -2 * (sin (ξ / 2))² * ((sin (θ1 / 2 - θ2 / 2) * cos (θ1 / 2 - θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2)) * (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))
   = 2 * (cos (ξ / 2))² * ((sin (θ1 / 2 + θ2 / 2) * cos (θ1 / 2 + θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite sin_plus. rewrite sin_minus.
rewrite cos_plus. rewrite cos_minus.
assert (-2 * (sin (ξ / 2))² *
((sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)) *
 (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))) +
2 * (cos (ξ / 2))² *
((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2)) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
   = 2 * ((sin (ξ / 2))² + (cos (ξ / 2))²) *
          (cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
            -sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) +
     2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) *
        (sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
              sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))) by lra.
rewrite H7. clear H7.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H7. reflexivity.
rewrite H7. lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 - (sin ξ * sin θ1 / (sin ξ * sin θ2)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 ((2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) / 
  (sin ξ * sin θ2))
  = ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ * sin θ1)
     + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))) / (sin ξ * sin θ2)) by lra.
rewrite H7. clear H7.
assert (sin θ1 = 2 * sin (θ1 / 2) * cos (θ1 / 2)).
rewrite <- sin_2a.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H7. reflexivity.
rewrite H7. clear H7.
rewrite <- rm02_eq in H.
rewrite rm02_diff in H.
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_plus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) = 
     2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
      2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (cos (θ2 / 2))² * cos (θ2 / 2)).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2))
   = 2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) 
     - 2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
assert ((cos (θ1 / 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ  * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
   -  2 * sin ξ  * cos ξ * (cos (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ1 / 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))
   = 2 * sin ξ  * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
    - 2 * sin ξ  * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (cos (θ2 / 2))² * cos (θ2 / 2) -
   (2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
    2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)) +
   (2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
    2 * sin ξ * cos ξ * (cos (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) -
   (2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
    2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²))
  = - sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
    + 2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
    - 2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)
    + 2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
    - 2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
  (2 * sin (θ1 / 2) * cos (θ1 / 2)) +
  (- sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
   2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) +
   2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)))
  = (- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
        (sin ξ * (2 * sin (θ2 / 2) * cos(θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite <- sin_2a.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
((2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) / 
 (sin ξ * sin θ2)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
- (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)) / (sin ξ * sin θ2))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
     * (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) +
   sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
    / (sin ξ * sin θ2)) by lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) *  sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   - 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) 
   + 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * 
  sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) by lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * (sin (θ1 / 2))² * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)
   - 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
   -2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)* sin (θ2 / 2)
  = 2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   -2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * (sin (θ1 / 2))²).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2)
   -2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2)*sin (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2)
   -2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*cos (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   -2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)*sin (θ2 / 2)
  = 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
   -2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 2 * (sin (θ1 / 2))² * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 (2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) -
  2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²) +
 (2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
  2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²) -
 (2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) -
  2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * (sin (θ1 / 2))²) -
 (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (cos (θ2 / 2))²) +
 (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²) -
 (2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) *
  (cos (θ1 / 2))²) +
 (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
  2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) *
  (cos (θ2 / 2))²) +
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
 = - sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
   + cos ξ * cos (θ1 / 2) * cos (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  + 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   -2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)
  + 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
  - 2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2)
  + 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
  + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
  + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
assert (2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
 = 2 * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * (sin ξ)²  * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)).
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 ξ) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
 = 2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
   -  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)).
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 ξ) as eq7.
rewrite <- eq7. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) * 0 + cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) +
 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
 2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) -
 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) +
 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 (2 * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)) +
 (2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)) +
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
 = (cos (θ1 / 2) * cos (θ2 / 2) * sin ξ) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)))).
unfold Rsqr. lra. 
rewrite H7. clear H7.
rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7. clear H7.
apply Rltb_lt in eq6.
autorewrite with R_db.
rewrite (Rmult_assoc ((- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2)))).
rewrite (Rmult_assoc (cos (θ1 * / 2) * cos (θ2 * / 2) * sin ξ)).
rewrite Rinv_r.
lca.
rewrite rm12_eq in eq6. lra.
assumption. assumption.
(* the mirror case of the above *)
destruct (rm12 θ1 ξ θ2 <? 0) eqn:eq7.
apply Rltb_lt in eq7.
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + - PI / 2)
   = -(PI / 2 - atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2))) by lra.
rewrite H6. clear H6.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_shift. rewrite sin_shift.
rewrite rm21_sin.
rewrite rm21_cos.
rewrite rm02_eq in H.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H6.
rewrite H.
assert (√ (0² + (sin ξ * sin θ2)²) = - sin ξ * sin θ2).
assert (0² = 0).
unfold Rsqr. lra.
rewrite H7.
autorewrite with R_db.
rewrite Rsqr_neg.
rewrite  sqrt_Rsqr.
reflexivity.
rewrite rm12_eq in eq7.
lra.
rewrite H7. clear H7.
assert ((sin ξ * sin θ1 / (- sin ξ * sin θ2))
    = - (sin ξ * sin θ1 / (sin ξ * sin θ2))).
autorewrite with R_db.
rewrite <- Ropp_inv_permute. lra.
rewrite rm12_eq in eq7. lra.
rewrite H7. clear H7.
assert ( (- ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) / (- sin ξ * sin θ2)))
  = ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) / (sin ξ * sin θ2))).
autorewrite with R_db.
rewrite <- Ropp_inv_permute. lra.
rewrite rm12_eq in eq7. lra.
rewrite H7. clear H7.
rewrite Cmult_c.
rewrite <- rm20_eq.
assert (rm20_minus θ1 ξ θ2 =
       2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
     - 2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
     + 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
     - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)).
unfold rm20_minus, rx,ry,rz,rw.
rewrite <- sin_plus. rewrite <- sin_minus.
rewrite <- cos_plus. rewrite <- cos_minus.
assert (-2 * (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2)) * (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))
  = -2 * (sin (ξ / 2))² * ((sin (θ1 / 2 - θ2 / 2) * cos (θ1 / 2 - θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2)) * (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))
   = 2 * (cos (ξ / 2))² * ((sin (θ1 / 2 + θ2 / 2) * cos (θ1 / 2 + θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite sin_plus. rewrite sin_minus.
rewrite cos_plus. rewrite cos_minus.
assert (-2 * (sin (ξ / 2))² *
((sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)) *
 (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))) +
2 * (cos (ξ / 2))² *
((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2)) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
   = 2 * ((sin (ξ / 2))² + (cos (ξ / 2))²) *
          (cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
            -sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) +
     2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) *
        (sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
              sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))) by lra.
rewrite H7. clear H7.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H7. reflexivity.
rewrite H7. lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 - (sin ξ * sin θ1 / (sin ξ * sin θ2)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 ((2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) / 
  (sin ξ * sin θ2))
  = ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ * sin θ1)
     + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))) / (sin ξ * sin θ2)) by lra.
rewrite H7. clear H7.
assert (sin θ1 = 2 * sin (θ1 / 2) * cos (θ1 / 2)).
rewrite <- sin_2a.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H7. reflexivity.
rewrite H7. clear H7.
rewrite <- rm02_eq in H.
rewrite rm02_diff in H.
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_plus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) = 
     2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
      2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (cos (θ2 / 2))² * cos (θ2 / 2)).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2))
   = 2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) 
     - 2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
assert ((cos (θ1 / 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ  * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
   -  2 * sin ξ  * cos ξ * (cos (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ1 / 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))
   = 2 * sin ξ  * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
    - 2 * sin ξ  * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (cos (θ2 / 2))² * cos (θ2 / 2) -
   (2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
    2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)) +
   (2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
    2 * sin ξ * cos ξ * (cos (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) -
   (2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
    2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²))
  = - sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
    + 2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
    - 2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)
    + 2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
    - 2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
  (2 * sin (θ1 / 2) * cos (θ1 / 2)) +
  (- sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
   2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) +
   2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)))
  = (- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
        (sin ξ * (2 * sin (θ2 / 2) * cos(θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite <- sin_2a.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
((2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) / 
 (sin ξ * sin θ2)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
- (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)) / (sin ξ * sin θ2))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
     * (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) +
   sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
    / (sin ξ * sin θ2)) by lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) *  sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   - 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) 
   + 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * 
  sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) by lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * (sin (θ1 / 2))² * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)
   - 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
   -2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)* sin (θ2 / 2)
  = 2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   -2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * (sin (θ1 / 2))²).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2)
   -2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2)*sin (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2)
   -2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*cos (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   -2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)*sin (θ2 / 2)
  = 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
   -2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 2 * (sin (θ1 / 2))² * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 (2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) -
  2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²) +
 (2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
  2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²) -
 (2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) -
  2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * (sin (θ1 / 2))²) -
 (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (cos (θ2 / 2))²) +
 (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²) -
 (2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) *
  (cos (θ1 / 2))²) +
 (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
  2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) *
  (cos (θ2 / 2))²) +
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
 = - sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
   + cos ξ * cos (θ1 / 2) * cos (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  + 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   -2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)
  + 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
  - 2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2)
  + 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
  + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
  + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
assert (2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
 = 2 * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * (sin ξ)²  * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)).
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 ξ) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
 = 2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
   -  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)).
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 ξ) as eq8.
rewrite <- eq8. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) * 0 + cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) +
 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
 2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) -
 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) +
 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 (2 * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)) +
 (2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)) +
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
 = (cos (θ1 / 2) * cos (θ2 / 2) * sin ξ) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)))).
unfold Rsqr. lra. 
rewrite H7. clear H7.
rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7. clear H7.
autorewrite with R_db.
rewrite (Rmult_assoc ((- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2)))).
rewrite (Rmult_assoc (cos (θ1 * / 2) * cos (θ2 * / 2) * sin ξ)).
rewrite Rinv_r.
lca.
rewrite rm12_eq in eq7. lra.
assumption. assumption.
(* third case of zero of rm02 *)
rewrite Rplus_0_r.
apply Rltb_le_false in eq6.
apply Rltb_le_false in eq7.
assert (rm12 θ1 ξ θ2 = 0) by lra.
rewrite rm02_eq in H.
rewrite rm12_eq in H6.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H7.
rewrite H6 in H7.
rewrite <- Rsqr_mult in H7.
assert (0² + 0² = 0).
unfold Rsqr. lra.
rewrite H8 in H7.
apply Rplus_eq_R0 in H7.
destruct H7.
apply Rsqr_eq_0 in H7.
rewrite <- rm20_eq in H7. lra.
apply Rle_0_sqr. apply Rle_0_sqr.
}

(* when rm20_minus θ1 ξ θ2 < 0 and 0 <= rm21 *)
destruct (rm20_minus θ1 ξ θ2 <? 0) eqn:eq4.
apply Rltb_lt in eq4.
destruct (0 <=? rm21 θ1 ξ θ2) eqn:eq5.
apply Rleb_le in eq5.
destruct (0 <? rm02 θ1 ξ θ2) eqn:eq6.
apply Rltb_lt in eq6.
{
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + PI + atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2))
  = PI + (atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2))) by lra.
rewrite H. clear H.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_plus.
rewrite sin_plus.
rewrite rm12_sin.
rewrite rm12_cos.
rewrite rm21_sin_neg.
rewrite rm21_cos_neg.
rewrite <- Rsqr_neg.
assert ((-
   (- (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) /
    √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
    ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) /
     √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²)) -
    - (sin ξ * sin θ1) /
    √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
    (sin ξ * sin θ2 / √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²))))
 =    (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) /
    √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
    ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) /
     √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²))
    - (sin ξ * sin θ1) /
    √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
    (sin ξ * sin θ2 / √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²))) by lra.
rewrite H. clear H.
assert ((-
  (- (sin ξ * sin θ1) /
   √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
   ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) /
    √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²)) +
   - (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) /
   √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
   (sin ξ * sin θ2 / √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²))))
 = ((sin ξ * sin θ1) /
   √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
   ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) /
    √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²)) +
    (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) /
   √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
   (sin ξ * sin θ2 / √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²)))) by lra.
rewrite H. clear H.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
rewrite <- (rm20_eq θ1 ξ θ2).
rewrite <- (rm02_eq θ1 ξ θ2).
rewrite <- (rm12_eq θ1 ξ θ2).
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H.
assert ((rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) -
   rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))%R
 = ((rm20_minus θ1 ξ θ2) * (rm02 θ1 ξ θ2) - (rm21 θ1 ξ θ2)
               * (rm12 θ1 ξ θ2)) / ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
assert ((rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) +
  rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))
  =
(rm21 θ1 ξ θ2 * rm02 θ1 ξ θ2 + rm20_minus θ1 ξ θ2 * rm12 θ1 ξ θ2)
       /((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
rewrite rm02_eq. rewrite rm12_eq.
rewrite Rsqr_mult.
rewrite sin_cos_q.
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
unfold rm02,rm12,rm21,rm20_minus.

assert (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
     /\ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) <> 0).
assert ((Rsqr (sin θ1 * cos θ2 + (cos ξ * cos θ1 * sin θ2)) + Rsqr(sin ξ) * Rsqr (sin θ2)) <> 0).
assert (0 < (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²).
rewrite <- rm02_eq.
rewrite <- Rsqr_mult.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt.
lra.
assert (0 <= (sin ξ * sin θ2)²) by apply Rle_0_sqr.
lra. lra.
rewrite sin_cos_q in H6.
apply Rmult_neq_0_reg in H6.
destruct H6.
apply Rmult_neq_0_reg in H7.
lra.
destruct H6.
assert (((-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) -
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (((rw θ1 ξ θ2))² - (rz θ1 ξ θ2 )²) * (((rx θ1 ξ θ2))² + (ry θ1 ξ θ2 )²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) =
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) /
   (4 *
    (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) / 
         ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite Rinv_mult_distr.
rewrite (Rmult_assoc (4 * ((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite (Rmult_comm (((sin (ξ * / 2))² * (sin (θ1 * / 2 + - (θ2 * / 2)))² +
  (cos (ξ * / 2))² * (sin (θ1 * / 2 + θ2 * / 2))²))).
rewrite (Rmult_assoc (/ 4)).
rewrite (Rmult_assoc (/ ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²))).
rewrite <- Rinv_l_sym.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite <- (Rmult_assoc 4).
rewrite Rinv_r.
lra. lra.
assumption. assumption. assumption.
lra.
apply Rmult_integral_contrapositive.
split.
assumption. assumption.
rewrite H8. clear H8.
assert (((2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) +
   (-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (2 * (rw θ1 ξ θ2) * (rz θ1 ξ θ2)) * ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) *
  ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) /
  (4 *
   (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) / 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite (Rmult_comm ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²)).
rewrite <- (Rmult_assoc 4).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite <- Rmult_assoc.
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rinv_r. lra.
apply Rmult_integral_contrapositive.
split. lra. assumption.
apply Rmult_integral_contrapositive.
split. lra. assumption.
assumption.
rewrite H8. clear H8.
assert (((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) =
    cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²)
           - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)).
unfold rw,rz.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = 2 * (ξ/2)) by lra.
rewrite <- H8. reflexivity.
rewrite H8. clear H8.
rewrite cos_2a.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) 
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * ((sin (ξ / 2))² + (cos (ξ / 2))²)).
rewrite sin2_cos2.
lra.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2 = sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
unfold rw,rz.
rewrite (Rmult_assoc 2).
rewrite (Rmult_comm (cos (ξ / 2) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_comm ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc 2). rewrite <- (Rmult_assoc 2).
rewrite <- (Rmult_assoc 2). rewrite <- sin_2a.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * ((cos (θ1 / 2))² * 
                  (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²))
   / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
          ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   = (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * 
       ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H8. unfold Rsqr. lra.
rewrite <- H8. clear H8.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
(sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
   = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) 
  * sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)
  - (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)))
  / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H8. clear H8.
assert (sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
 ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) ).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite <- H8. clear H8.
autorewrite with R_db.
rewrite (Rmult_assoc (- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
assumption. assumption. assumption.
assumption. assumption. assumption.
}
(* when rm02 < 0 and rm20 < 0 *)
destruct (rm02 θ1 ξ θ2 <? 0) eqn:eq7.
destruct (0 <=? rm12 θ1 ξ θ2) eqn:eq8.
{
apply Rltb_lt in eq7.
apply Rleb_le in eq8.
assert ( (atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + PI + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2) + PI))
    = (PI + (PI + ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2))))))) by lra.
rewrite H. clear H.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Ropp_involutive.
rewrite Ropp_involutive.
rewrite cos_plus.
rewrite sin_plus.
rewrite rm12_sin_neg.
rewrite rm12_cos_neg.
rewrite rm21_sin_neg.
rewrite rm21_cos_neg.
rewrite <- Rsqr_neg.
rewrite <- Rsqr_neg.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
rewrite <- (rm20_eq θ1 ξ θ2).
rewrite <- (rm02_eq θ1 ξ θ2).
rewrite <- (rm12_eq θ1 ξ θ2).
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H.
assert ((- rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (- rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) -
   - rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (- rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))%R
 = ((rm20_minus θ1 ξ θ2) * (rm02 θ1 ξ θ2) - (rm21 θ1 ξ θ2)
               * (rm12 θ1 ξ θ2)) / ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
assert ((- rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (- rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) +
  - rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (- rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))%R
  =
(rm21 θ1 ξ θ2 * rm02 θ1 ξ θ2 + rm20_minus θ1 ξ θ2 * rm12 θ1 ξ θ2)
       /((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
rewrite rm02_eq. rewrite rm12_eq.
rewrite Rsqr_mult.
rewrite sin_cos_q.
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
unfold rm02,rm12,rm21,rm20_minus.
assert (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
     /\ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) <> 0).
assert ((Rsqr (sin θ1 * cos θ2 + (cos ξ * cos θ1 * sin θ2)) + Rsqr(sin ξ) * Rsqr (sin θ2)) <> 0).
assert (0 < (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²).
rewrite <- rm02_eq.
rewrite <- Rsqr_mult.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt.
lra.
assert (0 <= (sin ξ * sin θ2)²) by apply Rle_0_sqr.
lra. lra.
rewrite sin_cos_q in H6.
apply Rmult_neq_0_reg in H6.
destruct H6.
apply Rmult_neq_0_reg in H7.
lra.
destruct H6.
assert (((-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) -
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (((rw θ1 ξ θ2))² - (rz θ1 ξ θ2 )²) * (((rx θ1 ξ θ2))² + (ry θ1 ξ θ2 )²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) =
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) /
   (4 *
    (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) / 
         ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite Rinv_mult_distr.
rewrite (Rmult_assoc (4 * ((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite (Rmult_comm (((sin (ξ * / 2))² * (sin (θ1 * / 2 + - (θ2 * / 2)))² +
  (cos (ξ * / 2))² * (sin (θ1 * / 2 + θ2 * / 2))²))).
rewrite (Rmult_assoc (/ 4)).
rewrite (Rmult_assoc (/ ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²))).
rewrite <- Rinv_l_sym.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite <- (Rmult_assoc 4).
rewrite Rinv_r.
lra. lra.
assumption. assumption. assumption.
lra.
apply Rmult_integral_contrapositive.
split.
assumption. assumption.
rewrite H8. clear H8.
assert (((2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) +
   (-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (2 * (rw θ1 ξ θ2) * (rz θ1 ξ θ2)) * ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) *
  ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) /
  (4 *
   (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) / 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite (Rmult_comm ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²)).
rewrite <- (Rmult_assoc 4).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite <- Rmult_assoc.
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rinv_r. lra.
apply Rmult_integral_contrapositive.
split. lra. assumption.
apply Rmult_integral_contrapositive.
split. lra. assumption.
assumption.
rewrite H8. clear H8.
assert (((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) =
    cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²)
           - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)).
unfold rw,rz.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = 2 * (ξ/2)) by lra.
rewrite <- H8. reflexivity.
rewrite H8. clear H8.
rewrite cos_2a.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) 
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * ((sin (ξ / 2))² + (cos (ξ / 2))²)).
rewrite sin2_cos2.
lra.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2 = sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
unfold rw,rz.
rewrite (Rmult_assoc 2).
rewrite (Rmult_comm (cos (ξ / 2) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_comm ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc 2). rewrite <- (Rmult_assoc 2).
rewrite <- (Rmult_assoc 2). rewrite <- sin_2a.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * ((cos (θ1 / 2))² * 
                  (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²))
   / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
          ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   = (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * 
       ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H8. unfold Rsqr. lra.
rewrite <- H8. clear H8.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
(sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
   = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) 
  * sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)
  - (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)))
  / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H8. clear H8.
assert (sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
 ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) ).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite <- H8. clear H8.
autorewrite with R_db.
rewrite (Rmult_assoc (- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
assumption. assumption. assumption.
assumption. assumption. assumption.
}
(* when rm02 = 0 and rm20 < 0 *)
{
apply Rltb_lt in eq7.
apply Rleb_lt_false in eq8.
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + PI + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2) - PI))
    =  ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2))))) by lra.
rewrite H. clear H.
rewrite cos_plus.
rewrite sin_plus.
rewrite rm12_sin_neg.
rewrite rm12_cos_neg.
rewrite rm21_sin_neg.
rewrite rm21_cos_neg.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
rewrite <- (rm20_eq θ1 ξ θ2).
rewrite <- (rm02_eq θ1 ξ θ2).
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- Rsqr_neg.
rewrite <- Rsqr_neg.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H.
assert ((- rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (- rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) -
   - rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (- rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))%R
 = ((rm20_minus θ1 ξ θ2) * (rm02 θ1 ξ θ2) - (rm21 θ1 ξ θ2)
               * (rm12 θ1 ξ θ2)) / ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
assert ((- rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (- rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) +
  - rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (- rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))%R
  =
(rm21 θ1 ξ θ2 * rm02 θ1 ξ θ2 + rm20_minus θ1 ξ θ2 * rm12 θ1 ξ θ2)
       /((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
rewrite rm02_eq. rewrite rm12_eq.
rewrite Rsqr_mult.
rewrite sin_cos_q.
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
unfold rm02,rm12,rm21,rm20_minus.
assert (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
     /\ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) <> 0).
assert ((Rsqr (sin θ1 * cos θ2 + (cos ξ * cos θ1 * sin θ2)) + Rsqr(sin ξ) * Rsqr (sin θ2)) <> 0).
assert (0 < (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²).
rewrite <- rm02_eq.
rewrite <- Rsqr_mult.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt.
lra.
assert (0 <= (sin ξ * sin θ2)²) by apply Rle_0_sqr.
lra. lra.
rewrite sin_cos_q in H6.
apply Rmult_neq_0_reg in H6.
destruct H6.
apply Rmult_neq_0_reg in H7.
lra.
destruct H6.
assert (((-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) -
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (((rw θ1 ξ θ2))² - (rz θ1 ξ θ2 )²) * (((rx θ1 ξ θ2))² + (ry θ1 ξ θ2 )²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) =
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) /
   (4 *
    (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) / 
         ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite Rinv_mult_distr.
rewrite (Rmult_assoc (4 * ((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite (Rmult_comm (((sin (ξ * / 2))² * (sin (θ1 * / 2 + - (θ2 * / 2)))² +
  (cos (ξ * / 2))² * (sin (θ1 * / 2 + θ2 * / 2))²))).
rewrite (Rmult_assoc (/ 4)).
rewrite (Rmult_assoc (/ ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²))).
rewrite <- Rinv_l_sym.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite <- (Rmult_assoc 4).
rewrite Rinv_r.
lra. lra.
assumption. assumption. assumption.
lra.
apply Rmult_integral_contrapositive.
split.
assumption. assumption.
rewrite H8. clear H8.
assert (((2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) +
   (-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (2 * (rw θ1 ξ θ2) * (rz θ1 ξ θ2)) * ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) *
  ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) /
  (4 *
   (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) / 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite (Rmult_comm ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²)).
rewrite <- (Rmult_assoc 4).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite <- Rmult_assoc.
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rinv_r. lra.
apply Rmult_integral_contrapositive.
split. lra. assumption.
apply Rmult_integral_contrapositive.
split. lra. assumption.
assumption.
rewrite H8. clear H8.
assert (((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) =
    cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²)
           - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)).
unfold rw,rz.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = 2 * (ξ/2)) by lra.
rewrite <- H8. reflexivity.
rewrite H8. clear H8.
rewrite cos_2a.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) 
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * ((sin (ξ / 2))² + (cos (ξ / 2))²)).
rewrite sin2_cos2.
lra.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2 = sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
unfold rw,rz.
rewrite (Rmult_assoc 2).
rewrite (Rmult_comm (cos (ξ / 2) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_comm ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc 2). rewrite <- (Rmult_assoc 2).
rewrite <- (Rmult_assoc 2). rewrite <- sin_2a.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * ((cos (θ1 / 2))² * 
                  (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²))
   / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
          ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   = (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * 
       ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H8. unfold Rsqr. lra.
rewrite <- H8. clear H8.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
(sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
   = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) 
  * sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)
  - (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)))
  / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H8. clear H8.
assert (sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
 ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) ).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite <- H8. clear H8.
autorewrite with R_db.
rewrite (Rmult_assoc (- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
assumption. assumption. assumption.
assumption. assumption. assumption.
}
(* when rm02 = 0 and rm20 < 0 *)
{
apply Rltb_le_false in eq6. 
apply Rltb_le_false in eq7.
assert (rm02 θ1 ξ θ2 = 0) by lra.
destruct (0 <? rm12 θ1 ξ θ2) eqn:eq8.
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + PI + PI / 2)
   = (PI + (PI / 2 + atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2)))) by lra.
rewrite H6. clear H6.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite <- cos_sin.
assert (cos (PI / 2 + atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2))
  = - sin (atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2))).
rewrite -> sin_cos. lra.
rewrite H6. clear H6.
rewrite rm21_sin_neg.
rewrite rm21_cos_neg.
rewrite <- Rsqr_neg.
rewrite rm02_eq in H.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H6.
rewrite H.
assert (√ (0² + (sin ξ * sin θ2)²) = sin ξ * sin θ2).
assert (0² = 0).
unfold Rsqr. lra.
rewrite H7.
autorewrite with R_db.
rewrite  sqrt_Rsqr.
reflexivity.
apply Rltb_lt in eq8. rewrite rm12_eq in eq8.
lra.
rewrite H7. clear H7.
rewrite Ropp_involutive.
assert ((- (- (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) / (sin ξ * sin θ2)))%R 
  = (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) / (sin ξ * sin θ2)%R) by lra.
rewrite H7. clear H7.
rewrite Cmult_c.
rewrite <- rm20_eq.
assert (rm20_minus θ1 ξ θ2 =
       2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
     - 2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
     + 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
     - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)).
unfold rm20_minus, rx,ry,rz,rw.
rewrite <- sin_plus. rewrite <- sin_minus.
rewrite <- cos_plus. rewrite <- cos_minus.
assert (-2 * (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2)) * (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))
  = -2 * (sin (ξ / 2))² * ((sin (θ1 / 2 - θ2 / 2) * cos (θ1 / 2 - θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2)) * (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))
   = 2 * (cos (ξ / 2))² * ((sin (θ1 / 2 + θ2 / 2) * cos (θ1 / 2 + θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite sin_plus. rewrite sin_minus.
rewrite cos_plus. rewrite cos_minus.
assert (-2 * (sin (ξ / 2))² *
((sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)) *
 (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))) +
2 * (cos (ξ / 2))² *
((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2)) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
   = 2 * ((sin (ξ / 2))² + (cos (ξ / 2))²) *
          (cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
            -sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) +
     2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) *
        (sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
              sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))) by lra.
rewrite H7. clear H7.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H7. reflexivity.
rewrite H7. lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (- (sin ξ * sin θ1) / (sin ξ * sin θ2)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 ((2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) / 
  (sin ξ * sin θ2))
  = ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ * sin θ1)
     + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))) / (sin ξ * sin θ2)) by lra.
rewrite H7. clear H7.
assert (sin θ1 = 2 * sin (θ1 / 2) * cos (θ1 / 2)).
rewrite <- sin_2a.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H7. reflexivity.
rewrite H7. clear H7.
rewrite <- rm02_eq in H.
rewrite rm02_diff in H.
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_plus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) = 
     2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
      2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (cos (θ2 / 2))² * cos (θ2 / 2)).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2))
   = 2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) 
     - 2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
assert ((cos (θ1 / 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ  * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
   -  2 * sin ξ  * cos ξ * (cos (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ1 / 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))
   = 2 * sin ξ  * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
    - 2 * sin ξ  * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (cos (θ2 / 2))² * cos (θ2 / 2) -
   (2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
    2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)) +
   (2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
    2 * sin ξ * cos ξ * (cos (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) -
   (2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
    2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²))
  = - sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
    + 2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
    - 2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)
    + 2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
    - 2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
  (2 * sin (θ1 / 2) * cos (θ1 / 2)) +
  (- sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
   2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) +
   2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)))
  = (- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
        (sin ξ * (2 * sin (θ2 / 2) * cos(θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite <- sin_2a.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
((2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) / 
 (sin ξ * sin θ2)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
(- (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))) / (sin ξ * sin θ2))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
     * (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) +
   sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
    / (sin ξ * sin θ2)) by lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) *  sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   - 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) 
   + 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * 
  sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) by lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * (sin (θ1 / 2))² * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)
   - 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
   -2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)* sin (θ2 / 2)
  = 2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   -2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * (sin (θ1 / 2))²).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2)
   -2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2)*sin (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2)
   -2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*cos (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   -2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)*sin (θ2 / 2)
  = 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
   -2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 2 * (sin (θ1 / 2))² * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 (2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) -
  2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²) +
 (2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
  2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²) -
 (2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) -
  2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * (sin (θ1 / 2))²) -
 (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (cos (θ2 / 2))²) +
 (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²) -
 (2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) *
  (cos (θ1 / 2))²) +
 (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
  2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) *
  (cos (θ2 / 2))²) +
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
 = - sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
   + cos ξ * cos (θ1 / 2) * cos (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  + 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   -2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)
  + 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
  - 2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2)
  + 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
  + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
  + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
assert (2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
 = 2 * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * (sin ξ)²  * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)).
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 ξ) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
 = 2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
   -  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)).
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 ξ) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) * 0 + cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) +
 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
 2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) -
 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) +
 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 (2 * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)) +
 (2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)) +
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
 = (cos (θ1 / 2) * cos (θ2 / 2) * sin ξ) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)))).
unfold Rsqr. lra. 
rewrite H7. clear H7.
rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7. clear H7.
apply Rltb_lt in eq8.
autorewrite with R_db.
rewrite (Rmult_assoc ((- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2)))).
rewrite (Rmult_assoc (cos (θ1 * / 2) * cos (θ2 * / 2) * sin ξ)).
rewrite Rinv_r.
lca.
rewrite rm12_eq in eq8. lra.
assumption. assumption.
(* the mirror case of the above *)
destruct (rm12 θ1 ξ θ2 <? 0) eqn:eq9.
apply Rltb_lt in eq9.
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + PI + - PI / 2)
   = -(PI / 2 - (PI + atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2)))) by lra.
rewrite H6. clear H6.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_shift. rewrite sin_shift.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Ropp_involutive.
rewrite rm21_sin_neg.
rewrite rm21_cos_neg.
rewrite <- Rsqr_neg.
assert ((-
   (- (sin ξ * sin θ1) /
    √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)))%R
 = ((sin ξ * sin θ1) /
    √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²))%R) by lra.
rewrite H6. clear H6.
rewrite rm02_eq in H.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H6.
rewrite H.
assert (√ (0² + (sin ξ * sin θ2)²) = - sin ξ * sin θ2).
assert (0² = 0).
unfold Rsqr. lra.
rewrite H7.
autorewrite with R_db.
rewrite Rsqr_neg.
rewrite  sqrt_Rsqr.
reflexivity.
rewrite rm12_eq in eq9.
lra.
rewrite H7. clear H7.
assert ((sin ξ * sin θ1 / (- sin ξ * sin θ2))
    = - (sin ξ * sin θ1 / (sin ξ * sin θ2))).
autorewrite with R_db.
rewrite <- Ropp_inv_permute. lra.
rewrite rm12_eq in eq9. lra.
rewrite H7. clear H7.
assert ( (- (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) / (- sin ξ * sin θ2))
  = ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) / (sin ξ * sin θ2))).
autorewrite with R_db.
rewrite <- Ropp_inv_permute. lra.
rewrite rm12_eq in eq9. lra.
rewrite H7. clear H7.
rewrite Cmult_c.
rewrite <- rm20_eq.
assert (rm20_minus θ1 ξ θ2 =
       2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
     - 2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
     + 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
     - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)).
unfold rm20_minus, rx,ry,rz,rw.
rewrite <- sin_plus. rewrite <- sin_minus.
rewrite <- cos_plus. rewrite <- cos_minus.
assert (-2 * (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2)) * (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))
  = -2 * (sin (ξ / 2))² * ((sin (θ1 / 2 - θ2 / 2) * cos (θ1 / 2 - θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2)) * (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))
   = 2 * (cos (ξ / 2))² * ((sin (θ1 / 2 + θ2 / 2) * cos (θ1 / 2 + θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite sin_plus. rewrite sin_minus.
rewrite cos_plus. rewrite cos_minus.
assert (-2 * (sin (ξ / 2))² *
((sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)) *
 (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))) +
2 * (cos (ξ / 2))² *
((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2)) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
   = 2 * ((sin (ξ / 2))² + (cos (ξ / 2))²) *
          (cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
            -sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) +
     2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) *
        (sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
              sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))) by lra.
rewrite H7. clear H7.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H7. reflexivity.
rewrite H7. lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 - (sin ξ * sin θ1 / (sin ξ * sin θ2)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 ((2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) / 
  (sin ξ * sin θ2))
  = ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ * sin θ1)
     + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))) / (sin ξ * sin θ2)) by lra.
rewrite H7. clear H7.
assert (sin θ1 = 2 * sin (θ1 / 2) * cos (θ1 / 2)).
rewrite <- sin_2a.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H7. reflexivity.
rewrite H7. clear H7.
rewrite <- rm02_eq in H.
rewrite rm02_diff in H.
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_plus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) = 
     2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
      2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (cos (θ2 / 2))² * cos (θ2 / 2)).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2))
   = 2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) 
     - 2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
assert ((cos (θ1 / 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ  * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
   -  2 * sin ξ  * cos ξ * (cos (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ1 / 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))
   = 2 * sin ξ  * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
    - 2 * sin ξ  * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (cos (θ2 / 2))² * cos (θ2 / 2) -
   (2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
    2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)) +
   (2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
    2 * sin ξ * cos ξ * (cos (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) -
   (2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
    2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²))
  = - sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
    + 2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
    - 2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)
    + 2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
    - 2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
  (2 * sin (θ1 / 2) * cos (θ1 / 2)) +
  (- sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
   2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) +
   2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)))
  = (- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
        (sin ξ * (2 * sin (θ2 / 2) * cos(θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite <- sin_2a.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
((2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) / 
 (sin ξ * sin θ2)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
- (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)) / (sin ξ * sin θ2))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
     * (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) +
   sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
    / (sin ξ * sin θ2)) by lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) *  sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   - 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) 
   + 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * 
  sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) by lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * (sin (θ1 / 2))² * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)
   - 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
   -2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)* sin (θ2 / 2)
  = 2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   -2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * (sin (θ1 / 2))²).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2)
   -2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2)*sin (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2)
   -2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*cos (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   -2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)*sin (θ2 / 2)
  = 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
   -2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 2 * (sin (θ1 / 2))² * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 (2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) -
  2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²) +
 (2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
  2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²) -
 (2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) -
  2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * (sin (θ1 / 2))²) -
 (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (cos (θ2 / 2))²) +
 (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²) -
 (2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) *
  (cos (θ1 / 2))²) +
 (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
  2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) *
  (cos (θ2 / 2))²) +
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
 = - sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
   + cos ξ * cos (θ1 / 2) * cos (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  + 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   -2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)
  + 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
  - 2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2)
  + 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
  + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
  + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
assert (2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
 = 2 * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * (sin ξ)²  * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)).
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 ξ) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
 = 2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
   -  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)).
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 ξ) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) * 0 + cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) +
 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
 2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) -
 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) +
 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 (2 * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)) +
 (2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)) +
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
 = (cos (θ1 / 2) * cos (θ2 / 2) * sin ξ) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)))).
unfold Rsqr. lra. 
rewrite H7. clear H7.
rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7. clear H7.
autorewrite with R_db.
rewrite (Rmult_assoc ((- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2)))).
rewrite (Rmult_assoc (cos (θ1 * / 2) * cos (θ2 * / 2) * sin ξ)).
rewrite Rinv_r.
lca.
rewrite rm12_eq in eq9. lra.
assumption. assumption.
(* third case of zero of rm02 *)
rewrite Rplus_0_r.
apply Rltb_le_false in eq8.
apply Rltb_le_false in eq9.
assert (rm12 θ1 ξ θ2 = 0) by lra.
rewrite rm02_eq in H.
rewrite rm12_eq in H6.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H7.
rewrite H6 in H7.
rewrite <- Rsqr_mult in H7.
assert (0² + 0² = 0).
unfold Rsqr. lra.
rewrite H8 in H7.
apply Rplus_eq_R0 in H7.
destruct H7.
apply Rsqr_eq_0 in H7.
rewrite <- rm20_eq in H7. lra.
apply Rle_0_sqr. apply Rle_0_sqr.
}
(* when rm20 < 0 and rm21 < 0 *)
destruct (0 <? rm02 θ1 ξ θ2) eqn:eq6.
apply Rltb_lt in eq6.
{
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) - PI + atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2))
  = -(PI - (atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2)))) by lra.
rewrite H. clear H.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite cos_plus.
rewrite sin_plus.
rewrite rm12_sin.
rewrite rm12_cos.
rewrite rm21_sin_neg.
rewrite rm21_cos_neg.
rewrite <- Rsqr_neg.
assert ((-
   (- (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) /
    √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
    ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) /
     √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²)) -
    - (sin ξ * sin θ1) /
    √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
    (sin ξ * sin θ2 / √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²))))
 =    (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) /
    √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
    ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) /
     √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²))
    - (sin ξ * sin θ1) /
    √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
    (sin ξ * sin θ2 / √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²))) by lra.
rewrite H. clear H.
assert ((-
  (- (sin ξ * sin θ1) /
   √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
   ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) /
    √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²)) +
   - (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) /
   √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
   (sin ξ * sin θ2 / √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²))))
 = ((sin ξ * sin θ1) /
   √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
   ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) /
    √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²)) +
    (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) /
   √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²) *
   (sin ξ * sin θ2 / √ ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²)))) by lra.
rewrite H. clear H.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
rewrite <- (rm20_eq θ1 ξ θ2).
rewrite <- (rm02_eq θ1 ξ θ2).
rewrite <- (rm12_eq θ1 ξ θ2).
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H.
assert ((rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) -
   rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))%R
 = ((rm20_minus θ1 ξ θ2) * (rm02 θ1 ξ θ2) - (rm21 θ1 ξ θ2)
               * (rm12 θ1 ξ θ2)) / ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
assert ((rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) +
  rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))
  =
(rm21 θ1 ξ θ2 * rm02 θ1 ξ θ2 + rm20_minus θ1 ξ θ2 * rm12 θ1 ξ θ2)
       /((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
rewrite rm02_eq. rewrite rm12_eq.
rewrite Rsqr_mult.
rewrite sin_cos_q.
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
unfold rm02,rm12,rm21,rm20_minus.

assert (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
     /\ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) <> 0).
assert ((Rsqr (sin θ1 * cos θ2 + (cos ξ * cos θ1 * sin θ2)) + Rsqr(sin ξ) * Rsqr (sin θ2)) <> 0).
assert (0 < (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²).
rewrite <- rm02_eq.
rewrite <- Rsqr_mult.
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt.
lra.
assert (0 <= (sin ξ * sin θ2)²) by apply Rle_0_sqr.
lra. lra.
rewrite sin_cos_q in H6.
apply Rmult_neq_0_reg in H6.
destruct H6.
apply Rmult_neq_0_reg in H7.
lra.
destruct H6.
assert (((-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) -
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (((rw θ1 ξ θ2))² - (rz θ1 ξ θ2 )²) * (((rx θ1 ξ θ2))² + (ry θ1 ξ θ2 )²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) =
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) /
   (4 *
    (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) / 
         ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite Rinv_mult_distr.
rewrite (Rmult_assoc (4 * ((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite (Rmult_comm (((sin (ξ * / 2))² * (sin (θ1 * / 2 + - (θ2 * / 2)))² +
  (cos (ξ * / 2))² * (sin (θ1 * / 2 + θ2 * / 2))²))).
rewrite (Rmult_assoc (/ 4)).
rewrite (Rmult_assoc (/ ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²))).
rewrite <- Rinv_l_sym.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite <- (Rmult_assoc 4).
rewrite Rinv_r.
lra. lra.
assumption. assumption. assumption.
lra.
apply Rmult_integral_contrapositive.
split.
assumption. assumption.
rewrite H8. clear H8.
assert (((2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) +
   (-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (2 * (rw θ1 ξ θ2) * (rz θ1 ξ θ2)) * ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) *
  ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) /
  (4 *
   (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) / 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite (Rmult_comm ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²)).
rewrite <- (Rmult_assoc 4).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite <- Rmult_assoc.
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rinv_r. lra.
apply Rmult_integral_contrapositive.
split. lra. assumption.
apply Rmult_integral_contrapositive.
split. lra. assumption.
assumption.
rewrite H8. clear H8.
assert (((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) =
    cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²)
           - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)).
unfold rw,rz.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = 2 * (ξ/2)) by lra.
rewrite <- H8. reflexivity.
rewrite H8. clear H8.
rewrite cos_2a.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) 
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * ((sin (ξ / 2))² + (cos (ξ / 2))²)).
rewrite sin2_cos2.
lra.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2 = sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
unfold rw,rz.
rewrite (Rmult_assoc 2).
rewrite (Rmult_comm (cos (ξ / 2) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_comm ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc 2). rewrite <- (Rmult_assoc 2).
rewrite <- (Rmult_assoc 2). rewrite <- sin_2a.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * ((cos (θ1 / 2))² * 
                  (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²))
   / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
          ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   = (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * 
       ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H8. unfold Rsqr. lra.
rewrite <- H8. clear H8.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
(sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
   = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) 
  * sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)
  - (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)))
  / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H8. clear H8.
assert (sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
 ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) ).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite <- H8. clear H8.
autorewrite with R_db.
rewrite (Rmult_assoc (- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
assumption. assumption. assumption.
assumption. assumption. assumption.
}
(* when rm02 < 0 and rm20 < 0 *)
destruct (rm02 θ1 ξ θ2 <? 0) eqn:eq7.
destruct (0 <=? rm12 θ1 ξ θ2) eqn:eq8.
{
apply Rltb_lt in eq7.
apply Rleb_le in eq8.
assert ( (atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) - PI + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2) + PI))
    = ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2))))) by lra.
rewrite H. clear H.
rewrite cos_plus.
rewrite sin_plus.
rewrite rm12_sin_neg.
rewrite rm12_cos_neg.
rewrite rm21_sin_neg.
rewrite rm21_cos_neg.
rewrite <- Rsqr_neg.
rewrite <- Rsqr_neg.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
rewrite <- (rm20_eq θ1 ξ θ2).
rewrite <- (rm02_eq θ1 ξ θ2).
rewrite <- (rm12_eq θ1 ξ θ2).
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H.
assert ((- rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (- rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) -
   - rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (- rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))%R
 = ((rm20_minus θ1 ξ θ2) * (rm02 θ1 ξ θ2) - (rm21 θ1 ξ θ2)
               * (rm12 θ1 ξ θ2)) / ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
assert ((- rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (- rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) +
  - rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (- rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))%R
  =
(rm21 θ1 ξ θ2 * rm02 θ1 ξ θ2 + rm20_minus θ1 ξ θ2 * rm12 θ1 ξ θ2)
       /((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
rewrite rm02_eq. rewrite rm12_eq.
rewrite Rsqr_mult.
rewrite sin_cos_q.
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
unfold rm02,rm12,rm21,rm20_minus.
assert (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
     /\ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) <> 0).
assert ((Rsqr (sin θ1 * cos θ2 + (cos ξ * cos θ1 * sin θ2)) + Rsqr(sin ξ) * Rsqr (sin θ2)) <> 0).
assert (0 < (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²).
rewrite <- rm02_eq.
rewrite <- Rsqr_mult.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt.
lra.
assert (0 <= (sin ξ * sin θ2)²) by apply Rle_0_sqr.
lra. lra.
rewrite sin_cos_q in H6.
apply Rmult_neq_0_reg in H6.
destruct H6.
apply Rmult_neq_0_reg in H7.
lra.
destruct H6.
assert (((-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) -
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (((rw θ1 ξ θ2))² - (rz θ1 ξ θ2 )²) * (((rx θ1 ξ θ2))² + (ry θ1 ξ θ2 )²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) =
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) /
   (4 *
    (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) / 
         ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite Rinv_mult_distr.
rewrite (Rmult_assoc (4 * ((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite (Rmult_comm (((sin (ξ * / 2))² * (sin (θ1 * / 2 + - (θ2 * / 2)))² +
  (cos (ξ * / 2))² * (sin (θ1 * / 2 + θ2 * / 2))²))).
rewrite (Rmult_assoc (/ 4)).
rewrite (Rmult_assoc (/ ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²))).
rewrite <- Rinv_l_sym.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite <- (Rmult_assoc 4).
rewrite Rinv_r.
lra. lra.
assumption. assumption. assumption.
lra.
apply Rmult_integral_contrapositive.
split.
assumption. assumption.
rewrite H8. clear H8.
assert (((2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) +
   (-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (2 * (rw θ1 ξ θ2) * (rz θ1 ξ θ2)) * ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) *
  ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) /
  (4 *
   (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) / 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite (Rmult_comm ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²)).
rewrite <- (Rmult_assoc 4).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite <- Rmult_assoc.
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rinv_r. lra.
apply Rmult_integral_contrapositive.
split. lra. assumption.
apply Rmult_integral_contrapositive.
split. lra. assumption.
assumption.
rewrite H8. clear H8.
assert (((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) =
    cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²)
           - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)).
unfold rw,rz.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = 2 * (ξ/2)) by lra.
rewrite <- H8. reflexivity.
rewrite H8. clear H8.
rewrite cos_2a.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) 
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * ((sin (ξ / 2))² + (cos (ξ / 2))²)).
rewrite sin2_cos2.
lra.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2 = sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
unfold rw,rz.
rewrite (Rmult_assoc 2).
rewrite (Rmult_comm (cos (ξ / 2) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_comm ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc 2). rewrite <- (Rmult_assoc 2).
rewrite <- (Rmult_assoc 2). rewrite <- sin_2a.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * ((cos (θ1 / 2))² * 
                  (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²))
   / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
          ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   = (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * 
       ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H8. unfold Rsqr. lra.
rewrite <- H8. clear H8.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
(sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
   = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) 
  * sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)
  - (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)))
  / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H8. clear H8.
assert (sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
 ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) ).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite <- H8. clear H8.
autorewrite with R_db.
rewrite (Rmult_assoc (- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
assumption. assumption. assumption.
assumption. assumption. assumption.
}
(* when rm02 = 0 and rm20 < 0 *)
{
apply Rltb_lt in eq7.
apply Rleb_lt_false in eq8.
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) - PI + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2) - PI))
    =  (- (PI + (PI - ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2)))))))) by lra.
rewrite H. clear H.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite Ropp_involutive.
rewrite Ropp_involutive.
rewrite cos_plus.
rewrite sin_plus.
rewrite rm12_sin_neg.
rewrite rm12_cos_neg.
rewrite rm21_sin_neg.
rewrite rm21_cos_neg.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
rewrite <- (rm20_eq θ1 ξ θ2).
rewrite <- (rm02_eq θ1 ξ θ2).
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- Rsqr_neg.
rewrite <- Rsqr_neg.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H.
assert ((- rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (- rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) -
   - rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
   (- rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))%R
 = ((rm20_minus θ1 ξ θ2) * (rm02 θ1 ξ θ2) - (rm21 θ1 ξ θ2)
               * (rm12 θ1 ξ θ2)) / ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
assert ((- rm21 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (- rm02 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) +
  - rm20_minus θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) *
  (- rm12 θ1 ξ θ2 / √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)))%R
  =
(rm21 θ1 ξ θ2 * rm02 θ1 ξ θ2 + rm20_minus θ1 ξ θ2 * rm12 θ1 ξ θ2)
       /((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
autorewrite with R_db.
assert (((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite Rsqr_sqrt. reflexivity.
assert (0 <= (rm02 θ1 ξ θ2)²). apply Rle_0_sqr.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra.
assert (/ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²) = / (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))²).
rewrite <- H6. reflexivity.
rewrite H7.
assert ((√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))² =
     (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)) * (√ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²))).
unfold Rsqr. reflexivity.
rewrite H8.
rewrite Rinv_mult_distr. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
assert (0 < √ ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
apply sqrt_lt_R0.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²). apply Rle_0_sqr.
lra. lra.
rewrite H6. clear H6.
rewrite rm02_eq. rewrite rm12_eq.
rewrite Rsqr_mult.
rewrite sin_cos_q.
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
unfold rm02,rm12,rm21,rm20_minus.
assert (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0
     /\ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) <> 0).
assert ((Rsqr (sin θ1 * cos θ2 + (cos ξ * cos θ1 * sin θ2)) + Rsqr(sin ξ) * Rsqr (sin θ2)) <> 0).
assert (0 < (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ)² * (sin θ2)²).
rewrite <- rm02_eq.
rewrite <- Rsqr_mult.
assert (0 < (rm02 θ1 ξ θ2)²).
rewrite Rsqr_neg.
apply Rsqr_pos_lt.
lra.
assert (0 <= (sin ξ * sin θ2)²) by apply Rle_0_sqr.
lra. lra.
rewrite sin_cos_q in H6.
apply Rmult_neq_0_reg in H6.
destruct H6.
apply Rmult_neq_0_reg in H7.
lra.
destruct H6.
assert (((-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) -
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
    (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (((rw θ1 ξ θ2))² - (rz θ1 ξ θ2 )²) * (((rx θ1 ξ θ2))² + (ry θ1 ξ θ2 )²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) =
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) *
   ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) /
   (4 *
    (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
     ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = ((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) / 
         ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite Rinv_mult_distr.
rewrite (Rmult_assoc (4 * ((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite (Rmult_comm (((sin (ξ * / 2))² * (sin (θ1 * / 2 + - (θ2 * / 2)))² +
  (cos (ξ * / 2))² * (sin (θ1 * / 2 + θ2 * / 2))²))).
rewrite (Rmult_assoc (/ 4)).
rewrite (Rmult_assoc (/ ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²))).
rewrite <- Rinv_l_sym.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (((rw θ1 ξ θ2)² + - (rz θ1 ξ θ2)²))).
rewrite <- (Rmult_assoc 4).
rewrite Rinv_r.
lra. lra.
assumption. assumption. assumption.
lra.
apply Rmult_integral_contrapositive.
split.
assumption. assumption.
rewrite H8. clear H8.
assert (((2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) +
   (-2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 + 2 * ry θ1 ξ θ2 * rw θ1 ξ θ2) *
   (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 - 2 * rx θ1 ξ θ2 * rw θ1 ξ θ2))
  = 4 * (2 * (rw θ1 ξ θ2) * (rz θ1 ξ θ2)) * ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((4 * (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) *
  ((rx θ1 ξ θ2)² + (ry θ1 ξ θ2)²) /
  (4 *
   (((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) *
    ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))))%R
 = (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2) / 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite (Rmult_comm 4).
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite (Rmult_comm ((sin (ξ * / 2))² * (cos (θ1 * / 2 + - (θ2 * / 2)))² +
   (cos (ξ * / 2))² * (cos (θ1 * / 2 + θ2 * / 2))²)).
rewrite <- (Rmult_assoc 4).
autorewrite with R_db.
rewrite Rinv_mult_distr.
rewrite <- Rmult_assoc.
rewrite (Rmult_assoc (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2)).
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rinv_r. lra.
apply Rmult_integral_contrapositive.
split. lra. assumption.
apply Rmult_integral_contrapositive.
split. lra. assumption.
assumption.
rewrite H8. clear H8.
assert (((rw θ1 ξ θ2)² - (rz θ1 ξ θ2)²) =
    cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²)
           - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)).
unfold rw,rz.
rewrite Rsqr_mult. rewrite Rsqr_mult.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (cos ξ = cos (2 * (ξ/2))).
assert (ξ = 2 * (ξ/2)) by lra.
rewrite <- H8. reflexivity.
rewrite H8. clear H8.
rewrite cos_2a.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) 
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * ((sin (ξ / 2))² + (cos (ξ / 2))²)).
rewrite sin2_cos2.
lra.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
assert (2 * rw θ1 ξ θ2 * rz θ1 ξ θ2 = sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
unfold rw,rz.
rewrite (Rmult_assoc 2).
rewrite (Rmult_comm (cos (ξ / 2) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_comm ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc (sin (ξ / 2))).
rewrite <- (Rmult_assoc 2). rewrite <- (Rmult_assoc 2).
rewrite <- (Rmult_assoc 2). rewrite <- sin_2a.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H8.
unfold Rsqr. lra.
rewrite H8. clear H8.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
  ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * ((cos (θ1 / 2))² * 
                  (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²))
   / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
unfold Rsqr. lra.
rewrite H8. clear H8.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
          ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
   = (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 ((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
   2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) 
  + (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * 
       ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 (ξ)). lra.
rewrite H8. unfold Rsqr. lra.
rewrite <- H8. clear H8.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
(sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
((cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)) /
 ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))
   = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) 
  * sin ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²)
  - (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
   (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2)))
  / ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H8. clear H8.
assert (sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
 ((cos (θ1 / 2))² * (cos (θ2 / 2))² - (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 (cos ξ * ((cos (θ1 / 2))² * (cos (θ2 / 2))² + (sin (θ1 / 2))² * (sin (θ2 / 2))²) -
  2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2))) ).
rewrite cos_plus. rewrite cos_minus.
rewrite Rsqr_plus. rewrite Rsqr_minus.
assert (((sin (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² +
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) +
 (cos (ξ / 2))² *
 ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))² -
  2 * (cos (θ1 / 2) * cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))))
 = ((sin (ξ / 2))² + (cos (ξ / 2))²) * ((cos (θ1 / 2) * cos (θ2 / 2))² + (sin (θ1 / 2) * sin (θ2 / 2))²)
   - ((cos (ξ / 2))² - (sin (ξ / 2))²) * 2 * (cos (θ1 / 2) *
        cos (θ2 / 2)) * (sin (θ1 / 2) * sin (θ2 / 2))) by lra.
rewrite H8. clear H8.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. 
rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H8. reflexivity.
rewrite H8. clear H8.
unfold Rsqr. lra.
rewrite <- H8. clear H8.
autorewrite with R_db.
rewrite (Rmult_assoc (- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
assumption. assumption. assumption.
assumption. assumption. assumption.
}
(* when rm02 = 0 and rm20 < 0 *)
{
apply Rltb_le_false in eq6. 
apply Rltb_le_false in eq7.
assert (rm02 θ1 ξ θ2 = 0) by lra.
destruct (0 <? rm12 θ1 ξ θ2) eqn:eq8.
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) - PI + PI / 2)
   = -(PI / 2 - atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2))) by lra.
rewrite H6. clear H6.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_shift. rewrite sin_shift.
rewrite rm21_sin_neg.
rewrite rm21_cos_neg.
rewrite <- Rsqr_neg.
rewrite rm02_eq in H.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H6.
rewrite H.
assert (√ (0² + (sin ξ * sin θ2)²) = sin ξ * sin θ2).
assert (0² = 0).
unfold Rsqr. lra.
rewrite H7.
autorewrite with R_db.
rewrite  sqrt_Rsqr.
reflexivity.
apply Rltb_lt in eq8. rewrite rm12_eq in eq8.
lra.
rewrite H7. clear H7.
assert ((- (- (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) / (sin ξ * sin θ2)))%R 
  = (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) / (sin ξ * sin θ2)%R) by lra.
rewrite H7. clear H7.
rewrite Cmult_c.
rewrite <- rm20_eq.
assert (rm20_minus θ1 ξ θ2 =
       2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
     - 2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
     + 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
     - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)).
unfold rm20_minus, rx,ry,rz,rw.
rewrite <- sin_plus. rewrite <- sin_minus.
rewrite <- cos_plus. rewrite <- cos_minus.
assert (-2 * (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2)) * (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))
  = -2 * (sin (ξ / 2))² * ((sin (θ1 / 2 - θ2 / 2) * cos (θ1 / 2 - θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2)) * (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))
   = 2 * (cos (ξ / 2))² * ((sin (θ1 / 2 + θ2 / 2) * cos (θ1 / 2 + θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite sin_plus. rewrite sin_minus.
rewrite cos_plus. rewrite cos_minus.
assert (-2 * (sin (ξ / 2))² *
((sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)) *
 (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))) +
2 * (cos (ξ / 2))² *
((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2)) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
   = 2 * ((sin (ξ / 2))² + (cos (ξ / 2))²) *
          (cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
            -sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) +
     2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) *
        (sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
              sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))) by lra.
rewrite H7. clear H7.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H7. reflexivity.
rewrite H7. lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (- (sin ξ * sin θ1) / (sin ξ * sin θ2)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 ((2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) / 
  (sin ξ * sin θ2))
  = ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ * sin θ1)
     + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))) / (sin ξ * sin θ2)) by lra.
rewrite H7. clear H7.
assert (sin θ1 = 2 * sin (θ1 / 2) * cos (θ1 / 2)).
rewrite <- sin_2a.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H7. reflexivity.
rewrite H7. clear H7.
rewrite <- rm02_eq in H.
rewrite rm02_diff in H.
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_plus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) = 
     2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
      2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (cos (θ2 / 2))² * cos (θ2 / 2)).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2))
   = 2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) 
     - 2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
assert ((cos (θ1 / 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ  * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
   -  2 * sin ξ  * cos ξ * (cos (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ1 / 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))
   = 2 * sin ξ  * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
    - 2 * sin ξ  * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (cos (θ2 / 2))² * cos (θ2 / 2) -
   (2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
    2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)) +
   (2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
    2 * sin ξ * cos ξ * (cos (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) -
   (2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
    2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²))
  = - sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
    + 2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
    - 2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)
    + 2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
    - 2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
  (2 * sin (θ1 / 2) * cos (θ1 / 2)) +
  (- sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
   2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) +
   2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)))
  = (- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
        (sin ξ * (2 * sin (θ2 / 2) * cos(θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite <- sin_2a.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
((2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) / 
 (sin ξ * sin θ2)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
(- (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))) / (sin ξ * sin θ2))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
     * (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) +
   sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
    / (sin ξ * sin θ2)) by lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) *  sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   - 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) 
   + 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * 
  sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) by lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * (sin (θ1 / 2))² * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)
   - 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
   -2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)* sin (θ2 / 2)
  = 2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   -2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * (sin (θ1 / 2))²).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2)
   -2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2)*sin (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2)
   -2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*cos (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   -2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)*sin (θ2 / 2)
  = 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
   -2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 2 * (sin (θ1 / 2))² * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 (2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) -
  2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²) +
 (2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
  2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²) -
 (2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) -
  2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * (sin (θ1 / 2))²) -
 (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (cos (θ2 / 2))²) +
 (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²) -
 (2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) *
  (cos (θ1 / 2))²) +
 (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
  2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) *
  (cos (θ2 / 2))²) +
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
 = - sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
   + cos ξ * cos (θ1 / 2) * cos (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  + 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   -2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)
  + 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
  - 2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2)
  + 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
  + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
  + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
assert (2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
 = 2 * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * (sin ξ)²  * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)).
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 ξ) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
 = 2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
   -  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)).
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 ξ) as eq9.
rewrite <- eq9. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) * 0 + cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) +
 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
 2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) -
 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) +
 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 (2 * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)) +
 (2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)) +
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
 = (cos (θ1 / 2) * cos (θ2 / 2) * sin ξ) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)))).
unfold Rsqr. lra. 
rewrite H7. clear H7.
rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7. clear H7.
apply Rltb_lt in eq8.
autorewrite with R_db.
rewrite (Rmult_assoc ((- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2)))).
rewrite (Rmult_assoc (cos (θ1 * / 2) * cos (θ2 * / 2) * sin ξ)).
rewrite Rinv_r.
lca.
rewrite rm12_eq in eq8. lra.
assumption. assumption.
(* the mirror case of the above *)
destruct (rm12 θ1 ξ θ2 <? 0) eqn:eq9.
apply Rltb_lt in eq9.
assert ((atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2) - PI + - PI / 2)
   = -(PI / 2 - (-(PI - atan (rm21 θ1 ξ θ2 / rm20_minus θ1 ξ θ2))))) by lra.
rewrite H6. clear H6.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_shift. rewrite sin_shift.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite Ropp_involutive.
rewrite rm21_sin_neg.
rewrite rm21_cos_neg.
rewrite <- Rsqr_neg.
assert ((-
   (- (sin ξ * sin θ1) /
    √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)))%R
 = ((sin ξ * sin θ1) /
    √ ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²))%R) by lra.
rewrite H6. clear H6.
rewrite rm02_eq in H.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H6.
rewrite H.
assert (√ (0² + (sin ξ * sin θ2)²) = - sin ξ * sin θ2).
assert (0² = 0).
unfold Rsqr. lra.
rewrite H7.
autorewrite with R_db.
rewrite Rsqr_neg.
rewrite  sqrt_Rsqr.
reflexivity.
rewrite rm12_eq in eq9.
lra.
rewrite H7. clear H7.
assert ((sin ξ * sin θ1 / (- sin ξ * sin θ2))
    = - (sin ξ * sin θ1 / (sin ξ * sin θ2))).
autorewrite with R_db.
rewrite <- Ropp_inv_permute. lra.
rewrite rm12_eq in eq9. lra.
rewrite H7. clear H7.
assert ( (- (cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) / (- sin ξ * sin θ2))
  = ((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2) / (sin ξ * sin θ2))).
autorewrite with R_db.
rewrite <- Ropp_inv_permute. lra.
rewrite rm12_eq in eq9. lra.
rewrite H7. clear H7.
rewrite Cmult_c.
rewrite <- rm20_eq.
assert (rm20_minus θ1 ξ θ2 =
       2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
     - 2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
     + 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
     - 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)).
unfold rm20_minus, rx,ry,rz,rw.
rewrite <- sin_plus. rewrite <- sin_minus.
rewrite <- cos_plus. rewrite <- cos_minus.
assert (-2 * (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2)) * (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))
  = -2 * (sin (ξ / 2))² * ((sin (θ1 / 2 - θ2 / 2) * cos (θ1 / 2 - θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2)) * (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))
   = 2 * (cos (ξ / 2))² * ((sin (θ1 / 2 + θ2 / 2) * cos (θ1 / 2 + θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite sin_plus. rewrite sin_minus.
rewrite cos_plus. rewrite cos_minus.
assert (-2 * (sin (ξ / 2))² *
((sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)) *
 (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))) +
2 * (cos (ξ / 2))² *
((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2)) *
 (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
   = 2 * ((sin (ξ / 2))² + (cos (ξ / 2))²) *
          (cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
            -sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) +
     2 * ((cos (ξ / 2))² - (sin (ξ / 2))²) *
        (sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
              sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))) by lra.
rewrite H7. clear H7.
rewrite sin2_cos2.
assert (((cos (ξ / 2))² - (sin (ξ / 2))²) = cos ξ).
unfold Rsqr. rewrite <- cos_2a.
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H7. reflexivity.
rewrite H7. lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 - (sin ξ * sin θ1 / (sin ξ * sin θ2)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 ((2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) / 
  (sin ξ * sin θ2))
  = ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ * sin θ1)
     + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))) / (sin ξ * sin θ2)) by lra.
rewrite H7. clear H7.
assert (sin θ1 = 2 * sin (θ1 / 2) * cos (θ1 / 2)).
rewrite <- sin_2a.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H7. reflexivity.
rewrite H7. clear H7.
rewrite <- rm02_eq in H.
rewrite rm02_diff in H.
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_plus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) = 
     2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
      2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (cos (θ2 / 2))² * cos (θ2 / 2)).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2))
   = 2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) 
     - 2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)).
assert ((cos (θ1 / 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ  * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
   -  2 * sin ξ  * cos ξ * (cos (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ1 / 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))
   = 2 * sin ξ  * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
    - 2 * sin ξ  * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2 / 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (cos (θ2 / 2))² * cos (θ2 / 2) -
   (2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
    2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * (sin (θ2 / 2))² * cos (θ2 / 2)) +
   (2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
    2 * sin ξ * cos ξ * (cos (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) -
   (2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
    2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²))
  = - sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
     (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
    + 2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
    - 2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)
    + 2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²
    - 2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
  (2 * sin (θ1 / 2) * cos (θ1 / 2)) +
  (- sin ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
   2 * sin ξ * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * sin ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) +
   2 * sin ξ * cos ξ * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * cos ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)))
  = (- sin (θ1 / 2) * sin (θ2 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) * 
        (sin ξ * (2 * sin (θ2 / 2) * cos(θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite <- sin_2a.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
((2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) / 
 (sin ξ * sin θ2)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
- (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)) / (sin ξ * sin θ2))
  = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
     * (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) +
   sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
    / (sin ξ * sin θ2)) by lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (2 * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) +
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2))
 = 2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) *  sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   - 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) 
   + 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * 
  sin (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)) by lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   - 2 * (sin (θ1 / 2))² * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
  = 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)
   - 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
   -2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
assert ((sin (θ2 / 2))² = 1 - (cos (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)* sin (θ2 / 2)
  = 2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
   -2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * (sin (θ1 / 2))²).
assert ((sin (θ1 / 2))² = 1 - (cos (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2)
   -2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * sin (θ1 / 2)*sin (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2)
   -2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*cos (θ2 / 2)*cos (θ2 / 2)
  = 2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
   -2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)*sin (θ2 / 2)*sin (θ2 / 2)
  = 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
   -2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 2 * (sin (θ1 / 2))² * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 (2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) -
  2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * (sin (θ2 / 2))²) +
 (2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
  2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²) -
 (2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) -
  2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * (sin (θ1 / 2))²) -
 (2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * (cos (θ2 / 2))²) +
 (2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) * (cos (θ1 / 2))²) -
 (2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) *
  (cos (θ1 / 2))²) +
 (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
  2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) *
  (cos (θ2 / 2))²) +
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
 = - sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
   + cos ξ * cos (θ1 / 2) * cos (θ2 / 2) *
   (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))² +
    2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  + 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   -2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2)
  + 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * cos (θ2 / 2) *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2)
  - 2 * cos ξ * sin (θ1 / 2)  * cos (θ1 / 2) * cos (θ1 / 2)  * cos (θ2 / 2)
  + 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2)  * sin (θ2 / 2) * cos (θ2 / 2)
  - 2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
  + 2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
  + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2))).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
assert (2 * cos ξ * cos ξ * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)
 = 2 * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
   2 * (sin ξ)²  * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)).
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 ξ) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos ξ * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
 = 2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
   -  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)).
assert ((sin ξ)² = 1 - (cos ξ)²).
specialize (sin2_cos2 ξ) as eq10.
rewrite <- eq10. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((- sin (θ1 / 2) * sin (θ2 / 2) * 0 + cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
 2 * cos (θ2 / 2) * cos (θ1 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 2 * cos (θ1 / 2) * sin (θ1 / 2) * sin (θ1 / 2) * sin (θ2 / 2) +
 2 * cos ξ * cos (θ1 / 2) * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) -
 2 * cos ξ * cos (θ2 / 2) * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) -
 2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * cos (θ1 / 2) * cos (θ2 / 2) +
 2 * cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
 (2 * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ2 / 2) * cos (θ1 / 2) * cos (θ2 / 2) * cos (θ2 / 2)) +
 (2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)) +
 sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))
 = (cos (θ1 / 2) * cos (θ2 / 2) * sin ξ) * (sin ξ * (2 * sin (θ2 / 2) * cos (θ2 / 2)))).
unfold Rsqr. lra. 
rewrite H7. clear H7.
rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7. clear H7.
autorewrite with R_db.
rewrite (Rmult_assoc ((- (sin (θ1 * / 2) * sin (θ2 * / 2)) + cos ξ * cos (θ1 * / 2) * cos (θ2 * / 2)))).
rewrite (Rmult_assoc (cos (θ1 * / 2) * cos (θ2 * / 2) * sin ξ)).
rewrite Rinv_r.
lca.
rewrite rm12_eq in eq9. lra.
assumption. assumption.
(* third case of zero of rm02 *)
rewrite Rplus_0_r.
apply Rltb_le_false in eq8.
apply Rltb_le_false in eq9.
assert (rm12 θ1 ξ θ2 = 0) by lra.
rewrite rm02_eq in H.
rewrite rm12_eq in H6.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H7.
rewrite H6 in H7.
rewrite <- Rsqr_mult in H7.
assert (0² + 0² = 0).
unfold Rsqr. lra.
rewrite H8 in H7.
apply Rplus_eq_R0 in H7.
destruct H7.
apply Rsqr_eq_0 in H7.
rewrite <- rm20_eq in H7. lra.
apply Rle_0_sqr. apply Rle_0_sqr.
}
(* when rm20 = 0 *)
{
apply Rltb_le_false in eq3.
apply Rltb_le_false in eq4.
assert (rm20_minus θ1 ξ θ2 = 0) by lra.
destruct (0 <? rm21 θ1 ξ θ2) eqn:eq5.
apply Rltb_lt in eq5.
destruct (0 <? rm02 θ1 ξ θ2) eqn:eq6.
apply Rltb_lt in eq6.
assert ((PI / 2 + atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2))
   = (PI / 2 - (-atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2)))) by lra.
rewrite H6. clear H6.
rewrite sin_shift. rewrite cos_shift.
rewrite sin_neg. rewrite cos_neg.
rewrite rm12_sin.
rewrite rm12_cos.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite Rsqr_mult in H6.
rewrite <- H6.
rewrite rm20_eq in H.
rewrite H.
assert (√ (0² + (sin ξ)² * (sin θ1)²) = (sin ξ * sin θ1)).
assert (Rsqr 0 = 0).
unfold Rsqr. lra.
rewrite H7.
rewrite <- Rsqr_mult.
rewrite Rplus_0_l.
rewrite sqrt_Rsqr. reflexivity.
rewrite rm21_eq in eq5. lra.
rewrite H7. clear H7.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 - (sin ξ * sin θ2 / (sin ξ * sin θ1)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1))
  = (- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ * (2 * sin (θ2/2) * cos (θ2/2))
     + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))
           / (sin ξ * (2 * sin (θ1/2) * cos (θ1/2)))).
rewrite <- sin_2a. rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H8.
lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * - (sin ξ * sin θ2 / (sin ξ * sin θ1))
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
   * (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)
   + sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ2/2) * cos (θ2/2)))
 / (sin ξ * (2 * sin (θ1/2) * cos (θ1/2)))).
rewrite <- sin_2a. rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H8.
lra.
rewrite H7. clear H7.
rewrite <- rm02_eq.
rewrite rm02_diff.
rewrite <- rm20_eq in H.
rewrite rm20_diff in H.
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_plus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²)
  = 2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² 
    - 2 * sin ξ * sin (θ2 / 2) * Rsqr (cos (θ1 / 2)) * cos (θ1 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
  = 2 * sin ξ * Rsqr (sin (θ1 / 2)) * cos (θ1 / 2) * sin (θ2 / 2)
    - 2 * sin ξ * Rsqr (sin (θ1 / 2)) * cos (θ1 / 2) * sin (θ2 / 2) * Rsqr (cos (θ2 / 2))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ1 / 2) * cos (θ2 / 2) * Rsqr (cos (θ2 / 2))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ * cos ξ * sin (θ1 / 2) * Rsqr (sin (θ2 / 2)) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * Rsqr (sin (θ2 / 2)) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * sin (θ2 / 2) * (cos (θ1 / 2))² * cos (θ1 / 2) * (cos (θ2 / 2))² -
   (2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
    2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) +
   (2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) -
    2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) * (cos (θ2 / 2))²) -
   (2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
    2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) * (cos (θ1 / 2))²))
  = - sin ξ * cos (θ1 / 2) * cos (θ2 / 2) *
     (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
    + 2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²
    - 2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
    + 2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
  (2 * sin (θ2 / 2) * cos (θ2 / 2)) +
  (2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) +
   2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) -
   2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)))
  = (- sin (θ2 / 2) * sin (θ1 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) *
     (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))).
unfold Rsqr. lra. 
rewrite H7. clear H7.
rewrite (Rmult_minus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_plus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_minus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite Rmult_minus_distr_r. rewrite Rmult_minus_distr_r. 
rewrite Rmult_minus_distr_r. rewrite Rmult_minus_distr_r.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²)
   = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
     - (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) *(sin (θ2 / 2))² *  cos (θ1 / 2)))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2/ 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
   = 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²
    - cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))²) * (sin (θ1 / 2))²).
assert ((sin (θ1/ 2))² = 1 - (cos (θ1/ 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ1 / 2)) -
 cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²) -
 (2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² -
  cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))²) * (sin (θ1 / 2))² -
  cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²))
  = - sin (θ1 / 2) * sin (θ2 / 2) *
     (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
     + 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
     -2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H7. clear H7. rewrite H.
assert (cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
   = 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
     - 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2/ 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
    = 2 * (cos ξ)² *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
      - cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1/ 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² +
(cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) -
  (2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²)) -
 (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) -
  (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   cos ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))))
  = cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
    (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
    + 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) 
    - 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² 
    - 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
    + 2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7. rewrite H.
assert (2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
     = 2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
        - 2 * (sin ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 ξ) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   = 2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
    - 2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 ξ) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² -
 (2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)) +
 (2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) +
 sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ2 / 2) * cos (θ2 / 2)))
  = (sin ξ * cos (θ1 / 2) * cos (θ2 / 2)) * (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
autorewrite with R_db.
rewrite Rmult_assoc.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
rewrite <- sin_2a.
assert ((2 * (θ1 * / 2)) = θ1) by lra.
rewrite H7. clear H7.
rewrite rm21_eq in eq5. lra.
assumption. assumption.
(* when rm02 < 0 *)
destruct (rm02 θ1 ξ θ2 <? 0) eqn:eq7.
destruct (0 <=? rm12 θ1 ξ θ2) eqn:eq8.
apply Rltb_lt in eq7.
assert ((PI / 2 + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2) + PI))
  = PI + (PI / 2 - (- (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2))))) by lra.
rewrite H6. clear H6.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite sin_shift. rewrite cos_shift.
rewrite sin_neg. rewrite cos_neg.
rewrite Ropp_involutive.
rewrite rm12_sin_neg.
rewrite rm12_cos_neg.
rewrite <- Rsqr_neg.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite Rsqr_mult in H6.
rewrite <- H6.
rewrite rm20_eq in H.
rewrite H.
assert (√ (0² + (sin ξ)² * (sin θ1)²) = (sin ξ * sin θ1)).
assert (Rsqr 0 = 0).
unfold Rsqr. lra.
rewrite H7.
rewrite <- Rsqr_mult.
rewrite Rplus_0_l.
rewrite sqrt_Rsqr. reflexivity.
rewrite rm21_eq in eq5. lra.
rewrite H7. clear H7.
assert ((- (- (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1)))%R
   = (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1)%R) by lra.
rewrite H7. clear H7.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (- (sin ξ * sin θ2) / (sin ξ * sin θ1)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1))
  = (- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ * (2 * sin (θ2/2) * cos (θ2/2))
     + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))
           / (sin ξ * (2 * sin (θ1/2) * cos (θ1/2)))).
rewrite <- sin_2a. rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H8.
lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (- (sin ξ * sin θ2) / (sin ξ * sin θ1))
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
   * (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)
   + sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ2/2) * cos (θ2/2)))
 / (sin ξ * (2 * sin (θ1/2) * cos (θ1/2)))).
rewrite <- sin_2a. rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H8.
lra.
rewrite H7. clear H7.
rewrite <- rm02_eq.
rewrite rm02_diff.
rewrite <- rm20_eq in H.
rewrite rm20_diff in H.
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_plus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²)
  = 2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² 
    - 2 * sin ξ * sin (θ2 / 2) * Rsqr (cos (θ1 / 2)) * cos (θ1 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
  = 2 * sin ξ * Rsqr (sin (θ1 / 2)) * cos (θ1 / 2) * sin (θ2 / 2)
    - 2 * sin ξ * Rsqr (sin (θ1 / 2)) * cos (θ1 / 2) * sin (θ2 / 2) * Rsqr (cos (θ2 / 2))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ1 / 2) * cos (θ2 / 2) * Rsqr (cos (θ2 / 2))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ * cos ξ * sin (θ1 / 2) * Rsqr (sin (θ2 / 2)) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * Rsqr (sin (θ2 / 2)) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * sin (θ2 / 2) * (cos (θ1 / 2))² * cos (θ1 / 2) * (cos (θ2 / 2))² -
   (2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
    2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) +
   (2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) -
    2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) * (cos (θ2 / 2))²) -
   (2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
    2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) * (cos (θ1 / 2))²))
  = - sin ξ * cos (θ1 / 2) * cos (θ2 / 2) *
     (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
    + 2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²
    - 2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
    + 2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
  (2 * sin (θ2 / 2) * cos (θ2 / 2)) +
  (2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) +
   2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) -
   2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)))
  = (- sin (θ2 / 2) * sin (θ1 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) *
     (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))).
unfold Rsqr. lra. 
rewrite H7. clear H7.
rewrite (Rmult_minus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_plus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_minus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite Rmult_minus_distr_r. rewrite Rmult_minus_distr_r. 
rewrite Rmult_minus_distr_r. rewrite Rmult_minus_distr_r.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²)
   = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
     - (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) *(sin (θ2 / 2))² *  cos (θ1 / 2)))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2/ 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
   = 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²
    - cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))²) * (sin (θ1 / 2))²).
assert ((sin (θ1/ 2))² = 1 - (cos (θ1/ 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ1 / 2)) -
 cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²) -
 (2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² -
  cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))²) * (sin (θ1 / 2))² -
  cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²))
  = - sin (θ1 / 2) * sin (θ2 / 2) *
     (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
     + 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
     -2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H7. clear H7. rewrite H.
assert (cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
   = 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
     - 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2/ 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
    = 2 * (cos ξ)² *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
      - cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1/ 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² +
(cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) -
  (2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²)) -
 (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) -
  (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   cos ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))))
  = cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
    (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
    + 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) 
    - 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² 
    - 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
    + 2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7. rewrite H.
assert (2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
     = 2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
        - 2 * (sin ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 ξ) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   = 2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
    - 2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 ξ) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² -
 (2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)) +
 (2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) +
 sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ2 / 2) * cos (θ2 / 2)))
  = (sin ξ * cos (θ1 / 2) * cos (θ2 / 2)) * (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
autorewrite with R_db.
rewrite Rmult_assoc.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
rewrite <- sin_2a.
assert ((2 * (θ1 * / 2)) = θ1) by lra.
rewrite H7. clear H7.
rewrite rm21_eq in eq5. lra.
assumption. assumption.
(* when rm20 = 0 and rm02 < 0 and rm12 < 0. *)
apply Rltb_lt in eq7.
assert ((PI / 2 + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2) - PI))
  = - (PI - (PI / 2 - (- (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2)))))) by lra.
rewrite H6. clear H6.
rewrite sin_neg. rewrite cos_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite sin_shift. rewrite cos_shift.
rewrite sin_neg. rewrite cos_neg.
rewrite Ropp_involutive.
rewrite rm12_sin_neg.
rewrite rm12_cos_neg.
rewrite <- Rsqr_neg.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite Rsqr_mult in H6.
rewrite <- H6.
rewrite rm20_eq in H.
rewrite H.
assert (√ (0² + (sin ξ)² * (sin θ1)²) = (sin ξ * sin θ1)).
assert (Rsqr 0 = 0).
unfold Rsqr. lra.
rewrite H7.
rewrite <- Rsqr_mult.
rewrite Rplus_0_l.
rewrite sqrt_Rsqr. reflexivity.
rewrite rm21_eq in eq5. lra.
rewrite H7. clear H7.
assert ((- (- (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1)))%R
   = (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1)%R) by lra.
rewrite H7. clear H7.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (- (sin ξ * sin θ2) / (sin ξ * sin θ1)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1))
  = (- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ * (2 * sin (θ2/2) * cos (θ2/2))
     + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))
           / (sin ξ * (2 * sin (θ1/2) * cos (θ1/2)))).
rewrite <- sin_2a. rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H8.
lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (- (sin ξ * sin θ2) / (sin ξ * sin θ1))
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
   * (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)
   + sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ2/2) * cos (θ2/2)))
 / (sin ξ * (2 * sin (θ1/2) * cos (θ1/2)))).
rewrite <- sin_2a. rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H8.
lra.
rewrite H7. clear H7.
rewrite <- rm02_eq.
rewrite rm02_diff.
rewrite <- rm20_eq in H.
rewrite rm20_diff in H.
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_plus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²)
  = 2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² 
    - 2 * sin ξ * sin (θ2 / 2) * Rsqr (cos (θ1 / 2)) * cos (θ1 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
  = 2 * sin ξ * Rsqr (sin (θ1 / 2)) * cos (θ1 / 2) * sin (θ2 / 2)
    - 2 * sin ξ * Rsqr (sin (θ1 / 2)) * cos (θ1 / 2) * sin (θ2 / 2) * Rsqr (cos (θ2 / 2))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ1 / 2) * cos (θ2 / 2) * Rsqr (cos (θ2 / 2))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ * cos ξ * sin (θ1 / 2) * Rsqr (sin (θ2 / 2)) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * Rsqr (sin (θ2 / 2)) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * sin (θ2 / 2) * (cos (θ1 / 2))² * cos (θ1 / 2) * (cos (θ2 / 2))² -
   (2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
    2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) +
   (2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) -
    2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) * (cos (θ2 / 2))²) -
   (2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
    2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) * (cos (θ1 / 2))²))
  = - sin ξ * cos (θ1 / 2) * cos (θ2 / 2) *
     (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
    + 2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²
    - 2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
    + 2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
  (2 * sin (θ2 / 2) * cos (θ2 / 2)) +
  (2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) +
   2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) -
   2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)))
  = (- sin (θ2 / 2) * sin (θ1 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) *
     (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))).
unfold Rsqr. lra. 
rewrite H7. clear H7.
rewrite (Rmult_minus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_plus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_minus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite Rmult_minus_distr_r. rewrite Rmult_minus_distr_r. 
rewrite Rmult_minus_distr_r. rewrite Rmult_minus_distr_r.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²)
   = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
     - (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) *(sin (θ2 / 2))² *  cos (θ1 / 2)))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2/ 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
   = 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²
    - cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))²) * (sin (θ1 / 2))²).
assert ((sin (θ1/ 2))² = 1 - (cos (θ1/ 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ1 / 2)) -
 cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²) -
 (2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² -
  cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))²) * (sin (θ1 / 2))² -
  cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²))
  = - sin (θ1 / 2) * sin (θ2 / 2) *
     (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
     + 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
     -2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H7. clear H7. rewrite H.
assert (cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
   = 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
     - 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2/ 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
    = 2 * (cos ξ)² *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
      - cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1/ 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² +
(cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) -
  (2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²)) -
 (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) -
  (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   cos ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))))
  = cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
    (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
    + 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) 
    - 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² 
    - 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
    + 2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7. rewrite H.
assert (2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
     = 2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
        - 2 * (sin ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 ξ) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   = 2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
    - 2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 ξ) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² -
 (2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)) +
 (2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) +
 sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ2 / 2) * cos (θ2 / 2)))
  = (sin ξ * cos (θ1 / 2) * cos (θ2 / 2)) * (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
autorewrite with R_db.
rewrite Rmult_assoc.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
rewrite <- sin_2a.
assert ((2 * (θ1 * / 2)) = θ1) by lra.
rewrite H7. clear H7.
rewrite rm21_eq in eq5. lra.
assumption. assumption.
(* when rm20 = 0 and rm02 = 0*)
apply Rltb_le_false in eq6.
apply Rltb_le_false in eq7.
assert (rm02 θ1 ξ θ2 = 0) by lra.
destruct (0 <? rm12 θ1 ξ θ2) eqn:eq8.
apply Rltb_lt in eq8.
assert ((PI / 2 + PI / 2) = PI) by lra.
rewrite H7. clear H7. 
rewrite cos_PI. rewrite sin_PI.
rewrite Cmult_c.
rewrite Rmult_0_r. rewrite Rmult_0_r.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H7. rewrite H6 in H7.
assert ((rm21 θ1 ξ θ2)² = (rm12 θ1 ξ θ2)²) by lra.
apply Rsqr_inj in H8.
assert (eq10 := eq8).
assert (eq9 := eq5).
rewrite rm12_eq in eq10. rewrite rm21_eq in eq9.
assert (sin ξ * sin θ2 <> 0) by lra.
assert (sin ξ * sin θ1 <> 0) by lra.
apply Rmult_neq_0_reg in H9.
apply Rmult_neq_0_reg in H10.
destruct H9. destruct H10.
unfold rm21,rm12 in H8.
assert (2 * rx θ1 ξ θ2 * rw θ1 ξ θ2 = 0) by lra.
unfold rx,rw in H13.
assert ((2 * sin (ξ / 2) * cos (ξ / 2)) * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)) *
                  (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)) = 0) by lra.
rewrite <- sin_2a in H14.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H15 in H14.
apply Rmult_integral in H14.
destruct H14.
apply Rmult_integral in H14.
destruct H14. lra.
assert (rx θ1 ξ θ2 = 0).
unfold rx. rewrite H14. lra.
unfold rm02 in H6.
assert ((ry θ1 ξ θ2)*(rw θ1 ξ θ2) = 0).
rewrite H16 in H6. lra.
unfold ry,rw in H17.
assert (cos (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2)) *
      (cos (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
  = (cos (ξ / 2))² * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))
        * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2))).
unfold Rsqr. lra.
rewrite H18 in H17. clear H18.
apply Rmult_integral in H17.
destruct H17.
apply Rmult_integral in H17.
destruct H17.
apply Rsqr_eq_0 in H17.
assert (sin ξ = 2 * sin (ξ/2) * cos (ξ/2)).
rewrite <- sin_2a. assert  (2 * (ξ / 2) = ξ) by lra. 
rewrite H18. reflexivity.
rewrite H18 in H9. rewrite H17 in H9. lra.
unfold rm12 in eq8.
assert (ry θ1 ξ θ2 = 0).
unfold ry. rewrite H17. lra.
rewrite H18 in eq8. rewrite H16 in eq8.
lra.
assert (cos (θ1 / 2) * cos (θ2 / 2) = sin (θ1 / 2) * sin (θ2 / 2)) by lra.
rewrite H18.
rewrite (Cmult_comm (cos ξ, sin ξ)).
rewrite (Cmult_assoc (cos (θ2 / 2))).
rewrite (Cmult_comm (cos (θ2 / 2))).
rewrite <- RtoC_mult.
rewrite <- RtoC_mult.
rewrite H18. lca.
assert (cos (θ1 / 2) * cos (θ2 / 2) = sin (θ1 / 2) * sin (θ2 / 2)) by lra.
rewrite H16.
rewrite (Cmult_comm (cos ξ, sin ξ)).
rewrite (Cmult_assoc (cos (θ2 / 2))).
rewrite (Cmult_comm (cos (θ2 / 2))).
rewrite <- RtoC_mult.
rewrite <- RtoC_mult.
rewrite H16. lca.
lra. lra.
destruct (rm12 θ1 ξ θ2 <? 0) eqn:eq9.
apply Rltb_lt in eq9.
assert ((PI / 2 + - PI / 2) = 0) by lra.
rewrite H7. clear H7.
rewrite sin_0. rewrite cos_0.
rewrite Cmult_c.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H7. rewrite H6 in H7.
assert ((rm21 θ1 ξ θ2)² = (rm12 θ1 ξ θ2)²) by lra.
rewrite (Rsqr_neg (rm12 θ1 ξ θ2)) in H8. 
apply Rsqr_inj in H8.
assert (eq10 := eq9).
assert (eq11 := eq5).
rewrite rm12_eq in eq10. rewrite rm21_eq in eq11.
assert (sin ξ * sin θ2 <> 0) by lra.
assert (sin ξ * sin θ1 <> 0) by lra.
apply Rmult_neq_0_reg in H9.
apply Rmult_neq_0_reg in H10.
destruct H9. destruct H10.
unfold rm21,rm12 in H8.
assert (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 = 0) by lra.
unfold ry,rz in H13.
assert ((2 * sin (ξ / 2) * cos (ξ / 2)) * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2)) *
                  (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)) = 0) by lra.
rewrite <- sin_2a in H14.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H15 in H14.
apply Rmult_integral in H14.
destruct H14.
apply Rmult_integral in H14.
destruct H14. lra.
assert (ry θ1 ξ θ2 = 0).
unfold ry. rewrite H14. lra.
unfold rm02 in H6.
assert (rx θ1 ξ θ2 * rz θ1 ξ θ2 = 0).
rewrite H16 in H6. lra.
unfold rx,rz in H17.
assert (sin (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)) *
      (sin (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))
  = (sin (ξ / 2))² * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))
        * (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))).
unfold Rsqr. lra.
rewrite H18 in H17. clear H18.
apply Rmult_integral in H17.
destruct H17.
apply Rmult_integral in H17.
destruct H17.
apply Rsqr_eq_0 in H17.
assert (sin ξ = 2 * sin (ξ/2) * cos (ξ/2)).
rewrite <- sin_2a. assert  (2 * (ξ / 2) = ξ) by lra. 
rewrite H18. reflexivity.
rewrite H18 in H9. rewrite H17 in H9. lra.
unfold rm12 in eq9.
assert (rx θ1 ξ θ2 = 0).
unfold rx. rewrite H17. lra.
rewrite H18 in eq9. rewrite H16 in eq9.
lra.
assert (cos (θ1 / 2) * cos (θ2 / 2) = - sin (θ1 / 2) * sin (θ2 / 2)) by lra.
rewrite H18.
rewrite (Cmult_comm (cos ξ, sin ξ)).
rewrite (Cmult_assoc (cos (θ2 / 2))).
rewrite (Cmult_comm (cos (θ2 / 2))).
rewrite <- RtoC_mult.
rewrite <- RtoC_mult.
rewrite H18. lca.
assert (cos (θ1 / 2) * cos (θ2 / 2) = - sin (θ1 / 2) * sin (θ2 / 2)) by lra.
rewrite H16.
rewrite (Cmult_comm (cos ξ, sin ξ)).
rewrite (Cmult_assoc (cos (θ2 / 2))).
rewrite (Cmult_comm (cos (θ2 / 2))).
rewrite <- RtoC_mult.
rewrite <- RtoC_mult.
rewrite H16. lca.
lra. lra.
apply Rltb_le_false in eq8.
apply Rltb_le_false in eq9.
assert (rm12 θ1 ξ θ2 = 0) by lra.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H8. rewrite H6 in H8.
rewrite H7 in H8.
assert ((rm21 θ1 ξ θ2)² = 0).
unfold Rsqr in H8.
unfold Rsqr. lra.
apply Rsqr_eq_0 in H9. lra.

(* when rm20 = 0, rm 21 < 0. *)
destruct (rm21 θ1 ξ θ2 <? 0) eqn:eq6.
destruct (0 <? rm02 θ1 ξ θ2) eqn:eq7.
apply Rltb_lt in eq7.
apply Rltb_lt in eq6.
assert ((- PI / 2 + atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2))
   = -(PI / 2 - (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2)))) by lra.
rewrite H6. clear H6.
rewrite sin_neg. rewrite cos_neg.
rewrite sin_shift. rewrite cos_shift.
rewrite rm12_sin.
rewrite rm12_cos.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite Rsqr_mult in H6.
rewrite <- H6.
rewrite rm20_eq in H.
rewrite H.
assert (√ (0² + (sin ξ)² * (sin θ1)²) = -(sin ξ * sin θ1)).
assert (Rsqr 0 = 0).
unfold Rsqr. lra.
rewrite H7.
rewrite <- Rsqr_mult.
rewrite Rsqr_neg.
rewrite Rplus_0_l.
rewrite sqrt_Rsqr. reflexivity.
rewrite rm21_eq in eq6. lra.
rewrite H7. clear H7.
assert ((sin ξ * sin θ2 / - (sin ξ * sin θ1))%R = - (sin ξ * sin θ2) / (sin ξ * sin θ1)).
autorewrite with R_db. rewrite <- Ropp_inv_permute. lra.
rewrite rm21_eq in eq6. lra.
assert ((- ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / - (sin ξ * sin θ1)))%R
  =  ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) /(sin ξ * sin θ1))%R).
autorewrite with R_db. rewrite <- Ropp_inv_permute. lra.
rewrite rm21_eq in eq6. lra.
rewrite H7. rewrite H8. clear H7. clear H8.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (- (sin ξ * sin θ2) / (sin ξ * sin θ1)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1))
  = (- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ * (2 * sin (θ2/2) * cos (θ2/2))
     + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))
           / (sin ξ * (2 * sin (θ1/2) * cos (θ1/2)))).
rewrite <- sin_2a. rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H8.
lra.
rewrite H7. clear H7.
assert (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (- (sin ξ * sin θ2) / (sin ξ * sin θ1)))
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
   * (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)
   + sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ2/2) * cos (θ2/2)))
 / (sin ξ * (2 * sin (θ1/2) * cos (θ1/2)))).
rewrite <- sin_2a. rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H8.
lra.
rewrite H7. clear H7.
rewrite <- rm02_eq.
rewrite rm02_diff.
rewrite <- rm20_eq in H.
rewrite rm20_diff in H.
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_plus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²)
  = 2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² 
    - 2 * sin ξ * sin (θ2 / 2) * Rsqr (cos (θ1 / 2)) * cos (θ1 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
  = 2 * sin ξ * Rsqr (sin (θ1 / 2)) * cos (θ1 / 2) * sin (θ2 / 2)
    - 2 * sin ξ * Rsqr (sin (θ1 / 2)) * cos (θ1 / 2) * sin (θ2 / 2) * Rsqr (cos (θ2 / 2))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ1 / 2) * cos (θ2 / 2) * Rsqr (cos (θ2 / 2))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ * cos ξ * sin (θ1 / 2) * Rsqr (sin (θ2 / 2)) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * Rsqr (sin (θ2 / 2)) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * sin (θ2 / 2) * (cos (θ1 / 2))² * cos (θ1 / 2) * (cos (θ2 / 2))² -
   (2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
    2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) +
   (2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) -
    2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) * (cos (θ2 / 2))²) -
   (2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
    2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) * (cos (θ1 / 2))²))
  = - sin ξ * cos (θ1 / 2) * cos (θ2 / 2) *
     (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
    + 2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²
    - 2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
    + 2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
  (2 * sin (θ2 / 2) * cos (θ2 / 2)) +
  (2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) +
   2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) -
   2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)))
  = (- sin (θ2 / 2) * sin (θ1 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) *
     (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))).
unfold Rsqr. lra. 
rewrite H7. clear H7.
rewrite (Rmult_minus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_plus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_minus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite Rmult_minus_distr_r. rewrite Rmult_minus_distr_r. 
rewrite Rmult_minus_distr_r. rewrite Rmult_minus_distr_r.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²)
   = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
     - (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) *(sin (θ2 / 2))² *  cos (θ1 / 2)))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2/ 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
   = 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²
    - cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))²) * (sin (θ1 / 2))²).
assert ((sin (θ1/ 2))² = 1 - (cos (θ1/ 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ1 / 2)) -
 cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²) -
 (2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² -
  cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))²) * (sin (θ1 / 2))² -
  cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²))
  = - sin (θ1 / 2) * sin (θ2 / 2) *
     (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
     + 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
     -2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H7. clear H7. rewrite H.
assert (cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
   = 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
     - 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2/ 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
    = 2 * (cos ξ)² *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
      - cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1/ 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² +
(cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) -
  (2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²)) -
 (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) -
  (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   cos ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))))
  = cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
    (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
    + 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) 
    - 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² 
    - 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
    + 2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7. rewrite H.
assert (2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
     = 2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
        - 2 * (sin ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 ξ) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   = 2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
    - 2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 ξ) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² -
 (2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)) +
 (2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) +
 sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ2 / 2) * cos (θ2 / 2)))
  = (sin ξ * cos (θ1 / 2) * cos (θ2 / 2)) * (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
autorewrite with R_db.
rewrite Rmult_assoc.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
rewrite <- sin_2a.
assert ((2 * (θ1 * / 2)) = θ1) by lra.
rewrite H7. clear H7.
rewrite rm21_eq in eq6. lra.
assumption. assumption.
(* when rm20 = 0 , and rm02 < 0 and rm21 < 0 *)
apply Rltb_lt in eq6.
destruct (rm02 θ1 ξ θ2 <? 0) eqn:eq8.
destruct (0 <=? rm12 θ1 ξ θ2) eqn:eq9.
apply Rltb_lt in eq8.
assert ((-PI / 2 + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2) + PI))
  = PI - (PI / 2 - (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2)))) by lra.
rewrite H6. clear H6.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite sin_shift. rewrite cos_shift.
rewrite rm12_sin_neg.
rewrite rm12_cos_neg.
rewrite <- Rsqr_neg.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite Rsqr_mult in H6.
rewrite <- H6.
rewrite rm20_eq in H.
rewrite H.
assert (√ (0² + (sin ξ)² * (sin θ1)²) = -(sin ξ * sin θ1)).
assert (Rsqr 0 = 0).
unfold Rsqr. lra.
rewrite H7.
rewrite <- Rsqr_mult.
rewrite Rsqr_neg.
rewrite Rplus_0_l.
rewrite sqrt_Rsqr. reflexivity.
rewrite rm21_eq in eq6. lra.
rewrite H7. clear H7.
assert ((- (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / - (sin ξ * sin θ1))%R
   = (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1)%R).
autorewrite with R_db. rewrite <- Ropp_inv_permute. lra.
rewrite rm21_eq in eq6. lra.
rewrite H7. clear H7.
assert ((- (- (sin ξ * sin θ2) / - (sin ξ * sin θ1)))%R = (- (sin ξ * sin θ2) / (sin ξ * sin θ1))).
autorewrite with R_db. rewrite <- Ropp_inv_permute. lra.
rewrite rm21_eq in eq6. lra.
rewrite H7. clear H7.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (- (sin ξ * sin θ2) / (sin ξ * sin θ1)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1))
  = (- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ * (2 * sin (θ2/2) * cos (θ2/2))
     + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))
           / (sin ξ * (2 * sin (θ1/2) * cos (θ1/2)))).
rewrite <- sin_2a. rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H8.
lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (- (sin ξ * sin θ2) / (sin ξ * sin θ1))
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
   * (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)
   + sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ2/2) * cos (θ2/2)))
 / (sin ξ * (2 * sin (θ1/2) * cos (θ1/2)))).
rewrite <- sin_2a. rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H8.
lra.
rewrite H7. clear H7.
rewrite <- rm02_eq.
rewrite rm02_diff.
rewrite <- rm20_eq in H.
rewrite rm20_diff in H.
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_plus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²)
  = 2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² 
    - 2 * sin ξ * sin (θ2 / 2) * Rsqr (cos (θ1 / 2)) * cos (θ1 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
  = 2 * sin ξ * Rsqr (sin (θ1 / 2)) * cos (θ1 / 2) * sin (θ2 / 2)
    - 2 * sin ξ * Rsqr (sin (θ1 / 2)) * cos (θ1 / 2) * sin (θ2 / 2) * Rsqr (cos (θ2 / 2))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ1 / 2) * cos (θ2 / 2) * Rsqr (cos (θ2 / 2))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ * cos ξ * sin (θ1 / 2) * Rsqr (sin (θ2 / 2)) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * Rsqr (sin (θ2 / 2)) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * sin (θ2 / 2) * (cos (θ1 / 2))² * cos (θ1 / 2) * (cos (θ2 / 2))² -
   (2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
    2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) +
   (2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) -
    2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) * (cos (θ2 / 2))²) -
   (2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
    2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) * (cos (θ1 / 2))²))
  = - sin ξ * cos (θ1 / 2) * cos (θ2 / 2) *
     (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
    + 2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²
    - 2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
    + 2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
  (2 * sin (θ2 / 2) * cos (θ2 / 2)) +
  (2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) +
   2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) -
   2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)))
  = (- sin (θ2 / 2) * sin (θ1 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) *
     (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))).
unfold Rsqr. lra. 
rewrite H7. clear H7.
rewrite (Rmult_minus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_plus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_minus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite Rmult_minus_distr_r. rewrite Rmult_minus_distr_r. 
rewrite Rmult_minus_distr_r. rewrite Rmult_minus_distr_r.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²)
   = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
     - (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) *(sin (θ2 / 2))² *  cos (θ1 / 2)))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2/ 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
   = 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²
    - cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))²) * (sin (θ1 / 2))²).
assert ((sin (θ1/ 2))² = 1 - (cos (θ1/ 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ1 / 2)) -
 cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²) -
 (2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² -
  cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))²) * (sin (θ1 / 2))² -
  cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²))
  = - sin (θ1 / 2) * sin (θ2 / 2) *
     (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
     + 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
     -2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H7. clear H7. rewrite H.
assert (cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
   = 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
     - 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2/ 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
    = 2 * (cos ξ)² *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
      - cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1/ 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² +
(cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) -
  (2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²)) -
 (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) -
  (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   cos ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))))
  = cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
    (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
    + 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) 
    - 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² 
    - 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
    + 2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7. rewrite H.
assert (2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
     = 2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
        - 2 * (sin ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 ξ) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   = 2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
    - 2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 ξ) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² -
 (2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)) +
 (2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) +
 sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ2 / 2) * cos (θ2 / 2)))
  = (sin ξ * cos (θ1 / 2) * cos (θ2 / 2)) * (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
autorewrite with R_db.
rewrite Rmult_assoc.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
rewrite <- sin_2a.
assert ((2 * (θ1 * / 2)) = θ1) by lra.
rewrite H7. clear H7.
rewrite rm21_eq in eq6. lra.
assumption. assumption.
(* when rm20 = 0 and rm02 < 0 and rm12 < 0. *)
apply Rltb_lt in eq8.
assert ((- PI / 2 + (atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2) - PI))
  = - (PI + (PI / 2 - ((atan (rm12 θ1 ξ θ2 / rm02 θ1 ξ θ2)))))) by lra.
rewrite H6. clear H6.
rewrite sin_neg. rewrite cos_neg.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite sin_shift. rewrite cos_shift.
rewrite Ropp_involutive.
rewrite rm12_sin_neg.
rewrite rm12_cos_neg.
rewrite <- Rsqr_neg.
assert (((cos θ1 * sin θ2 + cos ξ * sin θ1 * cos θ2)² + (sin ξ)² * (sin θ1)²)
  = ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)² + (sin ξ * sin θ2)²)).
rewrite <- rm02_eq.
rewrite <- (rm12_eq θ1 ξ θ2).
rewrite <- rm20_eq.
rewrite <- Rsqr_mult.
rewrite <- (rm21_eq θ1 ξ θ2).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite Rsqr_mult in H6.
rewrite <- H6.
rewrite rm20_eq in H.
rewrite H.
assert (√ (0² + (sin ξ)² * (sin θ1)²) = -(sin ξ * sin θ1)).
assert (Rsqr 0 = 0).
unfold Rsqr. lra.
rewrite H7.
rewrite <- Rsqr_mult.
rewrite Rsqr_neg.
rewrite Rplus_0_l.
rewrite sqrt_Rsqr. reflexivity.
rewrite rm21_eq in eq6. lra.
rewrite H7. clear H7.
assert (((- (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / -(sin ξ * sin θ1)))%R
   = (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1)%R).
autorewrite with R_db. rewrite <- Ropp_inv_permute. lra.
rewrite rm21_eq in eq6. lra.
rewrite H7. clear H7.
assert ((- (- (sin ξ * sin θ2) / - (sin ξ * sin θ1)))%R = (- (sin ξ * sin θ2) / (sin ξ * sin θ1))).
autorewrite with R_db. rewrite <- Ropp_inv_permute. lra.
rewrite rm21_eq in eq6. lra.
rewrite H7. clear H7.
rewrite Cmult_c.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
 (- (sin ξ * sin θ2) / (sin ξ * sin θ1)) -
 - sin ξ * sin (θ1 / 2) * sin (θ2 / 2) *
 ((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1))
  = (- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ * (2 * sin (θ2/2) * cos (θ2/2))
     + sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2))
           / (sin ξ * (2 * sin (θ1/2) * cos (θ1/2)))).
rewrite <- sin_2a. rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H8.
lra.
rewrite H7. clear H7.
assert ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
((sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2) / (sin ξ * sin θ1)) +
- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (- (sin ξ * sin θ2) / (sin ξ * sin θ1))
 = ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))
   * (sin θ1 * cos θ2 + cos ξ * cos θ1 * sin θ2)
   + sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ2/2) * cos (θ2/2)))
 / (sin ξ * (2 * sin (θ1/2) * cos (θ1/2)))).
rewrite <- sin_2a. rewrite <- sin_2a.
assert ((2 * (θ2 / 2)) = θ2) by lra.
rewrite H7.
assert ((2 * (θ1 / 2)) = θ1) by lra.
rewrite H8.
lra.
rewrite H7. clear H7.
rewrite <- rm02_eq.
rewrite rm02_diff.
rewrite <- rm20_eq in H.
rewrite rm20_diff in H.
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_plus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
rewrite (Rmult_minus_distr_l (sin ξ * sin (θ1 / 2) * sin (θ2 / 2))).
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²)
  = 2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² 
    - 2 * sin ξ * sin (θ2 / 2) * Rsqr (cos (θ1 / 2)) * cos (θ1 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
  = 2 * sin ξ * Rsqr (sin (θ1 / 2)) * cos (θ1 / 2) * sin (θ2 / 2)
    - 2 * sin ξ * Rsqr (sin (θ1 / 2)) * cos (θ1 / 2) * sin (θ2 / 2) * Rsqr (cos (θ2 / 2))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * Rsqr (cos (θ1 / 2)) * sin (θ1 / 2) * cos (θ2 / 2) * Rsqr (cos (θ2 / 2))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2 / 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
  = 2 * sin ξ * cos ξ * sin (θ1 / 2) * Rsqr (sin (θ2 / 2)) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * Rsqr (sin (θ2 / 2)) * cos (θ2 / 2) * (cos (θ1 / 2))²).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1 / 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * sin (θ2 / 2) * (cos (θ1 / 2))² * cos (θ1 / 2) * (cos (θ2 / 2))² -
   (2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) -
    2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) * (cos (θ2 / 2))²) +
   (2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) -
    2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) * (cos (θ2 / 2))²) -
   (2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) -
    2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2) * (cos (θ1 / 2))²))
  = - sin ξ * cos (θ1 / 2) * cos (θ2 / 2) *
     (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
    + 2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²
    - 2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2)
    + 2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2)
    - 2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite H.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert ((- (cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) * sin ξ *
  (2 * sin (θ2 / 2) * cos (θ2 / 2)) +
  (2 * sin ξ * sin (θ2 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
   2 * sin ξ * (sin (θ1 / 2))² * cos (θ1 / 2) * sin (θ2 / 2) +
   2 * sin ξ * cos ξ * (cos (θ1 / 2))² * sin (θ1 / 2) * cos (θ2 / 2) -
   2 * sin ξ * cos ξ * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ2 / 2)))
  = (- sin (θ2 / 2) * sin (θ1 / 2) + cos ξ * cos (θ1 / 2) * cos (θ2 / 2)) *
     (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))).
unfold Rsqr. lra. 
rewrite H7. clear H7.
rewrite (Rmult_minus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_plus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite (Rmult_minus_distr_l ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)))).
rewrite Rmult_minus_distr_r. rewrite Rmult_minus_distr_r. 
rewrite Rmult_minus_distr_r. rewrite Rmult_minus_distr_r.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²)
   = 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
     - (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) *(sin (θ2 / 2))² *  cos (θ1 / 2)))).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2/ 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
   = 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²
    - cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))²) * (sin (θ1 / 2))²).
assert ((sin (θ1/ 2))² = 1 - (cos (θ1/ 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 cos (θ1 / 2) * cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))² * cos (θ1 / 2)) -
 cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))²) -
 (2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² -
  cos (θ2 / 2) * (2 * sin (θ1 / 2) * (sin (θ2 / 2))²) * (sin (θ1 / 2))² -
  cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²))
  = - sin (θ1 / 2) * sin (θ2 / 2) *
     (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
     + 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2)
     -2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))²).
unfold Rsqr. lra.
rewrite H7. clear H7. rewrite H.
assert (cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
   = 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
     - 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²).
assert ((cos (θ2/ 2))² = 1 - (sin (θ2/ 2))²).
specialize (sin2_cos2 (θ2 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))
    = 2 * (cos ξ)² *  sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
      - cos ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))).
assert ((cos (θ1/ 2))² = 1 - (sin (θ1/ 2))²).
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
rewrite Rmult_0_r. rewrite Rplus_0_l.
assert (2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² +
(cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) -
  (2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
   2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) * (cos (θ2 / 2))²)) -
 (cos (θ1 / 2) * cos (θ2 / 2) * (2 * cos ξ * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2)) -
  (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
   cos ξ * sin (θ1 / 2) * sin (θ2 / 2) *
   (2 * cos ξ * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2))))
  = cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 
    (2 * (cos (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) -
    2 * (sin (θ1 / 2))² * sin (θ2 / 2) * cos (θ2 / 2) +
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (cos (θ2 / 2))² -
    2 * cos ξ * sin (θ1 / 2) * cos (θ1 / 2) * (sin (θ2 / 2))²)
    + 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) 
    - 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² 
    - 2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
    + 2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
unfold Rsqr. lra.
rewrite H7. clear H7. rewrite H.
assert (2 * (cos ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
     = 2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)
        - 2 * (sin ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 ξ) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert (2 * (cos ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
   = 2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)
    - 2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)).
assert ((cos ξ)² = 1 - (sin ξ)²).
specialize (sin2_cos2 ξ) as eqa.
rewrite <- eqa. lra. rewrite H7. unfold Rsqr. lra.
rewrite H7. clear H7.
assert ((cos ξ * cos (θ1 / 2) * cos (θ2 / 2) * 0 +
 2 * cos (θ1 / 2) * cos (θ2 / 2) * sin (θ1 / 2) * cos (θ1 / 2) -
 2 * sin (θ1 / 2) * cos (θ2 / 2) * (sin (θ2 / 2))² -
 (2 * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * (cos (θ1 / 2))² * cos (θ2 / 2)) +
 (2 * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2) -
  2 * (sin ξ)² * sin (θ1 / 2) * sin (θ2 / 2) * sin (θ2 / 2) * cos (θ2 / 2)) +
 sin ξ * sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * (2 * sin (θ2 / 2) * cos (θ2 / 2)))
  = (sin ξ * cos (θ1 / 2) * cos (θ2 / 2)) * (sin ξ * (2 * sin (θ1 / 2) * cos (θ1 / 2)))).
unfold Rsqr. lra.
rewrite H7. clear H7.
autorewrite with R_db.
rewrite Rmult_assoc.
rewrite (Rmult_assoc (sin ξ * cos (θ1 * / 2) * cos (θ2 * / 2))).
rewrite Rinv_r.
lca.
rewrite <- sin_2a.
assert ((2 * (θ1 * / 2)) = θ1) by lra.
rewrite H7. clear H7.
rewrite rm21_eq in eq6. lra.
assumption. assumption.
(* when rm20 = 0 and rm02 = 0*)
apply Rltb_le_false in eq7.
apply Rltb_le_false in eq8.
assert (rm02 θ1 ξ θ2 = 0) by lra.
destruct (0 <? rm12 θ1 ξ θ2) eqn:eq9.
apply Rltb_lt in eq9.
assert ((- PI / 2 + PI / 2) = 0) by lra.
rewrite H7. clear H7. 
rewrite cos_0. rewrite sin_0.
rewrite Cmult_c.
rewrite Rmult_0_r. rewrite Rmult_0_r.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H7. rewrite H6 in H7.
assert ((rm21 θ1 ξ θ2)² = (rm12 θ1 ξ θ2)²) by lra.
rewrite Rsqr_neg in H8.
apply Rsqr_inj in H8.
assert (eq10 := eq9).
assert (eq11 := eq6).
rewrite rm12_eq in eq10. rewrite rm21_eq in eq11.
assert (sin ξ * sin θ2 <> 0) by lra.
assert (sin ξ * sin θ1 <> 0) by lra.
apply Rmult_neq_0_reg in H9.
apply Rmult_neq_0_reg in H10.
destruct H9. destruct H10.
unfold rm21,rm12 in H8.
assert (2 * ry θ1 ξ θ2 * rz θ1 ξ θ2 = 0) by lra.
unfold ry,rz in H13.
assert ((2 * sin (ξ / 2) * cos (ξ / 2)) * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2)) *
                  (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)) = 0) by lra.
rewrite <- sin_2a in H14.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H15 in H14.
apply Rmult_integral in H14.
destruct H14.
apply Rmult_integral in H14.
destruct H14. lra.
assert (ry θ1 ξ θ2 = 0).
unfold ry. rewrite H14. lra.
unfold rm02 in H6.
assert (rx θ1 ξ θ2 * rz θ1 ξ θ2 = 0).
rewrite H16 in H6. lra.
unfold rx,rz in H17.
assert (sin (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)) *
      (sin (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))
  = (sin (ξ / 2))² * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))
        * (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))).
unfold Rsqr. lra.
rewrite H18 in H17. clear H18.
apply Rmult_integral in H17.
destruct H17.
apply Rmult_integral in H17.
destruct H17.
apply Rsqr_eq_0 in H17.
assert (sin ξ = 2 * sin (ξ/2) * cos (ξ/2)).
rewrite <- sin_2a. assert  (2 * (ξ / 2) = ξ) by lra. 
rewrite H18. reflexivity.
rewrite H18 in H9. rewrite H17 in H9. lra.
unfold rm12 in eq9.
assert (rx θ1 ξ θ2 = 0).
unfold rx. rewrite H17. lra.
rewrite H18 in eq9. rewrite H16 in eq9.
lra.
assert (cos (θ1 / 2) * cos (θ2 / 2) = - sin (θ1 / 2) * sin (θ2 / 2)) by lra.
rewrite H18.
rewrite (Cmult_comm (cos ξ, sin ξ)).
rewrite (Cmult_assoc (cos (θ2 / 2))).
rewrite (Cmult_comm (cos (θ2 / 2))).
rewrite <- RtoC_mult.
rewrite <- RtoC_mult.
rewrite H18. lca.
assert (cos (θ1 / 2) * cos (θ2 / 2) = - sin (θ1 / 2) * sin (θ2 / 2)) by lra.
rewrite H16.
rewrite (Cmult_comm (cos ξ, sin ξ)).
rewrite (Cmult_assoc (cos (θ2 / 2))).
rewrite (Cmult_comm (cos (θ2 / 2))).
rewrite <- RtoC_mult.
rewrite <- RtoC_mult.
rewrite H16. lca.
lra. lra.
(* when rm12 < 0, rm 21 < 0 rm20 = 0*)
destruct (rm12 θ1 ξ θ2 <? 0) eqn:eq10.
apply Rltb_lt in eq10.
assert ((- PI / 2 + - PI / 2) = - PI) by lra.
rewrite H7. clear H7.
rewrite sin_neg. rewrite cos_neg.
rewrite sin_PI. rewrite cos_PI.
rewrite Cmult_c.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H7. rewrite H6 in H7.
assert ((rm21 θ1 ξ θ2)² = (rm12 θ1 ξ θ2)²) by lra.
rewrite Rsqr_neg in H8.
rewrite (Rsqr_neg (rm12 θ1 ξ θ2)) in H8.
apply Rsqr_inj in H8.
assert (rm21 θ1 ξ θ2 = rm12 θ1 ξ θ2) as HA8  by lra.
assert (eq11 := eq10).
assert (eq12 := eq6).
rewrite rm12_eq in eq11. rewrite rm21_eq in eq12.
assert (sin ξ * sin θ2 <> 0) by lra.
assert (sin ξ * sin θ1 <> 0) by lra.
apply Rmult_neq_0_reg in H9.
apply Rmult_neq_0_reg in H10.
destruct H9. destruct H10.
unfold rm21,rm12 in H8.
assert (2 * rx θ1 ξ θ2 * rw θ1 ξ θ2 = 0) by lra.
unfold rx,rw in H13.
assert ((2 * sin (ξ / 2) * cos (ξ / 2)) * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)) *
                  (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)) = 0) by lra.
rewrite <- sin_2a in H14.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H15 in H14.
apply Rmult_integral in H14.
destruct H14.
apply Rmult_integral in H14.
destruct H14. lra.
assert (rx θ1 ξ θ2 = 0).
unfold rx. rewrite H14. lra.
unfold rm02 in H6.
assert ((ry θ1 ξ θ2)*(rw θ1 ξ θ2) = 0).
rewrite H16 in H6. lra.
unfold ry,rw in H17.
assert (cos (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2)) *
      (cos (ξ / 2) * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2)))
  = (cos (ξ / 2))² * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))
        * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2))).
unfold Rsqr. lra.
rewrite H18 in H17. clear H18.
apply Rmult_integral in H17.
destruct H17.
apply Rmult_integral in H17.
destruct H17.
apply Rsqr_eq_0 in H17.
assert (sin ξ = 2 * sin (ξ/2) * cos (ξ/2)).
rewrite <- sin_2a. assert  (2 * (ξ / 2) = ξ) by lra. 
rewrite H18. reflexivity.
rewrite H18 in H9. rewrite H17 in H9. lra.
unfold rm12 in eq10.
assert (ry θ1 ξ θ2 = 0).
unfold ry. rewrite H17. lra.
rewrite H18 in eq10. rewrite H16 in eq10.
lra.
assert (cos (θ1 / 2) * cos (θ2 / 2) = sin (θ1 / 2) * sin (θ2 / 2)) by lra.
rewrite H18.
rewrite (Cmult_comm (cos ξ, sin ξ)).
rewrite (Cmult_assoc (cos (θ2 / 2))).
rewrite (Cmult_comm (cos (θ2 / 2))).
rewrite <- RtoC_mult.
rewrite <- RtoC_mult.
rewrite H18. lca.
assert (cos (θ1 / 2) * cos (θ2 / 2) = sin (θ1 / 2) * sin (θ2 / 2)) by lra.
rewrite H16.
rewrite (Cmult_comm (cos ξ, sin ξ)).
rewrite (Cmult_assoc (cos (θ2 / 2))).
rewrite (Cmult_comm (cos (θ2 / 2))).
rewrite <- RtoC_mult.
rewrite <- RtoC_mult.
rewrite H16. lca.
lra. lra.
apply Rltb_le_false in eq9.
apply Rltb_le_false in eq10.
assert (rm12 θ1 ξ θ2 = 0) by lra.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H8. rewrite H6 in H8.
rewrite H7 in H8.
assert ((rm21 θ1 ξ θ2)² = 0).
unfold Rsqr in H8.
unfold Rsqr. lra.
apply Rsqr_eq_0 in H9. lra.
apply Rltb_le_false in eq5.
apply Rltb_le_false in eq6.
(* when rm20 = 0, rm21 = 0*)
assert (rm21 θ1 ξ θ2 = 0) by lra.
destruct (0 <? rm02 θ1 ξ θ2) eqn:eq7.
apply Rltb_lt in eq7.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H7. rewrite H6 in H7.
assert (0 < (rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²).
assert (0 < (rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²) by apply Rle_0_sqr.
lra.
rewrite <- H7 in H8. unfold Rsqr in H8. lra.
destruct (rm02 θ1 ξ θ2 <? 0) eqn:eq8.
apply Rltb_lt in eq8.
destruct (0 <=? rm12 θ1 ξ θ2) eqn:eq9.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H7. rewrite H6 in H7.
rewrite (Rsqr_neg ((rm02 θ1 ξ θ2))) in H7.
assert (0 < (-rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²).
assert (0 < (-rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²) by apply Rle_0_sqr.
lra.
rewrite <- H7 in H8. unfold Rsqr in H8. lra.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H7. rewrite H6 in H7.
rewrite (Rsqr_neg ((rm02 θ1 ξ θ2))) in H7.
assert (0 < (-rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²).
assert (0 < (-rm02 θ1 ξ θ2)²).
apply Rsqr_pos_lt. lra.
assert (0 <= (rm12 θ1 ξ θ2)²) by apply Rle_0_sqr.
lra.
rewrite <- H7 in H8. unfold Rsqr in H8. lra.
apply Rltb_le_false in eq7.
apply Rltb_le_false in eq8.
assert (rm02 θ1 ξ θ2 = 0) by lra.
destruct (0 <? rm12 θ1 ξ θ2) eqn:eq9.
apply Rltb_lt in eq9.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H8. rewrite H6 in H8. rewrite H7 in H8.
assert ((rm12 θ1 ξ θ2)² = 0).
unfold Rsqr in H8. unfold Rsqr. lra.
apply Rsqr_eq_0 in H9. lra.
destruct (rm12 θ1 ξ θ2 <? 0) eqn:eq10.
apply Rltb_lt in eq10.
assert (((rm20_minus θ1 ξ θ2)² + (rm21 θ1 ξ θ2)²) = ((rm02 θ1 ξ θ2)² + (rm12 θ1 ξ θ2)²)).
unfold rm02,rm12,rm20_minus,rm21.
unfold Rsqr. lra.
rewrite H in H8. rewrite H6 in H8. rewrite H7 in H8.
assert ((rm12 θ1 ξ θ2)² = 0).
unfold Rsqr in H8. unfold Rsqr. lra.
apply Rsqr_eq_0 in H9. lra.
apply Rltb_le_false in eq9.
apply Rltb_le_false in eq10.
assert (rm12 θ1 ξ θ2 = 0) by lra.
rewrite Rplus_0_r.
rewrite cos_0. rewrite sin_0.
rewrite Cmult_c.
unfold rm21 in H6.
unfold rm12 in H8.
assert(2 * rx θ1 ξ θ2 * rw θ1 ξ θ2 = 0) by lra.
assert (2 * rx θ1 ξ θ2 * rw θ1 ξ θ2 = 
    2 * sin (ξ / 2) * cos (ξ / 2) * (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))
    * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2))).
unfold rx,rw. lra.
rewrite H10 in H9. clear H10.
rewrite <- sin_2a in H9.
assert ((2 * (ξ / 2)) = ξ) by lra.
rewrite H10 in H9. clear H10.
apply Rmult_integral in H9.
destruct H9.
apply Rmult_integral in H9.
destruct H9.
assert (cos ξ = 1 \/ cos ξ = -1).
specialize (sin2_cos2 ξ) as eqa.
rewrite H9 in eqa.
assert ((cos ξ)² = Rsqr 1).
unfold Rsqr. unfold Rsqr in eqa. lra.
apply Rsqr_eq in H10. assumption.
destruct H10.
rewrite H9. rewrite H10.
lca.
unfold rm20_minus in H. unfold rm02 in H7.
assert (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 = 0) by lra.
assert (2 * rx θ1 ξ θ2 * rz θ1 ξ θ2 = 2 * (sin (ξ / 2))² * 
        (sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)) *
        (cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))).
unfold rx,rz,Rsqr. lra. rewrite H12 in H11.
apply Rmult_integral in H11.
destruct H11.
apply Rmult_integral in H11.
destruct H11.
apply Rmult_integral in H11.
destruct H11. lra.
assert (cos ξ = 1).
assert (ξ = 2 * (ξ/2)) by lra.
rewrite H13.
rewrite cos_2a.
assert (((cos (ξ / 2))²) = 1).
specialize (sin2_cos2 (ξ / 2)) as eqa.
rewrite H11 in eqa. lra.
unfold Rsqr in H14. rewrite H14.
unfold Rsqr in H11. rewrite H11.
lra. lra.
rewrite H9. rewrite H10.
assert (((cos (ξ / 2))²) = 0 /\ (((sin (ξ / 2))²) = 1)).
assert (ξ = 2 * (ξ / 2)) by lra.
rewrite H13 in H10.
rewrite cos_2a in H10.
specialize (sin2_cos2 (ξ / 2)) as eqa.
unfold Rsqr in eqa.
assert (cos (ξ / 2) * cos (ξ / 2) = 0) by lra.
split. unfold Rsqr. assumption.
rewrite H14 in eqa.
unfold Rsqr. lra.
destruct H13.
assert (rm22 θ1 ξ θ2 = 1).
unfold rm22,rx,ry.
apply Rsqr_eq_0 in H13.
rewrite H13. rewrite H11. lra.
apply Rltb_lt in eq1. lra.
assert (cos (θ1 / 2) * cos (θ2 / 2) = - sin (θ1 / 2) * sin (θ2 / 2)) by lra.
rewrite (Cmult_comm (cos ξ, sin ξ)).
rewrite (Cmult_assoc (cos (θ2 / 2))).
rewrite (Cmult_comm (cos (θ2 / 2))).
rewrite <- RtoC_mult.
rewrite <- RtoC_mult.
rewrite H9. rewrite H10.
rewrite H13.
lca.
assert (rx θ1 ξ θ2 = 0).
unfold rx. rewrite H9. lra.
unfold rm02 in H7.
assert (ry θ1 ξ θ2 * rw θ1 ξ θ2 = 0).
rewrite H10 in H7. lra.
assert (ry θ1 ξ θ2 * rw θ1 ξ θ2 = Rsqr (cos (ξ/2))
              * (sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))
              * (cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2))).
unfold ry,rw,Rsqr. lra.
rewrite H12 in H11.
apply Rmult_integral in H11.
destruct H11.
apply Rmult_integral in H11.
destruct H11.
assert (rm22 θ1 ξ θ2 = 1).
unfold rm22. rewrite H10.
apply Rsqr_eq_0 in H11. unfold ry.
rewrite H11. lra.
apply Rltb_lt in eq1. lra.
assert (rm22 θ1 ξ θ2 = 1).
unfold rm22. rewrite H10.
unfold ry.
rewrite H11. lra.
apply Rltb_lt in eq1. lra.
rewrite (Cmult_comm (cos ξ, sin ξ)).
rewrite (Cmult_assoc (cos (θ2 / 2))).
rewrite (Cmult_comm (cos (θ2 / 2))).
rewrite <- RtoC_mult.
rewrite <- RtoC_mult.
assert (cos (θ1 / 2) * cos (θ2 / 2) = sin (θ1 / 2) * sin (θ2 / 2)) by lra.
rewrite H13.
assert (ry θ1 ξ θ2 * rz θ1 ξ θ2 = 0) by lra.
unfold ry,rz in H14.
apply Rmult_integral in H14.
destruct H14.
apply Rmult_integral in H14.
destruct H14.
assert (rm22 θ1 ξ θ2 = 1).
unfold rm22. rewrite H10.
unfold ry.
rewrite H14. lra.
apply Rltb_lt in eq1. lra.
assert (rm22 θ1 ξ θ2 = 1).
unfold rm22. rewrite H10.
unfold ry.
rewrite H14. lra.
apply Rltb_lt in eq1. lra.
apply Rmult_integral in H14.
destruct H14.
assert (ξ = 2 * (ξ / 2)) by lra.
assert (sin ξ = 0).
rewrite H15. rewrite sin_2a.
rewrite H14. lra.
assert (cos  ξ = 1).
specialize (sin2_cos2 (ξ / 2)) as H17.
rewrite H14 in H17.
unfold Rsqr in H17.
rewrite H15.
rewrite cos_2a. rewrite H14.
lra.
rewrite H16. rewrite H17.
lca.
assert (sin (θ1 / 2) * sin (θ2 / 2) = 0) by lra.
rewrite (Rmult_comm (sin (θ2 / 2))).
rewrite (Rmult_assoc (cos ξ )).
rewrite (Rmult_assoc (-sin ξ )).
rewrite H15. lca.
rewrite (Cmult_comm (cos ξ, sin ξ)).
rewrite (Cmult_assoc (cos (θ2 / 2))).
rewrite (Cmult_comm (cos (θ2 / 2))).
rewrite <- RtoC_mult.
rewrite <- RtoC_mult.
assert (cos (θ1 / 2) * cos (θ2 / 2) = sin (θ1 / 2) * sin (θ2 / 2)) by lra.
rewrite H10.
assert (rw θ1 ξ θ2 = 0).
unfold rw. rewrite H9. lra.
assert (ry θ1 ξ θ2 * rz θ1 ξ θ2 = 0) by lra.
unfold rm02 in H7.
assert (rx θ1 ξ θ2 * rz θ1 ξ θ2 = 0).
rewrite H11 in H7. lra.
apply Rmult_integral in H12.
apply Rmult_integral in H13.
destruct H12. destruct H13.
assert (rm22  θ1 ξ θ2 = 1).
unfold rm22. rewrite H12. rewrite H13.
lra. apply Rltb_lt in eq1. lra.
unfold ry in H12. unfold rz in H13.
apply Rmult_integral in H12.
apply Rmult_integral in H13.
destruct H12. destruct H13.
specialize (sin2_cos2 (ξ / 2)) as H14.
rewrite H12 in H14. rewrite H13 in H14.
unfold Rsqr in H14. lra.
assert (sin (θ1 / 2) * sin (θ2 / 2) = 0) by lra.
rewrite (Rmult_comm (sin (θ2 / 2))).
rewrite (Rmult_assoc (cos ξ )).
rewrite (Rmult_assoc (-sin ξ )).
rewrite H14. lca.
destruct H13.
assert (ξ = 2 * (ξ / 2)) by lra.
assert (sin ξ = 0).
rewrite H14. rewrite sin_2a.
rewrite H13. lra.
assert (cos  ξ = 1).
specialize (sin2_cos2 (ξ / 2)) as H17.
rewrite H13 in H17.
unfold Rsqr in H17.
rewrite H14.
rewrite cos_2a. rewrite H13.
lra.
rewrite H15. rewrite H16.
lca.
assert (sin (θ1 / 2) * sin (θ2 / 2) = 0) by lra.
rewrite (Rmult_comm (sin (θ2 / 2))).
rewrite (Rmult_assoc (cos ξ )).
rewrite (Rmult_assoc (-sin ξ )).
rewrite H14. lca.
destruct H13.
unfold rx in H13. unfold rz in H12.
apply Rmult_integral in H12.
apply Rmult_integral in H13.
destruct H12. destruct H13.
assert (ξ = 2 * (ξ / 2)) by lra.
assert (sin ξ = 0).
rewrite H14. rewrite sin_2a.
rewrite H13. lra.
assert (cos  ξ = 1).
specialize (sin2_cos2 (ξ / 2)) as H17.
rewrite H13 in H17.
unfold Rsqr in H17.
rewrite H14.
rewrite cos_2a. rewrite H13.
lra.
rewrite H15. rewrite H16.
lca.
assert (ξ = 2 * (ξ / 2)) by lra.
assert (sin ξ = 0).
rewrite H14. rewrite sin_2a.
rewrite H12. lra.
assert (cos  ξ = 1).
specialize (sin2_cos2 (ξ / 2)) as H17.
rewrite H12 in H17.
unfold Rsqr in H17.
rewrite H14.
rewrite cos_2a. rewrite H12.
lra.
rewrite H15. rewrite H16.
lca.
assert (sin (θ1 / 2) * sin (θ2 / 2) = 0) by lra.
rewrite (Rmult_comm (sin (θ2 / 2))).
rewrite (Rmult_assoc (cos ξ )).
rewrite (Rmult_assoc (-sin ξ )).
rewrite H14. lca.
unfold rz in H12.
apply Rmult_integral in H12.
destruct H12. 
assert (ξ = 2 * (ξ / 2)) by lra.
assert (sin ξ = 0).
rewrite H14. rewrite sin_2a.
rewrite H12. lra.
assert (cos  ξ = 1).
specialize (sin2_cos2 (ξ / 2)) as H17.
rewrite H12 in H17.
unfold Rsqr in H17.
rewrite H14.
rewrite cos_2a. rewrite H12.
lra.
rewrite H15. rewrite H16.
lca.
assert (sin (θ1 / 2) * sin (θ2 / 2) = 0) by lra.
rewrite (Rmult_comm (sin (θ2 / 2))).
rewrite (Rmult_assoc (cos ξ )).
rewrite (Rmult_assoc (-sin ξ )).
rewrite H14. lca.
}

Qed.


Lemma yzy_to_zyz_correct : forall {dim} θ1 ξ θ2 q,
  (q < dim)%nat ->
  @Ry dim θ1 q ; Rz ξ q ; Ry θ2 q ≅
          Rz (to_zyz_phi θ1 ξ θ2) q ; Ry (to_zyz_theta θ1 ξ θ2) q ; Rz (to_zyz_lambda θ1 ξ θ2) q.
Proof.
intros.
remember (cos (θ1 / 2) * cos (θ2 / 2) - (cos ξ * sin (θ1 / 2) * sin (θ2 / 2))) as s.
remember (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) as t.
remember (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) as p.
unfold to_zyz_theta, to_zyz_phi, to_zyz_lambda.
destruct (rm22 θ1 ξ θ2 <? 1) eqn:eq1.
destruct (-1 <? rm22 θ1 ξ θ2) eqn:eq2.
assert (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) <> 0).
assert (0 < √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
apply sqrt_lt_R0.
remember ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) as r.
remember ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) as g.
assert (r + g = 1).
specialize (sqr_angle_four_1 (ξ / 2) (θ1 / 2 - θ2 / 2) (θ1 / 2 + θ2 / 2)) as eqc.
rewrite Heqr. rewrite Heqg. lra.
assert (0 <= r).
rewrite Heqr.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²) by apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²) by apply Rle_0_sqr.
lra.
assert (0 <= g).
rewrite Heqg.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²) by apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²) by apply Rle_0_sqr.
lra.
apply Rltb_lt in eq1.
apply Rltb_lt in eq2.
assert (rm22 θ1 ξ θ2 = 1 - 2 * g).
unfold rm22,rx,ry.
rewrite <- sin_plus.
rewrite <- sin_minus.
rewrite Heqg. unfold Rsqr. lra.
rewrite H3 in eq1. rewrite H3 in eq2.
assert (0 < g) by lra.
lra. lra.
assert (cos ((acos (rm22 θ1 ξ θ2)) / 2) = p \/ cos ((acos (rm22 θ1 ξ θ2)) / 2) = - p).
unfold rm22, rx,ry.
rewrite <- sin_minus.
rewrite <- sin_plus.
assert (2 * (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2)) * (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))
      = 2 * ((Rsqr (sin (ξ / 2))) * Rsqr (sin (θ1 / 2 - θ2 / 2)))).
unfold Rsqr. lra.
rewrite H1. clear H1.
assert (2 * (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2)) * (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))
   = 2 * ((Rsqr (cos (ξ / 2))) * Rsqr (sin (θ1 / 2 + θ2 / 2)))).
unfold Rsqr. lra.
rewrite H1. clear H1.
specialize (cos_2a_cos_half
     (acos
     (1 - 2 * ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))²) -
      2 * ((cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) / 2)) as eq3.
assert ((2 *
             (acos
                (1 - 2 * ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))²) -
                 2 * ((cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) / 2))
    = (acos
                (1 - 2 * ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))²) -
                 2 * ((cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)))) by lra.
rewrite H1 in eq3. clear H1.
rewrite cos_acos in eq3.
assert (((1 - 2 * ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))²) -
          2 * ((cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) + 1) / 2)
    = 1 - ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))²) - ((cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H1 in eq3. clear H1.
specialize (sqr_angle_four_1 (ξ / 2) (θ1 / 2 - θ2 / 2) (θ1 / 2 + θ2 / 2)) as eq4.
assert ((1 - (sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² - (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
            = ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H1 in eq3.
destruct eq3.
left. rewrite Heqp. assumption.
right. rewrite Heqp. assumption.
apply Rltb_lt in eq1.
apply Rltb_lt in eq2.
unfold rm22,rx,ry in eq1.
unfold rm22,rx,ry in eq2.
rewrite <- sin_minus in eq1.
rewrite <- sin_plus in eq1. 
rewrite <- sin_minus in eq2.
rewrite <- sin_plus in eq2. 
rewrite <- 2 Rsqr_mult.
unfold Rsqr. lra.
assert (0 <= p). rewrite Heqp.
apply  sqrt_pos. rewrite Heqp in H1.
assert (sin (acos (s / p)) = (t / p) \/ sin (acos (s / p)) = ((-t) / p)).
rewrite sin_acos.
rewrite Heqs.
rewrite Heqp.
specialize (delta_cos_sin (θ1 / 2) (θ2 / 2) ξ H0) as H3.
assert ((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
      √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))²
   = 1 - ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
      √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))²) by lra.
rewrite <- H4.
rewrite Heqt.
destruct (0 <=? (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2))) eqn:eq3.
apply Rleb_le in eq3.
right.
rewrite sqrt_Rsqr.
lra. 
assert (0 < √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
assert (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
  = (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) * 
/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H6.
apply Rinv_0_lt_compat in H5.
apply Rmult_le_pos. lra. lra.
apply Rleb_lt_false in eq3.
assert (0 < sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) by lra.
assert (0 < √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
apply Rinv_0_lt_compat in H6.
left.
assert ((- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))²
  = (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))²).
unfold Rsqr. lra.
rewrite H7.
rewrite sqrt_Rsqr.
lra. 
assert (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
 = sin ξ * sin (θ1 / 2) * sin (θ2 / 2) * 
/ √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)) by lra.
rewrite H8.
apply Rmult_le_pos. lra. lra.
rewrite Heqs. rewrite Heqp.
apply delta_cos_bound. assumption.
assert (sin (acos (rm22 θ1 ξ θ2) / 2) = 
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
 \/ sin (acos (rm22 θ1 ξ θ2) / 2) = 
  - √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
assert (Rsqr (cos (acos (rm22 θ1 ξ θ2) / 2)) = Rsqr p).
destruct H1. rewrite H1. rewrite Heqp. reflexivity.
rewrite Heqp.
rewrite H1.  rewrite <- Rsqr_neg. 
reflexivity.
specialize (sin2_cos2 (acos (rm22 θ1 ξ θ2) / 2)) as H5.
assert ((sin (acos (rm22 θ1 ξ θ2) / 2))² = 1 - p²) by lra.
assert (p² = ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite Heqp. rewrite Rsqr_sqrt. reflexivity.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²) by apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²) by apply Rle_0_sqr.
lra.
rewrite H7 in H6.
specialize (sqr_angle_four_1 (ξ / 2) (θ1 / 2 - θ2 / 2) (θ1 / 2 + θ2 / 2)) as H8.
assert ((sin (acos (rm22 θ1 ξ θ2) / 2))² = (sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² 
            + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) by lra.
specialize (Rsqr_sqrt ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² 
          + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) as H10.
assert (0 <= (sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²).
rewrite <- 2 Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²) by apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²) by apply Rle_0_sqr.
lra.
apply H10 in H11.
rewrite <- H11 in H9.
apply Rsqr_eq in H9.
assumption.
remember (√ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² +
        (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)) as r.
assert ((cos (acos (rm22 θ1 ξ θ2) / 2) = p /\ sin (acos (rm22 θ1 ξ θ2) / 2) = r)
         \/ (cos (acos (rm22 θ1 ξ θ2) / 2) = - p /\ sin (acos (rm22 θ1 ξ θ2) / 2) = - r)).
destruct H1. destruct H4.
left. lra.
apply Rltb_lt in eq1. apply Rltb_lt in eq2.
assert (cos (acos (rm22 θ1 ξ θ2)) = rm22 θ1 ξ θ2).
apply cos_acos. lra.
assert ((sin (acos (rm22 θ1 ξ θ2))) = sqrt (1 - Rsqr (rm22 θ1 ξ θ2))).
apply sin_acos. lra.
assert (0 <= r).
rewrite Heqr. apply sqrt_pos.
assert (r <> 0).
assert (cos (acos (rm22 θ1 ξ θ2)) = 2 * cos (acos (rm22 θ1 ξ θ2) / 2)  * cos (acos (rm22 θ1 ξ θ2) / 2) - 1).
assert ((acos (rm22 θ1 ξ θ2)) = 2 * ((acos (rm22 θ1 ξ θ2)) /2)) by lra.
assert (cos (2 * (acos (rm22 θ1 ξ θ2) / 2)) = 2 * cos (acos (rm22 θ1 ξ θ2) / 2)  * cos (acos (rm22 θ1 ξ θ2) / 2) - 1).
apply cos_2a_cos. rewrite <- H9.
rewrite <- H8. reflexivity.
intros R.
assert (Rsqr p + Rsqr r = 1).
rewrite Heqp. rewrite Heqr.
rewrite Rsqr_sqrt. rewrite Rsqr_sqrt. 
specialize (sqr_angle_four_1 (ξ / 2) (θ1 / 2 - θ2 / 2) (θ1 / 2 + θ2 / 2)) as H9.
lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
assert (p = 1).
rewrite R in H9. 
assert (p² = Rsqr 1).
unfold Rsqr. unfold Rsqr in H9. lra.
apply Rsqr_eq in H10.
destruct H10. assumption.
rewrite Heqp in H10. lra.
rewrite Heqp in H10.
rewrite <- H1 in H10.
rewrite H10 in H8.
assert (cos (acos (rm22 θ1 ξ θ2)) = 1) by lra.
rewrite cos_acos in H11. lra. lra.
assert (sin (acos (rm22 θ1 ξ θ2)) = 2 * sin (acos (rm22 θ1 ξ θ2) / 2) * cos (acos (rm22 θ1 ξ θ2) / 2)).
rewrite <- sin_2a.
assert ((2 * (acos (rm22 θ1 ξ θ2) / 2)) = (acos (rm22 θ1 ξ θ2))) by lra.
rewrite H9. reflexivity.
assert (0 <= sin (acos (rm22 θ1 ξ θ2))).
rewrite H6. apply sqrt_pos.
assert (2 * sin (acos (rm22 θ1 ξ θ2) / 2) *
     cos (acos (rm22 θ1 ξ θ2) / 2) < 0).
rewrite H4.
rewrite H1.
assert (0 < p) by lra.
assert (0 < r) by lra.
assert (0 < 2) by lra.
assert (2 * - r * p = - (2 * r * p)) by lra.
rewrite Heqp in H14.
rewrite H14.
apply Ropp_lt_gt_0_contravar.
assert (0 < 2 * r * p).
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat. assumption. assumption. assumption.
rewrite Heqp in H15.
lra. lra.
destruct H4.
apply Rltb_lt in eq1. apply Rltb_lt in eq2.
assert (cos (acos (rm22 θ1 ξ θ2)) = rm22 θ1 ξ θ2).
apply cos_acos. lra.
assert ((sin (acos (rm22 θ1 ξ θ2))) = sqrt (1 - Rsqr (rm22 θ1 ξ θ2))).
apply sin_acos. lra.
assert (0 <= r).
rewrite Heqr. apply sqrt_pos.
assert (r <> 0).
assert (cos (acos (rm22 θ1 ξ θ2)) = 2 * cos (acos (rm22 θ1 ξ θ2) / 2)  * cos (acos (rm22 θ1 ξ θ2) / 2) - 1).
assert ((acos (rm22 θ1 ξ θ2)) = 2 * ((acos (rm22 θ1 ξ θ2)) /2)) by lra.
assert (cos (2 * (acos (rm22 θ1 ξ θ2) / 2)) = 2 * cos (acos (rm22 θ1 ξ θ2) / 2)  * cos (acos (rm22 θ1 ξ θ2) / 2) - 1).
apply cos_2a_cos. rewrite <- H9.
rewrite <- H8. reflexivity.
intros R.
assert (Rsqr p + Rsqr r = 1).
rewrite Heqp. rewrite Heqr.
rewrite Rsqr_sqrt. rewrite Rsqr_sqrt. 
specialize (sqr_angle_four_1 (ξ / 2) (θ1 / 2 - θ2 / 2) (θ1 / 2 + θ2 / 2)) as H9.
lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * sin (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * sin (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²).
apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²).
apply Rle_0_sqr. lra.
assert (p = 1).
rewrite R in H9. 
assert (p² = Rsqr 1).
unfold Rsqr. unfold Rsqr in H9. lra.
apply Rsqr_eq in H10.
destruct H10. assumption.
rewrite Heqp in H10. lra.
rewrite Heqp in H10.
rewrite H10 in H1.
rewrite H1 in H8.
assert (cos (acos (rm22 θ1 ξ θ2)) = 1) by lra.
rewrite cos_acos in H11. lra. lra.
assert (sin (acos (rm22 θ1 ξ θ2)) = 2 * sin (acos (rm22 θ1 ξ θ2) / 2) * cos (acos (rm22 θ1 ξ θ2) / 2)).
rewrite <- sin_2a.
assert ((2 * (acos (rm22 θ1 ξ θ2) / 2)) = (acos (rm22 θ1 ξ θ2))) by lra.
rewrite H9. reflexivity.
assert (0 <= sin (acos (rm22 θ1 ξ θ2))).
rewrite H6. apply sqrt_pos.
assert (2 * sin (acos (rm22 θ1 ξ θ2) / 2) *
     cos (acos (rm22 θ1 ξ θ2) / 2) < 0).
rewrite H4.
rewrite H1.
assert (0 < p) by lra.
assert (0 < r) by lra.
assert (0 < 2) by lra.
assert (2 * r * - p = - (2 * r * p)) by lra.
rewrite Heqp in H14.
rewrite H14.
apply Ropp_lt_gt_0_contravar.
assert (0 < 2 * r * p).
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat. assumption. assumption. assumption.
rewrite Heqp in H15.
lra. lra.
right. lra.
clear H1. clear H4.
destruct H5. destruct H1. destruct H3.
(* first case: all angles are greater than zero. *)
unfold uc_cong; simpl. 
exists (- acos (s/p)).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
- (* first-sub-case: cos acos rm22 * Cexp = ... *)
unfold Cexp.
rewrite cos_neg.
rewrite sin_neg.
rewrite cos_acos.
rewrite H3. rewrite H1.
assert (((((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%R,
 (-
  (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R) *
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%C
  = (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) 
       * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R,
   (- (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
    * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R)%C) by lca.
rewrite H.
rewrite Rinv_r. lca. assumption.
apply delta_cos_bound. assumption.
- (* second-sub-case: Cexp atan (rm12/rm02) sin acos rm22 * Cexp = ... *)
rewrite (Cmult_comm (sin (acos (rm22 θ1 ξ θ2) / 2))).
rewrite (Cmult_assoc (Cexp (-
     acos
       ((cos (θ1 / 2) * cos (θ2 / 2) -
         cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
        √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
           (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
rewrite <- Cexp_add.
unfold Cexp.
rewrite C_smult_r.
rewrite C_smult_r.
rewrite sin_plus.
rewrite cos_plus.
rewrite cos_neg.
rewrite sin_neg.
rewrite H3. rewrite H4.
(*apply rm22_rewrite_case_1.
assumption.
- (* third-sub-case: Cexp atan (rm21/rm20) * sin acos rm22 = ... *)
rewrite (Cmult_assoc (Cexp
   (-
    acos
      ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
rewrite <- Cexp_add.
unfold Cexp.
rewrite C_smult_r.
rewrite C_smult_r.
rewrite sin_plus.
rewrite cos_plus.
rewrite cos_neg.
rewrite sin_neg.
rewrite H3. rewrite H4.
apply rm22_rewrite_case_2.
assumption.
- (* fourth-sub-case: Cexp (cos acos) * Cexp atan2 rm21 * cos (acos rm22) * Cexp atant2 rm12 *)
rewrite (Cmult_assoc (Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)))).
rewrite (Cmult_comm (Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)))).
rewrite <- Cmult_assoc. 
rewrite (Cmult_assoc (Cexp (- acos
      ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
assert ((Cexp
   (-
    acos
      ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
 cos (acos (rm22 θ1 ξ θ2) / 2))%C
  = ((cos (θ1 / 2) *  cos (θ2 / 2) - cos  ξ * sin (θ1 / 2) * sin (θ2 / 2))%R,
             (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2))%R)%C).
unfold Cexp.
rewrite cos_neg.
rewrite sin_neg.
rewrite cos_acos.
rewrite H3. rewrite H1.
assert (((((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%R,
 (-
  (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R) *
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%C
  = (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) 
       * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R,
   (- (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
    * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²
          + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R)%C) by lca.
rewrite H. clear H.
rewrite Rinv_r. lca. assumption.
apply delta_cos_bound. assumption.
rewrite H. clear H.
apply rm22_rewrite_case_3.
assumption. assumption.
- (* second case: sin (acos (s / p)) = - t / p *)
unfold uc_cong; simpl. 
exists (acos (s/p)).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
{
(* first-sub-case: cos acos rm22 * Cexp = ... *)
unfold Cexp.
rewrite cos_acos.
rewrite H3. rewrite H1.
assert (((((cos (θ1 / 2) * cos (θ2 / 2) -
    cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
      (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%R,
 (- (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%R) *
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%C
  = (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) 
       * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R,
   (- (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
    * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R)%C) by lca.
rewrite H.
rewrite Rinv_r. lca. assumption.
apply delta_cos_bound. assumption.
}

{ (* second-sub-case: Cexp atan (rm12/rm02) sin acos rm22 * Cexp = ... *)
rewrite (Cmult_comm (sin (acos (rm22 θ1 ξ θ2) / 2))).
rewrite (Cmult_assoc (Cexp
    (acos
       ((cos (θ1 / 2) * cos (θ2 / 2) -
         cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
        √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
           (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) )).
rewrite <- Cexp_add.
unfold Cexp.
rewrite C_smult_r.
rewrite C_smult_r.
rewrite sin_plus.
rewrite cos_plus.
rewrite H3. rewrite H4.
rewrite rm22_rewrite_case_1.
lca.
assumption.
}

{ (* third-sub-case: Cexp atan (rm21/rm20) * sin acos rm22 = ... *)
rewrite (Cmult_assoc (Cexp
   (acos
      ((cos (θ1 / 2) * cos (θ2 / 2) -
        cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
rewrite <- Cexp_add.
unfold Cexp.
rewrite C_smult_r.
rewrite C_smult_r.
rewrite sin_plus.
rewrite cos_plus.
rewrite H3. rewrite H4.
rewrite rm22_rewrite_case_2.
lca.
assumption.
}

{ (* fourth-sub-case: Cexp (cos acos) * Cexp atan2 rm21 * cos (acos rm22) * Cexp atant2 rm12 *)
rewrite (Cmult_assoc (Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)))).
rewrite (Cmult_comm (Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)))).
rewrite <- Cmult_assoc. 
rewrite (Cmult_assoc (Cexp
   (acos
      ((cos (θ1 / 2) * cos (θ2 / 2) -
        cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
assert ((Cexp
   (acos
      ((cos (θ1 / 2) * cos (θ2 / 2) -
        cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
 cos (acos (rm22 θ1 ξ θ2) / 2))%C
  = ((cos (θ1 / 2) *  cos (θ2 / 2) - cos  ξ * sin (θ1 / 2) * sin (θ2 / 2))%R,
             (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2))%R)%C).
unfold Cexp.
rewrite cos_acos.
rewrite H3. rewrite H1.
assert (((((cos (θ1 / 2) * cos (θ2 / 2) -
    cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
      (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%R,
 (- (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%R) *
 √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
    (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%C
  = (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) 
       * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R,
   (- (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
    * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R)%C) by lca.
rewrite H.
rewrite Rinv_r. lca. assumption.
apply delta_cos_bound. assumption.
rewrite H. clear H.
rewrite rm22_rewrite_case_3. lca.
assumption. assumption.
}
- (* third case: when cos/sin rm22 = -p and -r*)
destruct H1.
destruct H3.
unfold uc_cong; simpl. 
exists (PI - acos (s/p)).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
{(* first-sub-case: cos acos rm22 * Cexp = ... *)
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite cos_acos.
rewrite H3. rewrite H1.
assert ((((-
   ((cos (θ1 / 2) * cos (θ2 / 2) -
     cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
       (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R,
 (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%R) *
 (-
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%R)%C
  = (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) 
       * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R,
   (- (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
    * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R)%C) by lca.
rewrite H.
rewrite Rinv_r. lca. assumption.
apply delta_cos_bound. assumption.
}

{ (* second-sub-case: Cexp atan (rm12/rm02) sin acos rm22 * Cexp = ... *)
rewrite (Cmult_comm (sin (acos (rm22 θ1 ξ θ2) / 2))).
rewrite (Cmult_assoc (Cexp
    (PI -
     acos
       ((cos (θ1 / 2) * cos (θ2 / 2) -
         cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
        √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
           (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) )).
rewrite <- Cexp_add.
unfold Cexp.
rewrite C_smult_r.
rewrite C_smult_r.
rewrite sin_plus.
rewrite cos_plus.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite H3. rewrite H4.
rewrite rm22_rewrite_case_1.
lca.
assumption.
}

{ (* third-sub-case: Cexp atan (rm21/rm20) * sin acos rm22 = ... *)
rewrite (Cmult_assoc (Cexp
   (PI -
    acos
      ((cos (θ1 / 2) * cos (θ2 / 2) -
        cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
rewrite <- Cexp_add.
unfold Cexp.
rewrite C_smult_r.
rewrite C_smult_r.
rewrite sin_plus.
rewrite cos_plus.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite H3. rewrite H4.
rewrite rm22_rewrite_case_2.
lca.
assumption.
}

{ (* fourth-sub-case: Cexp (cos acos) * Cexp atan2 rm21 * cos (acos rm22) * Cexp atant2 rm12 *)
rewrite (Cmult_assoc (Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)))).
rewrite (Cmult_comm (Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)))).
rewrite <- Cmult_assoc. 
rewrite (Cmult_assoc (Cexp
   (PI -
    acos
      ((cos (θ1 / 2) * cos (θ2 / 2) -
        cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
assert ((Cexp
   (PI -
    acos
      ((cos (θ1 / 2) * cos (θ2 / 2) -
        cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
 cos (acos (rm22 θ1 ξ θ2) / 2))%C
  = ((cos (θ1 / 2) *  cos (θ2 / 2) - cos  ξ * sin (θ1 / 2) * sin (θ2 / 2))%R,
             (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2))%R)%C).
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite cos_acos.
rewrite H3. rewrite H1.
assert ((((-
   ((cos (θ1 / 2) * cos (θ2 / 2) -
     cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
       (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R,
 (sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%R) *
 (-
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%R)%C
  = (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) 
       * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R,
   (- (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
    * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R)%C) by lca.
rewrite H.
rewrite Rinv_r. lca. assumption.
apply delta_cos_bound. assumption.
rewrite H. clear H.
rewrite rm22_rewrite_case_3. lca.
assumption. assumption.
}

(* fourth case: when cos/sin rm22 = -p and -r and sin (acos (s / p)) = - t / p *)
unfold uc_cong; simpl. 
exists (PI + acos (s/p)).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
{(* first-sub-case: cos acos rm22 * Cexp = ... *)
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_acos.
rewrite H3. rewrite H1.
assert ((((-
   ((cos (θ1 / 2) * cos (θ2 / 2) -
     cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
       (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R,
 (-
  (- (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
      (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R) *
 (-
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%R)%C
  = (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) 
       * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R,
   (- (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
    * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R)%C) by lca.
rewrite H.
rewrite Rinv_r. lca. assumption.
apply delta_cos_bound. assumption.
}

{ (* second-sub-case: Cexp atan (rm12/rm02) sin acos rm22 * Cexp = ... *)
rewrite (Cmult_comm (sin (acos (rm22 θ1 ξ θ2) / 2))).
rewrite (Cmult_assoc (Cexp
    (PI +
     acos
       ((cos (θ1 / 2) * cos (θ2 / 2) -
         cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
        √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
           (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) )).
rewrite <- Cexp_add.
unfold Cexp.
rewrite C_smult_r.
rewrite C_smult_r.
rewrite sin_plus.
rewrite cos_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite H3. rewrite H4.
rewrite rm22_rewrite_case_1.
lca.
assumption.
}

{ (* third-sub-case: Cexp atan (rm21/rm20) * sin acos rm22 = ... *)
rewrite (Cmult_assoc (Cexp
   (PI +
    acos
      ((cos (θ1 / 2) * cos (θ2 / 2) -
        cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
rewrite <- Cexp_add.
unfold Cexp.
rewrite C_smult_r.
rewrite C_smult_r.
rewrite sin_plus.
rewrite cos_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite H3. rewrite H4.
rewrite rm22_rewrite_case_2.
lca.
assumption.
}

{ (* fourth-sub-case: Cexp (cos acos) * Cexp atan2 rm21 * cos (acos rm22) * Cexp atant2 rm12 *)
rewrite (Cmult_assoc (Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)))).
rewrite (Cmult_comm (Cexp (atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)))).
rewrite <- Cmult_assoc. 
rewrite (Cmult_assoc (Cexp
   (PI +
    acos
      ((cos (θ1 / 2) * cos (θ2 / 2) -
        cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))))).
assert ((Cexp
   (PI +
    acos
      ((cos (θ1 / 2) * cos (θ2 / 2) -
        cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
       √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
          (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
 cos (acos (rm22 θ1 ξ θ2) / 2))%C
  = ((cos (θ1 / 2) *  cos (θ2 / 2) - cos  ξ * sin (θ1 / 2) * sin (θ2 / 2))%R,
             (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2))%R)%C).
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_acos.
rewrite H3. rewrite H1.
assert ((((-
   ((cos (θ1 / 2) * cos (θ2 / 2) -
     cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
    √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
       (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R,
 (-
  (- (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
   √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
      (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R) *
 (-
  √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² +
     (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))%R)%C
  = (((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) 
       * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R,
   (- (sin ξ * sin (θ1 / 2) * sin (θ2 / 2)) *
   (√ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)
    * / √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)))%R)%C) by lca.
rewrite H.
rewrite Rinv_r. lca. assumption.
apply delta_cos_bound. assumption.
rewrite H. clear H.
rewrite rm22_rewrite_case_3. lca.
assumption. assumption.
}
- (* fifth case: when rm22 <= - 1, which is essentially rm22 = -1*)
assert (θ1 = θ1) by lra.
apply Rltb_le_false in eq2.
assert (rm22 θ1 ξ θ2 = 1 - 2 * (((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
unfold rm22,rx,ry,Rsqr.
rewrite <- sin_plus.
rewrite <- sin_minus.
lra.
assert (rm22 θ1 ξ θ2 = -1).
remember ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) as r.
remember ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) as g.
assert (r + g = 1).
specialize (sqr_angle_four_1 (ξ / 2) (θ1 / 2 - θ2 / 2) (θ1 / 2 + θ2 / 2)) as H2.
lra.
assert (0 <= r).
rewrite Heqr.
assert (0 <= (sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
lra.
assert (0 <= g).
assert (0 <= (sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
lra.
assert (r <= 1) by lra.
rewrite H1 in eq2.
assert (1 <= r) by lra.
lra.
assert ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))² = 1) by lra.
assert ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))² = 0).
remember ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) as r.
remember ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) as g.
assert (r + g = 1).
specialize (sqr_angle_four_1 (ξ / 2) (θ1 / 2 - θ2 / 2) (θ1 / 2 + θ2 / 2)) as H4.
lra. lra.
assert ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² = 0).
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult in H4. rewrite <- Rsqr_mult in H4.
apply Rplus_eq_0_l in H4. assumption.
apply Rle_0_sqr. apply Rle_0_sqr.
assert ((cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))² = 0).
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult in H4. rewrite <- Rsqr_mult in H4.
apply Rplus_eq_R0 in H4. destruct H4. assumption.
apply Rle_0_sqr. apply Rle_0_sqr.
apply Rmult_integral in H5.
apply Rmult_integral in H6.
destruct H5. destruct H6.
specialize (sin2_cos2 (ξ / 2)) as eq3.
rewrite H5 in eq3. rewrite H6 in eq3. lra.
assert ((cos (ξ / 2))² = 1).
specialize (sin2_cos2 (ξ / 2)) as eq3.
rewrite H5 in eq3. lra.
assert ((sin (θ1 / 2 + θ2 / 2))² = 1).
specialize (sin2_cos2 (θ1 / 2 + θ2 / 2)) as eq3.
rewrite H6 in eq3. lra.
assert ((sin (ξ / 2)) = 0).
apply Rsqr_eq_0 in H5.
assumption.
assert (sin ξ = 0).
assert (ξ  = 2 * (ξ / 2)) by lra. rewrite H10.
rewrite sin_2a. rewrite H9. lra.
assert (cos ξ = 1).
assert (ξ  = 2 * (ξ / 2)) by lra. rewrite H11.
rewrite cos_2a_sin. rewrite H9. lra.
apply Rsqr_eq_0 in H6. 
assert ((sin (θ1 / 2 + θ2 / 2))² = Rsqr 1).
unfold Rsqr. unfold Rsqr in H8. lra.
apply Rsqr_eq in H12.
destruct H12.
(* first-sub: when sin ξ = 0, cos ξ = 1, and (sin (θ1 / 2 + θ2 / 2)) = 1 *)
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite Cexp_0.
unfold Cexp.
rewrite H10. rewrite H11.
assert ((cos (θ2 / 2) * cos (θ1 / 2) +
 - (sin (θ2 / 2) * ((1, 0) * sin (θ1 / 2))))%C = ((cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H. 
rewrite cos_plus in H6. rewrite H6.
rewrite cos_PI2. lca.
rewrite Cexp_0. rewrite sin_PI2.
unfold atan2.
destruct (0 <? rm11 θ1 ξ θ2) eqn:eq3.
rewrite rm10_eq. rewrite rm11_eq.
rewrite H10.
rewrite Rmult_0_l.
assert (0 / cos ξ = 0) by lra.
rewrite H.
rewrite atan_0.
rewrite Cexp_neg. rewrite Cexp_0.
unfold Cexp.
rewrite H10. rewrite H11.
rewrite sin_plus in H12.
assert ((cos (θ2 / 2) * sin (θ1 / 2) +
  sin (θ2 / 2) * ((1, 0) * cos (θ1 / 2)))%C
  = ((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H14. rewrite H12. lca.
apply Rltb_le_false in eq3.
rewrite rm11_eq in eq3. rewrite H11 in eq3. lra.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp. rewrite H10. rewrite H11.
rewrite sin_plus in H12.
assert ((sin (θ2 / 2) * cos (θ1 / 2) +
 cos (θ2 / 2) * ((1, 0) * sin (θ1 / 2)))%C 
 = ((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2) )%R)%C) by lca.
rewrite H. rewrite H12. lca.
rewrite Cexp_0. rewrite cos_PI2.
unfold Cexp. rewrite H10. rewrite H11.
rewrite cos_plus in H6.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) +
 cos (θ2 / 2) * ((1, 0) * cos (θ1 / 2)))%C
  = ((cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H. rewrite H6. lca.
(* second-sub: when sin ξ = 0, cos ξ = 1, and (sin (θ1 / 2 + θ2 / 2)) = -1 *)
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite Cexp_PI.
unfold Cexp.
rewrite H10. rewrite H11.
assert ((cos (θ2 / 2) * cos (θ1 / 2) +
 - (sin (θ2 / 2) * ((1, 0) * sin (θ1 / 2))))%C = ((cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H. 
rewrite cos_plus in H6. rewrite H6.
rewrite cos_PI2. lca.
rewrite Cexp_PI. rewrite sin_PI2.
unfold atan2.
destruct (0 <? rm11 θ1 ξ θ2) eqn:eq3.
rewrite rm10_eq. rewrite rm11_eq.
rewrite H10.
rewrite Rmult_0_l.
assert (0 / cos ξ = 0) by lra.
rewrite H.
rewrite atan_0.
rewrite Cexp_neg. rewrite Cexp_0.
unfold Cexp.
rewrite H10. rewrite H11.
rewrite sin_plus in H12.
assert ((cos (θ2 / 2) * sin (θ1 / 2) +
  sin (θ2 / 2) * ((1, 0) * cos (θ1 / 2)))%C
  = ((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H14. rewrite H12. lca.
apply Rltb_le_false in eq3.
rewrite rm11_eq in eq3. rewrite H11 in eq3. lra.
rewrite Cexp_PI. rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp. rewrite H10. rewrite H11.
rewrite sin_plus in H12.
assert ((sin (θ2 / 2) * cos (θ1 / 2) +
 cos (θ2 / 2) * ((1, 0) * sin (θ1 / 2)))%C 
 = ((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2) )%R)%C) by lca.
rewrite H. rewrite H12. lca.
rewrite Cexp_0. rewrite cos_PI2.
unfold Cexp. rewrite H10. rewrite H11.
rewrite cos_plus in H6.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) +
 cos (θ2 / 2) * ((1, 0) * cos (θ1 / 2)))%C
  = ((cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H. rewrite H6. lca.
(* third-sub: when sin ξ = 0, cos ξ = -1, and (sin (θ1 / 2 - θ2 / 2)) = 1 *)
destruct H6.
specialize (sin2_cos2 (ξ / 2)) as eq3.
rewrite H6 in eq3.
assert ((sin (ξ / 2))² = 1) by lra.
assert ((sin (θ1 / 2 - θ2 / 2))² = 1).
specialize (sin2_cos2 (θ1 / 2 - θ2 / 2)) as eq4.
rewrite H5 in eq4. lra.
apply Rsqr_eq_0 in H6.
assert (sin ξ = 0).
assert (ξ  = 2 * (ξ / 2)) by lra. rewrite H9.
rewrite sin_2a. rewrite H6. lra.
assert (cos ξ = -1).
assert (ξ  = 2 * (ξ / 2)) by lra. rewrite H10.
rewrite cos_2a_cos. rewrite H6. lra.
apply Rsqr_eq_0 in H5. 
assert ((sin (θ1 / 2 - θ2 / 2))² = Rsqr 1).
unfold Rsqr. unfold Rsqr in H8. lra.
apply Rsqr_eq in H11.
destruct H11.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite Cexp_PI.
unfold Cexp.
rewrite H9. rewrite H10.
assert ((cos (θ2 / 2) * cos (θ1 / 2) +
 - (sin (θ2 / 2) * ((-1, 0) * sin (θ1 / 2))))%C = ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H. 
rewrite cos_minus in H5. rewrite H5.
rewrite cos_PI2. lca.
rewrite Cexp_PI. rewrite sin_PI2.
unfold atan2.
destruct (0 <? rm11 θ1 ξ θ2) eqn:eq5.
apply Rltb_lt in eq5.
rewrite rm11_eq in eq5.
rewrite H10 in eq5. lra.
destruct (rm11 θ1 ξ θ2 <? 0) eqn:eq6.
destruct (0 <=? rm10 θ1 ξ θ2) eqn:eq7.
rewrite rm10_eq. rewrite rm11_eq.
rewrite H10. rewrite H9.
rewrite Rmult_0_l.
assert (0 / -1 = 0) by lra.
rewrite H.
rewrite atan_0.
rewrite Cexp_neg. rewrite Rplus_0_l. rewrite Cexp_PI.
unfold Cexp.
rewrite H10. rewrite H9.
rewrite sin_minus in H11.
assert ((cos (θ2 / 2) * sin (θ1 / 2) +
  sin (θ2 / 2) * ((-1, 0) * cos (θ1 / 2)))%C
  = ((sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H13. rewrite H11. lca.
apply Rleb_lt_false in eq7.
rewrite rm10_eq in eq7. rewrite H9 in eq7. lra.
apply Rltb_le_false in eq6.
rewrite rm11_eq in eq6.
rewrite H10 in eq6. lra.
rewrite Cexp_PI. rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp. rewrite H10. rewrite H9.
rewrite sin_minus in H11.
assert ((sin (θ2 / 2) * cos (θ1 / 2) +
 cos (θ2 / 2) * ((-1, 0) * sin (θ1 / 2)))%C 
 = ((-(sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. rewrite H11. lca.
rewrite cos_PI2.
unfold Cexp. rewrite H10. rewrite H9.
rewrite cos_minus in H5.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) +
 cos (θ2 / 2) * ((-1, 0) * cos (θ1 / 2)))%C
  = ((-(cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. rewrite H5. lca.
(* fourth-sub: when sin ξ = 0, cos ξ = -1, and (sin (θ1 / 2 - θ2 / 2)) = -1 *)
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite Cexp_0.
unfold Cexp.
rewrite H9. rewrite H10.
assert ((cos (θ2 / 2) * cos (θ1 / 2) +
 - (sin (θ2 / 2) * ((-1, 0) * sin (θ1 / 2))))%C = ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H. 
rewrite cos_minus in H5. rewrite H5.
rewrite cos_PI2. lca.
rewrite Cexp_0. rewrite sin_PI2.
unfold atan2.
destruct (0 <? rm11 θ1 ξ θ2) eqn:eq5.
apply Rltb_lt in eq5.
rewrite rm11_eq in eq5.
rewrite H10 in eq5. lra.
destruct (rm11 θ1 ξ θ2 <? 0) eqn:eq6.
destruct (0 <=? rm10 θ1 ξ θ2) eqn:eq7.
rewrite rm10_eq. rewrite rm11_eq.
rewrite H10. rewrite H9.
rewrite Rmult_0_l.
assert (0 / -1 = 0) by lra.
rewrite H.
rewrite atan_0.
rewrite Cexp_neg. rewrite Rplus_0_l. rewrite Cexp_PI.
unfold Cexp.
rewrite H10. rewrite H9.
rewrite sin_minus in H11.
assert ((cos (θ2 / 2) * sin (θ1 / 2) +
  sin (θ2 / 2) * ((-1, 0) * cos (θ1 / 2)))%C
  = ((sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H13. rewrite H11. lca.
apply Rleb_lt_false in eq7.
rewrite rm10_eq in eq7. rewrite H9 in eq7. lra.
apply Rltb_le_false in eq6.
rewrite rm11_eq in eq6.
rewrite H10 in eq6. lra.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp. rewrite H10. rewrite H9.
rewrite sin_minus in H11.
assert ((sin (θ2 / 2) * cos (θ1 / 2) +
 cos (θ2 / 2) * ((-1, 0) * sin (θ1 / 2)))%C 
 = ((-(sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. rewrite H11. lca.
rewrite cos_PI2.
unfold Cexp. rewrite H10. rewrite H9.
rewrite cos_minus in H5.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) +
 cos (θ2 / 2) * ((-1, 0) * cos (θ1 / 2)))%C
  = ((-(cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. rewrite H5. lca.
(* fifth-sub: when cos (θ1 / 2) * cos (θ1 / 2) = 0, sin (θ1 / 2) * sin (θ1 / 2) = 0 and 0 < cos ξ *)
apply Rsqr_eq_0 in H5.
apply Rsqr_eq_0 in H6.
rewrite cos_minus in H5.
rewrite cos_plus in H6.
assert (cos (θ1 / 2) * cos (θ2 / 2) = 0) by lra.
assert (sin (θ1 / 2) * sin (θ2 / 2) = 0) by lra.
apply Rmult_integral in H7.
apply Rmult_integral in H8.
destruct H7. destruct H8.
specialize (sin2_cos2 (θ1 / 2)) as eq3.
rewrite H7 in eq3. rewrite H8 in eq3. unfold Rsqr in eq3. lra.
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite H7 in eqa.
assert ((sin (θ1 / 2))² = Rsqr 1).
unfold Rsqr in eqa. unfold Rsqr. lra.
apply Rsqr_eq in H9.
specialize (sin2_cos2 (θ2 / 2)) as eqb.
rewrite H8 in eqb.
assert ((cos (θ2 / 2))² = Rsqr 1).
unfold Rsqr in eqb. unfold Rsqr. lra.
apply Rsqr_eq in H10.
rewrite rm10_eq. rewrite rm11_eq.
unfold atan2.
assert (cos θ2 = 1).
assert (θ2 = 2 * (θ2/2)) by lra.
rewrite H11. rewrite cos_2a_sin.
rewrite H8. lra. rewrite H11.
rewrite Rmult_1_r.
destruct (0 <? cos ξ) eqn:eq3.
apply Rltb_lt in eq3.
assert (cos (atan (sin ξ / cos ξ)) = cos ξ).
rewrite cos_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H12. rewrite sin2_cos2. 
rewrite Rmult_1_l. rewrite Rmult_1_l.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rinv_involutive.
apply sqrt_Rsqr. lra.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
assert (sin (atan (sin ξ / cos ξ)) = sin ξ).
rewrite sin_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H13. rewrite sin2_cos2. 
rewrite Rmult_1_l.
rewrite Rmult_assoc.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rinv_involutive.
rewrite sqrt_Rsqr. 
rewrite <- Rinv_l_sym.
lra. lra. lra.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists ξ.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cmult_1_l. rewrite Cmult_1_l.
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
assert (cos ξ * cos ξ - sin ξ * - sin ξ = Rsqr (sin ξ) + Rsqr (cos ξ)).
unfold Rsqr. lra.
rewrite H.  rewrite sin2_cos2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2. lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cmult_1_l.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
assert (- cos ξ * cos ξ - - sin ξ * - sin ξ = - (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H.  rewrite sin2_cos2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
destruct H10.
unfold uc_cong; simpl. 
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cmult_1_l. rewrite Cmult_1_l.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
assert (- cos ξ * cos ξ - - sin ξ * - sin ξ = - (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H.  rewrite sin2_cos2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists (ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cmult_1_l.
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
assert (cos ξ * cos ξ - sin ξ * - sin ξ = (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H.  rewrite sin2_cos2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
(* sixth-sub: when cos (θ1 / 2) * cos (θ1 / 2) = 0, sin (θ1 / 2) * sin (θ1 / 2) = 0 and cos ξ <? 0 *)
destruct (cos ξ <? 0) eqn:eq4.
apply Rltb_lt in eq4.
assert (cos (atan (sin ξ / cos ξ)) = -cos ξ).
rewrite cos_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H12. rewrite sin2_cos2. 
rewrite Rmult_1_l. rewrite Rmult_1_l.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rinv_involutive.
rewrite Rsqr_neg.
apply sqrt_Rsqr. lra.
rewrite Rsqr_neg.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
assert (sin (atan (sin ξ / cos ξ)) = -sin ξ).
rewrite sin_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H13. rewrite sin2_cos2. 
rewrite Rmult_1_l.
rewrite Rmult_assoc.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rsqr_neg.
rewrite Rinv_involutive.
rewrite sqrt_Rsqr.
rewrite <- Ropp_mult_distr_r. 
rewrite <- Rinv_l_sym.
lra. lra. lra.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
destruct (0 <=? sin ξ) eqn:eq5.
apply Rleb_le in eq5.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists ξ.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cmult_1_l. rewrite Cmult_1_l.
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite (Rplus_comm (atan (sin ξ / cos ξ))).
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive.
rewrite Ropp_involutive.
assert (cos ξ * cos ξ - sin ξ * - sin ξ = (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H.  rewrite sin2_cos2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2. lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cmult_1_l.
unfold Cexp.
rewrite (Rplus_comm (atan (sin ξ / cos ξ))).
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive. rewrite Ropp_involutive.
assert (- cos ξ * cos ξ - - sin ξ * - sin ξ = - (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H.  rewrite sin2_cos2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
destruct H10.
unfold uc_cong; simpl. 
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cmult_1_l. rewrite Cmult_1_l.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite cos_neg. rewrite sin_neg.
rewrite (Rplus_comm (atan (sin ξ / cos ξ))).
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive.
rewrite Ropp_involutive.
assert (- cos ξ * cos ξ - - sin ξ * - sin ξ = - (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H.  rewrite sin2_cos2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists (ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cmult_1_l.
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite (Rplus_comm (atan (sin ξ / cos ξ))).
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive.
rewrite Ropp_involutive.
assert (cos ξ * cos ξ - sin ξ * - sin ξ = (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H.  rewrite sin2_cos2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
rewrite Ropp_minus_distr.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists ξ.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cmult_1_l. rewrite Cmult_1_l.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive.
assert (cos ξ * cos ξ - sin ξ * - sin ξ = (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H.  rewrite sin2_cos2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2. lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cmult_1_l.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive.
assert (- cos ξ * cos ξ - - sin ξ * - sin ξ = - (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H.  rewrite sin2_cos2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
destruct H10.
unfold uc_cong; simpl. 
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cmult_1_l. rewrite Cmult_1_l.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive.
assert (- cos ξ * cos ξ - - sin ξ * - sin ξ = - (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H.  rewrite sin2_cos2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists (ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cmult_1_l.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive.
assert (cos ξ * cos ξ - sin ξ * - sin ξ = (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H.  rewrite sin2_cos2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
apply Rltb_le_false in eq3.
apply Rltb_le_false in eq4.
assert (cos ξ = 0) by lra.
destruct (0 <? sin ξ) eqn:eq5.
apply Rltb_lt in eq5.
specialize (sin2_cos2 ξ) as eqc.
rewrite H12 in eqc.
assert (1 = Rsqr 1). unfold Rsqr. lra.
rewrite H13 in eqc.
assert (0 = Rsqr 0). unfold Rsqr. lra.
rewrite <- H14 in eqc.
rewrite Rplus_0_r in eqc.
apply Rsqr_eq in eqc.
destruct eqc.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists (PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite sin_PI2. unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite sin_PI2. rewrite cos_PI2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H15. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
unfold uc_cong; simpl. 
exists (PI + PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite sin_PI2. unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite cos_neg. rewrite sin_neg.
rewrite sin_PI2. rewrite cos_PI2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H15. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
destruct H10.
unfold uc_cong; simpl. 
exists (PI + PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite sin_PI2. unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite cos_neg. rewrite sin_neg.
rewrite sin_PI2. rewrite cos_PI2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H15. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
unfold uc_cong; simpl. 
exists (PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite sin_PI2. unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite sin_PI2. rewrite cos_PI2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H15. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca. lra.
destruct (sin ξ <? 0) eqn:eq6.
apply Rltb_lt in eq6.
specialize (sin2_cos2 ξ) as eqc.
rewrite H12 in eqc.
assert (1 = Rsqr 1). unfold Rsqr. lra.
rewrite H13 in eqc.
assert (0 = Rsqr 0). unfold Rsqr. lra.
rewrite <- H14 in eqc.
rewrite Rplus_0_r in eqc.
apply Rsqr_eq in eqc.
destruct eqc. lra.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists (PI + PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite sin_PI2. unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
assert ((- PI / 2) = - (PI / 2)) by lra.
rewrite H.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite sin_PI2. rewrite cos_PI2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H15. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
unfold uc_cong; simpl. 
exists (PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite sin_PI2. unfold Cexp.
assert ((- PI / 2) = - (PI / 2)) by lra.
rewrite H.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_neg. rewrite sin_neg.
rewrite sin_PI2. rewrite cos_PI2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H15. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
destruct H10.
unfold uc_cong; simpl. 
exists (PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite sin_PI2. unfold Cexp.
assert ((- PI / 2) = - (PI / 2)) by lra.
rewrite H.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_neg. rewrite sin_neg.
rewrite sin_PI2. rewrite cos_PI2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H15. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
unfold uc_cong; simpl. 
exists (PI + PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite sin_PI2. unfold Cexp.
assert ((- PI / 2) = - (PI / 2)) by lra.
rewrite H.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite cos_neg. rewrite sin_neg.
rewrite sin_PI2. rewrite cos_PI2.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H15. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
apply Rltb_le_false in eq5.
apply Rltb_le_false in eq6.
assert (sin ξ = 0) by lra.
specialize (sin2_cos2 ξ) as R.
rewrite H12 in R. rewrite H13 in R.
unfold Rsqr in R. lra.
(* seventh-sub-case: cos (θ1 / 2) = 0 and sin (θ2 / 2) = 0 *)
destruct H8.
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite H8 in eqa.
assert ((cos (θ1 / 2))² = Rsqr 1).
unfold Rsqr in eqa. unfold Rsqr. lra.
apply Rsqr_eq in H9.
specialize (sin2_cos2 (θ2 / 2)) as eqb.
rewrite H7 in eqb.
assert ((sin (θ2 / 2))² = Rsqr 1).
unfold Rsqr in eqb. unfold Rsqr. lra.
apply Rsqr_eq in H10.
rewrite rm10_eq. rewrite rm11_eq.
unfold atan2.
assert (cos θ2 = -1).
assert (θ2 = 2 * (θ2/2)) by lra.
rewrite H11. rewrite cos_2a_cos.
rewrite H7. lra. rewrite H11.
assert ((sin ξ * -1 / cos ξ) = - (sin ξ / cos ξ)) by lra.
rewrite H12. clear H12.
destruct (0 <? cos ξ) eqn:eq3.
apply Rltb_lt in eq3.
assert (cos (atan (sin ξ / cos ξ)) = cos ξ).
rewrite cos_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H12. rewrite sin2_cos2. 
rewrite Rmult_1_l. rewrite Rmult_1_l.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rinv_involutive.
apply sqrt_Rsqr. lra.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
assert (sin (atan (sin ξ / cos ξ)) = sin ξ).
rewrite sin_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H13. rewrite sin2_cos2. 
rewrite Rmult_1_l.
rewrite Rmult_assoc.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rinv_involutive.
rewrite sqrt_Rsqr. 
rewrite <- Rinv_l_sym.
lra. lra. lra.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0. rewrite Cmult_1_l. rewrite Cmult_1_l.
unfold Cexp.
rewrite atan_opp.
rewrite Ropp_involutive.
rewrite H12. rewrite H13.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2. lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_PI.
unfold Cexp.
rewrite atan_opp.
rewrite Ropp_involutive.
rewrite H12. rewrite H13.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI. rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
destruct H10.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_PI.
unfold Cexp.
rewrite atan_opp.
rewrite Ropp_involutive.
rewrite H12. rewrite H13.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
rewrite Cexp_PI.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
rewrite atan_opp.
rewrite Ropp_involutive.
rewrite H12. rewrite H13.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
(* eighth-sub: when cos (θ1 / 2) * cos (θ1 / 2) = 0, sin (θ1 / 2) * sin (θ1 / 2) = 0 and cos ξ <? 0 *)
destruct (cos ξ <? 0) eqn:eq4.
apply Rltb_lt in eq4.
assert (cos (atan (sin ξ / cos ξ)) = -cos ξ).
rewrite cos_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H12. rewrite sin2_cos2. 
rewrite Rmult_1_l. rewrite Rmult_1_l.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rinv_involutive.
rewrite Rsqr_neg.
apply sqrt_Rsqr. lra.
rewrite Rsqr_neg.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
assert (sin (atan (sin ξ / cos ξ)) = -sin ξ).
rewrite sin_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H13. rewrite sin2_cos2. 
rewrite Rmult_1_l.
rewrite Rmult_assoc.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rsqr_neg.
rewrite Rinv_involutive.
rewrite sqrt_Rsqr.
rewrite <- Ropp_mult_distr_r. 
rewrite <- Rinv_l_sym.
lra. lra. lra.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
destruct (0 <=? sin ξ * -1) eqn:eq5.
apply Rleb_le in eq5.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
unfold Cexp.
rewrite atan_opp.
rewrite (Rplus_comm (- atan (sin ξ / cos ξ))).
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_neg. rewrite sin_neg.
rewrite Ropp_involutive.
rewrite H12. rewrite H13.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_PI.
unfold Cexp.
rewrite atan_opp.
rewrite (Rplus_comm (- atan (sin ξ / cos ξ))).
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_neg. rewrite sin_neg.
rewrite Ropp_involutive.
rewrite H12. rewrite H13.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
rewrite Cexp_PI.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
destruct H10.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_PI.
unfold Cexp.
rewrite atan_opp.
rewrite (Rplus_comm (- atan (sin ξ / cos ξ))).
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_neg. rewrite sin_neg.
rewrite Ropp_involutive.
rewrite H12. rewrite H13.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
rewrite Cexp_PI.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
unfold Cexp.
rewrite atan_opp.
rewrite (Rplus_comm (- atan (sin ξ / cos ξ))).
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_neg. rewrite sin_neg.
rewrite Ropp_involutive.
rewrite H12. rewrite H13.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
unfold Cexp.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_0.
unfold Cexp.
rewrite atan_opp.
rewrite Ropp_minus_distr.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_PI.
unfold Cexp.
rewrite atan_opp.
rewrite Ropp_minus_distr.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
rewrite Cexp_PI.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
destruct H10.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_PI.
unfold Cexp.
rewrite atan_opp.
rewrite Ropp_minus_distr.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
rewrite Cexp_PI.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_0.
unfold Cexp.
rewrite atan_opp.
rewrite Ropp_minus_distr.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
apply Rltb_le_false in eq3.
apply Rltb_le_false in eq4.
assert (cos ξ = 0) by lra.
destruct (0 <? sin ξ * -1) eqn:eq5.
assert (sin ξ = -1).
specialize (sin2_cos2 ξ) as eqc.
rewrite H12 in eqc.
assert ((sin ξ)² = Rsqr 1).
unfold Rsqr. unfold Rsqr in eqc. lra.
apply Rsqr_eq in H13. destruct H13.
apply Rltb_lt in eq5. rewrite H13 in eq5. lra.
assumption.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_0.
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI2. rewrite sin_PI2.
rewrite H12. rewrite H13. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_PI.
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI2. rewrite sin_PI2.
rewrite H12. rewrite H13. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI. rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
destruct H10.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_PI.
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI2. rewrite sin_PI2.
rewrite H12. rewrite H13. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI. rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_0.
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI2. rewrite sin_PI2.
rewrite H12. rewrite H13. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
destruct (sin ξ * -1 <? 0) eqn:eq6.
assert (sin ξ = 1).
specialize (sin2_cos2 ξ) as eqc.
rewrite H12 in eqc.
assert ((sin ξ)² = Rsqr 1).
unfold Rsqr. unfold Rsqr in eqc. lra.
apply Rsqr_eq in H13. destruct H13.
assumption.
apply Rltb_le_false in eq5. rewrite H13 in eq5. lra.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_0.
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
assert ((- PI / 2) = - (PI /2)) by lra.
rewrite H. 
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI2. rewrite sin_PI2.
rewrite H12. rewrite H13. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_PI.
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
assert ((- PI / 2) = - (PI /2)) by lra.
rewrite H. 
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI2. rewrite sin_PI2.
rewrite H12. rewrite H13. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI. rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
destruct H10.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_PI.
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
assert ((- PI / 2) = - (PI /2)) by lra.
rewrite H. 
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI2. rewrite sin_PI2.
rewrite H12. rewrite H13. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI. rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite cos_PI2. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite sin_PI2.
rewrite Cexp_0.
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
assert ((- PI / 2) = - (PI /2)) by lra.
rewrite H. 
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI2. rewrite sin_PI2.
rewrite H12. rewrite H13. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite cos_PI2.
rewrite H7. rewrite H8. lca.
apply Rltb_le_false in eq5.
apply Rltb_le_false in eq6.
assert (sin ξ = 0) by lra.
specialize (sin2_cos2 ξ) as R.
rewrite H12 in R. rewrite H13 in R. unfold Rsqr in R. lra.
specialize (sin2_cos2 (θ2 / 2)) as R.
rewrite H7 in R. rewrite H8 in R. unfold Rsqr in R. lra.
- (* sixth case: when rm22 θ1 ξ θ2 = 1 *)
assert (θ1 = θ1) by lra.
apply Rltb_le_false in eq1.
assert (rm22 θ1 ξ θ2 = 1 - 2 * (((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²))).
unfold rm22,rx,ry,Rsqr.
rewrite <- sin_plus.
rewrite <- sin_minus.
lra.
assert (rm22 θ1 ξ θ2 = 1).
remember ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) as r.
remember ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) as g.
assert (r + g = 1).
specialize (sqr_angle_four_1 (ξ / 2) (θ1 / 2 - θ2 / 2) (θ1 / 2 + θ2 / 2)) as H2.
lra.
assert (0 <= r).
rewrite Heqr.
assert (0 <= (sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
lra.
assert (0 <= g).
assert (0 <= (sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²).
rewrite <- Rsqr_mult. apply Rle_0_sqr.
lra.
assert (r <= 1) by lra.
rewrite H1 in eq1.
assert (r <= 0) by lra.
lra.
assert ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))² = 0) by lra.
assert ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))² = 1).
remember ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) as r.
remember ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²) as g.
assert (r + g = 1).
specialize (sqr_angle_four_1 (ξ / 2) (θ1 / 2 - θ2 / 2) (θ1 / 2 + θ2 / 2)) as H4.
lra. lra.
assert ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² = 0).
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult in H3. rewrite <- Rsqr_mult in H3.
apply Rplus_eq_0_l in H3. assumption.
apply Rle_0_sqr. apply Rle_0_sqr.
assert ((cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))² = 0).
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult in H3. rewrite <- Rsqr_mult in H3.
apply Rplus_eq_R0 in H3. destruct H3. assumption.
apply Rle_0_sqr. apply Rle_0_sqr.
apply Rmult_integral in H5.
apply Rmult_integral in H6.
destruct H5. destruct H6.
specialize (sin2_cos2 (ξ / 2)) as eq3.
rewrite H5 in eq3. rewrite H6 in eq3. lra.
assert ((cos (ξ / 2))² = 1).
specialize (sin2_cos2 (ξ / 2)) as eq3.
rewrite H5 in eq3. lra.
assert ((cos (θ1 / 2 + θ2 / 2))² = 1).
specialize (sin2_cos2 (θ1 / 2 + θ2 / 2)) as eq3.
rewrite H6 in eq3. lra.
assert ((sin (ξ / 2)) = 0).
apply Rsqr_eq_0 in H5.
assumption.
assert (sin ξ = 0).
assert (ξ  = 2 * (ξ / 2)) by lra. rewrite H10.
rewrite sin_2a. rewrite H9. lra.
assert (cos ξ = 1).
assert (ξ  = 2 * (ξ / 2)) by lra. rewrite H11.
rewrite cos_2a_sin. rewrite H9. lra.
apply Rsqr_eq_0 in H6. 
assert ((cos (θ1 / 2 + θ2 / 2))² = Rsqr 1).
unfold Rsqr. unfold Rsqr in H8. lra.
apply Rsqr_eq in H12.
destruct H12.
(* first-sub: when sin ξ = 0, cos ξ = 1, and (cos (θ1 / 2 + θ2 / 2)) = 1 *)
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite Cexp_0.
unfold Cexp.
rewrite H10. rewrite H11.
assert ((cos (θ2 / 2) * cos (θ1 / 2) +
 - (sin (θ2 / 2) * ((1, 0) * sin (θ1 / 2))))%C = ((cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H. 
rewrite cos_plus in H12. rewrite H12.
assert (0 / 2 = 0) by lra. rewrite H14.
rewrite cos_0. lca.
rewrite Cexp_0. assert (0 / 2 = 0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp.
rewrite H10. rewrite H11.
rewrite sin_plus in H6.
assert ((cos (θ2 / 2) * sin (θ1 / 2) +
  sin (θ2 / 2) * ((1, 0) * cos (θ1 / 2)))%C
  = ((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H14. rewrite H6. lca.
rewrite Cexp_0. assert (0 / 2 = 0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp. rewrite H10. rewrite H11.
rewrite sin_plus in H6.
assert ((sin (θ2 / 2) * cos (θ1 / 2) +
 cos (θ2 / 2) * ((1, 0) * sin (θ1 / 2)))%C 
 = ((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2) )%R)%C) by lca.
rewrite H14. rewrite H6. lca.
rewrite Cexp_0. assert (0 / 2 = 0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp. rewrite H10. rewrite H11.
rewrite cos_plus in H12.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) +
 cos (θ2 / 2) * ((1, 0) * cos (θ1 / 2)))%C
  = ((cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H14. rewrite H12. 
unfold atan2. rewrite rm11_eq. rewrite rm10_eq.
rewrite H11. rewrite H10.
destruct (0 <? 1) eqn:eq3.
assert (0 * cos θ2 / 1 = 0) by lra.
rewrite H15. rewrite atan_0.
rewrite cos_0. rewrite sin_0.
lca.
apply Rltb_le_false in eq3. lra.
(* second-sub: when sin ξ = 0, cos ξ = 1, and (cos (θ1 / 2 + θ2 / 2)) = -1 *)
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite Cexp_PI.
unfold Cexp.
rewrite H10. rewrite H11.
assert ((cos (θ2 / 2) * cos (θ1 / 2) +
 - (sin (θ2 / 2) * ((1, 0) * sin (θ1 / 2))))%C = ((cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H. 
rewrite cos_plus in H12. rewrite H12.
assert (0 / 2 = 0) by lra. rewrite H14.
rewrite cos_0. lca.
rewrite Cexp_PI. assert (0 / 2 = 0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp.
rewrite H10. rewrite H11.
rewrite sin_plus in H6.
assert ((cos (θ2 / 2) * sin (θ1 / 2) +
  sin (θ2 / 2) * ((1, 0) * cos (θ1 / 2)))%C
  = ((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H14. rewrite H6. lca.
rewrite Cexp_PI. rewrite Cexp_0.
assert (0 / 2 = 0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp. rewrite H10. rewrite H11.
rewrite sin_plus in H6.
assert ((sin (θ2 / 2) * cos (θ1 / 2) +
 cos (θ2 / 2) * ((1, 0) * sin (θ1 / 2)))%C 
 = ((sin (θ1 / 2) * cos (θ2 / 2) + cos (θ1 / 2) * sin (θ2 / 2) )%R)%C) by lca.
rewrite H14. rewrite H6. lca.
rewrite Cexp_0. rewrite Cexp_PI.
assert (0 / 2 = 0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
unfold atan2. rewrite rm11_eq. rewrite rm10_eq.
rewrite H10. rewrite H11.
destruct (0 <? 1) eqn:eq3.
assert ((0 * cos θ2 / 1) = 0) by lra.
rewrite H14. rewrite atan_0.
rewrite cos_0. rewrite sin_0.
rewrite cos_plus in H12.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) +
 cos (θ2 / 2) * ((1, 0) * cos (θ1 / 2)))%C
  = ((cos (θ1 / 2) * cos (θ2 / 2) - sin (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H15. rewrite H12. lca.
apply Rltb_le_false in eq3. lra.
(* third-sub: when sin ξ = 0, cos ξ = -1, and (sin (θ1 / 2 - θ2 / 2)) = 1 *)
destruct H6.
specialize (sin2_cos2 (ξ / 2)) as eq3.
rewrite H6 in eq3.
assert ((sin (ξ / 2))² = 1) by lra.
assert ((cos (θ1 / 2 - θ2 / 2))² = 1).
specialize (sin2_cos2 (θ1 / 2 - θ2 / 2)) as eq4.
rewrite H5 in eq4. lra.
apply Rsqr_eq_0 in H6.
assert (sin ξ = 0).
assert (ξ  = 2 * (ξ / 2)) by lra. rewrite H9.
rewrite sin_2a. rewrite H6. lra.
assert (cos ξ = -1).
assert (ξ  = 2 * (ξ / 2)) by lra. rewrite H10.
rewrite cos_2a_cos. rewrite H6. lra.
apply Rsqr_eq_0 in H5. 
assert ((cos (θ1 / 2 - θ2 / 2))² = Rsqr 1).
unfold Rsqr. unfold Rsqr in H8. lra.
apply Rsqr_eq in H11.
destruct H11.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite Cexp_0.
unfold Cexp.
rewrite H9. rewrite H10.
assert ((cos (θ2 / 2) * cos (θ1 / 2) +
 - (sin (θ2 / 2) * ((-1, 0) * sin (θ1 / 2))))%C = ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H. 
rewrite cos_minus in H11. rewrite H11.
unfold Rdiv. rewrite Rmult_0_l.
rewrite cos_0. lca.
rewrite Cexp_0. 
assert (0 / 2 = 0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp.
rewrite H10. rewrite H9.
rewrite sin_minus in H5.
assert ((cos (θ2 / 2) * sin (θ1 / 2) +
  sin (θ2 / 2) * ((-1, 0) * cos (θ1 / 2)))%C
  = ((sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H13. rewrite H5. lca.
rewrite Cexp_0.
assert (0 / 2 = 0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp. rewrite H10. rewrite H9.
rewrite sin_minus in H5.
assert ((sin (θ2 / 2) * cos (θ1 / 2) +
 cos (θ2 / 2) * ((-1, 0) * sin (θ1 / 2)))%C 
 = ((-(sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H13. rewrite H5. lca.
assert (0 / 2 = 0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_0.
unfold Cexp. rewrite H10. rewrite H9.
rewrite cos_minus in H11.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) +
 cos (θ2 / 2) * ((-1, 0) * cos (θ1 / 2)))%C
  = ((-(cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H13. rewrite H11.
unfold atan2. rewrite rm11_eq. rewrite rm10_eq.
rewrite H9. rewrite H10. 
destruct (0 <? -1) eqn:eq6.
apply Rltb_lt in eq6. lra.
destruct (-1 <? 0) eqn:eq7.
rewrite Rmult_0_l.
destruct (0 <=? 0) eqn:eq8.
assert ((0 / -1) = 0) by lra. rewrite H14.
rewrite atan_0.
rewrite Rplus_0_l.
rewrite cos_PI. rewrite sin_PI.
lca.
apply Rleb_lt_false in eq8. lra.
apply Rltb_le_false in eq7. lra.
(* fourth-sub: when sin ξ = 0, cos ξ = -1, and (cos (θ1 / 2 - θ2 / 2)) = -1 *)
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite Cexp_PI.
unfold Cexp.
rewrite H9. rewrite H10.
assert ((cos (θ2 / 2) * cos (θ1 / 2) +
 - (sin (θ2 / 2) * ((-1, 0) * sin (θ1 / 2))))%C = ((cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H. 
rewrite cos_minus in H11. rewrite H11.
unfold Rdiv. rewrite Rmult_0_l.
rewrite cos_0. lca.
rewrite Cexp_PI. 
assert (0 / 2 = 0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp.
rewrite H10. rewrite H9.
rewrite sin_minus in H5.
assert ((cos (θ2 / 2) * sin (θ1 / 2) +
  sin (θ2 / 2) * ((-1, 0) * cos (θ1 / 2)))%C
  = ((sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2))%R)%C) by lca.
rewrite H13. rewrite H5. lca.
rewrite Cexp_0. rewrite Cexp_PI.
 assert (0 / 2 = 0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp. rewrite H10. rewrite H9.
rewrite sin_minus in H5.
assert ((sin (θ2 / 2) * cos (θ1 / 2) +
 cos (θ2 / 2) * ((-1, 0) * sin (θ1 / 2)))%C 
 = ((-(sin (θ1 / 2) * cos (θ2 / 2) - cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H13. rewrite H5. lca.
rewrite Cexp_PI. rewrite Cexp_0.
assert (0 / 2 = 0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp. rewrite H10. rewrite H9.
rewrite cos_minus in H11.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) +
 cos (θ2 / 2) * ((-1, 0) * cos (θ1 / 2)))%C
  = ((-(cos (θ1 / 2) * cos (θ2 / 2) + sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H13. rewrite H11.
unfold atan2. rewrite rm10_eq. rewrite rm11_eq.
rewrite H9. rewrite H10.
rewrite Rmult_0_l.
destruct (0 <? -1) eqn:eq6.
apply Rltb_lt in eq6. lra.
destruct (-1 <? 0) eqn:eq7.
destruct (0 <=? 0) eqn:eq8.
assert ((0 / -1)=0) by lra. rewrite H14.
rewrite atan_0. rewrite Rplus_0_l.
rewrite cos_PI. rewrite sin_PI.
lca.
apply Rleb_lt_false in eq8.
lra.
apply Rltb_le_false in eq7.
lra.
(* fifth-sub: when cos (θ1 / 2) * cos (θ1 / 2) = 0, sin (θ1 / 2) * sin (θ1 / 2) = 0 and 0 < cos ξ *)
apply Rsqr_eq_0 in H5.
apply Rsqr_eq_0 in H6.
rewrite sin_minus in H5.
rewrite sin_plus in H6.
assert (sin (θ1 / 2) * cos (θ2 / 2) = 0) by lra.
assert (cos (θ1 / 2) * sin (θ2 / 2) = 0) by lra.
apply Rmult_integral in H7.
apply Rmult_integral in H8.
destruct H7. destruct H8.
specialize (sin2_cos2 (θ1 / 2)) as eq3.
rewrite H7 in eq3. rewrite H8 in eq3. unfold Rsqr in eq3. lra.
specialize (sin2_cos2 (θ1 / 2)) as eqa.
rewrite H7 in eqa.
assert ((cos (θ1 / 2))² = Rsqr 1).
unfold Rsqr in eqa. unfold Rsqr. lra.
apply Rsqr_eq in H9.
specialize (sin2_cos2 (θ2 / 2)) as eqb.
rewrite H8 in eqb.
assert ((cos (θ2 / 2))² = Rsqr 1).
unfold Rsqr in eqb. unfold Rsqr. lra.
apply Rsqr_eq in H10.
rewrite rm10_eq. rewrite rm11_eq.
unfold atan2.
assert (cos θ2 = 1).
assert (θ2 = 2 * (θ2/2)) by lra.
rewrite H11. rewrite cos_2a_sin.
rewrite H8. lra. rewrite H11.
rewrite Rmult_1_r.
destruct (0 <? cos ξ) eqn:eq3.
apply Rltb_lt in eq3.
assert (cos (atan (sin ξ / cos ξ)) = cos ξ).
rewrite cos_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H12. rewrite sin2_cos2. 
rewrite Rmult_1_l. rewrite Rmult_1_l.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rinv_involutive.
apply sqrt_Rsqr. lra.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
assert (sin (atan (sin ξ / cos ξ)) = sin ξ).
rewrite sin_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H13. rewrite sin2_cos2. 
rewrite Rmult_1_l.
rewrite Rmult_assoc.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rinv_involutive.
rewrite sqrt_Rsqr. 
rewrite <- Rinv_l_sym.
lra. lra. lra.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite H12. rewrite H13. lca.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_PI. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
rewrite Cexp_PI. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI. rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_PI. rewrite Cexp_0.
unfold Cexp. rewrite H12. rewrite H13.
lca.
destruct H10.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_PI. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
rewrite Cexp_PI. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI. rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_PI. rewrite Cexp_0.
unfold Cexp. rewrite H12. rewrite H13.
lca.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite H12. rewrite H13. lca.
(* sixth-sub: when sin (θ1 / 2) = 0, sin (θ2 / 2) = 0 and cos ξ <? 0 *)
destruct (cos ξ <? 0) eqn:eq4.
apply Rltb_lt in eq4.
assert (cos (atan (sin ξ / cos ξ)) = -cos ξ).
rewrite cos_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H12. rewrite sin2_cos2. 
rewrite Rmult_1_l. rewrite Rmult_1_l.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rinv_involutive.
rewrite Rsqr_neg.
apply sqrt_Rsqr. lra.
rewrite Rsqr_neg.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
assert (sin (atan (sin ξ / cos ξ)) = -sin ξ).
rewrite sin_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H13. rewrite sin2_cos2. 
rewrite Rmult_1_l.
rewrite Rmult_assoc.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rsqr_neg.
rewrite Rinv_involutive.
rewrite sqrt_Rsqr.
rewrite <- Ropp_mult_distr_r. 
rewrite <- Rinv_l_sym.
lra. lra. lra.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
destruct (0 <=? sin ξ) eqn:eq5.
apply Rleb_le in eq5.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite (Rplus_comm (atan (sin ξ / cos ξ))).
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite H12. rewrite H13. lca.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_PI. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
rewrite Cexp_PI. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI. rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_PI. rewrite Cexp_0.
unfold Cexp. 
rewrite (Rplus_comm (atan (sin ξ / cos ξ))).
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite H12. rewrite H13.
lca.
destruct H10.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_PI. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
rewrite Cexp_PI. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI. rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_PI. rewrite Cexp_0.
unfold Cexp. 
rewrite (Rplus_comm (atan (sin ξ / cos ξ))).
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite H12. rewrite H13.
lca.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite (Rplus_comm (atan (sin ξ / cos ξ))).
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite H12. rewrite H13. lca.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite <- Ropp_minus_distr.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite H12. rewrite H13. lca.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_PI. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
rewrite Cexp_PI. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI. rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_PI. rewrite Cexp_0.
unfold Cexp. 
rewrite <- Ropp_minus_distr.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite H12. rewrite H13.
lca.
destruct H10.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_PI. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
rewrite Cexp_PI. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI. rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite Cexp_PI. rewrite Cexp_0.
unfold Cexp. 
rewrite <- Ropp_minus_distr.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite H12. rewrite H13.
lca.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite <- Ropp_minus_distr.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite H12. rewrite H13. lca.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
apply Rltb_le_false in eq3. apply Rltb_le_false in eq4.
assert (cos ξ = 0) by lra.
assert (Rsqr (sin ξ) = Rsqr 1).
specialize (sin2_cos2 ξ) as eqc.
rewrite H13 in eqc. unfold Rsqr in eqc.
unfold Rsqr. lra.
apply Rsqr_eq in H14.
destruct (0 <? sin ξ) eqn:eq5. apply Rltb_lt in eq5.
destruct H14.
unfold Cexp. rewrite H13. rewrite H14.
rewrite cos_PI2. rewrite sin_PI2. lca.
lra.
destruct (sin ξ <? 0) eqn:eq6.
apply Rltb_lt in eq6.
destruct H14. lra.
unfold Cexp. rewrite H13. rewrite H14.
assert (- PI / 2 = - (PI/2)) by lra.
rewrite H15.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI2. rewrite sin_PI2. lca.
apply Rltb_le_false in eq5.
apply Rltb_le_false in eq6.
assert (sin ξ=0) by lra.
destruct H14. lra. lra.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite Cexp_PI.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
apply Rltb_le_false in eq3. apply Rltb_le_false in eq4.
assert (cos ξ = 0) by lra.
assert (Rsqr (sin ξ) = Rsqr 1).
specialize (sin2_cos2 ξ) as eqc.
rewrite H13 in eqc. unfold Rsqr in eqc.
unfold Rsqr. lra.
apply Rsqr_eq in H14.
destruct (0 <? sin ξ) eqn:eq5. apply Rltb_lt in eq5.
destruct H14.
unfold Cexp. rewrite H13. rewrite H14.
rewrite cos_PI2. rewrite sin_PI2. lca.
lra.
destruct (sin ξ <? 0) eqn:eq6.
apply Rltb_lt in eq6.
destruct H14. lra.
unfold Cexp. rewrite H13. rewrite H14.
assert (- PI / 2 = - (PI/2)) by lra.
rewrite H15.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI2. rewrite sin_PI2. lca.
apply Rltb_le_false in eq5.
apply Rltb_le_false in eq6.
assert (sin ξ=0) by lra.
destruct H14. lra. lra.
destruct H10.
unfold uc_cong; simpl. 
exists PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_PI.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite Cexp_PI.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
apply Rltb_le_false in eq3. apply Rltb_le_false in eq4.
assert (cos ξ = 0) by lra.
assert (Rsqr (sin ξ) = Rsqr 1).
specialize (sin2_cos2 ξ) as eqc.
rewrite H13 in eqc. unfold Rsqr in eqc.
unfold Rsqr. lra.
apply Rsqr_eq in H14.
destruct (0 <? sin ξ) eqn:eq5. apply Rltb_lt in eq5.
destruct H14.
unfold Cexp. rewrite H13. rewrite H14.
rewrite cos_PI2. rewrite sin_PI2. lca.
lra.
destruct (sin ξ <? 0) eqn:eq6.
apply Rltb_lt in eq6.
destruct H14. lra.
unfold Cexp. rewrite H13. rewrite H14.
assert (- PI / 2 = - (PI/2)) by lra.
rewrite H15.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI2. rewrite sin_PI2. lca.
apply Rltb_le_false in eq5.
apply Rltb_le_false in eq6.
assert (sin ξ=0) by lra.
destruct H14. lra. lra.
unfold uc_cong; simpl. 
exists 0.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
apply Rltb_le_false in eq3. apply Rltb_le_false in eq4.
assert (cos ξ = 0) by lra.
assert (Rsqr (sin ξ) = Rsqr 1).
specialize (sin2_cos2 ξ) as eqc.
rewrite H13 in eqc. unfold Rsqr in eqc.
unfold Rsqr. lra.
apply Rsqr_eq in H14.
destruct (0 <? sin ξ) eqn:eq5. apply Rltb_lt in eq5.
destruct H14.
unfold Cexp. rewrite H13. rewrite H14.
rewrite cos_PI2. rewrite sin_PI2. lca.
lra.
destruct (sin ξ <? 0) eqn:eq6.
apply Rltb_lt in eq6.
destruct H14. lra.
unfold Cexp. rewrite H13. rewrite H14.
assert (- PI / 2 = - (PI/2)) by lra.
rewrite H15.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI2. rewrite sin_PI2. lca.
apply Rltb_le_false in eq5.
apply Rltb_le_false in eq6.
assert (sin ξ=0) by lra.
destruct H14. lra. lra.
(* seventh-sub: when cos (θ1 / 2) * cos (θ1 / 2) = 0, sin (θ1 / 2) * sin (θ1 / 2) = 0 and 0 < cos ξ *)
destruct H8.
assert ((sin (θ1 / 2))² = Rsqr 1).
specialize (sin2_cos2 (θ1 / 2)) as eq3.
rewrite H8 in eq3.
unfold Rsqr in eq3. unfold Rsqr. lra.
apply Rsqr_eq in H9.
assert ((sin (θ2 / 2))² = Rsqr 1).
specialize (sin2_cos2 (θ2 / 2)) as eq3.
rewrite H7 in eq3.
unfold Rsqr in eq3. unfold Rsqr. lra.
apply Rsqr_eq in H10.
rewrite rm10_eq. rewrite rm11_eq.
unfold atan2.
assert (cos θ2 = -1).
assert (θ2 = 2 * (θ2/2)) by lra.
rewrite H11. rewrite cos_2a_cos.
rewrite H7. lra. rewrite H11.
destruct (0 <? cos ξ) eqn:eq3.
apply Rltb_lt in eq3.
assert (cos (atan (sin ξ / cos ξ)) = cos ξ).
rewrite cos_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H12. rewrite sin2_cos2. 
rewrite Rmult_1_l. rewrite Rmult_1_l.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rinv_involutive.
apply sqrt_Rsqr. lra.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
assert (sin (atan (sin ξ / cos ξ)) = sin ξ).
rewrite sin_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H13. rewrite sin2_cos2. 
rewrite Rmult_1_l.
rewrite Rmult_assoc.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rinv_involutive.
rewrite sqrt_Rsqr. 
rewrite <- Rinv_l_sym.
lra. lra. lra.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
lca.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Cmult_1_l. rewrite Cmult_1_l.
rewrite Cmult_1_l.
assert ((sin ξ * -1 / cos ξ) = - ((sin ξ / cos ξ))) by lra.
rewrite H15.
rewrite atan_opp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
assert (- cos ξ * cos ξ - - sin ξ * - sin ξ = -(Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H16. rewrite sin2_cos2.
lca.
unfold uc_cong; simpl. 
exists (ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp.
lca.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
rewrite Cmult_1_l. rewrite Cmult_1_l.
assert ((sin ξ * -1 / cos ξ) = - ((sin ξ / cos ξ))) by lra.
rewrite H15.
rewrite atan_opp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
assert (cos ξ * cos ξ - sin ξ * - sin ξ = (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H16. rewrite sin2_cos2.
lca.
destruct H10.
unfold uc_cong; simpl. 
exists (ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp.
lca.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
rewrite Cmult_1_l. rewrite Cmult_1_l.
rewrite Cmult_1_l.
assert ((sin ξ * -1 / cos ξ) = - ((sin ξ / cos ξ))) by lra.
rewrite H15.
rewrite atan_opp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
assert (cos ξ * cos ξ - sin ξ * - sin ξ = (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H16. rewrite sin2_cos2.
lca.
unfold uc_cong; simpl. 
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
lca.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Cmult_1_l. rewrite Cmult_1_l.
assert ((sin ξ * -1 / cos ξ) = - ((sin ξ / cos ξ))) by lra.
rewrite H15.
rewrite atan_opp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
assert (- cos ξ * cos ξ - - sin ξ * - sin ξ = -(Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H16. rewrite sin2_cos2.
lca.
(* eighth-sub: when cos (θ1 / 2) * cos (θ1 / 2) = 0, sin (θ1 / 2) * sin (θ1 / 2) = 0 and cos ξ < 0 *)
destruct (cos ξ <? 0) eqn:eq4.
apply Rltb_lt in eq4.
assert (cos (atan (sin ξ / cos ξ)) = -cos ξ).
rewrite cos_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H12. rewrite sin2_cos2. 
rewrite Rmult_1_l. rewrite Rmult_1_l.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rinv_involutive.
rewrite Rsqr_neg.
apply sqrt_Rsqr. lra.
rewrite Rsqr_neg.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
assert (sin (atan (sin ξ / cos ξ)) = -sin ξ).
rewrite sin_atan. unfold Rdiv.
rewrite Rsqr_mult.
assert ((1 + (sin ξ)² * (/ cos ξ)²)
  = ((sin ξ)² + (cos ξ)²) * (/ cos ξ)²).
rewrite <- (Rinv_r ((cos ξ)²)).
rewrite Rsqr_inv. lra. lra.
assert (0 < (cos ξ)²).
apply Rsqr_pos_lt.  lra. lra.
rewrite H13. rewrite sin2_cos2. 
rewrite Rmult_1_l.
rewrite Rmult_assoc.
rewrite Rsqr_inv.
rewrite <- inv_sqrt.
rewrite Rsqr_neg.
rewrite Rinv_involutive.
rewrite sqrt_Rsqr.
rewrite <- Ropp_mult_distr_r. 
rewrite <- Rinv_l_sym.
lra. lra. lra.
rewrite sqrt_Rsqr.
lra. lra. apply Rsqr_pos_lt. lra. lra.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
lca.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
destruct (0 <=? sin ξ * -1) eqn:eq5.
assert ((sin ξ * -1 / cos ξ) = - (sin ξ/cos ξ)) by lra.
rewrite H15.
rewrite (Rplus_comm (atan (- (sin ξ / cos ξ)))).
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Cmult_1_l. rewrite Cmult_1_l. rewrite Cmult_1_l.
rewrite atan_opp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive. rewrite Ropp_involutive.
assert (- cos ξ * cos ξ - - sin ξ * - sin ξ = -(Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H16. rewrite sin2_cos2.
lca.
assert ((sin ξ * -1 / cos ξ) = - (sin ξ/cos ξ)) by lra.
rewrite H15.
rewrite <- Ropp_minus_distr.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Cmult_1_l. rewrite Cmult_1_l. rewrite Cmult_1_l.
rewrite atan_opp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive. rewrite Ropp_involutive.
assert (- cos ξ * cos ξ - - sin ξ * - sin ξ = -(Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H16. rewrite sin2_cos2.
lca.
unfold uc_cong; simpl. 
exists ξ.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
destruct (0 <=? sin ξ * -1) eqn:eq5.
assert ((sin ξ * -1 / cos ξ) = - (sin ξ/cos ξ)) by lra.
rewrite H15.
rewrite (Rplus_comm (atan (- (sin ξ / cos ξ)))).
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Cmult_1_l. rewrite Cmult_1_l.
rewrite atan_opp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive. rewrite Ropp_involutive.
assert (cos ξ * cos ξ - sin ξ * - sin ξ = (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H16. rewrite sin2_cos2.
lca.
assert ((sin ξ * -1 / cos ξ) = - (sin ξ/cos ξ)) by lra.
rewrite H15.
rewrite <- Ropp_minus_distr.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite Cmult_1_l. rewrite Cmult_1_l.
rewrite atan_opp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive. rewrite Ropp_involutive.
assert (cos ξ * cos ξ - sin ξ * - sin ξ = (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H16. rewrite sin2_cos2.
lca.
destruct H10.
unfold uc_cong; simpl. 
exists ξ.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
destruct (0 <=? sin ξ * -1) eqn:eq5.
assert ((sin ξ * -1 / cos ξ) = - (sin ξ/cos ξ)) by lra.
rewrite H15.
rewrite (Rplus_comm (atan (- (sin ξ / cos ξ)))).
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Cmult_1_l. rewrite Cmult_1_l. rewrite Cmult_1_l.
rewrite atan_opp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive. rewrite Ropp_involutive.
assert (cos ξ * cos ξ - sin ξ * - sin ξ = (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H16. rewrite sin2_cos2.
lca.
assert ((sin ξ * -1 / cos ξ) = - (sin ξ/cos ξ)) by lra.
rewrite H15.
rewrite <- Ropp_minus_distr.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite Cmult_1_l. rewrite Cmult_1_l. rewrite Cmult_1_l.
rewrite atan_opp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive. rewrite Ropp_involutive.
assert (cos ξ * cos ξ - sin ξ * - sin ξ = (Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H16. rewrite sin2_cos2.
lca.
unfold uc_cong; simpl. 
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
rewrite Cexp_0.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0.
unfold Cexp.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
lca.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
rewrite H7. rewrite H8.
rewrite H9. rewrite H10.
rewrite Cexp_0.
unfold Cexp.
destruct (0 <=? sin ξ * -1) eqn:eq5.
assert ((sin ξ * -1 / cos ξ) = - (sin ξ/cos ξ)) by lra.
rewrite H15.
rewrite (Rplus_comm (atan (- (sin ξ / cos ξ)))).
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Cmult_1_l. rewrite Cmult_1_l.
rewrite atan_opp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive. rewrite Ropp_involutive.
assert (- cos ξ * cos ξ - - sin ξ * - sin ξ = -(Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H16. rewrite sin2_cos2.
lca.
assert ((sin ξ * -1 / cos ξ) = - (sin ξ/cos ξ)) by lra.
rewrite H15.
rewrite <- Ropp_minus_distr.
rewrite cos_neg. rewrite sin_neg.
rewrite Rtrigo_facts.sin_pi_minus.
rewrite Rtrigo_facts.cos_pi_minus.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite Cmult_1_l. rewrite Cmult_1_l.
rewrite atan_opp.
rewrite cos_neg. rewrite sin_neg.
rewrite H12. rewrite H13.
rewrite Cmult_c.
rewrite Ropp_involutive. rewrite Ropp_involutive.
assert (- cos ξ * cos ξ - - sin ξ * - sin ξ = -(Rsqr (sin ξ) + Rsqr (cos ξ))).
unfold Rsqr. lra.
rewrite H16. rewrite sin2_cos2.
lca.
(* ninth-sub: when cos (θ1 / 2) * cos (θ1 / 2) = 0, sin (θ1 / 2) * sin (θ1 / 2) = 0 and cos ξ = 0 *)
apply Rltb_le_false in eq3.
apply Rltb_le_false in eq4.
assert ((cos ξ) = 0) by lra.
assert (Rsqr (sin ξ) = Rsqr 1).
specialize (sin2_cos2 ξ) as eqc.
rewrite H12 in eqc.
unfold Rsqr in eqc. unfold Rsqr. lra.
apply Rsqr_eq in H13.
destruct (0 <? sin ξ * -1) eqn:eq5.
apply Rltb_lt in eq5.
destruct H13. lra.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists (PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H13. lca. 
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite sin_PI2. rewrite cos_PI2.
rewrite sin_0. rewrite cos_0.
rewrite H12. rewrite H13. lca. 
unfold uc_cong; simpl. 
exists (PI + PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H13. lca. 
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite sin_PI2. rewrite cos_PI2.
rewrite sin_0. rewrite cos_0.
rewrite H12. rewrite H13. lca. 
destruct H10.
unfold uc_cong; simpl. 
exists (PI + PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H13. lca. 
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite sin_PI2. rewrite cos_PI2.
rewrite sin_0. rewrite cos_0.
rewrite H12. rewrite H13. lca. 
unfold uc_cong; simpl. 
exists (PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H13. lca. 
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite sin_PI2. rewrite cos_PI2.
rewrite sin_0. rewrite cos_0.
rewrite H12. rewrite H13. lca. 
destruct (sin ξ * -1 <? 0) eqn:eq6.
apply Rltb_lt in eq6.
destruct H13.
destruct H9. destruct H10.
unfold uc_cong; simpl. 
exists (PI + PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H13. lca. 
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
assert (- PI / 2 = - (PI / 2)) by lra.
rewrite H15. rewrite cos_neg. rewrite sin_neg.
rewrite sin_PI2. rewrite cos_PI2.
rewrite sin_0. rewrite cos_0.
rewrite H12. rewrite H13. lca. 
unfold uc_cong; simpl. 
exists (PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H13. lca. 
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
assert (- PI / 2 = - (PI / 2)) by lra.
rewrite H15. rewrite cos_neg. rewrite sin_neg.
rewrite sin_PI2. rewrite cos_PI2.
rewrite sin_0. rewrite cos_0.
rewrite H12. rewrite H13. lca.
destruct H10.
 unfold uc_cong; simpl. 
exists (PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H13. lca. 
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
assert (- PI / 2 = - (PI / 2)) by lra.
rewrite H15. rewrite cos_neg. rewrite sin_neg.
rewrite sin_PI2. rewrite cos_PI2.
rewrite sin_0. rewrite cos_0.
rewrite H12. rewrite H13. lca.
 unfold uc_cong; simpl. 
exists (PI + PI/2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite sin_PI2. rewrite cos_PI2.
rewrite H12. rewrite H13. lca. 
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite sin_0. lca.
rewrite H7. rewrite H8. rewrite H9. rewrite H10.
assert (0/2=0) by lra. rewrite H.
rewrite cos_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
assert (- PI / 2 = - (PI / 2)) by lra.
rewrite H15. rewrite cos_neg. rewrite sin_neg.
rewrite sin_PI2. rewrite cos_PI2.
rewrite sin_0. rewrite cos_0.
rewrite H12. rewrite H13. lca. 
lra.
apply Rltb_le_false in eq5.
apply Rltb_le_false in eq6.
assert (sin ξ = 0) by lra.
destruct H13. lra. lra.
specialize (sin2_cos2 (θ2 / 2)) as eqc.
rewrite H7 in eqc. rewrite H8 in eqc.
unfold Rsqr in eqc. lra.
Qed.


*)
Admitted.
