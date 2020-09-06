Require Export UnitaryListRepresentation.
Require Export NonUnitaryListRepresentation.
Require Export QArith.
Require Export ZArith.BinInt.
Require Export Reals.ROrderedType.
Require Export Reals.Ratan.

Local Open Scope Z_scope.
Local Open Scope R_scope.
Local Open Scope matrix_scope.
Local Open Scope ucom_scope.

(** RzQ Gate Set **)

Module QiSGateSet <: GateSet.

(* In our optimizer we use the gate set {H, X, RzQ, CNOT} where RzQ is
   rotation about the z-axis by i * PI / (2 ^ k) for integer i. We'll 
   call this the RzQ gate set. *)

Inductive QiS_Unitary : nat -> Set := 
  | UQiS_U1 (a : R)   : QiS_Unitary 1 
  | UQiS_U2 (a b : R)   : QiS_Unitary 1 
  | UQiS_U3 (a b c : R)   : QiS_Unitary 1 
  | UQiS_CNOT        : QiS_Unitary 2.
Definition U := QiS_Unitary.

Definition match_gate {n} (u u' : U n) : bool :=
  match u, u' with
  | UQiS_CNOT, UQiS_CNOT => true
  | UQiS_U1 q, UQiS_U1 q' => Reqb q q'
  | UQiS_U2 a b, UQiS_U2 a' b' => (Reqb a a') && (Reqb b b')
  | UQiS_U3 a b c, UQiS_U3 a' b' c' => (Reqb a a') && (Reqb b b') && (Reqb c c')
  | _, _ => false
  end.

(* Definition degree_to_pi (a:R) := ((a / 180) * PI). *)

Definition to_base {n} (u : U n) :=
  match u with
  | UQiS_U1 a     => U_R 0 0 (a * PI)
  | UQiS_U2 a b     => U_R (PI / 2) ( a * PI) ( b * PI)
  | UQiS_U3 a b c     => U_R ( a * PI) ( b * PI) ( c * PI)
  | UQiS_CNOT  => U_CNOT
  end.

(*
Lemma Qeq_div: forall (a b c:R), (a == b) -> (a / c) == (b / c).
Proof.
unfold Qeq.
intros. simpl.
rewrite Pos2Z.inj_mul.
rewrite Pos2Z.inj_mul.
assert (Qnum a * Qnum (/ c) * (Z.pos (Qden b) * Z.pos (Qden (/ c)))
          =  Qnum a * Z.pos (Qden b) * (Qnum (/ c) * Z.pos (Qden (/ c))))%Z.
rewrite Z.mul_assoc.
assert (Qnum a * Qnum (/ c) * Z.pos (Qden b) = Qnum a * Z.pos (Qden b) * Qnum (/ c))%Z.
rewrite <- Z.mul_assoc.
assert ((Qnum (/ c) * Z.pos (Qden b)) = (Z.pos (Qden b) * (Qnum (/ c))))%Z by apply Z.mul_comm.
rewrite -> H0.
rewrite Z.mul_assoc. reflexivity.
rewrite H0.
rewrite <- Z.mul_assoc. reflexivity.
rewrite H0.
assert (Qnum b * Qnum (/ c) * (Z.pos (Qden a) * Z.pos (Qden (/ c)))
          =  Qnum b * Z.pos (Qden a) * ( Qnum (/ c) * Z.pos (Qden (/ c))))%Z.
rewrite Z.mul_assoc.
assert (Qnum b * Qnum (/ c) * Z.pos (Qden a) = Qnum b * Z.pos (Qden a) * Qnum (/ c))%Z.
rewrite <- Z.mul_assoc.
assert ((Qnum (/ c) * Z.pos (Qden a)) = (Z.pos (Qden a) * (Qnum (/ c))))%Z by apply Z.mul_comm.
rewrite -> H1.
rewrite Z.mul_assoc. reflexivity.
rewrite H1.
rewrite <- Z.mul_assoc. reflexivity.
rewrite H1.
rewrite H. reflexivity.
Qed.*)


Lemma match_gate_implies_eq : forall n (u u' : U n), 
  match_gate u u' = true -> to_base u = to_base u'. 
Proof.
  intros n u u' H.
  dependent destruction u; dependent destruction u';
  auto; inversion H. 
  simpl.
  apply Reqb_eq in H1.
  rewrite H1. reflexivity.
  apply andb_true_iff in H1. destruct H1.
  apply Reqb_eq in H0. apply Reqb_eq in H1.
  rewrite H0, H1. reflexivity.
  apply andb_true_iff in H1. destruct H1.
  apply andb_true_iff in H0. destruct H0.
  apply Reqb_eq in H0. 
  apply Reqb_eq in H1.
  apply Reqb_eq in H2.
  rewrite H0, H1, H2. reflexivity.
Qed.

End QiSGateSet.
Export QiSGateSet.

Module QiSProps := UListRepresentationProps QiSGateSet.
Export QiSProps.

(* Useful shorthands. *)
Definition U1 {dim} a q := @App1 _ dim (UQiS_U1 a) q.
Definition U2 {dim} a b q := @App1 _ dim (UQiS_U2 a b) q.
Definition U3 {dim} a b c q := @App1 _ dim (UQiS_U3 a b c) q.
Definition CNOT {dim} q1 q2 := @App2 _ dim UQiS_CNOT q1 q2.
Definition QiS_ucom dim := ucom QiS_Unitary dim.
Definition QiS_ucom_l dim := gate_list QiS_Unitary dim.

(* equivalence of u1 ; u1 to a u1 gate. *)
Lemma two_u1_to_one: forall {dim:nat} (a a':R) (q:nat), 
     @uc_equiv dim (useq (uapp1 (@U_R 0 0 (a * PI)) q) (uapp1 (@U_R 0 0 (a' * PI)) q))
           (uapp1 (@U_R 0 0 ((a + a') * PI)) q).
Proof.
intros.
unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity. solve_matrix.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0. lca.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0. lca.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0. lca.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0.
repeat rewrite Rplus_0_l.
  autorewrite with C_db.
rewrite <- Cexp_add.
assert ((a' * PI + a * PI) = (a + a') * PI) by lra.
rewrite H1. reflexivity.
reflexivity.
Qed.

(* a u1 following with a u2 gates yeilds a result of u2 x u1. *)
Lemma u1_u2_to_one: forall {dim:nat} (a a' b:R) (q:nat), 
     @uc_equiv dim (useq (uapp1 (@U_R 0 0 (a * PI)) q) 
                 (uapp1 (@U_R (PI / 2) (a' * PI) (b * PI)) q))
           (uapp1 (@U_R (PI / 2) (a' * PI) ((a + b) * PI)) q).
Proof.
intros.
unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
solve_matrix.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0. lca.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0.
  autorewrite with R_db C_db.
rewrite Cmult_comm.
rewrite Cmult_assoc.
rewrite <- Cexp_add.
rewrite <- Rmult_plus_distr_r. reflexivity.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0. lca.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0.
  autorewrite with R_db C_db.
rewrite Cmult_comm.
rewrite Cmult_assoc.
rewrite <- Cexp_add.
assert (a * PI + (a' * PI + b * PI) = (a' * PI + (a + b) * PI))%R by lra.
rewrite H1. reflexivity. reflexivity.
Qed.

(* a u2 following with a u1 gates yeilds a result of u1 x u2. *)
Lemma u2_u1_to_one: forall {dim:nat} (a a' b:R) (q:nat), 
     @uc_equiv dim (useq (uapp1 (@U_R (PI / 2) (a' * PI) (b * PI)) q)
                        (uapp1 (@U_R 0 0 (a * PI)) q))
           (uapp1 (@U_R (PI / 2) ((a' + a) * PI) (b * PI)) q).
Proof.
intros.
unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
solve_matrix.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0. lca.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0. lca.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0.
  autorewrite with R_db C_db.
rewrite Cmult_assoc.
rewrite <- Cexp_add.
rewrite Rmult_plus_distr_r.
rewrite Rplus_comm. reflexivity.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0.
  autorewrite with R_db C_db.
rewrite Cmult_assoc.
rewrite <- Cexp_add.
assert (a * PI + (a' * PI + b * PI) = (a' + a) * PI + b * PI)%R by lra.
rewrite H1. reflexivity. reflexivity.
Qed.


(* a u1 following with a u3 gates yeilds a result of u3 x u1. *)
Lemma u1_u3_to_one: forall {dim:nat} (a a' b c:R) (q:nat), 
     @uc_equiv dim (useq (uapp1 (@U_R 0 0 (a * PI)) q) 
                 (uapp1 (@U_R (a' * PI) (b * PI) (c * PI)) q))
           (uapp1 (@U_R (a' * PI) (b * PI) ((a + c) * PI)) q).
Proof.
intros.
unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
solve_matrix.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0. lca.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0.
  autorewrite with R_db C_db.
rewrite Cmult_comm.
rewrite Cmult_assoc.
rewrite <- Cexp_add.
rewrite Rmult_plus_distr_r. reflexivity.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0. lca.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0.
  autorewrite with R_db C_db.
rewrite Cmult_comm.
rewrite Cmult_assoc.
rewrite <- Cexp_add.
assert (a * PI + (b * PI + c * PI) = b * PI + (a + c) * PI)%R by lra.
rewrite H1. reflexivity. reflexivity.
Qed.


(* a u3 following with a u1 gates yeilds a result of u1 x u3. *)
Lemma u3_u1_to_one: forall {dim:nat} (a a' b c:R) (q:nat), 
     @uc_equiv dim (useq (uapp1 (@U_R (a' * PI) (b * PI) (c * PI)) q)
                       (uapp1 (@U_R 0 0 (a * PI)) q))
           (uapp1 (@U_R (a' * PI) ((b + a) * PI) (c * PI)) q).
Proof.
intros.
unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
solve_matrix.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0. lca.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0. lca.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0.
  autorewrite with R_db C_db.
rewrite Cmult_assoc.
rewrite <- Cexp_add.
rewrite Rmult_plus_distr_r. rewrite Rplus_comm.
reflexivity.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0.
  autorewrite with R_db C_db.
rewrite Cmult_assoc.
rewrite <- Cexp_add.
assert (a * PI + (b * PI + c * PI) = (b + a) * PI + c * PI)%R by lra.
rewrite H1. reflexivity. reflexivity.
Qed.

(* two u2 gates yeilds a result of U3 (180 - b' - a) (a' + 90) (b + 90). *)
Lemma two_u2_to_one: forall {dim:nat} (a b a' b':R) (q:nat), 
     @uc_cong dim (useq (uapp1 (@U_R (PI / 2) (a * PI) (b * PI)) q)
                       (uapp1 (@U_R (PI / 2) (a' * PI) (b' * PI)) q))
           (uapp1 (@U_R ((1 - (b' + a)) * PI) ((a' + 1/2) * PI) ((b + 1/2) * PI)) q).
Proof.
intros.
unfold uc_cong; simpl.
exists (((b' + a) - 1) * (PI / 2)).
  autorewrite with eval_db.
  gridify.
assert ((I (2 ^ q)
    ⊗ rotation ((1 - (b' + a)) * PI) ((a' + 1 / 2) * PI) ((b + 1 / 2) * PI)
    ⊗ I (2 ^ d)) =
    I (2 ^ q)
    ⊗ (rotation ((1 - (b' + a)) * PI) ((a' + 1 / 2) * PI) ((b + 1 / 2) * PI)
    ⊗ I (2 ^ d))).
rewrite kron_assoc. reflexivity. rewrite H0. clear H0.
restore_dims.
rewrite <- Mscale_kron_dist_r.
rewrite <- Mscale_kron_dist_l.
rewrite <- kron_assoc.
apply f_equal2.
apply f_equal2. reflexivity.
solve_matrix.
-
assert ((Cexp (b' * PI) * sin (PI / 2 / 2) * (Cexp (a * PI) * sin (PI / 2 / 2)))
   = (Cexp (b' * PI) * Cexp (a * PI) * (sin (PI / 2 / 2) * sin (PI / 2 / 2))))%C by lca.
rewrite H0. clear H0.
rewrite <- Cexp_add.
assert (b' * PI + a * PI = (b' + a) * PI) by lra.
rewrite H0. clear H0.
assert ((b' + a - 1) * (PI / 2) =  - ((PI / 2) - (b' + a) * (PI / 2))) by lra.
rewrite H0. clear H0.
assert ((1 - (b' + a)) * PI / 2 = PI / 2 - ((b' + a) * (PI / 2))) by lra.
rewrite H0. clear H0.
unfold Cexp. rewrite <- cos_sym. rewrite sin_antisym.
rewrite sin_shift. rewrite cos_shift.
assert (((sin ((b' + a) * (PI / 2)), (- cos ((b' + a) * (PI / 2)))%R) *
 sin ((b' + a) * (PI / 2)))
 = ((sin ((b' + a) * (PI / 2)) * sin ((b' + a) * (PI / 2)))%R, 
        ((- cos ((b' + a) * (PI / 2))) * sin ((b' + a) * (PI / 2)))%R))%C by lca.
rewrite H0. clear H0.
assert (sin ((b' + a) * (PI / 2)) * sin ((b' + a) * (PI / 2))
       = 1 / 2 - cos (2 * ((b' + a) * (PI / 2))) / 2).
rewrite cos_2a_sin. lra.
rewrite H0. clear H0.
assert (- cos ((b' + a) * (PI / 2)) * sin ((b' + a) * (PI / 2))
   = - sin (2 * ((b' + a) * (PI / 2))) / 2).
rewrite sin_2a. lra.
rewrite H0. clear H0.
assert (2 * ((b' + a) * (PI / 2)) = (b' + a) * PI) by lra.
rewrite H0. clear H0.
assert (PI / 2 / 2 = PI / 4)%R by lra. rewrite H0. clear H0.
rewrite cos_PI4. rewrite sin_PI4.
assert ((1 / √ 2)%R * (1 / √ 2)%R = 1 / 2)%R.
field_simplify_eq. rewrite pow2_sqrt. reflexivity. lra.
intros R. apply sqrt_eq_0 in R. lra. lra.
assert ((1 / √ 2)%R * (1 / √ 2)%R  = (1 / √ 2 * (1 / √ 2))%R)%C by lca.
rewrite H1. rewrite H0. lca.
-
rewrite Cexp_add.
assert((b + 1 / 2) * PI = b * PI + PI / 2) by lra.
rewrite H0. clear H0.
rewrite Cexp_add.
assert ((cos (PI / 2 / 2) * (Cexp (b * PI) * sin (PI / 2 / 2)) +
  Cexp (b' * PI) * sin (PI / 2 / 2) *
  (Cexp (a * PI) * Cexp (b * PI) * cos (PI / 2 / 2)))
  = Cexp (b * PI) *
     (cos (PI / 2 / 2) * sin (PI / 2 / 2) +
          Cexp (b' * PI) * Cexp (a * PI) * (sin (PI / 2 / 2) * cos (PI / 2 / 2))))%C by lca.
rewrite H0. clear H0.
assert ((Cexp ((b' + a - 1) * (PI / 2)) *
  (Cexp (b * PI) * Cexp (PI / 2) * sin ((1 - (b' + a)) * PI / 2)))
   = Cexp (b * PI) * ((Cexp ((b' + a - 1) * (PI / 2)) * Cexp (PI / 2))
           * sin ((1 - (b' + a)) * PI / 2)))%C by lca.
rewrite H0. clear H0.
rewrite <- Cexp_add.
rewrite <- Cexp_add.
assert ((b' + a - 1) * (PI / 2) + PI / 2 = (b' + a) * (PI / 2)) by lra.
rewrite H0. clear H0.
assert ((1 - (b' + a)) * PI / 2 = PI / 2 - ((b' + a) * (PI / 2))) by lra.
rewrite H0. clear H0.
rewrite sin_shift.
unfold Cexp.
assert (((cos ((b' + a) * (PI / 2)), sin ((b' + a) * (PI / 2))) * cos ((b' + a) * (PI / 2)))
   = ((cos ((b' + a) * (PI / 2)) * cos ((b' + a) * (PI / 2)))%R,
               (sin ((b' + a) * (PI / 2)) * cos ((b' + a) * (PI / 2)))%R))%C by lca.
rewrite H0. clear H0.
assert ((cos ((b' + a) * (PI / 2)) * cos ((b' + a) * (PI / 2)))%R
      = cos (2 * ((b' + a) * (PI / 2))) / 2 + 1 / 2).
rewrite cos_2a_cos. lra. rewrite H0. clear H0.
assert ((sin ((b' + a) * (PI / 2)) * cos ((b' + a) * (PI / 2)))%R
   = sin (2 * ((b' + a) * (PI / 2))) / 2). rewrite sin_2a. lra.
rewrite H0. clear H0.
assert (PI / 2 / 2 = PI / 4)%R by lra. rewrite H0. clear H0.
rewrite cos_PI4. rewrite sin_PI4.
assert ((1 / √ 2)%R * (1 / √ 2)%R = 1 / 2)%R.
field_simplify_eq. rewrite pow2_sqrt. reflexivity. lra.
intros R. apply sqrt_eq_0 in R. lra. lra.
assert ((1 / √ 2)%R * (1 / √ 2)%R  = (1 / √ 2 * (1 / √ 2))%R)%C by lca.
rewrite H1. rewrite H0.
assert (2 * ((b' + a) * (PI / 2)) = b' * PI + a * PI) by lra.
rewrite H2. lca.
-
rewrite Cexp_add.
assert((a' + 1 / 2) * PI = a' * PI + PI / 2) by lra.
rewrite H0. clear H0.
rewrite Cexp_add.
assert ((Cexp (a' * PI) * sin (PI / 2 / 2) * cos (PI / 2 / 2) +
 Cexp (a' * PI) * Cexp (b' * PI) * cos (PI / 2 / 2) *
 (Cexp (a * PI) * sin (PI / 2 / 2)))%C
  = Cexp (a' * PI) *
     (sin (PI / 2 / 2) * cos (PI / 2 / 2) +
          Cexp (b' * PI) * Cexp (a * PI) * (cos (PI / 2 / 2) * sin (PI / 2 / 2))))%C by lca.
rewrite H0. clear H0.
assert ((Cexp ((b' + a - 1) * (PI / 2)) *
 (Cexp (a' * PI) * Cexp (PI / 2) * sin ((1 - (b' + a)) * PI / 2)))%C
   = Cexp (a' * PI) * ((Cexp ((b' + a - 1) * (PI / 2)) * Cexp (PI / 2))
           * sin ((1 - (b' + a)) * PI / 2)))%C by lca.
rewrite H0. clear H0.
rewrite <- Cexp_add.
rewrite <- Cexp_add.
assert ((b' + a - 1) * (PI / 2) + PI / 2 = (b' + a) * (PI / 2)) by lra.
rewrite H0. clear H0.
assert ((1 - (b' + a)) * PI / 2 = PI / 2 - ((b' + a) * (PI / 2))) by lra.
rewrite H0. clear H0.
rewrite sin_shift.
unfold Cexp.
assert (((cos ((b' + a) * (PI / 2)), sin ((b' + a) * (PI / 2))) * cos ((b' + a) * (PI / 2)))
   = ((cos ((b' + a) * (PI / 2)) * cos ((b' + a) * (PI / 2)))%R,
               (sin ((b' + a) * (PI / 2)) * cos ((b' + a) * (PI / 2)))%R))%C by lca.
rewrite H0. clear H0.
assert ((cos ((b' + a) * (PI / 2)) * cos ((b' + a) * (PI / 2)))%R
      = cos (2 * ((b' + a) * (PI / 2))) / 2 + 1 / 2).
rewrite cos_2a_cos. lra. rewrite H0. clear H0.
assert ((sin ((b' + a) * (PI / 2)) * cos ((b' + a) * (PI / 2)))%R
   = sin (2 * ((b' + a) * (PI / 2))) / 2). rewrite sin_2a. lra.
rewrite H0. clear H0.
assert (PI / 2 / 2 = PI / 4)%R by lra. rewrite H0. clear H0.
rewrite cos_PI4. rewrite sin_PI4.
assert ((1 / √ 2)%R * (1 / √ 2)%R = 1 / 2)%R.
field_simplify_eq. rewrite pow2_sqrt. reflexivity. lra.
intros R. apply sqrt_eq_0 in R. lra. lra.
assert ((1 / √ 2)%R * (1 / √ 2)%R  = (1 / √ 2 * (1 / √ 2))%R)%C by lca.
rewrite H1. rewrite H0.
assert (2 * ((b' + a) * (PI / 2)) = b' * PI + a * PI) by lra.
rewrite H2. lca.
-
rewrite Cexp_add.
rewrite Cexp_add.
rewrite Cexp_add.
assert((a' + 1 / 2) * PI = a' * PI + PI / 2) by lra.
rewrite H0. clear H0.
assert((b + 1 / 2) * PI = b * PI + PI / 2) by lra.
rewrite H0. clear H0.
rewrite Cexp_add.
rewrite Cexp_add.
assert ((- (Cexp (a' * PI) * sin (PI / 2 / 2) * (Cexp (b * PI) * sin (PI / 2 / 2))) +
 Cexp (a' * PI) * Cexp (b' * PI) * cos (PI / 2 / 2) *
 (Cexp (a * PI) * Cexp (b * PI) * cos (PI / 2 / 2)))%C
  = (Cexp (a' * PI) * Cexp (b * PI)) *
     (- (sin (PI / 2 / 2) * sin (PI / 2 / 2)) +
          Cexp (b' * PI) * Cexp (a * PI) * (cos (PI / 2 / 2) * cos (PI / 2 / 2))))%C by lca.
rewrite H0. clear H0.
assert ((Cexp ((b' + a - 1) * (PI / 2)) *
 (Cexp (a' * PI) * Cexp (PI / 2) * (Cexp (b * PI) * Cexp (PI / 2)) *
  cos ((1 - (b' + a)) * PI / 2)))%C
   = (Cexp (a' * PI) * Cexp (b * PI))
        * (((Cexp ((b' + a - 1) * (PI / 2)) * Cexp (PI / 2)) *
            cos ((1 - (b' + a)) * PI / 2)) *Cexp (PI / 2)))%C by lca.
rewrite H0. clear H0.
rewrite <- Cexp_add.
rewrite <- Cexp_add.
rewrite <- Cexp_add.
assert ((b' + a - 1) * (PI / 2) + PI / 2 = (b' + a) * (PI / 2)) by lra.
rewrite H0. clear H0.
assert ((1 - (b' + a)) * PI / 2 = PI / 2 - ((b' + a) * (PI / 2))) by lra.
rewrite H0. clear H0.
rewrite cos_shift.
rewrite Cexp_PI2.
unfold Cexp.
assert (((cos ((b' + a) * (PI / 2)), sin ((b' + a) * (PI / 2))) *
  sin ((b' + a) * (PI / 2)))%C
   = ((cos ((b' + a) * (PI / 2)) * sin ((b' + a) * (PI / 2)))%R,
               (sin ((b' + a) * (PI / 2)) * sin ((b' + a) * (PI / 2)))%R))%C by lca.
rewrite H0. clear H0.
assert ((sin ((b' + a) * (PI / 2)) * sin ((b' + a) * (PI / 2)))%R
      = 1 / 2 - cos (2 * ((b' + a) * (PI / 2))) / 2).
rewrite cos_2a_sin. lra. rewrite H0. clear H0.
assert ((cos ((b' + a) * (PI / 2)) * sin ((b' + a) * (PI / 2)))%R
   = sin (2 * ((b' + a) * (PI / 2))) / 2). rewrite sin_2a. lra.
rewrite H0. clear H0.
assert (PI / 2 / 2 = PI / 4)%R by lra. rewrite H0. clear H0.
rewrite cos_PI4. rewrite sin_PI4.
assert ((1 / √ 2)%R * (1 / √ 2)%R = 1 / 2)%R.
field_simplify_eq. rewrite pow2_sqrt. reflexivity. lra.
intros R. apply sqrt_eq_0 in R. lra. lra.
assert ((1 / √ 2)%R * (1 / √ 2)%R  = (1 / √ 2 * (1 / √ 2))%R)%C by lca.
rewrite H1. rewrite H0.
assert (2 * ((b' + a) * (PI / 2)) = b' * PI + a * PI) by lra.
rewrite H2. lca.
-
reflexivity.
Qed.

(*
Lemma is_Z: forall (n :Z) (a: Q), (0 < n)%Z -> 
      Qnum a mod (n * Z.pos (Qden a)) = 0%Z -> (exists (x:Z), a = inject_Z (n * x)).
Proof.
intros.
apply  Z_div_exact_full_2 in H0.
assert ((n * Z.pos (Qden a) * (Qnum a / (n * Z.pos (Qden a))))
      = (n * (Qnum a / (n * Z.pos (Qden a)))) * Z.pos (Qden a))%Z by lia.
(*
rewrite H1 in H0. clear H1.
assert ((inject_Z (n * (Qnum a / (n * Z.pos (Qden a))) * Z.pos (Qden a))) / (inject_Z (Z.pos (Qden a)))
       = inject_Z (n * (Qnum a / (n * Z.pos (Qden a)))))%Q.
rewrite inject_Z_mult.
2: {rewrite <- H0 in H1.
    assert (a = inject_Z (Qnum a) / inject_Z (Z.pos (Qden a))). 
    assert (a = Qmake (Qnum a) (Qden a))%Q.
}
rewrite Qdiv_mult_l.
rewrite Q_div_mult_full. reflexivity. lia.
assert (inject_Z ((Qnum a) / Z.pos (Qden a)) = a).*)
Admitted.

Lemma cos_Z: forall (a: Z), cos (IZR a * 2 * PI) = 1%R.
Proof.
intros.
destruct a.
assert (0 * 2 * PI = 0)%R by lra. rewrite H. rewrite cos_0. reflexivity.
rewrite <- positive_nat_Z. rewrite <- INR_IZR_INZ.
assert (INR (Pos.to_nat p) * 2 * PI = 0 + 2 * INR (Pos.to_nat p) * PI)%R by lra.
rewrite H. rewrite cos_period. apply cos_0.
rewrite <- Pos2Z.opp_pos. rewrite opp_IZR.
rewrite <- positive_nat_Z. rewrite <- INR_IZR_INZ.
assert (- INR (Pos.to_nat p) * 2 * PI = - (INR (Pos.to_nat p) * 2 * PI))%R by lra.
rewrite H. rewrite cos_neg.
assert (INR (Pos.to_nat p) * 2 * PI = 0 + 2 * INR (Pos.to_nat p) * PI)%R by lra.
rewrite H0. rewrite cos_period. apply cos_0.
Qed.

Lemma sin_Z: forall (a: Z), sin (IZR a * 2 * PI) = 0%R.
Proof.
intros.
destruct a.
assert (0 * 2 * PI = 0)%R by lra. rewrite H. rewrite sin_0. reflexivity.
rewrite <- positive_nat_Z. rewrite <- INR_IZR_INZ.
assert (INR (Pos.to_nat p) * 2 * PI = 0 + 2 * INR (Pos.to_nat p) * PI)%R by lra.
rewrite H. rewrite sin_period. apply sin_0.
rewrite <- Pos2Z.opp_pos. rewrite opp_IZR.
rewrite <- positive_nat_Z. rewrite <- INR_IZR_INZ.
assert (- INR (Pos.to_nat p) * 2 * PI = - (INR (Pos.to_nat p) * 2 * PI))%R by lra.
rewrite H. rewrite sin_neg.
assert (INR (Pos.to_nat p) * 2 * PI = 0 + 2 * INR (Pos.to_nat p) * PI)%R by lra.
rewrite H0. rewrite sin_period. rewrite sin_0; lra.
Qed.
*)

Lemma cos_1_cos_half: forall (x:R), cos x = 1 -> cos (x / 2) = 1 \/ cos (x / 2) = -1.
Proof.
intros.
assert (sin x = 0).
specialize (sin2_cos2 (x)) as H1. 
rewrite H in H1.
assert (1² = 1).
unfold Rsqr. lra. rewrite H0 in H1.
assert ((sin x)² = 0) by lra.
apply Rsqr_0_uniq in H2. assumption.
assert (x = 2 * (x / 2)) by lra.
rewrite H1 in H. rewrite H1 in H0.
rewrite sin_2a in H0.
assert (sin (x / 2) * cos (x / 2) = 0) by lra.
apply Rmult_integral in H2.
destruct H2.
specialize (sin2_cos2 (x / 2)) as H3.
rewrite H2 in H3.
assert (0² = 0). unfold Rsqr. lra.
rewrite H4 in H3.
assert ((cos (x / 2))² = 1) by lra.
specialize ( pow_R1 (cos (x / 2)) 2) as H6.
assert ((cos (x / 2))² = cos (x / 2) ^ 2).
unfold Rsqr. lra.
rewrite H7 in H5. apply H6 in H5.
destruct H5.
assert ((cos (x / 2)) < 0 \/ cos (x / 2) >= 0) by lra.
destruct H8.
apply Rabs_left in H8.
rewrite H8 in H5.
right. lra.
apply Rabs_right in H8. rewrite H8 in H5.
left. apply H5.
inversion H5.
rewrite cos_2a_cos in H.
rewrite H2 in H. lra.
Qed. 

Lemma cos_1_sin_half: forall (x:R), cos x = 1 -> sin (x / 2) = 0.
Proof.
intros.
assert (sin x = 0).
specialize (sin2_cos2 (x)) as H1. 
rewrite H in H1.
assert (1² = 1).
unfold Rsqr. lra. rewrite H0 in H1.
assert ((sin x)² = 0) by lra.
apply Rsqr_0_uniq in H2. assumption.
assert (x = 2 * (x / 2)) by lra.
rewrite H1 in H. rewrite H1 in H0.
rewrite sin_2a in H0.
assert (sin (x / 2) * cos (x / 2) = 0) by lra.
apply Rmult_integral in H2.
destruct H2.
assumption.
rewrite cos_2a_cos in H.
rewrite H2 in H. lra.
Qed. 

Lemma sin_1_half: forall (x:R), sin x = 1 -> 
      (cos (x / 2) = 1 / √ 2 /\ sin (x / 2) = 1 / √ 2)
            \/ (cos (x / 2) = - 1 / √ 2 /\ sin (x / 2) = - 1 / √ 2).
Proof.
intros.
assert (cos x = 0).
specialize (sin2_cos2 (x)) as H1. 
rewrite H in H1.
assert (1² = 1).
unfold Rsqr. lra. rewrite H0 in H1.
assert ((cos x)² = 0) by lra.
apply Rsqr_0_uniq in H2. assumption.
assert (x = 2 * (x / 2)) by lra.
rewrite H1 in H. rewrite H1 in H0.
rewrite sin_2a in H.
assert (sin (x / 2) * cos (x / 2) = 1 / 2) by lra.
assert (H3 := H0).
rewrite cos_2a_cos in H0.
rewrite cos_2a_sin in H3.
assert (cos (x / 2) * cos (x / 2) = 1 / 2) by lra.
assert (sin (x / 2) * sin (x / 2) = 1 / 2) by lra.
assert (cos (x / 2) < 0 \/ 0 <= cos (x / 2)) by lra.
assert (sin (x / 2) < 0 \/ 0 <= sin (x / 2)) by lra.
destruct H6. destruct H7.
assert (0 < - cos (x / 2)) by lra.
assert (0 < - sin (x / 2)) by lra.
assert ((- cos (x / 2)) * (- cos (x / 2)) = 1 / 2) by lra.
assert ((- sin (x / 2)) * (- sin (x / 2)) = 1 / 2) by lra.
apply  sqrt_lem_1 in H10.
apply  sqrt_lem_1 in H11.
rewrite  sqrt_div_alt in H10.  rewrite sqrt_div_alt in H11.
rewrite sqrt_1 in H10. rewrite sqrt_1 in H11.
right. lra. lra. lra. lra. lra. lra. lra.
assert (0 < - cos (x / 2)) by lra.
assert ((- cos (x / 2)) * (- cos (x / 2)) = 1 / 2) by lra.
apply  sqrt_lem_1 in H5.
apply  sqrt_lem_1 in H9.
rewrite <- H5 in H2.
assert (cos (x / 2) = - √ (1 / 2)) by lra.
rewrite H10 in H2.
assert (√ (1 / 2) * - √ (1 / 2) = - (√ (1 / 2) * √ (1 / 2))) by lra.
rewrite H11 in H2.
rewrite sqrt_sqrt in H2. lra. lra. lra.  lra. lra. assumption.
destruct H7.
assert (0 < - sin (x / 2)) by lra.
assert ((- sin (x / 2)) * (- sin (x / 2)) = 1 / 2) by lra.
apply  sqrt_lem_1 in H4.
apply  sqrt_lem_1 in H9.
rewrite <- H4 in H2.
assert (sin (x / 2) = - √ (1 / 2)) by lra.
rewrite H10 in H2.
assert (- √ (1 / 2) * √ (1 / 2) = - (√ (1 / 2) * √ (1 / 2))) by lra.
rewrite H11 in H2.
rewrite sqrt_sqrt in H2. lra. lra. lra.  lra. lra. assumption.
apply  sqrt_lem_1 in H4.
apply  sqrt_lem_1 in H5.
left. split. rewrite <- H4.
rewrite  sqrt_div_alt. rewrite sqrt_1. reflexivity. lra.
rewrite <- H5.
rewrite  sqrt_div_alt. rewrite sqrt_1. reflexivity. lra.
lra. lra. lra. assumption.
Qed. 

Lemma sin_neg_1_half: forall (x:R), sin x = - 1 -> 
      (cos (x / 2) = - 1 / √ 2 /\ sin (x / 2) = 1 / √ 2)
            \/ (cos (x / 2) = 1 / √ 2 /\ sin (x / 2) = - 1 / √ 2).
Proof.
intros.
assert (cos x = 0).
specialize (sin2_cos2 (x)) as H1. 
rewrite H in H1.
assert ((-1)² = 1).
unfold Rsqr. lra. rewrite H0 in H1.
assert ((cos x)² = 0) by lra.
apply Rsqr_0_uniq in H2. assumption.
assert (x = 2 * (x / 2)) by lra.
rewrite H1 in H. rewrite H1 in H0.
rewrite sin_2a in H.
assert (sin (x / 2) * cos (x / 2) = - 1 / 2) by lra.
assert (H3 := H0).
rewrite cos_2a_cos in H0.
rewrite cos_2a_sin in H3.
assert (cos (x / 2) * cos (x / 2) = 1 / 2) by lra.
assert (sin (x / 2) * sin (x / 2) = 1 / 2) by lra.
assert (cos (x / 2) < 0 \/ 0 <= cos (x / 2)) by lra.
assert (sin (x / 2) < 0 \/ 0 <= sin (x / 2)) by lra.
destruct H6. destruct H7.
assert (0 < - cos (x / 2)) by lra.
assert (0 < - sin (x / 2)) by lra.
assert ((- cos (x / 2)) * (- cos (x / 2)) = 1 / 2) by lra.
assert ((- sin (x / 2)) * (- sin (x / 2)) = 1 / 2) by lra.
apply  sqrt_lem_1 in H10.
apply  sqrt_lem_1 in H11.
assert (cos (x / 2) = - √ (1 / 2)) by lra.
assert (sin (x / 2) = - √ (1 / 2)) by lra.
rewrite H12 in H2. rewrite H13 in H2.
assert (√ (1 / 2) * √ (1 / 2) = -1 / 2) by lra.
rewrite sqrt_sqrt in H14.
1 - 6: lra.
assert (0 < - cos (x / 2)) by lra.
assert ((- cos (x / 2)) * (- cos (x / 2)) = 1 / 2) by lra.
apply sqrt_lem_1 in H9. apply sqrt_lem_1 in H5.
assert (cos (x / 2) = - √ (1 / 2)) by lra.
left. split. rewrite  sqrt_div_alt in H10.
rewrite sqrt_1 in H10. lra. lra.
rewrite sqrt_div_alt in H5. rewrite sqrt_1 in H5.
1 - 6: lra.
destruct H7.
assert (0 < - sin (x / 2)) by lra.
assert ((- sin (x / 2)) * (- sin (x / 2)) = 1 / 2) by lra.
apply  sqrt_lem_1 in H9.
apply  sqrt_lem_1 in H4.
right. split.
rewrite <- H4.
rewrite sqrt_div_alt. rewrite sqrt_1. reflexivity.
lra.
rewrite sqrt_div_alt in H9. rewrite sqrt_1 in H9.
assert (sin (x / 2) = - 1 / √ 2) by lra.
1 - 6: lra.
apply  sqrt_lem_1 in H4.
apply  sqrt_lem_1 in H5.
rewrite <- H4 in H2. 
rewrite <- H5 in H2.
rewrite sqrt_sqrt in H2.
1-6: lra.
Qed. 


(* if a in u3 is zero then it is a u1 gate *)
Lemma u3_to_u1: forall {dim:nat} (a b c:R) (q:nat), 
    cos (a * PI) = 1 -> 
     @uc_cong dim (uapp1 (@U_R (a * PI) (b * PI) (c * PI)) q)
           (uapp1 (@U_R 0 0 ( (b + c) * PI)) q).
Proof.
intros.
unfold uc_cong; simpl.
  autorewrite with eval_db.
  gridify.
apply cos_1_cos_half in H as H0.
apply cos_1_sin_half in H.
destruct H0.
exists 0.
rewrite Cexp_0.
rewrite Mscale_1_l.
apply f_equal2.
apply f_equal2. reflexivity.
unfold rotation.
  prep_matrix_equality.
destruct x. destruct y.
rewrite H0.
assert (0 / 2 = 0) by lra.
rewrite H1. rewrite cos_0. reflexivity.
destruct y.
rewrite H.
assert (0 / 2 = 0) by lra.
rewrite H1.
rewrite sin_0. lca. 
reflexivity.
destruct x. destruct y.
rewrite H.
assert (0 / 2 = 0) by lra.
rewrite H1. rewrite sin_0. lca.
destruct y.
rewrite H0.
assert (0 / 2 = 0) by lra.
rewrite H1.
rewrite cos_0.
assert (b * PI + c * PI = 0 + (b + c) * PI) by lra.
rewrite H2.
1 - 4: reflexivity.
exists (PI). rewrite Cexp_PI.
assert (-1 .* (I (2 ^ q) ⊗ rotation 0 0 ((b + c) * PI) ⊗ I (2 ^ d))
   = (I (2 ^ q) ⊗ ( -1 .* rotation 0 0 ((b + c) * PI)) ⊗ I (2 ^ d))).
distribute_scale. reflexivity.
rewrite H1. clear H1.
apply f_equal2.
apply f_equal2. reflexivity.
solve_matrix.
unfold rotation.
destruct x. destruct y.
rewrite H0.
assert (0 / 2 = 0) by lra.
rewrite H1. rewrite cos_0. lca.
destruct y.
rewrite H.
assert (0 / 2 = 0) by lra.
rewrite H1.
rewrite sin_0. lca. lca. 
destruct x. destruct y.
rewrite H.
assert (0 / 2 = 0) by lra.
rewrite H1. rewrite sin_0. lca.
destruct y.
rewrite H0.
assert (0 / 2 = 0) by lra.
rewrite H1.
rewrite cos_0.
assert (b * PI + c * PI = 0 + (b + c) * PI) by lra.
rewrite H2. lca. lca.  lca. 
reflexivity.
Qed.

(* if a in u3 a b c is PI / 2 then it is a u2 b c gate *)
Lemma u3_to_u2: forall {dim:nat} (a b c:R) (q:nat), 
    sin (a * PI) = 1 -> 
     @uc_cong dim (uapp1 (@U_R (a * PI) (b * PI) (c * PI)) q)
           (uapp1 (@U_R (PI / 2) ( b * PI) ( c * PI)) q).
Proof.
intros.
unfold uc_cong; simpl.
  autorewrite with eval_db.
  gridify.
apply sin_1_half in H as H0.
destruct H0.
destruct H0.
exists 0.
rewrite Cexp_0. rewrite Mscale_1_l.
apply f_equal2.
apply f_equal2. reflexivity.
unfold rotation.
  prep_matrix_equality.
destruct x. destruct y.
rewrite H0.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite cos_PI4. reflexivity.
destruct y.
rewrite H1.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite sin_PI4. reflexivity.
reflexivity.
destruct x. destruct y.
rewrite H1.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite sin_PI4. reflexivity.
destruct y.
rewrite H0.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite cos_PI4.
1 - 4: reflexivity.
destruct H0.
exists (PI). rewrite Cexp_PI.
rewrite <- Mscale_kron_dist_l.
rewrite <- Mscale_kron_dist_r.
apply f_equal2.
apply f_equal2. reflexivity.
solve_matrix.
unfold rotation.
destruct x. destruct y.
rewrite H0.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite cos_PI4. lca.
destruct y.
rewrite H1.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite sin_PI4. lca. lca.
destruct x. destruct y.
rewrite H1.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite sin_PI4. lca.
destruct y.
rewrite H0.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite cos_PI4. lca. lca. lca.
reflexivity.
Qed.

(* if a in u3 a b c is 3* PI / 2 then it is a u2 b c gate *)
Lemma u3_to_u2_neg: forall {dim:nat} (a b c:R) (q:nat), 
    sin (a * PI) = - 1 -> 
     @uc_cong dim (uapp1 (@U_R (a * PI) (b * PI) (c * PI)) q)
           (uapp1 (@U_R (PI / 2) ((b + 1) * PI) ((c - 1) * PI)) q).
Proof.
intros.
unfold uc_cong; simpl.
  autorewrite with eval_db.
  gridify.
apply sin_neg_1_half in H as H0.
destruct H0.
destruct H0.
exists PI.
rewrite Cexp_PI.
rewrite <- Mscale_kron_dist_l.
rewrite <- Mscale_kron_dist_r.
apply f_equal2.
apply f_equal2. reflexivity.
solve_matrix.
unfold rotation.
destruct x. destruct y.
rewrite H0.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite cos_PI4. lca.
destruct y.
rewrite H1.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite sin_PI4.
assert ((c - 1) * PI = c * PI + (- PI)) by lra.
rewrite H3.
rewrite Cexp_add.
assert (Cexp (- PI) = -1).
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI. rewrite sin_PI. lca.
rewrite H4. lca. lca.
destruct x. destruct y.
rewrite H1.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite sin_PI4.
assert (((b + 1) * PI) = b * PI + PI) by lra.
rewrite H3. rewrite Cexp_add.
rewrite Cexp_PI. lca.
destruct y.
rewrite H0.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite cos_PI4.
assert ((c - 1) * PI = c * PI + (- PI)) by lra.
rewrite H3.
rewrite Cexp_add. rewrite Cexp_add. rewrite Cexp_add.
assert (Cexp (- PI) = -1).
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI. rewrite sin_PI. lca.
assert (((b + 1) * PI) = b * PI + PI) by lra.
rewrite H5. rewrite Cexp_add.
rewrite Cexp_PI. rewrite H4. lca.
lca. lca. reflexivity.
destruct H0. exists 0.
rewrite Cexp_0.
rewrite Mscale_1_l.
apply f_equal2.
apply f_equal2. reflexivity.
unfold rotation.
prep_matrix_equality.
destruct x. destruct y.
rewrite H0.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite cos_PI4. lca.
destruct y.
rewrite H1.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite sin_PI4.
assert ((c - 1) * PI = c * PI + (- PI)) by lra.
rewrite H3.
rewrite Cexp_add.
assert (Cexp (- PI) = -1).
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI. rewrite sin_PI. lca.
rewrite H4.
lca. reflexivity.
destruct x. destruct y.
rewrite H1.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite sin_PI4.
assert (((b + 1) * PI) = b * PI + PI) by lra.
rewrite H3. rewrite Cexp_add.
rewrite Cexp_PI. lca.
destruct y.
rewrite H0.
assert (PI / 2 / 2 = PI / 4) by lra.
rewrite H2. rewrite cos_PI4.
assert ((c - 1) * PI = c * PI + (- PI)) by lra.
rewrite H3.
rewrite Cexp_add. rewrite Cexp_add. rewrite Cexp_add.
assert (Cexp (- PI) = -1).
unfold Cexp.
rewrite cos_neg. rewrite sin_neg.
rewrite cos_PI. rewrite sin_PI. lca.
assert (((b + 1) * PI) = b * PI + PI) by lra.
rewrite H5. rewrite Cexp_add.
rewrite Cexp_PI. rewrite H4. lca.
1 - 3: reflexivity.
Qed.

(* if u1's lambda is zero, then it is SKIP *)
Lemma u1_to_skip: forall {dim:nat} (a:R) (q:nat), 
    (q < dim)%nat -> cos (a * PI) = 1 -> 
     @uc_equiv dim (uapp1 (@U_R 0 0 (a * PI)) q) SKIP.
Proof.
intros.
unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
unfold rotation. 
  prep_matrix_equality.
destruct x0. destruct y.
assert (0 / 2 = 0)%R by lra. rewrite H.
rewrite cos_0. reflexivity.
 destruct y.
assert (0 / 2 = 0)%R by lra. rewrite H.
rewrite sin_0. lca. reflexivity.
destruct x0. destruct y.
assert (0 / 2 = 0)%R by lra. rewrite H.
rewrite sin_0. lca.
 destruct y.
assert (0 / 2 = 0)%R by lra. rewrite H.
rewrite cos_0.
assert ((0 + a * PI) = a * PI) by lra.
rewrite H1. clear H1.
unfold Cexp.
assert (sin (a * PI) = 0).
specialize (sin2_cos2 (a * PI)) as H1. 
rewrite H0 in H1.
assert (1² = 1).
unfold Rsqr. lra. rewrite H2 in H1.
assert ((sin (a * PI))² = 0) by lra.
apply Rsqr_0_uniq in H3. assumption.
rewrite H0. rewrite H1. lca. lca.
unfold I.
destruct ((S (S x0) =? y)%nat && (S (S x0) <? 2))%nat eqn:eq.
apply andb_true_iff in eq. destruct eq.
apply Nat.ltb_lt in H1. lia. reflexivity.
reflexivity.
destruct dim. inversion H. lia.
Qed.

(* defining the result of U3 + U3 *)
Definition re_a (t1 t2 a b: R) : R := (cos (t1 /2) * cos (t2 / 2)) - (cos (a + b) * sin (t1 / 2) * sin (t2 / 2)).

Definition im_a (t1 t2 a b: R) : R := - sin (a + b) * sin (t1 / 2) * sin (t2 / 2).

Definition re_b (t1 t2 a b: R) : R := - (cos (t1 /2) * sin (t2 / 2)) - (cos (a + b) * sin (t1 / 2) * cos (t2 / 2)).

Definition im_b (t1 t2 a b: R) : R := - sin (a + b) * sin (t1 / 2) * cos (t2 / 2).

Definition alpha (t1 t2 a b:R) :R := acos (sqrt ((re_a t1 t2 a b)^2 + (im_a t1 t2 a b)^2)).

Definition beta (t1 t2 a b:R) :R := acos ((re_a t1 t2 a b) / (sqrt ((re_a t1 t2 a b)^2 + (im_a t1 t2 a b)^2))).


(* two u3 gates yeilds a result of U3 of ZYZ rotation. *)
(* first, if re_a = 0 /\ im_a = 0, since u3 is a unitary matrix, the result is u3 PI theta1 lambda2 *)
Lemma two_u3_to_one_zero: forall {dim:nat} (a b c a' b' c':R) (q:nat), 
    re_a a a' c b' = 0 -> im_a a a' c b' = 0 ->
    @uc_equiv dim (useq (uapp1 (@U_R a b c) q)
                       (uapp1 (@U_R a' b' c') q))
           (uapp1 (@U_R PI b c') q)
   \/ @uc_equiv dim (useq (uapp1 (@U_R a b c) q)
                       (uapp1 (@U_R a' b' c') q))
           (uapp1 (@U_R (3 * PI) b c') q).
Proof.
intros.
unfold re_a in H.
unfold im_a in H0.
assert (sin (c + b') * sin (a / 2) * sin (a' / 2) = 0) by lra.
apply Rmult_integral in H1.
destruct H1.
apply Rmult_integral in H1.
destruct H1.
assert (cos (c + b') = 1 \/ cos (c + b') = -1).
specialize (sin2_cos2 (c + b')) as H2.
rewrite H1 in H2. 
assert (0²=0).
unfold Rsqr. lra. rewrite H3 in H2. clear H3.
assert (1²=1). unfold Rsqr. lra. 
rewrite <- H3 in H2. clear H3.
assert ((cos (c + b'))² = 1²) by lra.
apply Rsqr_eq in H3. lra.
destruct H2.
rewrite H2 in H.
assert (cos (a / 2) * cos (a' / 2) - sin (a / 2) * sin (a' / 2) = 0) by lra.
rewrite <-  cos_plus  in H3.
assert (sin (a / 2 + a' / 2) = 1 \/ sin (a / 2 + a' / 2) = -1).
specialize (sin2_cos2 (a / 2 + a' / 2)) as H4.
rewrite H3 in H4. 
assert (0²=0).
unfold Rsqr. lra. rewrite H5 in H4. clear H5.
assert (1²=1). unfold Rsqr. lra. 
rewrite <- H5 in H4. clear H5.
assert ((sin (a / 2 + a' / 2))² = 1²) by lra.
apply Rsqr_eq in H5. lra.
destruct H4.
left.
unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
solve_matrix.
Admitted.


(* the main theorem *)
Lemma two_u3_to_one: forall {dim:nat} (a b c a' b' c':R) (q:nat), 
    re_a a a' c b' <> 0 \/ im_a a a' c b' <> 0 ->
     @uc_cong dim (useq (uapp1 (@U_R a b c) q)
                       (uapp1 (@U_R a' b' c') q))
           (uapp1 (@U_R (alpha a a' c b') (b + b' + c + 2 * (beta a a' c b')) c') q).
Proof.
intros.
remember (alpha a a' c b') as t. unfold alpha in Heqt.
remember (beta a a' c b') as dl. unfold beta in Heqdl.
unfold uc_cong; simpl.
  autorewrite with eval_db.
  gridify.
exists (beta a a' c b').
rewrite <- Mscale_kron_dist_l.
rewrite <- Mscale_kron_dist_r.
apply f_equal2.
apply f_equal2. reflexivity.
solve_matrix.
Admitted.




