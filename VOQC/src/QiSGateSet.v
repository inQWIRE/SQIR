Require Export UnitaryListRepresentation.
Require Export NonUnitaryListRepresentation.
Require Export QArith.
Require Export ZArith.BinInt.
Require Export Reals.ROrderedType.

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

(* if a in u3 is zero then it is a u1 gate *)
Lemma u3_to_u1: forall {dim:nat} (a b c:R) (q:nat), 
    (exists n, a = INR n * (2 * PI)) -> 
     @uc_cong dim (uapp1 (@U_R a (b * PI) (c * PI)) q)
           (uapp1 (@U_R 0 0 ( (b + c) * PI)) q).
Proof.
intros.
unfold uc_cong; simpl.
  autorewrite with eval_db.
  gridify.
destruct H.
destruct (Nat.even x) eqn:eq1.
apply Nat.even_spec in eq1.
unfold Nat.Even in eq1.
destruct eq1.
rewrite H0 in H.
rewrite mult_INR in H.
assert (INR 2 = 2%R).
unfold INR. reflexivity. rewrite H1 in H.
clear H0. clear H1.
exists 0. rewrite Cexp_0. rewrite Mscale_1_l.
apply f_equal2.
apply f_equal2. reflexivity.
unfold rotation.
  prep_matrix_equality.
destruct x1. destruct y.
rewrite H.
assert (2 * INR x0 * (2 * PI) / 2
          = 0 + 2 * INR x0 * PI) by lra.
rewrite H0. clear H0.
rewrite cos_period.
assert (0 / 2 = 0) by lra.
rewrite H0. reflexivity.
destruct y.
rewrite H.
assert (2 * INR x0 * (2 * PI) / 2
          = 0 + 2 * INR x0 * PI) by lra.
rewrite H0. clear H0.
rewrite sin_period.
assert (0 / 2 = 0) by lra.
rewrite H0.
rewrite sin_0. lca. 
reflexivity.
destruct x1. destruct y.
rewrite H.
assert (2 * INR x0 * (2 * PI) / 2
          = 0 + 2 * INR x0 * PI) by lra.
rewrite H0. clear H0.
rewrite sin_period.
assert (0 / 2 = 0) by lra.
rewrite H0. rewrite sin_0. lca.
destruct y.
rewrite H.
assert (2 * INR x0 * (2 * PI) / 2
          = 0 + 2 * INR x0 * PI) by lra.
rewrite H0. clear H0.
rewrite cos_period.
assert (0 / 2 = 0) by lra.
rewrite H0.
rewrite cos_0.
assert (b * PI + c * PI = 0 + (b + c) * PI) by lra.
rewrite H1.
1 - 4: reflexivity.
apply negb_true_iff in eq1.
replace (¬ (Nat.even x)) with (Nat.odd x) in eq1 by reflexivity.
apply Nat.odd_spec in eq1.
unfold Nat.Odd in eq1.
destruct eq1.
rewrite H0 in H.
rewrite plus_INR in H.
rewrite mult_INR in H.
assert (INR 2 = 2%R).
unfold INR. reflexivity. rewrite H1 in H.
assert (INR 1 = 1%R).
unfold INR. reflexivity. rewrite H2 in H.
clear H0. clear H1. clear H2.
exists (PI). rewrite Cexp_PI.
assert (-1 .* (I (2 ^ q) ⊗ rotation 0 0 ((b + c) * PI) ⊗ I (2 ^ d))
   = (I (2 ^ q) ⊗ ( -1 .* rotation 0 0 ((b + c) * PI)) ⊗ I (2 ^ d))).
distribute_scale. reflexivity.
rewrite H0. clear H0.
apply f_equal2.
apply f_equal2. reflexivity.
solve_matrix.
unfold rotation.
destruct x1. destruct y.
rewrite H.
assert ((2 * INR x0 + 1) * (2 * PI) / 2
          = PI + 2 * INR x0 * PI) by lra.
rewrite H0. clear H0.
rewrite cos_period.
assert (0 / 2 = 0) by lra.
rewrite H0. rewrite cos_0. rewrite cos_PI. lca.
destruct y.
rewrite H.
assert ((2 * INR x0 + 1) * (2 * PI) / 2
          = PI + 2 * INR x0 * PI) by lra.
rewrite H0. clear H0.
rewrite sin_period.
assert (0 / 2 = 0) by lra.
rewrite H0.
rewrite sin_0. rewrite sin_PI. lca. lca. 
destruct x1. destruct y.
rewrite H.
assert ((2 * INR x0 + 1) * (2 * PI) / 2
          = PI + 2 * INR x0 * PI) by lra.
rewrite H0. clear H0.
rewrite sin_period.
assert (0 / 2 = 0) by lra.
rewrite H0. rewrite sin_0. rewrite sin_PI. lca.
destruct y.
rewrite H.
assert ((2 * INR x0 + 1) * (2 * PI) / 2
          = PI + 2 * INR x0 * PI) by lra.
rewrite H0. clear H0.
rewrite cos_period.
assert (0 / 2 = 0) by lra.
rewrite H0.
rewrite cos_0. rewrite cos_PI.
assert (b * PI + c * PI = 0 + (b + c) * PI) by lra.
rewrite H1. lca. lca.  lca. 
reflexivity.
Qed.

(* if u1's lambda is zero, then it is SKIP *)
Lemma u1_to_skip: forall {dim:nat} (a:R) (q:nat), 
    (q < dim)%nat -> (exists n, a = INR n * (2 * PI)) -> 
     @uc_equiv dim (uapp1 (@U_R 0 0 (a)) q) SKIP.
Proof.
intros.
unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
unfold rotation. 
  prep_matrix_equality.
destruct H0.
destruct x0. destruct y.
assert (0 / 2 = 0)%R by lra. rewrite H0.
rewrite cos_0. reflexivity.
 destruct y.
assert (0 / 2 = 0)%R by lra. rewrite H0.
rewrite sin_0. lca. reflexivity.
destruct x0. destruct y.
assert (0 / 2 = 0)%R by lra. rewrite H0.
rewrite sin_0. lca.
 destruct y.
assert (0 / 2 = 0)%R by lra. rewrite H0.
rewrite cos_0.
rewrite H.
assert (0 + INR x1 * (2 * PI) = 0 + 2 * INR x1 * PI) by lra.
rewrite H1.
unfold Cexp.
rewrite sin_period. rewrite cos_period.
rewrite sin_0. rewrite cos_0. lca.
reflexivity.
unfold I.
destruct ((S (S x0) =? y)%nat && (S (S x0) <? 2))%nat eqn:eq.
apply andb_true_iff in eq. destruct eq.
apply Nat.ltb_lt in H1. lia. reflexivity.
reflexivity.
destruct dim. inversion H. lia.
Qed.
