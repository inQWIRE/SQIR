Require Export UnitaryListRepresentation.
Require Export NonUnitaryListRepresentation.
Require Export QArith.
Require Export ZArith.BinInt.

Local Open Scope Z_scope.
Local Open Scope Q_scope.
Local Open Scope matrix_scope.
Local Open Scope ucom_scope.

(** RzQ Gate Set **)

Module QiSGateSet <: GateSet.

(* In our optimizer we use the gate set {H, X, RzQ, CNOT} where RzQ is
   rotation about the z-axis by i * PI / (2 ^ k) for integer i. We'll 
   call this the RzQ gate set. *)

Inductive QiS_Unitary : nat -> Set := 
  | UQiS_U1 (a : Q)   : QiS_Unitary 1 
  | UQiS_U2 (a b : Q)   : QiS_Unitary 1 
  | UQiS_U3 (a b c : Q)   : QiS_Unitary 1 
  | UQiS_CNOT        : QiS_Unitary 2.
Definition U := QiS_Unitary.

Definition match_gate {n} (u u' : U n) : bool :=
  match u, u' with
  | UQiS_CNOT, UQiS_CNOT => true
  | UQiS_U1 q, UQiS_U1 q' => Qeq_bool q q'
  | UQiS_U2 a b, UQiS_U2 a' b' => (Qeq_bool a a') && (Qeq_bool b b')
  | UQiS_U3 a b c, UQiS_U3 a' b' c' => (Qeq_bool a a') && (Qeq_bool b b') && (Qeq_bool c c')
  | _, _ => false
  end.

Definition degree_to_pi (a:Q) := ((Qreals.Q2R (a / 180)) * PI)%R.

Definition to_base {n} (u : U n) :=
  match u with
  | UQiS_U1 a     => U_R 0 0 (Qreals.Q2R a * PI)
  | UQiS_U2 a b     => U_R (PI / 2) (Qreals.Q2R a * PI) (Qreals.Q2R b * PI)
  | UQiS_U3 a b c     => U_R (Qreals.Q2R a * PI) (Qreals.Q2R b * PI) (Qreals.Q2R c * PI)
  | UQiS_CNOT  => U_CNOT
  end.

Lemma Qeq_div: forall (a b c:Q), (a == b) -> (a / c) == (b / c).
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
Qed.


Lemma match_gate_implies_eq : forall n (u u' : U n), 
  match_gate u u' = true -> to_base u = to_base u'. 
Proof.
  intros n u u' H.
  dependent destruction u; dependent destruction u';
  auto; inversion H. 
  simpl.
  apply Qeq_bool_iff in H1.
  apply f_equal.
 apply RMicromega.Q2R_m in H1. rewrite H1. reflexivity.
  simpl.
  apply andb_true_iff in H1. destruct H1.
  apply Qeq_bool_iff in H1.   apply Qeq_bool_iff in H0.
  apply RMicromega.Q2R_m in H0.
  apply RMicromega.Q2R_m in H1.
  rewrite H0. rewrite H1. reflexivity.
  simpl.
  apply andb_true_iff in H1. destruct H1.
  apply andb_true_iff in H0. destruct H0.
  apply Qeq_bool_iff in H0. 
  apply Qeq_bool_iff in H1.
  apply Qeq_bool_iff in H2.
  apply RMicromega.Q2R_m in H0.
  apply RMicromega.Q2R_m in H1.
  apply RMicromega.Q2R_m in H2.
  rewrite H0. rewrite H1. rewrite H2. reflexivity.
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
Lemma two_u1_to_one: forall {dim:nat} (a a':Q) (q:nat), 
     @uc_equiv dim (useq (uapp1 (@U_R 0 0 (Qreals.Q2R a * PI)) q) (uapp1 (@U_R 0 0 (Qreals.Q2R a' * PI)) q))
           (uapp1 (@U_R 0 0 (Qreals.Q2R (a + a') * PI)) q).
Proof.
intros.
unfold uc_equiv; simpl.
unfold Qreals.Q2R; simpl.
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
simpl.
repeat rewrite Rplus_0_l.
  autorewrite with C_db.
unfold Cexp, Cmult;simpl.
rewrite <- cos_plus.
assert ((cos (IZR (Qnum a') * / IZR (Z.pos (Qden a')) * PI) *
 sin (IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI) +
 sin (IZR (Qnum a') * / IZR (Z.pos (Qden a')) * PI) *
 cos (IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI))%R
  =  (sin (IZR (Qnum a') * / IZR (Z.pos (Qden a')) * PI) *
        cos (IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI)
  + cos (IZR (Qnum a') * / IZR (Z.pos (Qden a')) * PI) *
          sin (IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI))%R) by lra.
rewrite H1. rewrite <- sin_plus.
assert ((IZR (Qnum a') * / IZR (Z.pos (Qden a')) * PI + IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI)
     = (IZR (Qnum a * Z.pos (Qden a') + Qnum a' * Z.pos (Qden a)) *
    / IZR (Z.pos (Qden a * Qden a')) * PI))%R.
assert ((IZR (Qnum a') * / IZR (Z.pos (Qden a')) * PI + IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI)%R
       = ((IZR (Qnum a') * / IZR (Z.pos (Qden a')) + IZR (Qnum a) * / IZR (Z.pos (Qden a))) * PI)%R) by lra.
rewrite H2. rewrite Pos2Z.inj_mul.
rewrite plus_IZR. repeat rewrite mult_IZR.
field_simplify_eq. reflexivity. split.
intro contra.
assert (Z.pos (Qden a') <> 0)%Z. lia.
apply not_0_IZR in H3. rewrite contra in H3. contradiction.
intro contra.
assert (Z.pos (Qden a) <> 0)%Z. lia.
apply not_0_IZR in H3. rewrite contra in H3. contradiction.
rewrite H2. reflexivity. reflexivity.
Qed.

(* a u1 following with a u2 gates yeilds a result of u2 x u1. *)
Lemma u1_u2_to_one: forall {dim:nat} (a a' b:Q) (q:nat), 
     @uc_equiv dim (useq (uapp1 (@U_R 0 0 (Qreals.Q2R a * PI)) q) 
                 (uapp1 (@U_R (PI / 2) (Qreals.Q2R a' * PI) (Qreals.Q2R b * PI)) q))
           (uapp1 (@U_R (PI / 2) (Qreals.Q2R a' * PI) (Qreals.Q2R (a + b) * PI)) q).
Proof.
intros.
unfold uc_equiv; simpl.
unfold Qreals.Q2R; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
rewrite Pos2Z.inj_mul.
rewrite plus_IZR. repeat rewrite mult_IZR. 
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
assert (Cexp (IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI) *
  Cexp (IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI)
   = Cexp
    ((IZR (Qnum a) * IZR (Z.pos (Qden b)) + IZR (Qnum b) * IZR (Z.pos (Qden a))) *
     / (IZR (Z.pos (Qden a)) * IZR (Z.pos (Qden b))) * PI))%C.
unfold Cexp, Cmult;simpl.
rewrite <- cos_plus.
assert ((cos (IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI) *
 sin (IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI) +
 sin (IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI) *
 cos (IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI))%R
  =  (sin (IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI) *
        cos (IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI)
  + cos (IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI) *
          sin (IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI))%R) by lra.
rewrite H1. rewrite <- sin_plus.
assert ((IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI + IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI)
     = ((IZR (Qnum a) * IZR (Z.pos (Qden b)) + IZR (Qnum b) * IZR (Z.pos (Qden a))) *
    / (IZR (Z.pos (Qden a)) * IZR (Z.pos (Qden b))) * PI))%R.
field_simplify_eq. reflexivity. split.
intro contra.
assert (Z.pos (Qden b) <> 0)%Z. lia.
apply not_0_IZR in H2. rewrite contra in H2. contradiction.
intro contra.
assert (Z.pos (Qden a) <> 0)%Z. lia.
apply not_0_IZR in H2. rewrite contra in H2. contradiction.
rewrite H2. reflexivity. rewrite H1. reflexivity.
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
assert ((IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI +
    (IZR (Qnum a') * / IZR (Z.pos (Qden a')) * PI +
     IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI))
   = (IZR (Qnum a') * / IZR (Z.pos (Qden a')) * PI +
    (IZR (Qnum a) * IZR (Z.pos (Qden b)) + IZR (Qnum b) * IZR (Z.pos (Qden a))) *
    / (IZR (Z.pos (Qden a)) * IZR (Z.pos (Qden b))) * PI))%R.
field_simplify_eq. reflexivity. split.
intro contra.
assert (Z.pos (Qden b) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
split.
intro contra.
assert (Z.pos (Qden a) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
intro contra.
assert (Z.pos (Qden a') <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
rewrite H1. reflexivity. reflexivity.
Qed.

(* a u2 following with a u1 gates yeilds a result of u1 x u2. *)
Lemma u2_u1_to_one: forall {dim:nat} (a a' b:Q) (q:nat), 
     @uc_equiv dim (useq (uapp1 (@U_R (PI / 2) (Qreals.Q2R a' * PI) (Qreals.Q2R b * PI)) q)
                        (uapp1 (@U_R 0 0 (Qreals.Q2R a * PI)) q))
           (uapp1 (@U_R (PI / 2) (Qreals.Q2R (a' + a) * PI) (Qreals.Q2R b * PI)) q).
Proof.
intros.
unfold uc_equiv; simpl.
unfold Qreals.Q2R; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
rewrite Pos2Z.inj_mul.
rewrite plus_IZR. repeat rewrite mult_IZR. 
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
assert ((IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI + IZR (Qnum a') * / IZR (Z.pos (Qden a')) * PI) 
    = (IZR (Qnum a') * IZR (Z.pos (Qden a)) + IZR (Qnum a) * IZR (Z.pos (Qden a'))) *
    / (IZR (Z.pos (Qden a')) * IZR (Z.pos (Qden a))) * PI)%R. 
field_simplify_eq. reflexivity. split.
intro contra.
assert (Z.pos (Qden a) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
intro contra.
assert (Z.pos (Qden a') <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
rewrite H1. reflexivity.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0.
  autorewrite with R_db C_db.
rewrite Cmult_assoc.
rewrite <- Cexp_add.
assert (IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI +
    (IZR (Qnum a') * / IZR (Z.pos (Qden a')) * PI +
     IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI)
    = (IZR (Qnum a') * IZR (Z.pos (Qden a)) + IZR (Qnum a) * IZR (Z.pos (Qden a'))) *
    / (IZR (Z.pos (Qden a')) * IZR (Z.pos (Qden a))) * PI +
    IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI)%R. 
field_simplify_eq. reflexivity. split.
intro contra.
assert (Z.pos (Qden b) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
split.
intro contra.
assert (Z.pos (Qden a) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
intro contra.
assert (Z.pos (Qden a') <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
rewrite H1. reflexivity. reflexivity.
Qed.


(* a u1 following with a u3 gates yeilds a result of u3 x u1. *)
Lemma u1_u3_to_one: forall {dim:nat} (a a' b c:Q) (q:nat), 
     @uc_equiv dim (useq (uapp1 (@U_R 0 0 (Qreals.Q2R a * PI)) q) 
                 (uapp1 (@U_R (Qreals.Q2R a' * PI) (Qreals.Q2R b * PI) (Qreals.Q2R c * PI)) q))
           (uapp1 (@U_R (Qreals.Q2R a' * PI) (Qreals.Q2R b * PI) (Qreals.Q2R (a + c) * PI)) q).
Proof.
intros.
unfold uc_equiv; simpl.
unfold Qreals.Q2R; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
rewrite Pos2Z.inj_mul.
rewrite plus_IZR. repeat rewrite mult_IZR. 
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
assert ((IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI + IZR (Qnum c) * / IZR (Z.pos (Qden c)) * PI)
    = (IZR (Qnum a) * IZR (Z.pos (Qden c)) + IZR (Qnum c) * IZR (Z.pos (Qden a))) *
     / (IZR (Z.pos (Qden a)) * IZR (Z.pos (Qden c))) * PI)%R. 
field_simplify_eq. reflexivity. split.
intro contra.
assert (Z.pos (Qden c) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
intro contra.
assert (Z.pos (Qden a) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
rewrite H1. reflexivity.
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
assert ((IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI +
    (IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI + IZR (Qnum c) * / IZR (Z.pos (Qden c)) * PI))
   = IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI +
    (IZR (Qnum a) * IZR (Z.pos (Qden c)) + IZR (Qnum c) * IZR (Z.pos (Qden a))) *
    / (IZR (Z.pos (Qden a)) * IZR (Z.pos (Qden c))) * PI)%R.
field_simplify_eq. reflexivity. split.
intro contra.
assert (Z.pos (Qden c) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
split.
intro contra.
assert (Z.pos (Qden a) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
intro contra.
assert (Z.pos (Qden b) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
rewrite H1. reflexivity. reflexivity.
Qed.


(* a u3 following with a u1 gates yeilds a result of u1 x u3. *)
Lemma u3_u1_to_one: forall {dim:nat} (a a' b c:Q) (q:nat), 
     @uc_equiv dim (useq (uapp1 (@U_R (Qreals.Q2R a' * PI) (Qreals.Q2R b * PI) (Qreals.Q2R c * PI)) q)
                       (uapp1 (@U_R 0 0 (Qreals.Q2R a * PI)) q))
           (uapp1 (@U_R (Qreals.Q2R a' * PI) (Qreals.Q2R (b + a) * PI) (Qreals.Q2R c * PI)) q).
Proof.
intros.
unfold uc_equiv; simpl.
unfold Qreals.Q2R; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
rewrite Pos2Z.inj_mul.
rewrite plus_IZR. repeat rewrite mult_IZR. 
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
assert ((IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI + IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI)
    = ((IZR (Qnum b) * IZR (Z.pos (Qden a)) + IZR (Qnum a) * IZR (Z.pos (Qden b))) *
    / (IZR (Z.pos (Qden b)) * IZR (Z.pos (Qden a))) * PI))%R. 
field_simplify_eq. reflexivity. split.
intro contra.
assert (Z.pos (Qden a) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
intro contra.
assert (Z.pos (Qden b) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
rewrite H1. reflexivity.
assert (0 / 2 = 0)%R.
lra. rewrite H0.
rewrite cos_0. rewrite sin_0.
  autorewrite with R_db C_db.
rewrite Cmult_assoc.
rewrite <- Cexp_add.
assert ((IZR (Qnum a) * / IZR (Z.pos (Qden a)) * PI +
    (IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI + IZR (Qnum c) * / IZR (Z.pos (Qden c)) * PI))
   = ((IZR (Qnum b) * IZR (Z.pos (Qden a)) + IZR (Qnum a) * IZR (Z.pos (Qden b))) *
    / (IZR (Z.pos (Qden b)) * IZR (Z.pos (Qden a))) * PI +
    IZR (Qnum c) * / IZR (Z.pos (Qden c)) * PI))%R.
field_simplify_eq. reflexivity. split.
intro contra.
assert (Z.pos (Qden c) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
split.
intro contra.
assert (Z.pos (Qden a) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
intro contra.
assert (Z.pos (Qden b) <> 0)%Z. lia.
apply not_0_IZR in H1. rewrite contra in H1. contradiction.
rewrite H1. reflexivity. reflexivity.
Qed.

(* two u2 gates yeilds a result of U3 (180 - b' - a) (a' + 90) (b + 90). *)
Lemma two_u2_to_one: forall {dim:nat} (a b a' b':Q) (q:nat), 
     @uc_equiv dim (useq (uapp1 (@U_R (PI / 2) (Qreals.Q2R a * PI) (Qreals.Q2R b * PI)) q)
                       (uapp1 (@U_R (PI / 2) (Qreals.Q2R a' * PI) (Qreals.Q2R b' * PI)) q))
           (uapp1 (@U_R (Qreals.Q2R (1 - (b' + a)) * PI) (Qreals.Q2R (a' + 1/2) * PI) (Qreals.Q2R (b + 1/2) * PI)) q).
Proof.
intros.
unfold uc_equiv; simpl.
unfold Qreals.Q2R; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
repeat rewrite Pos2Z.inj_mul.
repeat rewrite plus_IZR. repeat rewrite mult_IZR. 
solve_matrix.
destruct (- (Qnum b' * Z.pos (Qden a) + Qnum a * Z.pos (Qden b')) * 1)%Z eqn:eq1.
repeat rewrite Pos2Z.inj_mul. rewrite mult_IZR.
Admitted.

Lemma is_Z: forall (n :Z) (a: Q), (0 < n)%Z -> 
      Qnum a mod (n * Z.pos (Qden a)) = 0%Z -> (exists (x:Z), a = inject_Z (n * x)).
Proof.
intros.
apply  Z_div_exact_full_2 in H0.
exists ((Qnum a / (4 * Z.pos (Qden a))))%Z. 
Admitted.

Lemma cos_Z: forall (a: Z), cos (IZR a * 2 * PI) = 1%R.
Proof.
intros.
Admitted.

Lemma sin_Z: forall (a: Z), sin (IZR a * 2 * PI) = 0%R.
Proof.
intros.
Admitted.


(* if a in u3 is zero then it is a u1 gate *)
Lemma u3_to_u1: forall {dim:nat} (a b c:Q) (q:nat), 
    Zmod (Qnum a) (4 * (QDen a)) = 0%Z -> 
     @uc_equiv dim (uapp1 (@U_R (Qreals.Q2R a * PI) (Qreals.Q2R b * PI) (Qreals.Q2R c * PI)) q)
           (uapp1 (@U_R 0 0 (Qreals.Q2R (b + c) * PI)) q).
Proof.
intros.
unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2.
apply f_equal2. reflexivity.
unfold rotation.
  prep_matrix_equality.
destruct x. destruct y.
apply is_Z in H. destruct H. rewrite H. 
rewrite inject_Z_mult. rewrite Qreals.Q2R_mult.
unfold inject_Z, Qreals.Q2R; simpl.
assert (0 / 2 = 0)%R by lra. rewrite H0.
rewrite cos_0.
assert (4 * / 1 * (IZR x * / 1) * PI / 2
      = (IZR x) * 2 * PI)%R by lra. 
rewrite -> H1. rewrite cos_Z. reflexivity. lia.
destruct y.
apply is_Z in H. destruct H. rewrite H. 
rewrite inject_Z_mult. rewrite Qreals.Q2R_mult.
unfold inject_Z, Qreals.Q2R; simpl.
assert (0 / 2 = 0)%R by lra. rewrite H0.
rewrite sin_0.
assert (4 * / 1 * (IZR x * / 1) * PI / 2
      = (IZR x) * 2 * PI)%R by lra. 
rewrite -> H1. rewrite sin_Z. lca. lia. reflexivity.
destruct x. destruct y.
apply is_Z in H. destruct H. rewrite H. 
rewrite inject_Z_mult. rewrite Qreals.Q2R_mult.
unfold inject_Z, Qreals.Q2R; simpl.
assert (0 / 2 = 0)%R by lra. rewrite H0.
rewrite sin_0.
assert (4 * / 1 * (IZR x * / 1) * PI / 2
      = (IZR x) * 2 * PI)%R by lra. 
rewrite -> H1. rewrite sin_Z. lca. lia.
destruct y.
apply is_Z in H. destruct H. rewrite H. 
rewrite inject_Z_mult. rewrite Qreals.Q2R_mult.
unfold inject_Z, Qreals.Q2R; simpl.
assert (0 / 2 = 0)%R by lra. rewrite H0.
rewrite cos_0.
assert (4 * / 1 * (IZR x * / 1) * PI / 2
      = (IZR x) * 2 * PI)%R by lra. 
rewrite -> H1. rewrite cos_Z.
repeat rewrite Pos2Z.inj_mul.
repeat rewrite plus_IZR. repeat rewrite mult_IZR.  
autorewrite with C_db R_db.
assert (IZR (Qnum b) * / IZR (Z.pos (Qden b)) * PI + IZR (Qnum c) * / IZR (Z.pos (Qden c)) * PI
   = (IZR (Qnum b) * IZR (Z.pos (Qden c)) + IZR (Qnum c) * IZR (Z.pos (Qden b))) *
   / (IZR (Z.pos (Qden b)) * IZR (Z.pos (Qden c))) * PI)%R.
field_simplify_eq. reflexivity. split.
intro contra.
assert (Z.pos (Qden c) <> 0)%Z. lia.
apply not_0_IZR in H2. rewrite contra in H2. contradiction.
intro contra.
assert (Z.pos (Qden b) <> 0)%Z. lia.
apply not_0_IZR in H2. rewrite contra in H2. contradiction.
rewrite H2. 
1 - 5: reflexivity.
Qed.

(* if u1's lambda is zero, then it is SKIP *)
Lemma u1_to_skip: forall {dim:nat} (a:Q) (q:nat), 
    (q < dim)%nat -> Zmod (Qnum a) (2 * (QDen a)) = 0%Z -> 
     @uc_equiv dim (uapp1 (@U_R 0 0 (Qreals.Q2R a * PI)) q) SKIP.
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
apply is_Z in H0. destruct H0. rewrite H0. 
rewrite inject_Z_mult. rewrite Qreals.Q2R_mult.
unfold inject_Z, Qreals.Q2R; simpl.
unfold Cexp.
assert ((0 + 2 * / 1 * (IZR x0 * / 1) * PI) 
    = IZR x0 * 2 * PI)%R by lra. rewrite H1.
rewrite cos_Z. rewrite sin_Z. lca. reflexivity.
reflexivity.
unfold I.
destruct ((S (S x0) =? y)%nat && (S (S x0) <? 2))%nat eqn:eq.
apply andb_true_iff in eq. destruct eq.
apply Nat.ltb_lt in H1. lia. reflexivity.
reflexivity.
destruct dim. inversion H. lia.
Qed.

