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

Module IBMGateSet <: GateSet.

(* In our optimizer we use the gate set {H, X, RzQ, CNOT} where RzQ is
   rotation about the z-axis by i * PI / (2 ^ k) for integer i. We'll 
   call this the RzQ gate set. *)

Inductive IBM_Unitary : nat -> Set := 
  | UIBM_U1 (a : R)     : IBM_Unitary 1 
  | UIBM_U2 (a b : R)   : IBM_Unitary 1 
  | UIBM_U3 (a b c : R) : IBM_Unitary 1 
  | UIBM_CNOT           : IBM_Unitary 2.
Definition U := IBM_Unitary.

Definition match_gate {n} (u u' : U n) : bool :=
  match u, u' with
  | UIBM_CNOT, UIBM_CNOT            => true
  | UIBM_U1 q, UIBM_U1 q'           => Reqb q q'
  | UIBM_U2 a b, UIBM_U2 a' b'      => (Reqb a a') && (Reqb b b')
  | UIBM_U3 a b c, UIBM_U3 a' b' c' => (Reqb a a') && (Reqb b b') && (Reqb c c')
  | _, _ => false
  end.

Definition to_base {n} (u : U n) :=
  match u with
  | UIBM_U1 a     => U_R 0 0 a
  | UIBM_U2 a b   => U_R (PI / 2) a b
  | UIBM_U3 a b c => U_R a b c
  | UIBM_CNOT     => U_CNOT
  end.

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

End IBMGateSet.
Export IBMGateSet.

Module IBMProps := UListRepresentationProps IBMGateSet.
Export IBMProps.

(* Useful shorthands. *)
Definition U1 {dim} a q := @App1 _ dim (UIBM_U1 a) q.
Definition U2 {dim} a b q := @App1 _ dim (UIBM_U2 a b) q.
Definition U3 {dim} a b c q := @App1 _ dim (UIBM_U3 a b c) q.
Definition CNOT {dim} q1 q2 := @App2 _ dim UIBM_CNOT q1 q2.
Definition IBM_ucom dim := ucom IBM_Unitary dim.
Definition IBM_ucom_l dim := gate_list IBM_Unitary dim.

(* u1 ; u1 → u1 *)
(* Technically, we could prove all of these without the q < dim condition.
   I was just feeling unmotivated to destruct on dim =? 0.
   I should write a tactic to do this... *)
Lemma combine_u1_u1: forall {dim:nat} (a a' : R) (q : nat), 
  (q < dim)%nat ->
  [@U1 dim a q] ++ [U1 a' q] =l= [U1 (a + a') q].
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db.
  2: lia.
  gridify.
  do 2 (apply f_equal2; try reflexivity).
  solve_matrix.
  all: autorewrite with R_db C_db Cexp_db trig_db; lca.
Qed.

(* u1 ; u2 → u2 *)
Lemma combine_u1_u2: forall {dim:nat} (a a' b : R) (q : nat), 
  (q < dim)%nat ->
  [@U1 dim a q] ++ [U2 a' b q] =l= [U2 a' (a + b) q].
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db.
  2: lia.
  gridify.
  do 2 (apply f_equal2; try reflexivity).
  solve_matrix.
  all: autorewrite with R_db C_db Cexp_db trig_db; lca.
Qed.

(* u2 ; u1 → u2 *)
Lemma combine_u2_u1: forall {dim:nat} (a a' b : R) (q : nat), 
  (q < dim)%nat ->
  [@U2 dim a b q] ++ [U1 a' q] =l= [U2 (a + a') b q].
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db.
  2: lia.
  gridify.
  do 2 (apply f_equal2; try reflexivity).
  solve_matrix.
  all: autorewrite with R_db C_db Cexp_db trig_db; lca.
Qed.

(* u1 ; u3 → u3 *)
Lemma combine_u1_u3: forall {dim:nat} (a a' b c : R) (q : nat), 
  (q < dim)%nat ->
  [@U1 dim a q] ++ [U3 a' b c q] =l= [U3 a' b (a + c) q].
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db.
  2: lia.
  gridify.
  do 2 (apply f_equal2; try reflexivity).
  solve_matrix.
  all: autorewrite with R_db C_db Cexp_db trig_db; lca.
Qed.

(* u3 ; u1 → u3 *)
Lemma combine_u3_u1: forall {dim:nat} (a a' b c : R) (q : nat), 
  (q < dim)%nat ->
  [@U3 dim a b c q] ++ [U1 a' q] =l= [U3 a (a' + b) c q].
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db.
  2: lia.
  gridify.
  do 2 (apply f_equal2; try reflexivity).
  solve_matrix.
  all: autorewrite with R_db C_db Cexp_db trig_db; lca.
Qed.

(* u2 ; u2 → u3 *)
Lemma combine_u2_u2: forall {dim} (a b a' b' : R) (q : nat), 
  (q < dim)%nat ->
  ([@U2 dim a b q] ++ [U2 a' b' q]) ≅l≅ ([U3 (PI - (a + b')) (a' + PI/2) (b + PI/2) q]).
Proof.
  intros.
  unfold uc_cong_l, uc_cong; simpl.
  exists ((a + b' - PI) / 2).
  autorewrite with eval_db.
  2: lia.
  gridify.
  rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
  do 2 (apply f_equal2; try reflexivity).
  solve_matrix.
  - group_Cexp. 
    replace ((a + b' - PI) / 2) with (- (PI / 2 - (a + b') / 2)) by lra.
    replace ((PI - (a + b')) / 2) with (PI / 2 - (a + b') / 2) by lra.
    unfold Cexp.
    rewrite <- cos_sym, sin_antisym.
    rewrite sin_shift, cos_shift.
    unfold Cplus, Cmult; simpl; autorewrite with R_db.
    replace (PI * / 2 * / 2) with (PI / 4) by lra.
    rewrite cos_PI4, sin_PI4.
    repeat rewrite Rmult_assoc.
    replace ((1 / √ 2) * (1 / √ 2))%R with (1 / 2)%R.
    replace (sin ((a + b') * / 2) * sin ((a + b') * / 2))
      with (1 / 2 - cos (2 * ((a + b') / 2)) / 2).
    replace (- (cos ((a + b') * / 2) * sin ((a + b') * / 2))) 
      with (- sin (2 * ((a + b') / 2)) / 2).
    replace (2 * ((a + b') / 2)) with (a + b') by lra.
    lca.
    rewrite sin_2a. lra.
    rewrite cos_2a_sin. lra.
    field_simplify_eq. rewrite pow2_sqrt. reflexivity. lra.
    nonzero.
  - group_Cexp. 
    replace ((a + b' - PI) / 2 + (b + PI / 2)) with ((a + b') / 2 + b) by lra.
    replace ((PI - (a + b')) / 2) with (PI / 2 - (a + b') / 2) by lra.
    rewrite <- 2 Cmult_assoc, (Cmult_comm (cos _)).
    rewrite <- Cmult_plus_distr_r.
    unfold Cexp.
    rewrite sin_shift.
    unfold Cplus, Cmult; simpl; autorewrite with R_db.
    replace (PI * / 2 * / 2) with (PI / 4) by lra.
    rewrite cos_PI4, sin_PI4.
    replace ((1 / √ 2) * (1 / √ 2))%R with (1 / 2)%R.
    rewrite Rplus_assoc, (Rplus_comm b b'), <- Rplus_assoc.
    rewrite 2 (cos_plus _ b).
    rewrite 2 (sin_plus _ b).
    repeat rewrite Rminus_unfold.
    repeat rewrite Rmult_plus_distr_r. 
    repeat rewrite (Rmult_comm (_ (_ * / _ + _))). 
    repeat rewrite <- Ropp_mult_distr_l.
    repeat rewrite Rmult_assoc.
    replace (cos (a * / 2 + b' * / 2) * cos (a * / 2 + b' * / 2))
      with (cos (2 * ((a + b') / 2)) / 2 + 1 / 2).
    replace (sin (a * / 2 + b' * / 2) * cos (a * / 2 + b' * / 2))
      with (sin (2 * ((a + b') / 2)) / 2).
    replace (2 * ((a + b') / 2)) with (a + b') by lra.
    lca.
    rewrite sin_2a. 
    replace (a * / 2 + b' * / 2) with ((a + b') / 2) by lra.
    lra.
    rewrite cos_2a_cos.
    replace (a * / 2 + b' * / 2) with ((a + b') / 2) by lra.
    lra.
    field_simplify_eq. rewrite pow2_sqrt. reflexivity. lra.
    nonzero.
  - group_Cexp. 
    replace ((a + b' - PI) / 2 + (a' + PI / 2)) with ((a + b') / 2 + a') by lra.
    replace ((PI - (a + b')) / 2) with (PI / 2 - (a + b') / 2) by lra.
    rewrite <- 2 Cmult_assoc, (Cmult_comm (cos _)).
    rewrite <- Cmult_plus_distr_r.
    unfold Cexp.
    rewrite sin_shift.
    unfold Cplus, Cmult; simpl; autorewrite with R_db.
    replace (PI * / 2 * / 2) with (PI / 4) by lra.
    rewrite cos_PI4, sin_PI4.
    replace ((1 / √ 2) * (1 / √ 2))%R with (1 / 2)%R.
    rewrite (Rplus_comm a' b'), <- Rplus_assoc.
    rewrite 2 (cos_plus _ a').
    rewrite 2 (sin_plus _ a').
    repeat rewrite Rminus_unfold.
    repeat rewrite Rmult_plus_distr_r. 
    repeat rewrite (Rmult_comm (_ (_ * / _ + _))). 
    repeat rewrite <- Ropp_mult_distr_l.
    repeat rewrite Rmult_assoc.
    replace (cos (a * / 2 + b' * / 2) * cos (a * / 2 + b' * / 2))
      with (cos (2 * ((a + b') / 2)) / 2 + 1 / 2).
    replace (sin (a * / 2 + b' * / 2) * cos (a * / 2 + b' * / 2))
      with (sin (2 * ((a + b') / 2)) / 2).
    replace (2 * ((a + b') / 2)) with (a + b') by lra.
    lca.
    rewrite sin_2a. 
    replace (a * / 2 + b' * / 2) with ((a + b') / 2) by lra.
    lra.
    rewrite cos_2a_cos.
    replace (a * / 2 + b' * / 2) with ((a + b') / 2) by lra.
    lra.
    field_simplify_eq. rewrite pow2_sqrt. reflexivity. lra.
    nonzero.
  - group_Cexp. 
    replace ((a + b' - PI) / 2 + (a' + PI / 2 + (b + PI / 2))) 
      with (PI / 2 + (a + b') / 2 + a' + b) by lra.
    replace ((PI - (a + b')) / 2) with (PI / 2 - (a + b') / 2) by lra.
    unfold Cexp.
    repeat rewrite Rplus_assoc.
    rewrite cos_shift, <- cos_sin. 
    replace (cos (PI / 2 + ((a + b') / 2 + (a' + b)))) 
      with (- sin ((a + b') / 2 + (a' + b))).
    unfold Cplus, Cmult; simpl; autorewrite with R_db.
    replace (PI * / 2 * / 2) with (PI / 4) by lra.
    rewrite cos_PI4, sin_PI4.
    repeat rewrite Rmult_assoc.
    replace ((1 / √ 2) * (1 / √ 2))%R with (1 / 2)%R.
    replace (a + (b + (a' + b'))) with (a + b' + (a' + b)) by lra.
    rewrite 2 (cos_plus _ (a' + b)).
    rewrite 2 (sin_plus _ (a' + b)).
    repeat rewrite Rminus_unfold.
    repeat rewrite Rmult_plus_distr_r. 
    repeat rewrite (Rmult_comm (_ (_ * / _ + _))). 
    repeat rewrite <- Ropp_mult_distr_l.
    repeat rewrite Rmult_assoc.
    replace (sin (a * / 2 + b' * / 2) * sin (a * / 2 + b' * / 2))
      with (1 / 2 - cos (2 * ((a + b') / 2)) / 2).
    replace (cos (a * / 2 + b' * / 2) * sin (a * / 2 + b' * / 2))
      with (sin (2 * ((a + b') / 2)) / 2).
    replace (2 * ((a + b') / 2)) with (a + b') by lra.
    rewrite (Rplus_comm b a'). 
    lca.
    rewrite sin_2a. 
    replace (a * / 2 + b' * / 2) with ((a + b') / 2) by lra.
    lra.
    rewrite cos_2a_sin.
    replace (a * / 2 + b' * / 2) with ((a + b') / 2) by lra.
    lra.
    field_simplify_eq. rewrite pow2_sqrt. reflexivity. lra.
    nonzero.
    rewrite sin_cos. lra.
Qed.

Lemma cos_1_implies_sin_0 : forall x, cos x = 1 -> sin x = 0.
Proof.
  intros.
  specialize (sin2_cos2 (x)) as H1. 
  rewrite H in H1.
  replace 1² with 1 in H1 by (unfold Rsqr; lra).
  assert ((sin x)² = 0) by lra.
  apply Rsqr_0_uniq in H0. 
  assumption.
Qed.

Lemma cos_1_cos_half: forall (x:R), cos x = 1 -> cos (x / 2) = 1 \/ cos (x / 2) = -1.
Proof.
  intros x Hcos.
  apply cos_1_implies_sin_0 in Hcos as Hsin. 
  replace x with (2 * (x / 2)) in Hsin by lra.
  rewrite sin_2a in Hsin.
  assert (sin (x / 2) * cos (x / 2) = 0) by lra.
  apply Rmult_integral in H.
  destruct H.
  specialize (sin2_cos2 (x / 2)) as H1.
  rewrite H in H1.
  replace 0² with 0 in H1 by (unfold Rsqr; lra).
  assert ((cos (x / 2))² = 1) by lra.
  rewrite Rsqr_pow2 in H0.
  apply pow_R1 in H0. 
  destruct H0.
  assert ((cos (x / 2)) < 0 \/ cos (x / 2) >= 0) by lra.
  destruct H2.
  apply Rabs_left in H2.
  right. lra.
  apply Rabs_right in H2.
  left. lra.
  inversion H0.
  replace x with (2 * (x / 2)) in Hcos by lra.
  rewrite cos_2a_cos in Hcos.
  rewrite H in Hcos. lra.
Qed. 

Lemma cos_1_sin_half: forall (x:R), cos x = 1 -> sin (x / 2) = 0.
Proof.
  intros x Hcos.
  apply cos_1_implies_sin_0 in Hcos as Hsin. 
  replace x with (2 * (x / 2)) in Hsin by lra.
  rewrite sin_2a in Hsin.
  assert (sin (x / 2) * cos (x / 2) = 0) by lra.
  apply Rmult_integral in H.
  destruct H.
  assumption.
  replace x with (2 * (x / 2)) in Hcos by lra.
  rewrite cos_2a_cos in Hcos.
  rewrite H in Hcos. lra.
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

(* if u3's first argument is 0 mod 2π then it's a u1 gate *)
Lemma u3_to_u1: forall {dim:nat} (a b c : R) (q : nat),
  (q < dim)%nat -> 
  cos a = 1 -> 
  [@U3 dim a b c q] ≅l≅ [U1 (b + c) q].
Proof.
  intros.
  unfold uc_cong_l, uc_cong; simpl.
  autorewrite with eval_db.
  2: lia.
  gridify.
  apply cos_1_cos_half in H0 as H.
  apply cos_1_sin_half in H0.
  destruct H.
  - exists 0.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
    do 2 (apply f_equal2; try reflexivity).
    unfold rotation.
    solve_matrix.
    all: try rewrite H0; try rewrite H.
    all: autorewrite with R_db C_db Cexp_db trig_db; auto.
  - exists PI.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
    do 2 (apply f_equal2; try reflexivity).
    unfold rotation.
    solve_matrix.
    all: try rewrite H0; try rewrite H.
    all: autorewrite with R_db C_db Cexp_db trig_db; auto.
    lca.
Qed.

(* if u3's first argument is PI/2 mod 2π then it's a u2 gate *)
Lemma u3_to_u2: forall {dim:nat} (a b c : R) (q : nat), 
  (q < dim)%nat -> 
  sin a = 1 -> 
  [@U3 dim a b c q] ≅l≅ [U2 b c q]. 
Proof.
  intros.
  unfold uc_cong_l, uc_cong; simpl.
  autorewrite with eval_db.
  2: lia.
  gridify.
  apply sin_1_half in H0.
  destruct H0 as [[? ?] | [? ?]]. 
  - exists 0.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
    do 2 (apply f_equal2; try reflexivity).
    unfold rotation.
    solve_matrix.
    all: try rewrite H0; try rewrite H.
    all: replace (PI / 2 / 2) with (PI / 4) by lra.
    all: try rewrite cos_PI4; try rewrite sin_PI4.
    all: autorewrite with R_db C_db Cexp_db trig_db; auto.
  - exists PI.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
    do 2 (apply f_equal2; try reflexivity).
    unfold rotation.
    solve_matrix.
    all: try rewrite H0; try rewrite H.
    all: replace (PI / 2 / 2) with (PI / 4) by lra.
    all: try rewrite cos_PI4; try rewrite sin_PI4.
    all: autorewrite with R_db C_db Cexp_db trig_db; lca.
Qed.

(* if u3's first argument is -PI/2 mod 2π then it's a u2 gate *)
Lemma u3_to_u2_neg: forall {dim:nat} (a b c : R) (q : nat), 
  (q < dim)%nat -> 
  sin a = -1 -> 
  [@U3 dim a b c q] ≅l≅ [U2 (b + PI) (c - PI) q].
Proof.
  intros.
  unfold uc_cong_l, uc_cong; simpl.
  autorewrite with eval_db.
  2: lia.
  gridify.
  apply sin_neg_1_half in H0.
  destruct H0 as [[? ?] | [? ?]]. 
  - exists PI.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
    do 2 (apply f_equal2; try reflexivity).
    unfold rotation.
    solve_matrix.
    all: try rewrite H0; try rewrite H.
    all: replace (PI / 2 / 2) with (PI / 4) by lra.
    all: try rewrite cos_PI4; try rewrite sin_PI4.
    all: autorewrite with R_db C_db Cexp_db trig_db; lca.
  - exists 0.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
    do 2 (apply f_equal2; try reflexivity).
    unfold rotation.
    solve_matrix.
    all: try rewrite H0; try rewrite H.
    all: replace (PI / 2 / 2) with (PI / 4) by lra.
    all: try rewrite cos_PI4; try rewrite sin_PI4.
    all: autorewrite with R_db C_db Cexp_db trig_db; lca.
Qed.

(* if u1's argument is 0 mod 2π then it's a SKIP *)
Lemma u1_to_skip: forall {dim:nat} (a : R) (q : nat), 
  (q < dim)%nat -> 
  cos a = 1 -> 
  [@U1 dim a q] =l= [].
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db.
  2: lia.
  gridify.
  do 2 (apply f_equal2; try reflexivity).
  unfold rotation.
  solve_matrix.
  all: autorewrite with R_db C_db Cexp_db trig_db; auto.
  unfold Cexp.
  rewrite H0, (cos_1_implies_sin_0 _ H0).
  lca.
Qed.

(* The code below is fairly direct translation of Qiskit's 'Quaternion' class.
   https://qiskit.org/documentation/_modules/qiskit/quantum_info/operators/quaternion.html *)
(* It appears that a Boolean comparison operator is not defined over Reals.
   I'll be asserting that such an operator exists until we come up with a
   better solution. *)
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
  2*(rx θ1 ξ θ2)*(rz θ1 ξ θ2) + 2*(ry θ1 ξ θ2)*(rw θ1 ξ θ2). 

Definition rm12 (θ1 ξ θ2 : R) : R :=
  2*(ry θ1 ξ θ2)*(rz θ1 ξ θ2) - 2*(rx θ1 ξ θ2)*(rw θ1 ξ θ2). 

Definition rm22 (θ1 ξ θ2 : R) : R :=
  1 - 2 * (rx θ1 ξ θ2) * (rx θ1 ξ θ2) - 2 * (ry θ1 ξ θ2) * (ry θ1 ξ θ2).

Definition rm10 (θ1 ξ θ2 : R) : R :=
  2*(rx θ1 ξ θ2)*(ry θ1 ξ θ2) + 2*(rz θ1 ξ θ2)*(rw θ1 ξ θ2). 

Definition rm11 (θ1 ξ θ2 : R) : R :=
  1 - 2*(rx θ1 ξ θ2)*(rx θ1 ξ θ2) - 2*(rz θ1 ξ θ2)*(rz θ1 ξ θ2). 


Definition rm20_minus (θ1 ξ θ2 : R) : R :=
  - 2*(rx θ1 ξ θ2)*(rz θ1 ξ θ2) + 2*(ry θ1 ξ θ2)*(rw θ1 ξ θ2). 

Definition rm21 (θ1 ξ θ2 : R) : R :=
  2*(ry θ1 ξ θ2)*(rz θ1 ξ θ2) + 2*(rx θ1 ξ θ2)*(rw θ1 ξ θ2). 


(* Convert a quaternion to a sequence of ZYZ Euler angles.
   We extract the formula for phi, theta and lambda directly.  *)
Definition to_zyz_theta (θ1 ξ θ2 : R) : R :=
  if rm22 θ1 ξ θ2 <? 1
    then if -1 <? rm22 θ1 ξ θ2 then acos (rm22 θ1 ξ θ2)
         else PI else 0.

Definition to_zyz_phi (θ1 ξ θ2 : R) : R :=
  if rm22 θ1 ξ θ2 <? 1
    then if -1 <? rm22 θ1 ξ θ2 then atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2)
         else - atan2 (rm10 θ1 ξ θ2) (rm11 θ1 ξ θ2) else atan2 (rm10 θ1 ξ θ2) (rm11 θ1 ξ θ2).

Definition to_zyz_lambda (θ1 ξ θ2 : R) : R :=
  if rm22 θ1 ξ θ2 <? 1
    then if -1 <? rm22 θ1 ξ θ2 then atan2 (rm21 θ1 ξ θ2) (rm20_minus θ1 ξ θ2)
         else 0 else 0.

Lemma yzy_to_zyz_correct_1 : forall {dim} θ1 ξ θ2 q,
  (q < dim)%nat ->
  sin (θ1/2) = 0 -> cos (θ2/2) = 0 ->
  @Ry dim θ1 q ; Rz ξ q ; Ry θ2 q ≅
          Rz (to_zyz_phi θ1 ξ θ2) q ; Ry (to_zyz_theta θ1 ξ θ2) q ; Rz (to_zyz_lambda θ1 ξ θ2) q.
Proof.
intros.
assert (cos (θ1 / 2) * cos (θ1 / 2) = 1).
specialize (sin2_cos2 (θ1 / 2)) as eq1.
rewrite H0 in eq1. unfold Rsqr in eq1. lra.
assert (sin (θ2 / 2) * sin (θ2 / 2) = 1).
specialize (sin2_cos2 (θ2 / 2)) as eq1.
rewrite H1 in eq1. unfold Rsqr in eq1. lra.
assert (rw θ1 ξ θ2 = 0).
unfold rw. rewrite H0. rewrite H1.
lra.
assert (rz θ1 ξ θ2 = 0).
unfold rz. rewrite H0. rewrite H1.
lra.
assert (rm22 θ1 ξ θ2 = -1).
unfold rm22,rx,ry. rewrite H0. rewrite H1.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((2 * (sin (ξ * / 2) * (cos (θ1 * / 2) * sin (θ2 * / 2))) *
 (sin (ξ * / 2) * (cos (θ1 * / 2) * sin (θ2 * / 2))))
   = (2 * (Rsqr (sin (ξ / 2)))
       * (cos (θ1 / 2) * cos (θ1 / 2))
       * (sin (θ2 / 2) * sin (θ2 / 2)))).
unfold Rsqr. lra.
rewrite H6.
assert ((2 * (cos (ξ * / 2) * (cos (θ1 * / 2) * sin (θ2 * / 2))) *
 (cos (ξ * / 2) * (cos (θ1 * / 2) * sin (θ2 * / 2))))
   = (2 * (Rsqr (cos (ξ / 2)))
       * (cos (θ1 / 2) * cos (θ1 / 2))
       * (sin (θ2 / 2) * sin (θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7.
rewrite H2. rewrite H3.
assert (1 + - (2 * (sin (ξ / 2))² * 1 * 1) + - (2 * (cos (ξ / 2))² * 1 * 1)
     = 1 - 2 * ((sin (ξ / 2))² + (cos (ξ / 2))²)) by lra.
rewrite H8.
rewrite sin2_cos2.
lra.
unfold to_zyz_theta,to_zyz_phi,to_zyz_lambda.
destruct (rm22 θ1 ξ θ2 <? 1) eqn:eq1.
destruct (-1 <? rm22 θ1 ξ θ2) eqn:eq2.
apply Rltb_lt in eq2.
rewrite H6 in eq2. lra.
-
apply Rltb_le_false in eq2.
assert (rm11 θ1 ξ θ2 = cos ξ).
unfold rm11. rewrite H5.
unfold rx. rewrite H0. rewrite H1.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((2 * (sin (ξ * / 2) * (cos (θ1 * / 2) * sin (θ2 * / 2))) *
 (sin (ξ * / 2) * (cos (θ1 * / 2) * sin (θ2 * / 2))))
 = (2 * (sin (ξ / 2) * sin (ξ / 2)) * (cos (θ1 / 2) * cos (θ1 / 2)) *
      (sin (θ2 / 2) * sin (θ2 / 2)))) by lra.
rewrite H7. rewrite H2. rewrite H3.
assert (1 + - (2 * (sin (ξ / 2) * sin (ξ / 2)) * 1 * 1)
   = 1 - 2 * sin (ξ / 2) * sin (ξ / 2)) by lra.
rewrite H8. rewrite <- cos_2a_sin. 
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H9. reflexivity.
assert (rm10 θ1 ξ θ2 = - sin ξ).
unfold rm10. rewrite H5.
unfold rx,ry. rewrite H0. rewrite H1.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((2 * (sin (ξ * / 2) * (cos (θ1 * / 2) * sin (θ2 * / 2))) *
 (cos (ξ * / 2) * (cos (θ1 * / 2) * sin (θ2 * / 2))))
 = ((2 * (sin (ξ / 2) * cos (ξ / 2)) * (cos (θ1 / 2) * cos (θ1 / 2)) *
      (sin (θ2 / 2) * sin (θ2 / 2))))) by lra.
rewrite H8. rewrite H2. rewrite H3.
assert (- (2 * (sin (ξ / 2) * cos (ξ / 2)) * 1 * 1)
   = - (2 * sin (ξ / 2) * cos (ξ / 2))) by lra.
rewrite H9. rewrite <- sin_2a. 
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H10. reflexivity.
rewrite H7. rewrite H8.
unfold atan2.
destruct (0 <? cos ξ) eqn:eq3.
assert ((- sin ξ / cos ξ) = - tan ξ).
unfold tan. lra. rewrite H9. clear H9.
assert (Rsqr (cos (θ1 / 2)) = Rsqr 1).
unfold Rsqr; lra.
assert (Rsqr (sin (θ2 / 2)) = Rsqr 1).
unfold Rsqr; lra.
apply Rsqr_eq in H9. apply Rsqr_eq in H10.
destruct H9. destruct H10.
{
rewrite atan_opp.
assert ((- - atan (tan ξ)) = atan (tan ξ)) by lra.
rewrite H11. clear H11.
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
unfold Cexp.
apply Rltb_lt in eq3.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite tan_atan. reflexivity.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
{
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- (0 * 0 + (- (1))%R * (Cexp ξ * 1)))%C
   = Cexp ξ) by lca.
rewrite H. clear H.
rewrite atan_opp.
assert (- - atan (tan ξ) = atan (tan ξ)) by lra.
rewrite H. clear H.
assert ((- (-1 * (1 * Cexp (atan (tan ξ)))))%C
   = Cexp (atan (tan ξ))) by lca.
rewrite H. clear H.
unfold Cexp.
apply Rltb_lt in eq3.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite tan_atan. reflexivity.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca. 
}

destruct H10.
{
rewrite atan_opp.
assert ((- - atan (tan ξ)) = atan (tan ξ)) by lra.
rewrite H11. clear H11.
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((- (Cexp ξ * (- (1))%R))%C
   = Cexp ξ) by lca.
rewrite H. clear H.
assert ((- (-1 * Cexp (atan (tan ξ))))%C
   = Cexp (atan (tan ξ))) by lca.
rewrite H. clear H.
unfold Cexp.
apply Rltb_lt in eq3.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite tan_atan. reflexivity.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
{
rewrite atan_opp.
assert ((- - atan (tan ξ)) = atan (tan ξ)) by lra.
rewrite H11. clear H11.
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
unfold Cexp.
apply Rltb_lt in eq3.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite tan_atan. lca.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}

destruct (cos ξ <? 0) eqn:eq4.
apply Rltb_lt in eq4.
destruct (0 <=? - sin ξ) eqn:eq5.
assert ((- sin ξ / cos ξ) = - tan ξ).
unfold tan. lra. rewrite H9. clear H9.
assert (Rsqr (cos (θ1 / 2)) = Rsqr 1).
unfold Rsqr; lra.
assert (Rsqr (sin (θ2 / 2)) = Rsqr 1).
unfold Rsqr; lra.
apply Rsqr_eq in H9. apply Rsqr_eq in H10.
destruct H9. destruct H10.
{
rewrite atan_opp.
assert ((- (- atan (tan ξ) + PI)) = atan (tan ξ) - PI) by lra.
rewrite H11. clear H11.
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- RtoC_inv.
assert ((/ -1)%R = -1) by lra.
rewrite H. clear H.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((- (Cexp (atan (tan ξ)) * -1))%C
   = Cexp (atan (tan ξ))%C) by lca.
rewrite H. clear H.
unfold Cexp.
assert (0 < cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus.
lra.
assert (cos ξ = - cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus. lra.
rewrite H12. clear H12.
assert (sin ξ = - sin (PI + ξ)).
rewrite Rtrigo_facts.sin_pi_plus. lra.
rewrite H12. clear H12.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan. lca.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption. lra.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
{
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- (0 * 0 + (- (1))%R * (Cexp ξ * 1)))%C = (Cexp ξ)%C) by lca.
rewrite H. clear H.
rewrite atan_opp.
assert ((- (- atan (tan ξ) + PI)) = atan (tan ξ) - PI) by lra.
rewrite H. clear H.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((-1 * (Cexp (atan (tan ξ)) * / -1))%C = (Cexp (atan (tan ξ)) * (-1 * / -1))%C) by lca.
rewrite H. clear H.
rewrite Cinv_r.
unfold Cexp.
assert (0 < cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus.
lra.
assert (cos ξ = - cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus. lra.
rewrite H12. clear H12.
assert (sin ξ = - sin (PI + ξ)).
rewrite Rtrigo_facts.sin_pi_plus. lra.
rewrite H12. clear H12.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan. lca.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
intros R.
apply RtoC_inj in R. lra.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
destruct H10.
{
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- (0 * 0 + 1 * (Cexp ξ * (- (1))%R)))%C = (Cexp ξ)%C) by lca.
rewrite H. clear H.
rewrite atan_opp.
assert ((- (- atan (tan ξ) + PI)) = atan (tan ξ) - PI) by lra.
rewrite H. clear H.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((-1 * (Cexp (atan (tan ξ)) * / -1))%C = (Cexp (atan (tan ξ)) * (-1 * / -1))%C) by lca.
rewrite H. clear H.
rewrite Cinv_r.
unfold Cexp.
assert (0 < cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus.
lra.
assert (cos ξ = - cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus. lra.
rewrite H12. clear H12.
assert (sin ξ = - sin (PI + ξ)).
rewrite Rtrigo_facts.sin_pi_plus. lra.
rewrite H12. clear H12.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan. lca.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
intros R.
apply RtoC_inj in R. lra.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
{
rewrite atan_opp.
assert ((- (- atan (tan ξ) + PI)) = atan (tan ξ) - PI) by lra.
rewrite H11. clear H11.
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- RtoC_inv.
assert ((/ -1)%R = -1) by lra.
rewrite H. clear H.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((- (Cexp (atan (tan ξ)) * -1))%C
   = Cexp (atan (tan ξ))%C) by lca.
rewrite H. clear H.
unfold Cexp.
assert (0 < cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus.
lra.
assert (cos ξ = - cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus. lra.
rewrite H12. clear H12.
assert (sin ξ = - sin (PI + ξ)).
rewrite Rtrigo_facts.sin_pi_plus. lra.
rewrite H12. clear H12.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan. lca.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption. lra.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
assert ((- sin ξ / cos ξ) = - tan ξ).
unfold tan. lra. rewrite H9. clear H9.
assert (Rsqr (cos (θ1 / 2)) = Rsqr 1).
unfold Rsqr; lra.
assert (Rsqr (sin (θ2 / 2)) = Rsqr 1).
unfold Rsqr; lra.
apply Rsqr_eq in H9. apply Rsqr_eq in H10.
destruct H9. destruct H10.
{
rewrite atan_opp.
assert ((- (- atan (tan ξ) - PI)) = atan (tan ξ) + PI) by lra.
rewrite H11. clear H11.
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((- (Cexp (atan (tan ξ)) * -1))%C
   = Cexp (atan (tan ξ))%C) by lca.
rewrite H. clear H.
unfold Cexp.
assert (0 < cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus.
lra.
assert (cos ξ = - cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus. lra.
rewrite H12. clear H12.
assert (sin ξ = - sin (PI + ξ)).
rewrite Rtrigo_facts.sin_pi_plus. lra.
rewrite H12. clear H12.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan. lca.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra. assumption.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
{
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- (0 * 0 + (- (1))%R * (Cexp ξ * 1)))%C = (Cexp ξ)%C) by lca.
rewrite H. clear H.
rewrite atan_opp.
assert ((- (- atan (tan ξ) - PI)) = atan (tan ξ) + PI) by lra.
rewrite H. clear H.
 autorewrite with R_db C_db Cexp_db trig_db.
unfold Cexp.
assert (0 < cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus.
lra.
assert (cos ξ = - cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus. lra.
rewrite H12. clear H12.
assert (sin ξ = - sin (PI + ξ)).
rewrite Rtrigo_facts.sin_pi_plus. lra.
rewrite H12. clear H12.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan. lca.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
destruct H10.
{
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- (0 * 0 + 1 * (Cexp ξ * (- (1))%R)))%C = (Cexp ξ)%C) by lca.
rewrite H. clear H.
rewrite atan_opp.
assert ((- (- atan (tan ξ) - PI)) = atan (tan ξ) + PI) by lra.
rewrite H. clear H.
 autorewrite with R_db C_db Cexp_db trig_db.
unfold Cexp.
assert (0 < cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus.
lra.
assert (cos ξ = - cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus. lra.
rewrite H12. clear H12.
assert (sin ξ = - sin (PI + ξ)).
rewrite Rtrigo_facts.sin_pi_plus. lra.
rewrite H12. clear H12.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan. lca.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
{
rewrite atan_opp.
assert ((- (- atan (tan ξ) - PI)) = atan (tan ξ) + PI) by lra.
rewrite H11. clear H11.
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
unfold Cexp.
assert (0 < cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus.
lra.
assert (cos ξ = - cos (PI + ξ)).
rewrite Rtrigo_facts.cos_pi_plus. lra.
rewrite H12. clear H12.
assert (sin ξ = - sin (PI + ξ)).
rewrite Rtrigo_facts.sin_pi_plus. lra.
rewrite H12. clear H12.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan. lca.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
specialize (Rle_0_sqr (tan ξ)) as R1.
lra.
assumption.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
apply Rltb_le_false in eq3.
apply Rltb_le_false in eq4.
specialize (Rle_antisym (cos ξ) 0 eq3 eq4) as eq5.
destruct (0 <? - sin ξ) eqn:eq6.
assert (Rsqr (cos (θ1 / 2)) = Rsqr 1).
unfold Rsqr; lra.
assert (Rsqr (sin (θ2 / 2)) = Rsqr 1).
unfold Rsqr; lra.
apply Rsqr_eq in H9. apply Rsqr_eq in H10.
assert (sin ξ = -1). 
apply Rltb_lt in eq6.
assert (sin ξ < 0) by lra.
specialize (sin2_cos2 ξ) as H12.
rewrite eq5 in H12.
assert ((sin ξ)² = Rsqr 1). unfold Rsqr. unfold Rsqr in H12. lra.
apply Rsqr_eq in H13.
destruct H13. lra.
assumption.
destruct H9. destruct H10.
{
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite  sin_neg.
rewrite cos_neg.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
{
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite  sin_neg.
rewrite cos_neg.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
destruct H10.
{
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite  sin_neg.
rewrite cos_neg.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
{
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite  sin_neg.
rewrite cos_neg.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
destruct (- sin ξ <? 0) eqn:eq7.
apply Rltb_lt in eq7.
assert (0 < sin ξ) as eq8 by lra.
assert (Rsqr (cos (θ1 / 2)) = Rsqr 1).
unfold Rsqr; lra.
assert (Rsqr (sin (θ2 / 2)) = Rsqr 1).
unfold Rsqr; lra.
apply Rsqr_eq in H9. apply Rsqr_eq in H10.
assert (sin ξ = 1). 
specialize (sin2_cos2 ξ) as H12.
rewrite eq5 in H12.
assert ((sin ξ)² = Rsqr 1). unfold Rsqr. unfold Rsqr in H12. lra.
apply Rsqr_eq in H11.
destruct H11. assumption.
lra.
destruct H9. destruct H10.
{
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite sin_neg.
rewrite Ropp_div.
rewrite sin_neg.
rewrite cos_neg.
rewrite cos_neg.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
{
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite sin_neg.
rewrite Ropp_div.
rewrite sin_neg.
rewrite cos_neg.
rewrite cos_neg.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
destruct H10.
{
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite sin_neg.
rewrite Ropp_div.
rewrite sin_neg.
rewrite cos_neg.
rewrite cos_neg.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
{
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite sin_neg.
rewrite Ropp_div.
rewrite sin_neg.
rewrite cos_neg.
rewrite cos_neg.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
apply Rltb_le_false in eq6.
apply Rltb_le_false in eq7.
assert (sin ξ = 0) by lra.
specialize (sin2_cos2 ξ) as R.
rewrite eq5 in R. rewrite H9 in R.
unfold Rsqr in R. lra.
-
apply Rltb_le_false in eq1.
lra.
Qed.

Lemma yzy_to_zyz_correct_2 : forall {dim} θ1 ξ θ2 q,
  (q < dim)%nat ->
  cos (θ1/2) = 0 -> sin (θ2/2) = 0 ->
  @Ry dim θ1 q ; Rz ξ q ; Ry θ2 q ≅
          Rz (to_zyz_phi θ1 ξ θ2) q ; Ry (to_zyz_theta θ1 ξ θ2) q ; Rz (to_zyz_lambda θ1 ξ θ2) q.
Proof.
intros.
assert (cos (θ2 / 2) * cos (θ2 / 2) = 1).
specialize (sin2_cos2 (θ2 / 2)) as eq1.
rewrite H1 in eq1. unfold Rsqr in eq1. lra.
assert (sin (θ1 / 2) * sin (θ1 / 2) = 1).
specialize (sin2_cos2 (θ1 / 2)) as eq1.
rewrite H0 in eq1. unfold Rsqr in eq1. lra.
assert (rw θ1 ξ θ2 = 0).
unfold rw. rewrite H0. rewrite H1.
lra.
assert (rz θ1 ξ θ2 = 0).
unfold rz. rewrite H0. rewrite H1.
lra.
assert (rm22 θ1 ξ θ2 = -1).
unfold rm22,rx,ry. rewrite H0. rewrite H1.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((2 * (sin (ξ * / 2) * (sin (θ1 * / 2) * cos (θ2 * / 2))) *
 (sin (ξ * / 2) * (sin (θ1 * / 2) * cos (θ2 * / 2))))
   = (2 * (Rsqr (sin (ξ / 2)))
       * (sin (θ1 / 2) * sin (θ1 / 2))
       * (cos (θ2 / 2) * cos (θ2 / 2)))).
unfold Rsqr. lra.
rewrite H6.
assert ((2 * (cos (ξ * / 2) * (sin (θ1 * / 2) * cos (θ2 * / 2))) *
 (cos (ξ * / 2) * (sin (θ1 * / 2) * cos (θ2 * / 2))))
   = (2 * (Rsqr (cos (ξ / 2)))
       * (sin (θ1 / 2) * sin (θ1 / 2))
       * (cos (θ2 / 2) * cos (θ2 / 2)))).
unfold Rsqr. lra.
rewrite H7.
rewrite H2. rewrite H3.
assert (1 + - (2 * (sin (ξ / 2))² * 1 * 1) + - (2 * (cos (ξ / 2))² * 1 * 1)
     = 1 - 2 * ((sin (ξ / 2))² + (cos (ξ / 2))²)) by lra.
rewrite H8.
rewrite sin2_cos2.
lra.
unfold to_zyz_theta,to_zyz_phi,to_zyz_lambda.
destruct (rm22 θ1 ξ θ2 <? 1) eqn:eq1.
destruct (-1 <? rm22 θ1 ξ θ2) eqn:eq2.
apply Rltb_lt in eq2.
rewrite H6 in eq2. lra.
-
assert (rm11 θ1 ξ θ2 = cos ξ).
unfold rm11. rewrite H5.
unfold rx. rewrite H0. rewrite H1.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((2 * (sin (ξ * / 2) * (sin (θ1 * / 2) * cos (θ2 * / 2))) *
 (sin (ξ * / 2) * (sin (θ1 * / 2) * cos (θ2 * / 2))))
 = (2 * (sin (ξ / 2) * sin (ξ / 2)) * (sin (θ1 / 2) * sin (θ1 / 2)) *
      (cos (θ2 / 2) * cos (θ2 / 2)))) by lra.
rewrite H7. rewrite H2. rewrite H3.
assert (1 + - (2 * (sin (ξ / 2) * sin (ξ / 2)) * 1 * 1)
   = 1 - 2 * sin (ξ / 2) * sin (ξ / 2)) by lra.
rewrite H8. rewrite <- cos_2a_sin. 
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H9. reflexivity.
assert (rm10 θ1 ξ θ2 = sin ξ).
unfold rm10. rewrite H5.
unfold rx,ry. rewrite H0. rewrite H1.
 autorewrite with R_db C_db Cexp_db trig_db.
assert ((2 * (sin (ξ * / 2) * (sin (θ1 * / 2) * cos (θ2 * / 2))) *
 (cos (ξ * / 2) * (sin (θ1 * / 2) * cos (θ2 * / 2))))
 = ((2 * (sin (ξ / 2) * cos (ξ / 2)) * (sin (θ1 / 2) * sin (θ1 / 2)) *
      (cos (θ2 / 2) * cos (θ2 / 2))))) by lra.
rewrite H8. rewrite H2. rewrite H3.
assert ((2 * (sin (ξ / 2) * cos (ξ / 2)) * 1 * 1)
   = (2 * sin (ξ / 2) * cos (ξ / 2))) by lra.
rewrite H9. rewrite <- sin_2a. 
assert (2 * (ξ / 2) = ξ) by lra.
rewrite H10. reflexivity.
rewrite H7. rewrite H8.
unfold atan2.
destruct (0 <? cos ξ) eqn:eq3.
assert ((sin ξ / cos ξ) = tan ξ).
unfold tan. lra. rewrite H9. clear H9.
assert (Rsqr (cos (θ2 / 2)) = Rsqr 1).
unfold Rsqr; lra.
assert (Rsqr (sin (θ1 / 2)) = Rsqr 1).
unfold Rsqr; lra.
apply Rsqr_eq in H9. apply Rsqr_eq in H10.
destruct H9. destruct H10.
{
  unfold uc_cong; simpl.
exists ξ.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- (1 * 1 + 0 * (Cexp ξ * 0)))%C = - 1) by lca.
rewrite H. clear H.
assert ((- (Cexp ξ * (1 * Cexp (- atan (tan ξ)))))%C = (- (Cexp ξ * Cexp (- atan (tan ξ))))%C) by lca.
rewrite H. clear H.
unfold Cexp.
apply Rltb_lt in eq3.
rewrite cos_neg, sin_neg.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite tan_atan.
unfold Cmult. simpl.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- sqrt_inv.
rewrite sqrt_sqrt.
assert (tan ξ * √ (/ (1 + (tan ξ)²)) * (tan ξ * √ (/ (1 + (tan ξ)²)))
    = (tan ξ * tan ξ) * (√ (/ (1 + (tan ξ)²)) * √ (/ (1 + (tan ξ)²)))) by lra.
rewrite H. clear H.
rewrite sqrt_sqrt.
assert ((/ (1 + (tan ξ)²) + tan ξ * tan ξ * / (1 + (tan ξ)²))%R
         = ((1 + (tan ξ)²) * / (1 + (tan ξ)²))%R).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite Rinv_r. lca.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
{
  unfold uc_cong; simpl.
exists (ξ+PI).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- (1 * (- (1))%R + 0 * (Cexp ξ * 0)))%C = 1%C) by lca.
rewrite H. clear H.
assert ((- (Cexp (ξ + PI) * (1 * Cexp (- atan (tan ξ)))))%C = (Cexp ξ * Cexp (- atan (tan ξ)))%C).
 autorewrite with R_db C_db Cexp_db trig_db. lca.
rewrite H. clear H.
unfold Cexp.
apply Rltb_lt in eq3.
rewrite cos_neg, sin_neg.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite tan_atan.
unfold Cmult. simpl.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- sqrt_inv.
rewrite sqrt_sqrt.
assert (tan ξ * √ (/ (1 + (tan ξ)²)) * (tan ξ * √ (/ (1 + (tan ξ)²)))
    = (tan ξ * tan ξ) * (√ (/ (1 + (tan ξ)²)) * √ (/ (1 + (tan ξ)²)))) by lra.
rewrite H. clear H.
rewrite sqrt_sqrt.
assert ((/ (1 + (tan ξ)²) + tan ξ * tan ξ * / (1 + (tan ξ)²))%R
         = ((1 + (tan ξ)²) * / (1 + (tan ξ)²))%R).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite Rinv_r. lca.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
destruct H10.
{
  unfold uc_cong; simpl.
exists (ξ+PI).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- ((- (1))%R * 1 + 0 * (Cexp ξ * 0)))%C = 1%C) by lca.
rewrite H. clear H.
assert ((- (Cexp (ξ + PI) * (1 * Cexp (- atan (tan ξ)))))%C = (Cexp ξ * Cexp (- atan (tan ξ)))%C).
 autorewrite with R_db C_db Cexp_db trig_db. lca.
rewrite H. clear H.
unfold Cexp.
apply Rltb_lt in eq3.
rewrite cos_neg, sin_neg.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite tan_atan.
unfold Cmult. simpl.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- sqrt_inv.
rewrite sqrt_sqrt.
assert (tan ξ * √ (/ (1 + (tan ξ)²)) * (tan ξ * √ (/ (1 + (tan ξ)²)))
    = (tan ξ * tan ξ) * (√ (/ (1 + (tan ξ)²)) * √ (/ (1 + (tan ξ)²)))) by lra.
rewrite H. clear H.
rewrite sqrt_sqrt.
assert ((/ (1 + (tan ξ)²) + tan ξ * tan ξ * / (1 + (tan ξ)²))%R
         = ((1 + (tan ξ)²) * / (1 + (tan ξ)²))%R).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite Rinv_r. lca.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
{
  unfold uc_cong; simpl.
exists ξ.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- ((- (1))%R * (- (1))%R + 0 * (Cexp ξ * 0)))%C = - 1) by lca.
rewrite H. clear H.
assert ((- (Cexp ξ * (1 * Cexp (- atan (tan ξ)))))%C = (- (Cexp ξ * Cexp (- atan (tan ξ))))%C) by lca.
rewrite H. clear H.
unfold Cexp.
apply Rltb_lt in eq3.
rewrite cos_neg, sin_neg.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite tan_atan.
unfold Cmult. simpl.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- sqrt_inv.
rewrite sqrt_sqrt.
assert (tan ξ * √ (/ (1 + (tan ξ)²)) * (tan ξ * √ (/ (1 + (tan ξ)²)))
    = (tan ξ * tan ξ) * (√ (/ (1 + (tan ξ)²)) * √ (/ (1 + (tan ξ)²)))) by lra.
rewrite H. clear H.
rewrite sqrt_sqrt.
assert ((/ (1 + (tan ξ)²) + tan ξ * tan ξ * / (1 + (tan ξ)²))%R
         = ((1 + (tan ξ)²) * / (1 + (tan ξ)²))%R).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite Rinv_r. lca.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
apply eq3.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
destruct (cos ξ <? 0) eqn:eq4.
apply Rltb_lt in eq4.
destruct (0 <=? sin ξ) eqn:eq5.
assert ((sin ξ / cos ξ) = tan ξ).
unfold tan. lra. rewrite H9. clear H9.
assert (Rsqr (cos (θ2 / 2)) = Rsqr 1).
unfold Rsqr; lra.
assert (Rsqr (sin (θ1 / 2)) = Rsqr 1).
unfold Rsqr; lra.
apply Rsqr_eq in H9. apply Rsqr_eq in H10.
destruct H9. destruct H10.
{
  unfold uc_cong; simpl.
exists ξ.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- (1 * 1 + 0 * (Cexp ξ * 0)))%C = (-1)%C) by lca.
rewrite H. clear H.
assert ((- (Cexp ξ * (1 * Cexp (- (atan (tan ξ) + PI)))))%C
        = (- (Cexp (PI + ξ) * Cexp (- atan (tan ξ))))%C).
 autorewrite with R_db C_db Cexp_db trig_db. lca.
rewrite H. clear H.
unfold Cexp.
assert (0 < cos (PI + ξ)) as eq6.
rewrite Rtrigo_facts.cos_pi_plus.
lra.
rewrite cos_neg, sin_neg.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan.
unfold Cmult. simpl.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- sqrt_inv.
rewrite sqrt_sqrt.
assert (tan ξ * √ (/ (1 + (tan ξ)²)) * (tan ξ * √ (/ (1 + (tan ξ)²)))
    = (tan ξ * tan ξ) * (√ (/ (1 + (tan ξ)²)) * √ (/ (1 + (tan ξ)²)))) by lra.
rewrite H. clear H.
rewrite sqrt_sqrt.
assert ((/ (1 + (tan ξ)²) + tan ξ * tan ξ * / (1 + (tan ξ)²))%R
         = ((1 + (tan ξ)²) * / (1 + (tan ξ)²))%R).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite Rinv_r. lca.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
{
  unfold uc_cong; simpl.
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- (1 * (- (1))%R + 0 * (Cexp ξ * 0)))%C  = 1%C) by lca.
rewrite H. clear H.
assert ((- (Cexp (PI + ξ) * (1 * Cexp (- (atan (tan ξ) + PI)))))%C
        = (Cexp (PI + ξ) * Cexp (- atan (tan ξ)))%C).
 autorewrite with R_db C_db Cexp_db trig_db. lca.
rewrite H. clear H.
unfold Cexp.
assert (0 < cos (PI + ξ)) as eq6.
rewrite Rtrigo_facts.cos_pi_plus.
lra.
rewrite cos_neg, sin_neg.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan.
unfold Cmult. simpl.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- sqrt_inv.
rewrite sqrt_sqrt.
assert (tan ξ * √ (/ (1 + (tan ξ)²)) * (tan ξ * √ (/ (1 + (tan ξ)²)))
    = (tan ξ * tan ξ) * (√ (/ (1 + (tan ξ)²)) * √ (/ (1 + (tan ξ)²)))) by lra.
rewrite H. clear H.
rewrite sqrt_sqrt.
assert ((/ (1 + (tan ξ)²) + tan ξ * tan ξ * / (1 + (tan ξ)²))%R
         = ((1 + (tan ξ)²) * / (1 + (tan ξ)²))%R).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite Rinv_r. lca.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
destruct H10.
{
  unfold uc_cong; simpl.
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- ((- (1))%R * 1 + 0 * (Cexp ξ * 0)))%C  = 1%C) by lca.
rewrite H. clear H.
assert ((- (Cexp (PI + ξ) * (1 * Cexp (- (atan (tan ξ) + PI)))))%C
        = (Cexp (PI + ξ) * Cexp (- atan (tan ξ)))%C).
 autorewrite with R_db C_db Cexp_db trig_db. lca.
rewrite H. clear H.
unfold Cexp.
assert (0 < cos (PI + ξ)) as eq6.
rewrite Rtrigo_facts.cos_pi_plus.
lra.
rewrite cos_neg, sin_neg.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan.
unfold Cmult. simpl.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- sqrt_inv.
rewrite sqrt_sqrt.
assert (tan ξ * √ (/ (1 + (tan ξ)²)) * (tan ξ * √ (/ (1 + (tan ξ)²)))
    = (tan ξ * tan ξ) * (√ (/ (1 + (tan ξ)²)) * √ (/ (1 + (tan ξ)²)))) by lra.
rewrite H. clear H.
rewrite sqrt_sqrt.
assert ((/ (1 + (tan ξ)²) + tan ξ * tan ξ * / (1 + (tan ξ)²))%R
         = ((1 + (tan ξ)²) * / (1 + (tan ξ)²))%R).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite Rinv_r. lca.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
{
  unfold uc_cong; simpl.
exists ξ.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- ((- (1))%R * (- (1))%R + 0 * (Cexp ξ * 0)))%C = (-1)%C) by lca.
rewrite H. clear H.
assert ((- (Cexp ξ * (1 * Cexp (- (atan (tan ξ) + PI)))))%C
        = (-(Cexp (PI + ξ) * Cexp (- atan (tan ξ))))%C).
 autorewrite with R_db C_db Cexp_db trig_db. lca.
rewrite H. clear H.
unfold Cexp.
assert (0 < cos (PI + ξ)) as eq6.
rewrite Rtrigo_facts.cos_pi_plus.
lra.
rewrite cos_neg, sin_neg.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan.
unfold Cmult. simpl.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- sqrt_inv.
rewrite sqrt_sqrt.
assert (tan ξ * √ (/ (1 + (tan ξ)²)) * (tan ξ * √ (/ (1 + (tan ξ)²)))
    = (tan ξ * tan ξ) * (√ (/ (1 + (tan ξ)²)) * √ (/ (1 + (tan ξ)²)))) by lra.
rewrite H. clear H.
rewrite sqrt_sqrt.
assert ((/ (1 + (tan ξ)²) + tan ξ * tan ξ * / (1 + (tan ξ)²))%R
         = ((1 + (tan ξ)²) * / (1 + (tan ξ)²))%R).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite Rinv_r. lca.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
assert ((sin ξ / cos ξ) = tan ξ).
unfold tan. lra. rewrite H9. clear H9.
assert (Rsqr (cos (θ2 / 2)) = Rsqr 1).
unfold Rsqr; lra.
assert (Rsqr (sin (θ1 / 2)) = Rsqr 1).
unfold Rsqr; lra.
assert (- (atan (tan ξ) - PI) = (- atan (tan ξ)) + PI) by lra.
rewrite H11. clear H11.
apply Rsqr_eq in H9. apply Rsqr_eq in H10.
destruct H9. destruct H10.
{
  unfold uc_cong; simpl.
exists ξ.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- (1 * 1 + 0 * (Cexp ξ * 0)))%C = (-1)%C) by lca.
rewrite H. clear H.
assert ((- (Cexp ξ * (1 * Cexp (- atan (tan ξ) + PI))))%C
        = (-(Cexp (PI + ξ) * Cexp (- atan (tan ξ))))%C).
 autorewrite with R_db C_db Cexp_db trig_db. lca.
rewrite H. clear H.
unfold Cexp.
assert (0 < cos (PI + ξ)) as eq6.
rewrite Rtrigo_facts.cos_pi_plus.
lra.
rewrite cos_neg, sin_neg.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan.
unfold Cmult. simpl.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- sqrt_inv.
rewrite sqrt_sqrt.
assert (tan ξ * √ (/ (1 + (tan ξ)²)) * (tan ξ * √ (/ (1 + (tan ξ)²)))
    = (tan ξ * tan ξ) * (√ (/ (1 + (tan ξ)²)) * √ (/ (1 + (tan ξ)²)))) by lra.
rewrite H. clear H.
rewrite sqrt_sqrt.
assert ((/ (1 + (tan ξ)²) + tan ξ * tan ξ * / (1 + (tan ξ)²))%R
         = ((1 + (tan ξ)²) * / (1 + (tan ξ)²))%R).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite Rinv_r. lca.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
{
  unfold uc_cong; simpl.
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- (1 * (- (1))%R + 0 * (Cexp ξ * 0)))%C = 1%C) by lca.
rewrite H. clear H.
assert ((- (Cexp (PI + ξ) * (1 * Cexp (- atan (tan ξ) + PI))))%C
        = (Cexp (PI + ξ) * Cexp (- atan (tan ξ)))%C).
 autorewrite with R_db C_db Cexp_db trig_db. lca.
rewrite H. clear H.
unfold Cexp.
assert (0 < cos (PI + ξ)) as eq6.
rewrite Rtrigo_facts.cos_pi_plus.
lra.
rewrite cos_neg, sin_neg.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan.
unfold Cmult. simpl.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- sqrt_inv.
rewrite sqrt_sqrt.
assert (tan ξ * √ (/ (1 + (tan ξ)²)) * (tan ξ * √ (/ (1 + (tan ξ)²)))
    = (tan ξ * tan ξ) * (√ (/ (1 + (tan ξ)²)) * √ (/ (1 + (tan ξ)²)))) by lra.
rewrite H. clear H.
rewrite sqrt_sqrt.
assert ((/ (1 + (tan ξ)²) + tan ξ * tan ξ * / (1 + (tan ξ)²))%R
         = ((1 + (tan ξ)²) * / (1 + (tan ξ)²))%R).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite Rinv_r. lca.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
destruct H10.
{
  unfold uc_cong; simpl.
exists (PI + ξ).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- ((- (1))%R * 1 + 0 * (Cexp ξ * 0)))%C = 1%C) by lca.
rewrite H. clear H.
assert ((- (Cexp (PI + ξ) * (1 * Cexp (- atan (tan ξ) + PI))))%C
        = (Cexp (PI + ξ) * Cexp (- atan (tan ξ)))%C).
 autorewrite with R_db C_db Cexp_db trig_db. lca.
rewrite H. clear H.
unfold Cexp.
assert (0 < cos (PI + ξ)) as eq6.
rewrite Rtrigo_facts.cos_pi_plus.
lra.
rewrite cos_neg, sin_neg.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan.
unfold Cmult. simpl.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- sqrt_inv.
rewrite sqrt_sqrt.
assert (tan ξ * √ (/ (1 + (tan ξ)²)) * (tan ξ * √ (/ (1 + (tan ξ)²)))
    = (tan ξ * tan ξ) * (√ (/ (1 + (tan ξ)²)) * √ (/ (1 + (tan ξ)²)))) by lra.
rewrite H. clear H.
rewrite sqrt_sqrt.
assert ((/ (1 + (tan ξ)²) + tan ξ * tan ξ * / (1 + (tan ξ)²))%R
         = ((1 + (tan ξ)²) * / (1 + (tan ξ)²))%R).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite Rinv_r. lca.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
{
  unfold uc_cong; simpl.
exists ξ.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2.
assert ((- ((- (1))%R * (- (1))%R + 0 * (Cexp ξ * 0)))%C = (-1)%C) by lca.
rewrite H. clear H.
assert ((- (Cexp ξ * (1 * Cexp (- atan (tan ξ) + PI))))%C
        = (-(Cexp (PI + ξ) * Cexp (- atan (tan ξ))))%C).
 autorewrite with R_db C_db Cexp_db trig_db. lca.
rewrite H. clear H.
unfold Cexp.
assert (0 < cos (PI + ξ)) as eq6.
rewrite Rtrigo_facts.cos_pi_plus.
lra.
rewrite cos_neg, sin_neg.
rewrite 2 Rtrigo_facts.sin_tan.
rewrite 2 Rtrigo_facts.cos_tan.
rewrite Rtrigo_facts.tan_pi_plus.
rewrite tan_atan.
unfold Cmult. simpl.
 autorewrite with R_db C_db Cexp_db trig_db.
rewrite <- sqrt_inv.
rewrite sqrt_sqrt.
assert (tan ξ * √ (/ (1 + (tan ξ)²)) * (tan ξ * √ (/ (1 + (tan ξ)²)))
    = (tan ξ * tan ξ) * (√ (/ (1 + (tan ξ)²)) * √ (/ (1 + (tan ξ)²)))) by lra.
rewrite H. clear H.
rewrite sqrt_sqrt.
assert ((/ (1 + (tan ξ)²) + tan ξ * tan ξ * / (1 + (tan ξ)²))%R
         = ((1 + (tan ξ)²) * / (1 + (tan ξ)²))%R).
unfold Rsqr. lra.
rewrite H. clear H.
rewrite Rinv_r. lca.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
assert (0 < (1 + (tan ξ)²)).
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
apply Rinv_0_lt_compat in H. lra.
specialize (Rle_0_sqr (tan ξ))as R1.
lra.
lra.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite cos_atan.
 autorewrite with R_db.
apply  Rinv_0_lt_compat.
assert (√ (1 + (tan ξ)²) <> 0).
intros R.
apply sqrt_eq_0 in R. 
apply  Rplus_opp_r_uniq in R.
specialize (Rle_0_sqr (tan ξ))as R1.
rewrite R in R1. lra.
apply Rplus_le_le_0_compat. lra.
apply Rle_0_sqr.
specialize (sqrt_pos (1 + (tan ξ)²)) as R.
lra.
assumption.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite sin_PI2.
 autorewrite with R_db C_db Cexp_db trig_db.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite Cexp_0. rewrite cos_PI2.
lca.
}
apply Rltb_le_false in eq3.
apply Rltb_le_false in eq4.
specialize (Rle_antisym (cos ξ) 0 eq3 eq4) as eq5.
destruct (0 <? sin ξ) eqn:eq6.
assert (Rsqr (cos (θ2 / 2)) = Rsqr 1).
unfold Rsqr; lra.
assert (Rsqr (sin (θ1 / 2)) = Rsqr 1).
unfold Rsqr; lra.
apply Rsqr_eq in H9. apply Rsqr_eq in H10.
assert (sin ξ = 1). 
apply Rltb_lt in eq6.
specialize (sin2_cos2 ξ) as H12.
rewrite eq5 in H12.
assert ((sin ξ)² = Rsqr 1). unfold Rsqr. unfold Rsqr in H12. lra.
apply Rsqr_eq in H11.
destruct H11. lra. lra.
destruct H9. destruct H10.
{
  unfold uc_cong; simpl.
exists (PI / 2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite  sin_neg.
rewrite cos_neg.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
unfold Cexp.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
{
  unfold uc_cong; simpl.
exists (PI + PI / 2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite  sin_neg.
rewrite cos_neg.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
destruct H10.
{
  unfold uc_cong; simpl.
exists (PI + PI / 2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite  sin_neg.
rewrite cos_neg.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
{
  unfold uc_cong; simpl.
exists (PI / 2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite  sin_neg.
rewrite cos_neg.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
unfold Cexp.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
destruct (sin ξ <? 0) eqn:eq7.
apply Rltb_lt in eq7.
assert (Rsqr (cos (θ2 / 2)) = Rsqr 1).
unfold Rsqr; lra.
assert (Rsqr (sin (θ1 / 2)) = Rsqr 1).
unfold Rsqr; lra.
apply Rsqr_eq in H9. apply Rsqr_eq in H10.
assert (sin ξ = -1). 
specialize (sin2_cos2 ξ) as H12.
rewrite eq5 in H12.
assert ((sin ξ)² = Rsqr 1). unfold Rsqr. unfold Rsqr in H12. lra.
apply Rsqr_eq in H11.
destruct H11. lra.
assumption.
assert ((- (- PI / 2)) = PI / 2) by lra.
rewrite H12. clear H12.
destruct H9. destruct H10.
{
  unfold uc_cong; simpl.
exists (PI + PI / 2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
{
  unfold uc_cong; simpl.
exists (PI / 2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
unfold Cexp.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
destruct H10.
{
  unfold uc_cong; simpl.
exists (PI / 2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
unfold Cexp.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
{
  unfold uc_cong; simpl.
exists (PI + PI / 2).
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
rewrite H0. rewrite H1.
rewrite cos_PI2. lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite sin_PI2. rewrite Cexp_0.
unfold Cexp.
rewrite Rtrigo_facts.sin_pi_plus.
rewrite Rtrigo_facts.cos_pi_plus.
rewrite cos_PI2.
rewrite sin_PI2.
rewrite eq5. rewrite H11.
lca.
rewrite H0. rewrite H1.
rewrite H9. rewrite H10.
rewrite cos_PI2. rewrite Cexp_0.
lca.
}
apply Rltb_le_false in eq6.
apply Rltb_le_false in eq7.
assert (sin ξ = 0) by lra.
specialize (sin2_cos2 ξ) as R.
rewrite eq5 in R. rewrite H9 in R.
unfold Rsqr in R. lra.
-
apply Rltb_le_false in eq1.
lra.
Qed.

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
 

Lemma yzy_to_zyz_correct_3 : forall {dim} θ1 ξ θ2 q,
  (q < dim)%nat ->
  cos ξ = 1 -> cos (θ1 / 2 + θ2 /2) = 0 ->
  @Ry dim θ1 q ; Rz ξ q ; Ry θ2 q ≅
          Rz (to_zyz_phi θ1 ξ θ2) q ; Ry (to_zyz_theta θ1 ξ θ2) q ; Rz (to_zyz_lambda θ1 ξ θ2) q.
Proof.
intros.
specialize (cos_1_sin ξ H0) as H2.
specialize (cos_1_half_cos ξ H0) as H3.
specialize (cos_1_half_sin ξ H0) as H4.
specialize (cos_0_sin (θ1 / 2 + θ2 / 2) H1) as H5.
assert (rm22 θ1 ξ θ2 = -1).
unfold rm22.
unfold rx. rewrite H4. 
unfold ry. rewrite <- sin_plus.
destruct H3. destruct H5.
rewrite H5. rewrite H3. lra.
rewrite H5. rewrite H3. lra.
destruct H5.
rewrite H5. rewrite H3. lra.
rewrite H5. rewrite H3. lra.
destruct H3. destruct H5.
-
unfold to_zyz_phi,to_zyz_theta,to_zyz_lambda.
destruct (rm22 θ1 ξ θ2 <? 1) eqn:eq1.
destruct (-1 <? rm22 θ1 ξ θ2) eqn:eq2.
apply Rltb_lt in eq2. lra.
assert (rm10 θ1 ξ θ2 = 0).
unfold rm10. unfold rx,rz.
rewrite H4. lra.
assert (rm11 θ1 ξ θ2 = 1).
unfold rm11. unfold rx,rz.
rewrite H4. lra.
rewrite H7. rewrite H8.
unfold atan2. destruct (0 <? 1) eqn:eq3.
assert(0 / 1 = 0) by lra.
rewrite H9. clear H9.
rewrite atan_0.
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
unfold Cexp. rewrite H0. rewrite H2.
assert ((cos (θ2 / 2) * cos (θ1 / 2) + - (sin (θ2 / 2) * ((1, 0) * sin (θ1 / 2))))%C
  = ((cos (θ1 / 2) * cos (θ2 / 2) - (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_plus. rewrite H1.
rewrite cos_PI2. reflexivity.
assert (- 0 = 0) by lra. rewrite H. clear H.
rewrite Cexp_0.
unfold Cexp. rewrite H0. rewrite H2.
assert ((- (cos (θ2 / 2) * sin (θ1 / 2) + sin (θ2 / 2) * ((1, 0) * cos (θ1 / 2))))%C
  = (-(sin (θ1 / 2) * cos (θ2 / 2) + (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_plus. rewrite H5.
rewrite sin_PI2. lca.
rewrite Cexp_0.
unfold Cexp. rewrite H0. rewrite H2.
assert ((sin (θ2 / 2) * cos (θ1 / 2) + cos (θ2 / 2) * ((1, 0) * sin (θ1 / 2)))%C
        = ((sin (θ1 / 2) * cos (θ2 / 2) + (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_plus.
rewrite H5. rewrite sin_PI2. lca.
assert (- 0 = 0) by lra. rewrite H. clear H.
rewrite Cexp_0.
unfold Cexp.
rewrite H0. rewrite H2.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) + cos (θ2 / 2) * ((1, 0) * cos (θ1 / 2)))%C
   = ((cos (θ1 / 2) * cos (θ2 / 2) - (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_plus.
rewrite H1. rewrite cos_PI2. lca.
apply Rltb_le_false in eq3. lra.
apply Rltb_le_false in eq1. lra.
-
unfold to_zyz_phi,to_zyz_theta,to_zyz_lambda.
destruct (rm22 θ1 ξ θ2 <? 1) eqn:eq1.
destruct (-1 <? rm22 θ1 ξ θ2) eqn:eq2.
apply Rltb_lt in eq2. lra.
assert (rm10 θ1 ξ θ2 = 0).
unfold rm10. unfold rx,rz.
rewrite H4. lra.
assert (rm11 θ1 ξ θ2 = 1).
unfold rm11. unfold rx,rz.
rewrite H4. lra.
rewrite H7. rewrite H8.
unfold atan2. destruct (0 <? 1) eqn:eq3.
assert(0 / 1 = 0) by lra.
rewrite H9. clear H9.
rewrite atan_0.
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
unfold Cexp. rewrite H0. rewrite H2.
assert ((cos (θ2 / 2) * cos (θ1 / 2) + - (sin (θ2 / 2) * ((1, 0) * sin (θ1 / 2))))%C
  = ((cos (θ1 / 2) * cos (θ2 / 2) - (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_plus. rewrite H1.
rewrite cos_PI2. lca.
assert (- 0 = 0) by lra. rewrite H. clear H.
rewrite Cexp_0.
unfold Cexp. rewrite H0. rewrite H2.
assert ((- (cos (θ2 / 2) * sin (θ1 / 2) + sin (θ2 / 2) * ((1, 0) * cos (θ1 / 2))))%C
  = (-(sin (θ1 / 2) * cos (θ2 / 2) + (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_plus. rewrite H5.
rewrite sin_PI2. lca.
rewrite Cexp_0.
unfold Cexp. rewrite H0. rewrite H2.
assert ((sin (θ2 / 2) * cos (θ1 / 2) + cos (θ2 / 2) * ((1, 0) * sin (θ1 / 2)))%C
        = ((sin (θ1 / 2) * cos (θ2 / 2) + (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_plus.
rewrite H5. rewrite sin_PI2. lca.
assert (- 0 = 0) by lra. rewrite H. clear H.
rewrite Cexp_0.
unfold Cexp.
rewrite H0. rewrite H2.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) + cos (θ2 / 2) * ((1, 0) * cos (θ1 / 2)))%C
   = ((cos (θ1 / 2) * cos (θ2 / 2) - (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_plus.
rewrite H1. rewrite cos_PI2. lca.
apply Rltb_le_false in eq3. lra.
apply Rltb_le_false in eq1. lra.
-
destruct H5.
unfold to_zyz_phi,to_zyz_theta,to_zyz_lambda.
destruct (rm22 θ1 ξ θ2 <? 1) eqn:eq1.
destruct (-1 <? rm22 θ1 ξ θ2) eqn:eq2.
apply Rltb_lt in eq2. lra.
assert (rm10 θ1 ξ θ2 = 0).
unfold rm10. unfold rx,rz.
rewrite H4. lra.
assert (rm11 θ1 ξ θ2 = 1).
unfold rm11. unfold rx,rz.
rewrite H4. lra.
rewrite H7. rewrite H8.
unfold atan2. destruct (0 <? 1) eqn:eq3.
assert(0 / 1 = 0) by lra.
rewrite H9. clear H9.
rewrite atan_0.
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
unfold Cexp. rewrite H0. rewrite H2.
assert ((cos (θ2 / 2) * cos (θ1 / 2) + - (sin (θ2 / 2) * ((1, 0) * sin (θ1 / 2))))%C
  = ((cos (θ1 / 2) * cos (θ2 / 2) - (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_plus. rewrite H1.
rewrite cos_PI2. lca.
assert (- 0 = 0) by lra. rewrite H. clear H.
rewrite Cexp_0.
unfold Cexp. rewrite H0. rewrite H2.
assert ((- (cos (θ2 / 2) * sin (θ1 / 2) + sin (θ2 / 2) * ((1, 0) * cos (θ1 / 2))))%C
  = (-(sin (θ1 / 2) * cos (θ2 / 2) + (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_plus. rewrite H5.
rewrite sin_PI2. lca.
rewrite Cexp_0.
unfold Cexp. rewrite H0. rewrite H2.
assert ((sin (θ2 / 2) * cos (θ1 / 2) + cos (θ2 / 2) * ((1, 0) * sin (θ1 / 2)))%C
        = ((sin (θ1 / 2) * cos (θ2 / 2) + (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_plus.
rewrite H5. rewrite sin_PI2. lca.
assert (- 0 = 0) by lra. rewrite H. clear H.
rewrite Cexp_0.
unfold Cexp.
rewrite H0. rewrite H2.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) + cos (θ2 / 2) * ((1, 0) * cos (θ1 / 2)))%C
   = ((cos (θ1 / 2) * cos (θ2 / 2) - (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_plus.
rewrite H1. rewrite cos_PI2. lca.
apply Rltb_le_false in eq3. lra.
apply Rltb_le_false in eq1. lra.
unfold to_zyz_phi,to_zyz_theta,to_zyz_lambda.
destruct (rm22 θ1 ξ θ2 <? 1) eqn:eq1.
destruct (-1 <? rm22 θ1 ξ θ2) eqn:eq2.
apply Rltb_lt in eq2. lra.
assert (rm10 θ1 ξ θ2 = 0).
unfold rm10. unfold rx,rz.
rewrite H4. lra.
assert (rm11 θ1 ξ θ2 = 1).
unfold rm11. unfold rx,rz.
rewrite H4. lra.
rewrite H7. rewrite H8.
unfold atan2. destruct (0 <? 1) eqn:eq3.
assert(0 / 1 = 0) by lra.
rewrite H9. clear H9.
rewrite atan_0.
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
unfold Cexp. rewrite H0. rewrite H2.
assert ((cos (θ2 / 2) * cos (θ1 / 2) + - (sin (θ2 / 2) * ((1, 0) * sin (θ1 / 2))))%C
  = ((cos (θ1 / 2) * cos (θ2 / 2) - (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_plus. rewrite H1.
rewrite cos_PI2. lca.
assert (- 0 = 0) by lra. rewrite H. clear H.
rewrite Cexp_0.
unfold Cexp. rewrite H0. rewrite H2.
assert ((- (cos (θ2 / 2) * sin (θ1 / 2) + sin (θ2 / 2) * ((1, 0) * cos (θ1 / 2))))%C
  = (-(sin (θ1 / 2) * cos (θ2 / 2) + (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_plus. rewrite H5.
rewrite sin_PI2. lca.
rewrite Cexp_0.
unfold Cexp. rewrite H0. rewrite H2.
assert ((sin (θ2 / 2) * cos (θ1 / 2) + cos (θ2 / 2) * ((1, 0) * sin (θ1 / 2)))%C
        = ((sin (θ1 / 2) * cos (θ2 / 2) + (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_plus.
rewrite H5. rewrite sin_PI2. lca.
assert (- 0 = 0) by lra. rewrite H. clear H.
rewrite Cexp_0.
unfold Cexp.
rewrite H0. rewrite H2.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) + cos (θ2 / 2) * ((1, 0) * cos (θ1 / 2)))%C
   = ((cos (θ1 / 2) * cos (θ2 / 2) - (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_plus.
rewrite H1. rewrite cos_PI2. lca.
apply Rltb_le_false in eq3. lra.
apply Rltb_le_false in eq1. lra.
Qed.


Lemma yzy_to_zyz_correct_4 : forall {dim} θ1 ξ θ2 q,
  (q < dim)%nat ->
  cos ξ = -1 -> cos (θ1 / 2 - θ2 /2) = 0 ->
  @Ry dim θ1 q ; Rz ξ q ; Ry θ2 q ≅
          Rz (to_zyz_phi θ1 ξ θ2) q ; Ry (to_zyz_theta θ1 ξ θ2) q ; Rz (to_zyz_lambda θ1 ξ θ2) q.
Proof.
intros.
specialize (cos_neg_1_sin ξ H0) as H2.
specialize (cos_neg_1_half_cos ξ H0) as H3.
specialize (cos_neg_1_half_sin ξ H0) as H4.
specialize (cos_0_sin (θ1 / 2 - θ2 / 2) H1) as H5.
assert (rm22 θ1 ξ θ2 = -1).
unfold rm22.
unfold ry. rewrite H3. 
unfold rx. rewrite <- sin_minus.
destruct H4. destruct H5.
rewrite H5. rewrite H4. lra.
rewrite H5. rewrite H4. lra.
destruct H5.
rewrite H5. rewrite H4. lra.
rewrite H5. rewrite H4. lra.
destruct H4. destruct H5.
-
unfold to_zyz_phi,to_zyz_theta,to_zyz_lambda.
destruct (rm22 θ1 ξ θ2 <? 1) eqn:eq1.
destruct (-1 <? rm22 θ1 ξ θ2) eqn:eq2.
apply Rltb_lt in eq2. lra.
assert (rm10 θ1 ξ θ2 = 0).
unfold rm10. unfold rw,ry.
rewrite H3. lra.
assert (rm11 θ1 ξ θ2 = -1).
unfold rm11. unfold rx,rz.
rewrite H4. 
rewrite <- sin_minus.
rewrite <- cos_minus.
rewrite H1. rewrite H5.
lra.
rewrite H7. rewrite H8.
unfold atan2. destruct (0 <? -1) eqn:eq3.
apply Rltb_lt in eq3. lra.
destruct (-1 <? 0) eqn:eq4.
destruct (0 <=? 0) eqn:eq5.
assert(0 / -1 = 0) by lra.
rewrite H9. clear H9.
rewrite atan_0.
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
unfold Cexp. rewrite H0. rewrite H2.
assert ((cos (θ2 / 2) * cos (θ1 / 2) + - (sin (θ2 / 2) * ((-1, 0) * sin (θ1 / 2))))%C
  = ((cos (θ1 / 2) * cos (θ2 / 2) + (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_minus. rewrite H1.
rewrite cos_PI2. lca.
assert (- (0 + PI) = - PI) by lra. rewrite H. clear H.
rewrite Cexp_neg. rewrite Cexp_PI.
unfold Cexp. rewrite H0. rewrite H2.
assert ((- (cos (θ2 / 2) * sin (θ1 / 2) + sin (θ2 / 2) * ((-1, 0) * cos (θ1 / 2))))%C
  = (-(sin (θ1 / 2) * cos (θ2 / 2) - (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_minus. rewrite H5.
rewrite sin_PI2. lca.
rewrite Cexp_0.
unfold Cexp. rewrite H0. rewrite H2.
assert ((sin (θ2 / 2) * cos (θ1 / 2) + cos (θ2 / 2) * ((-1, 0) * sin (θ1 / 2)))%C
        = (-(sin (θ1 / 2) * cos (θ2 / 2) - (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_minus.
rewrite H5. rewrite sin_PI2. lca.
assert (- (0 + PI) = - PI) by lra. rewrite H. clear H.
rewrite Cexp_neg. rewrite Cexp_PI.
unfold Cexp.
rewrite H0. rewrite H2.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) + cos (θ2 / 2) * ((-1, 0) * cos (θ1 / 2)))%C
   = (-(cos (θ1 / 2) * cos (θ2 / 2) + (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_minus.
rewrite H1. rewrite cos_PI2. lca.
apply Rleb_lt_false in eq5. lra.
apply Rltb_le_false in eq4. lra.
apply Rltb_le_false in eq1. lra.
-
unfold to_zyz_phi,to_zyz_theta,to_zyz_lambda.
destruct (rm22 θ1 ξ θ2 <? 1) eqn:eq1.
destruct (-1 <? rm22 θ1 ξ θ2) eqn:eq2.
apply Rltb_lt in eq2. lra.
assert (rm10 θ1 ξ θ2 = 0).
unfold rm10. unfold rw,ry.
rewrite H3. lra.
assert (rm11 θ1 ξ θ2 = -1).
unfold rm11. unfold rx,rz.
rewrite H4. 
rewrite <- sin_minus.
rewrite <- cos_minus.
rewrite H1. rewrite H5.
lra.
rewrite H7. rewrite H8.
unfold atan2. destruct (0 <? -1) eqn:eq3.
apply Rltb_lt in eq3. lra.
destruct (-1 <? 0) eqn:eq4.
destruct (0 <=? 0) eqn:eq5.
assert(0 / -1 = 0) by lra.
rewrite H9. clear H9.
rewrite atan_0.
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
unfold Cexp. rewrite H0. rewrite H2.
assert ((cos (θ2 / 2) * cos (θ1 / 2) + - (sin (θ2 / 2) * ((-1, 0) * sin (θ1 / 2))))%C
  = ((cos (θ1 / 2) * cos (θ2 / 2) + (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_minus. rewrite H1.
rewrite cos_PI2. lca.
assert (- (0 + PI) = - PI) by lra. rewrite H. clear H.
rewrite Cexp_neg. rewrite Cexp_PI.
unfold Cexp. rewrite H0. rewrite H2.
assert ((- (cos (θ2 / 2) * sin (θ1 / 2) + sin (θ2 / 2) * ((-1, 0) * cos (θ1 / 2))))%C
  = (-(sin (θ1 / 2) * cos (θ2 / 2) - (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_minus. rewrite H5.
rewrite sin_PI2. lca.
rewrite Cexp_0.
unfold Cexp. rewrite H0. rewrite H2.
assert ((sin (θ2 / 2) * cos (θ1 / 2) + cos (θ2 / 2) * ((-1, 0) * sin (θ1 / 2)))%C
        = (-(sin (θ1 / 2) * cos (θ2 / 2) - (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_minus.
rewrite H5. rewrite sin_PI2. lca.
assert (- (0 + PI) = - PI) by lra. rewrite H. clear H.
rewrite Cexp_neg. rewrite Cexp_PI.
unfold Cexp.
rewrite H0. rewrite H2.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) + cos (θ2 / 2) * ((-1, 0) * cos (θ1 / 2)))%C
   = (-(cos (θ1 / 2) * cos (θ2 / 2) + (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_minus.
rewrite H1. rewrite cos_PI2. lca.
apply Rleb_lt_false in eq5. lra.
apply Rltb_le_false in eq4. lra.
apply Rltb_le_false in eq1. lra.
-
destruct H5.
unfold to_zyz_phi,to_zyz_theta,to_zyz_lambda.
destruct (rm22 θ1 ξ θ2 <? 1) eqn:eq1.
destruct (-1 <? rm22 θ1 ξ θ2) eqn:eq2.
apply Rltb_lt in eq2. lra.
assert (rm10 θ1 ξ θ2 = 0).
unfold rm10. unfold rw,ry.
rewrite H3. lra.
assert (rm11 θ1 ξ θ2 = -1).
unfold rm11. unfold rx,rz.
rewrite H4. 
rewrite <- sin_minus.
rewrite <- cos_minus.
rewrite H1. rewrite H5.
lra.
rewrite H7. rewrite H8.
unfold atan2. destruct (0 <? -1) eqn:eq3.
apply Rltb_lt in eq3. lra.
destruct (-1 <? 0) eqn:eq4.
destruct (0 <=? 0) eqn:eq5.
assert(0 / -1 = 0) by lra.
rewrite H9. clear H9.
rewrite atan_0.
  unfold uc_cong; simpl.
exists PI.
rewrite Cexp_PI.
  autorewrite with eval_db.
  gridify.
    rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
unfold Cexp. rewrite H0. rewrite H2.
assert ((cos (θ2 / 2) * cos (θ1 / 2) + - (sin (θ2 / 2) * ((-1, 0) * sin (θ1 / 2))))%C
  = ((cos (θ1 / 2) * cos (θ2 / 2) + (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_minus. rewrite H1.
rewrite cos_PI2. lca.
assert (- (0 + PI) = - PI) by lra. rewrite H. clear H.
rewrite Cexp_neg. rewrite Cexp_PI.
unfold Cexp. rewrite H0. rewrite H2.
assert ((- (cos (θ2 / 2) * sin (θ1 / 2) + sin (θ2 / 2) * ((-1, 0) * cos (θ1 / 2))))%C
  = (-(sin (θ1 / 2) * cos (θ2 / 2) - (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_minus. rewrite H5.
rewrite sin_PI2. lca.
rewrite Cexp_0.
unfold Cexp. rewrite H0. rewrite H2.
assert ((sin (θ2 / 2) * cos (θ1 / 2) + cos (θ2 / 2) * ((-1, 0) * sin (θ1 / 2)))%C
        = (-(sin (θ1 / 2) * cos (θ2 / 2) - (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_minus.
rewrite H5. rewrite sin_PI2. lca.
assert (- (0 + PI) = - PI) by lra. rewrite H. clear H.
rewrite Cexp_neg. rewrite Cexp_PI.
unfold Cexp.
rewrite H0. rewrite H2.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) + cos (θ2 / 2) * ((-1, 0) * cos (θ1 / 2)))%C
   = (-(cos (θ1 / 2) * cos (θ2 / 2) + (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_minus.
rewrite H1. rewrite cos_PI2. lca.
apply Rleb_lt_false in eq5. lra.
apply Rltb_le_false in eq4. lra.
apply Rltb_le_false in eq1. lra.
unfold to_zyz_phi,to_zyz_theta,to_zyz_lambda.
destruct (rm22 θ1 ξ θ2 <? 1) eqn:eq1.
destruct (-1 <? rm22 θ1 ξ θ2) eqn:eq2.
apply Rltb_lt in eq2. lra.
assert (rm10 θ1 ξ θ2 = 0).
unfold rm10. unfold rw,ry.
rewrite H3. lra.
assert (rm11 θ1 ξ θ2 = -1).
unfold rm11. unfold rx,rz.
rewrite H4. 
rewrite <- sin_minus.
rewrite <- cos_minus.
rewrite H1. rewrite H5.
lra.
rewrite H7. rewrite H8.
unfold atan2. destruct (0 <? -1) eqn:eq3.
apply Rltb_lt in eq3. lra.
destruct (-1 <? 0) eqn:eq4.
destruct (0 <=? 0) eqn:eq5.
assert(0 / -1 = 0) by lra.
rewrite H9. clear H9.
rewrite atan_0.
  unfold uc_cong; simpl.
exists 0.
rewrite Cexp_0.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
solve_matrix.
unfold Cexp. rewrite H0. rewrite H2.
assert ((cos (θ2 / 2) * cos (θ1 / 2) + - (sin (θ2 / 2) * ((-1, 0) * sin (θ1 / 2))))%C
  = ((cos (θ1 / 2) * cos (θ2 / 2) + (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_minus. rewrite H1.
rewrite cos_PI2. lca.
assert (- (0 + PI) = - PI) by lra. rewrite H. clear H.
rewrite Cexp_neg. rewrite Cexp_PI.
unfold Cexp. rewrite H0. rewrite H2.
assert ((- (cos (θ2 / 2) * sin (θ1 / 2) + sin (θ2 / 2) * ((-1, 0) * cos (θ1 / 2))))%C
  = (-(sin (θ1 / 2) * cos (θ2 / 2) - (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_minus. rewrite H5.
rewrite sin_PI2. lca.
rewrite Cexp_0.
unfold Cexp. rewrite H0. rewrite H2.
assert ((sin (θ2 / 2) * cos (θ1 / 2) + cos (θ2 / 2) * ((-1, 0) * sin (θ1 / 2)))%C
        = (-(sin (θ1 / 2) * cos (θ2 / 2) - (cos (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- sin_minus.
rewrite H5. rewrite sin_PI2. lca.
assert (- (0 + PI) = - PI) by lra. rewrite H. clear H.
rewrite Cexp_neg. rewrite Cexp_PI.
unfold Cexp.
rewrite H0. rewrite H2.
assert ((- (sin (θ2 / 2) * sin (θ1 / 2)) + cos (θ2 / 2) * ((-1, 0) * cos (θ1 / 2)))%C
   = (-(cos (θ1 / 2) * cos (θ2 / 2) + (sin (θ1 / 2) * sin (θ2 / 2)))%R)%C) by lca.
rewrite H. clear H.
rewrite <- cos_minus.
rewrite H1. rewrite cos_PI2. lca.
apply Rleb_lt_false in eq5. lra.
apply Rltb_le_false in eq4. lra.
apply Rltb_le_false in eq1. lra.
Qed.

Lemma sqr_bound: forall (x y:R), Rsqr x + Rsqr y = 1 -> ((-1 <= x <= 1) /\ (-1 <= y <= 1)).
Proof.
intros.
split.
assert (Rsqr x <= 1).
assert (0 <= Rsqr x).
apply Rle_0_sqr.
assert (0 <= Rsqr y). 
apply Rle_0_sqr. lra.
split.
assert ( 1 = Rsqr 1).
unfold Rsqr. lra.
rewrite H1 in H0.
apply Rsqr_neg_pos_le_0 in H0.
assumption. lra.
assert ( 1 = Rsqr 1).
unfold Rsqr. lra.
rewrite H1 in H0.
apply Rsqr_incr_0_var in H0.
assumption. lra.
assert (Rsqr y <= 1).
assert (0 <= Rsqr y).
apply Rle_0_sqr.
assert (0 <= Rsqr x). 
apply Rle_0_sqr. lra.
split.
assert ( 1 = Rsqr 1).
unfold Rsqr. lra.
rewrite H1 in H0.
apply Rsqr_neg_pos_le_0 in H0.
assumption. lra.
assert ( 1 = Rsqr 1).
unfold Rsqr. lra.
rewrite H1 in H0.
apply Rsqr_incr_0_var in H0.
assumption. lra.
Qed.

Lemma sqr_4_bound_1: forall (x y u v:R), Rsqr x + Rsqr y + Rsqr u + Rsqr v = 1 
 -> -1 <= x <= 1.
Proof.
intros.
assert (Rsqr x <= 1).
assert (0 <= Rsqr x).
apply Rle_0_sqr.
assert (0 <= Rsqr y). 
apply Rle_0_sqr.
assert (0 <= Rsqr u). 
apply Rle_0_sqr.
assert (0 <= Rsqr v). 
apply Rle_0_sqr.
lra.
assert ( 1 = Rsqr 1).
unfold Rsqr. lra.
rewrite H1 in H0.
split.
apply Rsqr_neg_pos_le_0 in H0.
assumption. lra.
apply Rsqr_incr_0_var in H0.
assumption. lra.
Qed.

Lemma sqr_4_bound_2: forall (x y u v:R), Rsqr x + Rsqr y + Rsqr u + Rsqr v = 1 
 -> -1 <= y <= 1.
Proof.
intros.
assert (Rsqr y <= 1).
assert (0 <= Rsqr x).
apply Rle_0_sqr.
assert (0 <= Rsqr y). 
apply Rle_0_sqr.
assert (0 <= Rsqr u). 
apply Rle_0_sqr.
assert (0 <= Rsqr v). 
apply Rle_0_sqr.
lra.
assert ( 1 = Rsqr 1).
unfold Rsqr. lra.
rewrite H1 in H0.
split.
apply Rsqr_neg_pos_le_0 in H0.
assumption. lra.
apply Rsqr_incr_0_var in H0.
assumption. lra.
Qed.

Lemma sqr_4_bound_3: forall (x y u v:R), Rsqr x + Rsqr y + Rsqr u + Rsqr v = 1 
 -> -1 <= u <= 1.
Proof.
intros.
assert (Rsqr u <= 1).
assert (0 <= Rsqr x).
apply Rle_0_sqr.
assert (0 <= Rsqr y). 
apply Rle_0_sqr.
assert (0 <= Rsqr u). 
apply Rle_0_sqr.
assert (0 <= Rsqr v). 
apply Rle_0_sqr.
lra.
assert ( 1 = Rsqr 1).
unfold Rsqr. lra.
rewrite H1 in H0.
split.
apply Rsqr_neg_pos_le_0 in H0.
assumption. lra.
apply Rsqr_incr_0_var in H0.
assumption. lra.
Qed.

Lemma sqr_4_bound_4: forall (x y u v:R), Rsqr x + Rsqr y + Rsqr u + Rsqr v = 1 
 -> -1 <= v <= 1.
Proof.
intros.
assert (Rsqr v <= 1).
assert (0 <= Rsqr x).
apply Rle_0_sqr.
assert (0 <= Rsqr y). 
apply Rle_0_sqr.
assert (0 <= Rsqr u). 
apply Rle_0_sqr.
assert (0 <= Rsqr v). 
apply Rle_0_sqr.
lra.
assert ( 1 = Rsqr 1).
unfold Rsqr. lra.
rewrite H1 in H0.
split.
apply Rsqr_neg_pos_le_0 in H0.
assumption. lra.
apply Rsqr_incr_0_var in H0.
assumption. lra.
Qed.

Lemma sqr_angle_four_1 : forall (x y z: R),
   (Rsqr (sin x)) * (Rsqr (sin y)) + (Rsqr (sin x)) * (Rsqr (cos y))
   + (Rsqr (cos x)) * (Rsqr (sin z)) + (Rsqr (cos x)) * (Rsqr (cos z)) = 1.
Proof.
intros.
assert ((sin x)² * (sin y)² + (sin x)² * (cos y)² = (sin x)² * ((sin y)² + (cos y)²)) by lra.
rewrite H. clear H.
rewrite sin2_cos2.
assert ((sin x)² * 1 + (cos x)² * (sin z)² + (cos x)² * (cos z)²
    = (sin x)² + (cos x)² * ((sin z)² + (cos z)²)) by lra.
rewrite H. clear H.
rewrite sin2_cos2.
assert ((sin x)² + (cos x)² * 1 = (sin x)² + (cos x)²) by lra.
rewrite H. clear H.
rewrite sin2_cos2.
reflexivity.
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
rewrite 2 Rsqr_div.
remember (√ ((sin (z / 2))² * (cos (x - y))² + (cos (z / 2))² * (cos (x + y))²)) as t.
autorewrite with R_db.
assert ((cos x * cos y + - (cos z * sin x * sin y))² * / t² + (- (sin z * sin x * sin y))² * / t²
 = ((cos x * cos y - (cos z * sin x * sin y))² + (- (sin z * sin x * sin y))²) * / t²).
autorewrite with R_db. lra. 
rewrite H0. clear H0.
rewrite Rsqr_minus.
rewrite <- Rsqr_neg.
rewrite 5 Rsqr_mult.
rewrite Heqt.
rewrite Rsqr_sqrt.
rewrite cos_plus.
rewrite cos_minus.
rewrite Rsqr_minus.
rewrite Rsqr_plus.
assert (((cos x)² * (cos y)² + (cos z)² * (sin x)² * (sin y)² -
 2 * (cos x * cos y) * (cos z * sin x * sin y) + (sin z)² * (sin x)² * (sin y)²)
  = ((cos x)² * (cos y)² -
 2 * (cos x * cos y) * (cos z * sin x * sin y) + 
  (((sin z)² + (cos z)²) * (sin x)² * (sin y)²))) by lra.
rewrite H0. clear H0.
rewrite sin2_cos2.
assert (((sin (z / 2))² * ((cos x * cos y)² + (sin x * sin y)² 
            + 2 * (cos x * cos y) * (sin x * sin y)) +
       (cos (z / 2))² * ((cos x * cos y)² + (sin x * sin y)²
         - 2 * (cos x * cos y) * (sin x * sin y)))
 = (((sin (z / 2))² + (cos (z / 2))²) * (cos x * cos y)²
   - 2 * ((cos (z / 2)) * (cos (z / 2)) - ((sin (z / 2)) * (sin (z / 2))))
          * (cos x * cos y) * (sin x * sin y)
    + ((sin (z / 2))² + (cos (z / 2))²) *  (sin x * sin y)²)).
unfold Rsqr. lra.
rewrite H0. clear H0.
rewrite sin2_cos2.
rewrite <- cos_2a.
assert (2 * (z / 2) = z) by lra.
rewrite H0. clear H0.
rewrite 2 Rsqr_mult.
assert ((1 * ((cos x)² * (cos y)²) - 2 * cos z * (cos x * cos y) * (sin x * sin y) +
 1 * ((sin x)² * (sin y)²))
  = ((cos x)² * (cos y)² - 2 * (cos x * cos y) * (cos z * sin x * sin y) + 1 * (sin x)² * (sin y)²))
  by lra.
rewrite H0. clear H0.
rewrite Rinv_r.
reflexivity.
specialize (Rsqr_sqrt ((sin (z / 2))² * (cos (x - y))² + (cos (z / 2))² * (cos (x + y))²)) as H1.
assert (0 <= (sin (z / 2))² * (cos (x - y))² + (cos (z / 2))² * (cos (x + y))²).
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
assert (0 <= (sin (z / 2) * cos (x - y))²).
apply Rle_0_sqr.
assert (0 <= (cos (z / 2) * cos (x + y))²).
apply Rle_0_sqr.
lra.
apply H1 in H0. clear H1.
rewrite Heqt in H.
specialize (Rsqr_pos_lt (√ ((sin (z / 2))² * (cos (x - y))² + (cos (z / 2))² * (cos (x + y))²)) H) as H3.
rewrite Rsqr_sqrt in H3.
rewrite cos_plus in H3.
rewrite cos_minus in H3.
rewrite Rsqr_minus in H3.
rewrite Rsqr_plus in H3.
assert (((sin (z / 2))² * ((cos x * cos y)² + (sin x * sin y)² 
            + 2 * (cos x * cos y) * (sin x * sin y)) +
       (cos (z / 2))² * ((cos x * cos y)² + (sin x * sin y)²
         - 2 * (cos x * cos y) * (sin x * sin y)))
 = (((sin (z / 2))² + (cos (z / 2))²) * (cos x * cos y)²
   - 2 * ((cos (z / 2)) * (cos (z / 2)) - ((sin (z / 2)) * (sin (z / 2))))
          * (cos x * cos y) * (sin x * sin y)
    + ((sin (z / 2))² + (cos (z / 2))²) *  (sin x * sin y)²)).
unfold Rsqr. lra.
rewrite H1 in H3. clear H1.
rewrite sin2_cos2 in H3.
rewrite <- cos_2a in H3.
assert (2 * (z / 2) = z) by lra.
rewrite H1 in H3. clear H1.
rewrite 2 Rsqr_mult in H3.
assert ((1 * ((cos x)² * (cos y)²) - 2 * cos z * (cos x * cos y) * (sin x * sin y) +
 1 * ((sin x)² * (sin y)²))
  = ((cos x)² * (cos y)² - 2 * (cos x * cos y) * (cos z * sin x * sin y) + 1 * (sin x)² * (sin y)²))
  by lra.
rewrite H1 in H3. clear H1.
lra.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
assert (0 <= (sin (z / 2) * cos (x - y))²).
apply Rle_0_sqr.
assert (0 <= (cos (z / 2) * cos (x + y))²).
apply Rle_0_sqr.
lra.
rewrite <- Rsqr_mult.
rewrite <- Rsqr_mult.
assert (0 <= (sin (z / 2) * cos (x - y))²).
apply Rle_0_sqr.
assert (0 <= (cos (z / 2) * cos (x + y))²).
apply Rle_0_sqr.
lra.
assumption.
assumption.
Qed.

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


Lemma yzy_to_zyz_correct_5 : forall {dim} θ1 ξ θ2 q,
  (q < dim)%nat ->
    (sqrt (Rsqr (sin (ξ / 2)) * Rsqr (cos (θ1 / 2  - θ2 / 2))
         +  Rsqr (cos (ξ / 2)) * Rsqr (cos (θ1 / 2 + θ2 / 2))) <> 0)%R
  ->
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
apply  sqrt_pos. rewrite Heqp in H2.
assert (sin (acos (s / p)) = (t / p) \/ sin (acos (s / p)) = ((-t) / p)).
rewrite sin_acos.
rewrite Heqs.
rewrite Heqp.
rewrite Heqp in H0.
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
apply delta_cos_bound. rewrite Heqp in H0. assumption.
assert (sin (acos (rm22 θ1 ξ θ2) / 2) = 
  √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)
 \/ sin (acos (rm22 θ1 ξ θ2) / 2) = 
  - √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²)).
assert (Rsqr (cos (acos (rm22 θ1 ξ θ2) / 2)) = Rsqr p).
destruct H1. rewrite H1. reflexivity.
rewrite H1. unfold Rsqr. lra.
specialize (sin2_cos2 (acos (rm22 θ1 ξ θ2) / 2)) as H5.
assert ((sin (acos (rm22 θ1 ξ θ2) / 2))² = 1 - p²) by lra.
assert (p² = ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²)).
rewrite Heqp. rewrite Rsqr_sqrt. reflexivity.
rewrite <- Rsqr_mult. rewrite <- Rsqr_mult.
assert (0 <= (sin (ξ / 2) * cos (θ1 / 2 - θ2 / 2))²) by apply Rle_0_sqr.
assert (0 <= (cos (ξ / 2) * cos (θ1 / 2 + θ2 / 2))²) by apply Rle_0_sqr.
lra.
rewrite H7 in H6.
rewrite Heqp in H0.
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
destruct H1. destruct H3. destruct H4.
  unfold uc_cong; simpl. (* first case: all angles are greater than zero. *)
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
assert ((cos (θ2 / 2) * cos (θ1 / 2) + - (sin (θ2 / 2) * ((cos ξ, sin ξ) * sin (θ1 / 2))))%C
   = ((cos (θ2 / 2) * cos (θ1 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2))%R,
     (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2))%R)%C ) by lca.
rewrite H.
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
rewrite H6. clear H6.
rewrite Rinv_r. lca. assumption.
apply delta_cos_bound. assumption.
- (* second-sub-case: Cexp atan (rm12/rm02) sin acos rm22 * Cexp = ... *)
assert ((Cexp
    (-
     acos
       ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
        √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
  (sin (acos (rm22 θ1 ξ θ2) / 2) * Cexp (atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2))))%C
  = ((Cexp
    (-
     acos
       ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
        √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))) *
    Cexp (atan2 (rm12 θ1 ξ θ2) (rm02 θ1 ξ θ2))) * sin (acos (rm22 θ1 ξ θ2) / 2))%C) by lca.
rewrite H. clear H.
rewrite <- Cexp_add.
unfold Cexp.
rewrite C_smult_r.
rewrite C_smult_r.
rewrite sin_plus.
rewrite cos_plus.
rewrite cos_neg.
rewrite sin_neg.
rewrite H3. rewrite H4.
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
- (* when sin (acos (rm22 θ1 ξ θ2) / 2) =
      - √ ((sin (ξ / 2))² * (sin (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (sin (θ1 / 2 + θ2 / 2))²) *)

Admitted.


(*
 autorewrite with R_db C_db Cexp_db trig_db.

unfold Cexp.
rewrite cos_acos.
rewrite sin_acos.
specialize (delta_cos_sin (θ1 / 2) (θ2 / 2) ξ H0) as H2.
assert (1 - ((cos (θ1 / 2) * cos (θ2 / 2) - cos ξ * sin (θ1 / 2) * sin (θ2 / 2)) /
      √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))²
   = (- sin ξ * sin (θ1 / 2) * sin (θ2 / 2) /
      √ ((sin (ξ / 2))² * (cos (θ1 / 2 - θ2 / 2))² + (cos (ξ / 2))² * (cos (θ1 / 2 + θ2 / 2))²))²) by lra.
rewrite H. clear H.
specialize (cos_2a_cos_half (acos (rm22 θ1 ξ θ2) / 2)) as H.
destruct H.
rewrite H.
assert (2 * (acos (rm22 θ1 ξ θ2) / 2) = acos (rm22 θ1 ξ θ2)) by lra.
rewrite H3.
clear H3.
rewrite cos_acos.
6: {
unfold atan2.
}
Admitted.

(*
Lemma yzy_to_zyz_correct : forall {dim} θ1 ξ θ2 q,
  (q < dim)%nat ->
  @Ry dim θ1 q ; Rz ξ q ; Ry θ2 q ≅
          Rz (to_zyz_phi θ1 ξ θ2) q ; Ry (to_zyz_theta θ1 ξ θ2) q ; Rz (to_zyz_lambda θ1 ξ θ2) q.
Proof.
intros.
  unfold uc_cong; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
Admitted.
*)

Lemma combine_u3_u3: forall {dim} (θ1 ϕ1 λ1 θ2 ϕ2 λ2 : R) (q : nat), 
  (q < dim)%nat ->
  ([@U3 dim θ1 ϕ1 λ1 q] ++ [U3 θ2 ϕ2 λ2 q]) ≅l≅
        ([U3 (to_zyz_theta θ1 (ϕ1 + λ2) θ2)
               ((to_zyz_lambda θ1 (ϕ1 + λ2) θ2)+ϕ2) (λ1+(to_zyz_phi θ1 (ϕ1 + λ2) θ2)) q]).
Proof.
  intros.
  unfold uc_cong_l, uc_cong; simpl.
  exists PI.
  autorewrite with eval_db.
  2: lia.
  gridify.
  rewrite <- Mscale_kron_dist_l, <- Mscale_kron_dist_r.
  do 2 (apply f_equal2; try reflexivity).
  solve_matrix.
Admitted.

(* Convert a sequence of YZY Euler angles to a quaternion. 
   the normalize is unnecessary because the norm is always 1. *)
Definition to_zyz (q : quaternion) : (R * R * R) :=
  let m := to_matrix q in
  match m with
  | ((_, _, m02), (m10, m11, m12), (m20, m21, m22)) =>
    if m22 <? 1
    then if -1 <? m22
         then (atan2 m12 m02, acos m22, atan2 m21 (- m20))
         else (- atan2 m10 m11, PI, 0)
    else (atan2 m10 m11, 0, 0)
  end.


Definition from_yzy (θ1 ξ θ2 : R) : quaternion :=
  let q1 : quaternion := (cos (θ1 / 2), 0, sin (θ1 / 2), 0) in
  let q2 : quaternion := (cos (ξ / 2), 0, 0, sin (ξ / 2)) in
  let q3 : quaternion := (cos (θ2 / 2), 0, sin (θ2 / 2), 0) in
  normalize (mult (mult q1 q2) q3).

Definition yzy_to_zyz ξ θ1 θ2 :=
  let q := from_yzy θ1 ξ θ2 in
  match to_zyz q with
  | (ϕ, θ, λ) => (θ, ϕ, λ)
  end.

Definition compose_u3 (θ1 ϕ1 λ1 θ2 ϕ2 λ2 : R) :=
  match yzy_to_zyz (ϕ1 + λ2) θ1 θ2 with
  | (θ', ϕ', λ') => UIBM_U3 θ' (λ' + ϕ2) (λ1 + ϕ')
  end.


(* The following lemma will likely be difficult to prove :) 
   Try to break it into small parts! *)
Lemma yzy_to_zyz_correct : forall {dim} ξ θ1 θ2 ϕ θ λ q,
  (q < dim)%nat ->
  yzy_to_zyz ξ θ1 θ2 = (θ, ϕ, λ) ->
  @Ry dim θ1 q ; Rz ξ q ; Ry θ2 q ≡ Rz ϕ q ; Ry θ q ; Rz λ q.
Proof.
intros.
  unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
apply f_equal2; try reflexivity.
apply f_equal2; try reflexivity.
  solve_matrix.
unfold yzy_to_zyz in H0.
unfold from_yzy in H0.
unfold mult,normalize,to_zyz in H0.
 autorewrite with R_db C_db Cexp_db trig_db in H0.
destruct (θ, ϕ, λ). destruct p.
Admitted.

Lemma u3_is_ZYZ_rotation : forall dim θ ϕ λ q,
  (q < dim)%nat ->
  list_to_ucom [@U3 dim θ ϕ λ q] ≡ Rz λ q ; Ry θ q ; Rz ϕ q.
Proof.
  intros.
  unfold uc_equiv; simpl.
  autorewrite with eval_db.
  2: lia.
  gridify.
  do 2 (apply f_equal2; try reflexivity).
  solve_matrix.
  group_Cexp.
  reflexivity.
Qed.

Lemma compose_u3_correct : forall dim θ1 ϕ1 λ1 θ2 ϕ2 λ2 q,
  (q < dim)%nat ->
  [@U3 dim θ1 ϕ1 λ1 q] ++ [U3 θ2 ϕ2 λ2 q] =l= [App1 (compose_u3 θ1 ϕ1 λ1 θ2 ϕ2 λ2) q].
Proof.
  intros.
  unfold uc_equiv_l.
  rewrite list_to_ucom_append. 
  rewrite 2 u3_is_ZYZ_rotation by lia.
  repeat rewrite <- useq_assoc.
  rewrite (useq_assoc _ (Rz ϕ1 _) (Rz λ2 _)).
  rewrite Rz_Rz_add.
  unfold compose_u3.
  destruct (yzy_to_zyz (ϕ1 + λ2) θ1 θ2) eqn:Hyzy_to_zyz.
  destruct p.
  eapply yzy_to_zyz_correct in Hyzy_to_zyz.
  2: apply H.
  rewrite (useq_assoc _ (Ry θ1 _)).
  rewrite (useq_assoc _ _ (Ry θ2 _)).
  rewrite Hyzy_to_zyz.
  repeat rewrite useq_assoc.
  rewrite Rz_Rz_add.
  repeat rewrite <- useq_assoc.
  rewrite Rz_Rz_add.
  rewrite <- u3_is_ZYZ_rotation by assumption.
  reflexivity.
Qed.
*)
