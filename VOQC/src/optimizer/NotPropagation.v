Require Import Proportional.
Require Import Equivalences.
Require Export RzkGateSet.

Local Close Scope C_scope.
Local Close Scope R_scope.

Local Open Scope ucom_scope.

(* Propagate an X gate on qubit q as far right as possible, cancelling the
   gate if possible. The rules in Nam et al. use Toffoli gates with +/- controls;
   we achieve the same effect by propagating X through H, CNOT, and Rz gates 
   (although our omission of the Toffoli gate does not allow us to change polarity 
   of T/T† gates).

   Note that this optimization may increase the number of gates due to how
   X propagates through CNOT. These additional gates will often be removed by
   later passes. *)

Fixpoint propagate_X {dim} (l : Rzk_ucom_l dim) q n :=
  match n with
  | O => X q :: l
  | S n' =>
      match l with
      | [] => [X q]
      | u :: t =>
          if does_not_reference_appl q u
          then u :: propagate_X t q n'
          else match u with
               | App1 URzk_X n => t
               | App1 URzk_H n => u :: Z q :: t
               | App1 (URzk_Rz i) n => (* introduces global phase *)
                  invert_rotation i n :: propagate_X t q n'
               | App2 URzk_CNOT m n =>
                   if q =? m 
                   then u :: propagate_X (propagate_X t m n') n n'
                   else u :: propagate_X t q n'
               | _ => X q :: l (* impossible case *)
               end
      end
  end.

Fixpoint not_propagation' {dim} (l : Rzk_ucom_l dim) n :=
  match n with
  | O => l
  | S n' => 
      match l with
      | [] => [] 
      | App1 URzk_X q :: t => not_propagation' (propagate_X t q n) n'
      | u  :: t => u :: not_propagation' t n'
      end
  end.

(* Worst case, every CNOT propagates two X gates, so we start with
   n = 2 × (length n). The n = 0 case should be unreachable. *)
Definition not_propagation {dim} (l : Rzk_ucom_l dim) := 
  not_propagation' l (2 * List.length l).

(* Proofs *)

Lemma H_Z_commutes : forall {dim} q,
  [@H dim q] ++ [Z q] =l= [X q] ++ [H q].
Proof.
  intros. 
  unfold uc_equiv_l, uc_equiv; simpl.
  repeat rewrite Mmult_assoc.
  apply f_equal2; trivial.
  replace (IZR Rzk_k * PI / IZR Rzk_k)%R with PI.
  2: unfold Rzk_k; lra.
  rewrite pauli_x_rotation.
  rewrite pauli_z_rotation.
  rewrite hadamard_rotation.
  autorewrite with eval_db.
  gridify.
  do 2 (apply f_equal2; trivial).
  solve_matrix.
Qed.

Lemma X_X_cancels : forall {dim} q,
  q < dim -> [@X dim q] ++ [X q] =l= [].
Proof.
  intros. 
  unfold uc_equiv_l, uc_equiv; simpl.
  rewrite pauli_x_rotation.
  autorewrite with eval_db.
  2: lia.
  gridify.
  Qsimpl; reflexivity.
Qed.

Lemma Rz_X_commutes : forall {dim} q i,
  ([@X dim q] ++ [Rz i q]) ≅l≅ ([invert_rotation i q] ++ [X q]).
Proof.
  intros.
  Local Opaque Z.sub.
  unfold uc_cong_l, uc_cong; simpl.
  exists (IZR i * PI / IZR Rzk_k)%R.
  rewrite pauli_x_rotation.
  repeat rewrite phase_shift_rotation.
  repeat rewrite Mmult_assoc.
  rewrite <- Mscale_mult_dist_r.
  apply f_equal2; trivial.
  autorewrite with eval_db.
  gridify.
  rewrite <- Mscale_kron_dist_l.
  rewrite <- Mscale_kron_dist_r.
  do 2 (apply f_equal2; trivial).
  replace 65536%Z with (2 * Rzk_k)%Z by reflexivity.
  rewrite <- phase_mod_2PI_scaled. 
  2: unfold Rzk_k; lia.
  unfold phase_shift; solve_matrix.
  rewrite minus_IZR.
  autorewrite with R_db.
  repeat rewrite Rmult_plus_distr_r.
  rewrite Cexp_add.
  replace (65536 * PI * / IZR Rzk_k)%R with (2 * PI)%R. 
  2: unfold Rzk_k; lra.
  rewrite Cexp_2PI. 
  autorewrite with C_db. Search (- _ * _)%R.
  do 2 rewrite <- Ropp_mult_distr_l.
  symmetry. apply Cexp_mul_neg_r.
Qed.

Lemma propagate_X_through_CNOT_control : forall {dim} m n,
  [@X dim m] ++ [CNOT m n] =l= [CNOT m n] ++ [X n] ++ [X m].
Proof.
  intros dim m n.
  unfold uc_equiv_l, uc_equiv; simpl.
  repeat rewrite Mmult_assoc.
  apply f_equal2; trivial.
  rewrite pauli_x_rotation.
  autorewrite with eval_db.
  gridify; trivial.
  Qsimpl.
  rewrite Mplus_comm. reflexivity.
  Qsimpl.
  rewrite Mplus_comm. reflexivity.
Qed.

Lemma propagate_X_through_CNOT_target : forall {dim} m n,
  [@X dim n] ++ [CNOT m n] =l= [CNOT m n] ++ [X n].
Proof.
  intros dim m n.
  unfold uc_equiv_l, uc_equiv; simpl.
  repeat rewrite Mmult_assoc.
  apply f_equal2; trivial.
  rewrite pauli_x_rotation.
  autorewrite with eval_db.
  gridify; Qsimpl; reflexivity.
Qed.

Lemma propagate_X_preserves_semantics : forall {dim} (l : Rzk_ucom_l dim) q n,
  (q < dim)%nat -> propagate_X l q n ≅l≅ (X q :: l).
Proof.
  intros dim l q n Hq.
  generalize dependent q.
  generalize dependent l.
  induction n; intros l q Hq; try reflexivity.
  destruct l; try reflexivity.
  simpl. 
  destruct (does_not_reference_appl q g) eqn:dnr.
  rewrite IHn; try assumption.
  rewrite 2 (cons_to_app _ (_ :: l)).
  rewrite 2 (cons_to_app _ l); repeat rewrite app_assoc.
  apply uc_equiv_cong_l.
  apply uc_app_congruence; try reflexivity.
  symmetry; apply does_not_reference_commutes_app1. 
  simpl. apply andb_true_iff; auto.
  destruct g as [u | u | u]. 
  - simpl in dnr. apply negb_false_iff in dnr. 
    apply beq_nat_true in dnr; subst.
    dependent destruction u.
    rewrite 2 (cons_to_app _ (_ :: l)).
    rewrite 2 (cons_to_app _ l); repeat rewrite app_assoc.
    apply uc_equiv_cong_l.
    apply uc_app_congruence; try reflexivity.
    apply H_Z_commutes.
    repeat rewrite (cons_to_app _ (_ :: l)).
    repeat rewrite (cons_to_app _ l); repeat rewrite app_assoc.
    apply uc_equiv_cong_l.
    rewrite X_X_cancels; try assumption; reflexivity.
    rewrite IHn; try assumption.
    repeat rewrite (cons_to_app _ (_ :: l)).
    repeat rewrite (cons_to_app _ l); repeat rewrite app_assoc.
    rewrite <- Rz_X_commutes; reflexivity.
  - dependent destruction u. 
    bdestruct (q =? n0); subst.
    bdestruct (n1 <? dim).
    2: apply uc_equiv_cong_l; unfold uc_equiv_l, uc_equiv; simpl;
       autorewrite with eval_db; bdestruct_all; Msimpl_light; reflexivity.
    repeat rewrite IHn by assumption.
    rewrite cons_to_app.
    repeat rewrite (cons_to_app _ (_ :: l)).
    repeat rewrite (cons_to_app _ l); repeat rewrite app_assoc.
    apply uc_equiv_cong_l; apply uc_app_congruence; try reflexivity.
    symmetry; rewrite <- app_assoc.
    apply propagate_X_through_CNOT_control.
    rewrite IHn by assumption.
    repeat rewrite (cons_to_app _ (_ :: l)).
    repeat rewrite (cons_to_app _ l); repeat rewrite app_assoc.
    apply uc_equiv_cong_l; apply uc_app_congruence; try reflexivity.   
    bdestruct (q =? n1); subst.
    symmetry; apply propagate_X_through_CNOT_target.
    apply negb_false_iff in dnr. 
    apply orb_true_iff in dnr. 
    destruct dnr; bdestruct (n0 =? q); bdestruct (n1 =? q); try lia; discriminate. 
  - inversion u.
Qed.

Lemma propagate_X_well_typed : forall {dim} (l : Rzk_ucom_l dim) q n,
  (q < dim)%nat -> uc_well_typed_l l -> uc_well_typed_l (propagate_X l q n).
Proof.
  intros dim l q n Hq WT.
  specialize (propagate_X_preserves_semantics l q n Hq) as H.
  assert (uc_well_typed_l (X q :: l)).
  constructor; assumption.
  symmetry in H.
  apply uc_cong_l_implies_WT in H; assumption.
Qed.

Lemma not_propagation_sound : forall {dim} (l : Rzk_ucom_l dim), 
  uc_well_typed_l l -> not_propagation l ≅l≅ l.
Proof.
  intros dim l WT.
  assert (forall n, not_propagation' l n ≅l≅ l).
  { intros n.
    generalize dependent l.
    induction n; intros l WT; try reflexivity.
    Local Opaque propagate_X. 
    destruct l; try reflexivity.
    inversion WT; subst; simpl.
    dependent destruction u.
    all: try (rewrite IHn; try assumption; reflexivity).
    rewrite IHn.
    apply propagate_X_preserves_semantics; try assumption.
    apply propagate_X_well_typed; assumption. }
  apply H.
Qed.

Lemma not_propagation_WT : forall {dim} (l : Rzk_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (not_propagation l).
Proof.
  intros dim l WT.
  specialize (not_propagation_sound l WT) as H.
  symmetry in H.
  apply uc_cong_l_implies_WT in H; assumption.
Qed.

