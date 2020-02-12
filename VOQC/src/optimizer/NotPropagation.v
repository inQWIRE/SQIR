Require Import Proportional.
Require Import Equivalences.
Require Export PI4GateSet.

Local Close Scope C_scope.
Local Close Scope R_scope.

Local Open Scope ucom_scope.

(* Propagate an X gate on qubit q as far right as possible, cancelling the
   gate if possible. The rules in Nam et al. use Toffoli gates with +/- controls;
   we achieve the same effect by switching between propagating X and propagating
   Z when necessary (although our omission of the Toffoli gate does not allow
   us to change polarity of T/T† gates).

   Note that this optimization may increase the number of gates due to how
   X propagates through CNOT. These additional gates will often be removed by
   later passes. *)

Fixpoint propagate_X {dim} (l : PI4_ucom_l dim) q n :=
  match n with
  | O => X q :: l
  | S n' =>
      match l with
      | [] => [X q]
      | u :: t =>
          if does_not_reference_appl q u
          then u :: propagate_X t q n'
          else match u with
               | App1 UPI4_X n => t
               | App1 UPI4_H n => u :: Z q :: t
               | App1 (UPI4_PI4 k) n => (* introduces global phase *)
                   App1 (UPI4_PI4 (8 - k)%Z) n :: propagate_X t q n'
               | App2 UPI4_CNOT m n =>
                   if q =? m 
                   then u :: propagate_X (propagate_X t m n') n n'
                   else u :: propagate_X t q n'
               | _ => X q :: l (* impossible case *)
               end
      end
  end.

Fixpoint not_propagation' {dim} (l : PI4_ucom_l dim) n :=
  match n with
  | O => l
  | S n' => 
      match l with
      | [] => [] 
      | App1 UPI4_X q :: t =>
          let l' := propagate_X t q n in
          not_propagation' l' n'
      | u  :: t => u :: not_propagation' t n'
      end
  end.

(* Worst case, every CNOT propagates two X gates, so we start with
   n = 2 × (length n). The n = 0 case should be unreachable. *)
Definition not_propagation {dim} (l : PI4_ucom_l dim) := 
  not_propagation' l (2 * List.length l).

(* Proofs *)

Lemma H_Z_commutes : forall {dim} q,
  [@H dim q] ++ [Z q] =l= [X q] ++ [H q].
Proof.
  intros. 
  unfold uc_equiv_l, uc_equiv; simpl.
  repeat rewrite Mmult_assoc.
  apply f_equal2; trivial.
  replace (4 * PI / 4)%R with PI by lra.
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

Lemma Rz_X_commutes : forall {dim} q k,
  ([@X dim q] ++ [App1 (UPI4_PI4 k) q]) ≅l≅ ([App1 (UPI4_PI4 (8 - k)) q] ++ [X q]).
Proof.
  intros.
  Local Opaque Z.sub.
  unfold uc_cong_l, uc_cong; simpl.
  exists (IZR k * PI / 4)%R.
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
  solve_matrix.
  rewrite minus_IZR.
  autorewrite with R_db.
  repeat rewrite Rmult_plus_distr_r.
  rewrite Cexp_add.
  replace (8 * PI * / 4)%R with (2 * PI)%R by lra.
  rewrite (Cmult_comm (Cexp (2 * PI))).
  rewrite Cmult_assoc.
  rewrite <- Cexp_add.
  replace (IZR k * PI * / 4 + - IZR k * PI * / 4)%R with 0%R by lra.
  rewrite Cexp_2PI, Cexp_0.
  lca.
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

Lemma propagate_X_preserves_semantics : forall {dim} (l : PI4_ucom_l dim) q n,
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
  destruct g. 
  - simpl in dnr. apply negb_false_iff in dnr. 
    apply beq_nat_true in dnr; subst.
    dependent destruction p.
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
    rewrite Rz_X_commutes; reflexivity.
  - dependent destruction p. 
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
  - inversion p.
Qed.

Lemma propagate_X_well_typed : forall {dim} (l : PI4_ucom_l dim) q n,
  (q < dim)%nat -> uc_well_typed_l l -> uc_well_typed_l (propagate_X l q n).
Proof.
  intros dim l q n Hq WT.
  specialize (propagate_X_preserves_semantics l q n Hq) as H.
  assert (uc_well_typed_l (X q :: l)).
  constructor; assumption.
  symmetry in H.
  apply uc_cong_l_implies_WT in H; assumption.
Qed.

Lemma not_propagation_sound : forall {dim} (l : PI4_ucom_l dim), 
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

Lemma not_propagation_WT : forall {dim} (l : PI4_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (not_propagation l).
Proof.
  intros dim l WT.
  specialize (not_propagation_sound l WT) as H.
  symmetry in H.
  apply uc_cong_l_implies_WT in H; assumption.
Qed.

