Require Import Proportional.
Require Import Equivalences.
Require Export RzQGateSet.

Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

Local Open Scope ucom_scope.

(* Propagate an X gate on qubit q as far right as possible, cancelling the
   gate if possible. The rules in Nam et al. use Toffoli gates with +/- controls;
   we achieve the same effect by propagating X through H, CNOT, and Rz gates 
   (although our omission of the Toffoli gate does not allow us to change polarity 
   of T/T† gates).

   Note that this optimization may increase the number of gates due to how
   X propagates through CNOT. These additional gates will often be removed by
   later passes. *)

Fixpoint propagate_X {dim} (l : RzQ_ucom_l dim) q n acc :=
  match n with
  | O => rev_append acc (X q :: l)
  | S n' =>
      match l with
      | [] => rev_append acc [X q]
      | u :: t =>
          if does_not_reference_appl q u
          then propagate_X t q n' (u :: acc)
          else match u with
               | App1 URzQ_X n => rev_append acc t
               | App1 URzQ_H n => rev_append acc (u :: Z q :: t)
               | App1 (URzQ_Rz a) n => (* introduces global phase *)
                   propagate_X t q n' (invert_rotation a n :: acc)
               | App2 URzQ_CNOT m n =>
                   if q =? m 
                   then let t' := propagate_X t n n' [] in
                        propagate_X t' m n' (u :: acc)
                   else propagate_X t q n' (u :: acc)
               | _ => rev_append acc (X q :: l) (* impossible case *)
               end
      end
  end.

Fixpoint not_propagation' {dim} (l : RzQ_ucom_l dim) n acc :=
  match n with
  | O => rev_append acc l
  | S n' => 
      match l with
      | [] => rev_append acc [] 
      | App1 URzQ_X q :: t => not_propagation' (propagate_X t q n []) n' acc
      | u  :: t => not_propagation' t n' (u :: acc)
      end
  end.

(* Worst case, every CNOT propagates two X gates, so we start with
   n = 2 × (length n). The n = 0 case should be unreachable. *)
Definition not_propagation {dim} (l : RzQ_ucom_l dim) := 
  not_propagation' l (2 * List.length l) [].

(* Proofs *)

Lemma H_Z_commutes : forall {dim} q,
  [@H dim q] ++ [Z q] =l= [X q] ++ [H q].
Proof.
  intros. 
  unfold uc_equiv_l, uc_equiv; simpl.
  repeat rewrite Mmult_assoc.
  apply f_equal2; trivial.
  unfold Qreals.Q2R; simpl. 
  replace (1 * / 1 * PI)%R with PI by lra. 
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

Lemma Rz_X_commutes : forall {dim} q a,
  ([@X dim q] ++ [Rz a q]) ≅l≅ ([invert_rotation a q] ++ [X q]).
Proof.
  intros.
  Local Opaque Z.sub.
  unfold uc_cong_l, uc_cong; simpl.
  exists (Qreals.Q2R a * PI)%R.
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
  rewrite Qreals.Q2R_minus.
  remember (Qreals.Q2R a) as qa.
  unfold Qreals.Q2R; simpl.
  unfold phase_shift; solve_matrix.
  rewrite <- Cexp_add.
  replace (qa * PI + (2 * / 1 - qa) * PI)%R with (2 * PI)%R by lra.
  rewrite Cexp_2PI. 
  reflexivity.
Qed.

Lemma propagate_X_through_CNOT_control : forall {dim} m n,
  [@X dim m] ++ [CNOT m n] =l= [CNOT m n] ++ [X m] ++ [X n].
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

Lemma propagate_X_preserves_semantics : forall {dim} (l : RzQ_ucom_l dim) q n acc,
  (q < dim)%nat -> propagate_X l q n acc ≅l≅ (rev acc ++ (X q :: l)).
Proof.
  intros dim l q n.
  generalize dependent q.
  generalize dependent l.
  induction n; intros l q acc Hq; simpl.
  rewrite rev_append_rev. reflexivity.
  destruct l; simpl.
  rewrite rev_append_rev. reflexivity.
  destruct (does_not_reference_appl q g) eqn:dnr.
  rewrite IHn; auto. simpl.
  rewrite (cons_to_app _ (_ :: l)).
  rewrite 2 (cons_to_app _ l); repeat rewrite app_assoc.
  apply uc_equiv_cong_l.
  apply uc_app_congruence; try reflexivity.
  repeat rewrite <- app_assoc.
  apply uc_app_congruence; try reflexivity.
  symmetry; apply does_not_reference_commutes_app1. 
  simpl. apply andb_true_iff; auto.
  destruct g as [u | u | u]. 
  - simpl in dnr. apply negb_false_iff in dnr. 
    apply beq_nat_true in dnr; subst.
    dependent destruction u.
    rewrite rev_append_rev.
    rewrite 2 (cons_to_app _ (_ :: l)).
    rewrite 2 (cons_to_app _ l); repeat rewrite app_assoc.
    apply uc_equiv_cong_l.
    apply uc_app_congruence; try reflexivity.
    repeat rewrite <- app_assoc.
    apply uc_app_congruence; try reflexivity.
    apply H_Z_commutes.
    rewrite rev_append_rev.
    repeat rewrite (cons_to_app _ (_ :: l)).
    repeat rewrite (cons_to_app _ l); repeat rewrite app_assoc.
    apply uc_equiv_cong_l.
    rewrite <- (app_assoc _ [X q]).
    rewrite X_X_cancels; auto.
    rewrite app_nil_r; reflexivity.
    rewrite IHn; auto. simpl.
    repeat rewrite (cons_to_app _ (_ :: l)).
    repeat rewrite (cons_to_app _ l); repeat rewrite app_assoc.
    rewrite <- (app_assoc _ _ [X q]).
    rewrite <- (app_assoc _ [X q]).
    rewrite <- Rz_X_commutes; reflexivity.    
  - dependent destruction u. 
    bdestruct (q =? n0); subst.
    rewrite (IHn _ n0); auto. simpl.
    bdestruct (n1 <? dim).
    rewrite IHn; auto. simpl.
    repeat rewrite (cons_to_app _ (_ :: l)).
    repeat rewrite (cons_to_app _ l); repeat rewrite app_assoc.
    apply uc_equiv_cong_l; apply uc_app_congruence; try reflexivity.
    repeat rewrite <- app_assoc.
    apply uc_app_congruence; try reflexivity.
    symmetry.
    apply propagate_X_through_CNOT_control.
    apply uc_equiv_cong_l; unfold uc_equiv_l, uc_equiv; simpl.
    repeat (try rewrite RzQ_to_base_ucom_l_app; try rewrite list_to_ucom_append; simpl).
    autorewrite with eval_db; bdestruct_all; do 2 Msimpl_light; try reflexivity.
    lia.
    rewrite IHn; auto. simpl.
    repeat rewrite (cons_to_app _ (_ :: l)).
    repeat rewrite (cons_to_app _ l); repeat rewrite app_assoc.
    apply uc_equiv_cong_l; apply uc_app_congruence; try reflexivity. 
    repeat rewrite <- app_assoc.
    apply uc_app_congruence; try reflexivity.  
    bdestruct (q =? n1); subst.
    symmetry; apply propagate_X_through_CNOT_target.
    apply negb_false_iff in dnr. 
    apply orb_true_iff in dnr. 
    destruct dnr; bdestruct (n0 =? q); bdestruct (n1 =? q); try lia; discriminate. 
  - inversion u.
Qed.

Lemma propagate_X_well_typed : forall {dim} (l : RzQ_ucom_l dim) q n acc,
  (q < dim)%nat -> uc_well_typed_l l -> uc_well_typed_l acc ->
  uc_well_typed_l (propagate_X l q n acc).
Proof.
  intros dim l q n acc Hq Hacc WT.
  specialize (propagate_X_preserves_semantics l q n acc Hq) as H.
  assert (uc_well_typed_l (rev acc ++ X q :: l)).
  apply uc_well_typed_l_app; split. 
  rewrite <- uc_well_typed_l_rev; auto. 
  constructor; auto.
  symmetry in H.
  apply uc_cong_l_implies_WT in H; assumption.
Qed.

Lemma not_propagation_sound : forall {dim} (l : RzQ_ucom_l dim), 
  uc_well_typed_l l -> not_propagation l ≅l≅ l.
Proof.
  assert (H: forall {dim} (l : RzQ_ucom_l dim) n acc, 
          uc_well_typed_l l -> not_propagation' l n acc ≅l≅ (rev acc ++ l)).
  { intros dim l n.
    generalize dependent l.
    Local Opaque propagate_X. 
    induction n; intros l acc WT; simpl.
    rewrite rev_append_rev. reflexivity.
    destruct l; simpl.
    rewrite rev_append_rev. reflexivity.
    inversion WT; subst.
    dependent destruction u.
    all: try (rewrite IHn; auto; simpl; rewrite <- app_assoc; reflexivity).
    rewrite IHn.  
    apply uc_cong_l_app_congruence; try reflexivity.
    rewrite propagate_X_preserves_semantics; auto. reflexivity.
    apply propagate_X_well_typed; auto. constructor. lia. }
  intros ? ? H0.
  apply H; auto.
Qed.

Lemma not_propagation_WT : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (not_propagation l).
Proof.
  intros dim l WT.
  specialize (not_propagation_sound l WT) as H.
  symmetry in H.
  apply uc_cong_l_implies_WT in H; assumption.
Qed.

