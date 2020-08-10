Require Import Proportional.
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

Require Import FSets.FSetAVL.
Require Import FSets.FSetFacts.

Module FSet := FSetAVL.Make(Coq.Structures.OrderedTypeEx.Nat_as_OT).
Module FSetFacts := FSetFacts.Facts FSet.
Module FSetProps := FSetProperties.Properties FSet.

Lemma mem_reflect : forall x s, reflect (FSet.In x s) (FSet.mem x s).
Proof. intros x l. apply iff_reflect. apply FSetFacts.mem_iff. Qed.
Hint Resolve mem_reflect : bdestruct.

(* Apply an X gate to every qubits in set qs. *)
Definition finalize {dim} qs : RzQ_ucom_l dim := 
  FSet.fold (fun q a => X q :: a) qs []. 

(* l   : input program
   qs  : qubits where an X gate is currently being propagated
   acc : accumulator for tail recursion *)
Fixpoint not_propagation' {dim} (l acc : RzQ_ucom_l dim) qs :=
  match l with
  | [] => rev_append acc (finalize qs)
  | App1 URzQ_X q :: t => 
      let qs' := if FSet.mem q qs then FSet.remove q qs else FSet.add q qs in
      not_propagation' t acc qs'
  | App1 URzQ_H q :: t =>
      if FSet.mem q qs
      then not_propagation' t (Z q :: H q :: acc) (FSet.remove q qs)
      else not_propagation' t (H q :: acc) qs
  | App1 (URzQ_Rz a) q :: t =>
      if FSet.mem q qs
      then not_propagation' t (invert_rotation a q :: acc) qs
      else not_propagation' t (Rz a q :: acc) qs
  | App2 URzQ_CNOT m n :: t =>
      let qs' := if FSet.mem m qs 
                 then if FSet.mem n qs then FSet.remove n qs else FSet.add n qs
                 else qs in
      not_propagation' t (CNOT m n :: acc) qs'
  | _ => acc (* impossible case *)
  end.

Definition not_propagation {dim} (l : RzQ_ucom_l dim) := 
  not_propagation' l [] FSet.empty.

(* Proofs *)

Lemma finalize_unfold : forall {dim} q qs,
  FSet.In q qs ->
  finalize qs =l= [@X dim q] ++ finalize (FSet.remove q qs).
Proof.
  intros.
  symmetry.
  simpl.
  unfold finalize.
  specialize (FSetProps.remove_fold_1 (uc_equiv_l_rel dim)) as Hfold.
  specialize (Hfold (fun q a => X q :: a)).
  simpl in Hfold.
  apply Hfold; auto; clear Hfold.
  unfold compat_op; solve_proper. 
  unfold transpose.
  intros.
  rewrite 2 (cons_to_app _ (_ :: _)).
  rewrite 2 (cons_to_app _ z).
  apply_app_congruence.
  bdestruct (x =? y).
  subst.
  reflexivity.
  apply does_not_reference_commutes_app1.
  simpl.
  apply andb_true_intro; split; auto.
  rewrite negb_true_iff. 
  apply eqb_neq; auto.
Qed.

Lemma finalize_equal : forall {dim} qs1 qs2,
  FSet.Equal qs1 qs2 ->
  @finalize dim qs1 =l= finalize qs2.
Proof.
  intros.
  unfold finalize.
  apply FSetProps.fold_equal; auto.
  apply uc_equiv_l_rel.
  unfold compat_op; solve_proper. 
  unfold transpose.
  intros.
  rewrite 2 (cons_to_app _ (_ :: _)).
  rewrite 2 (cons_to_app _ z).
  apply_app_congruence.
  bdestruct (x =? y).
  subst.
  reflexivity.
  apply does_not_reference_commutes_app1.
  simpl.
  apply andb_true_intro; split; auto.
  rewrite negb_true_iff. 
  apply eqb_neq; auto.
Qed.

Lemma finalize_empty : forall {dim},
  @finalize dim FSet.empty = [].
Proof. 
  intros.
  unfold finalize.
  apply FSetProps.fold_empty.
Qed.

Lemma finalize_dnr : forall {dim} q qs,
  not (FSet.In q qs) -> 
  does_not_reference (@finalize dim qs) q = true.
Proof.
  intros.
  unfold finalize.
  apply FSetProps.fold_rec; intros.
  reflexivity.
  simpl.
  apply andb_true_intro; split; auto.
  rewrite negb_true_iff. 
  apply eqb_neq.
  intro contra.
  subst.
  contradiction.
Qed.

Lemma not_propagation'_preserves_semantics : forall {dim} (l acc : RzQ_ucom_l dim) qs,
  uc_well_typed_l l ->
  not_propagation' l acc qs ≅l≅ 
    (rev acc ++ (finalize qs) ++ l).
Proof.
  intros dim l.
  induction l; intros acc qs WT.
  simpl.
  rewrite rev_append_rev, app_nil_r.
  reflexivity.
  destruct a; dependent destruction r; simpl;
  inversion WT; subst.
  - (* H case *)
    bdestruct (FSet.mem n qs); rewrite IHl by assumption; 
    apply uc_equiv_cong_l; simpl.
    + rewrite (finalize_unfold _ _ H) by assumption.
      rewrite (cons_to_app _ l).
      apply_app_congruence.
      rewrite <- (does_not_reference_commutes_app1 _ URzQ_H).
      apply_app_congruence.
      unfold_uc_equiv_l.
      replace (Qreals.Q2R 1 * PI)%R with PI.
      apply H_comm_Z.
      unfold Qreals.Q2R; simpl; lra.
      apply finalize_dnr.
      apply FSet.remove_1; auto.
    + rewrite (cons_to_app _ l).
      apply_app_congruence.
      apply does_not_reference_commutes_app1.
      apply finalize_dnr; auto.
  - (* X case *)
    rewrite IHl by assumption.
    apply uc_equiv_cong_l.
    rewrite (cons_to_app _ l).
    bdestruct (FSet.mem n qs).
    + rewrite (finalize_unfold n qs) by assumption.
      unfold X.
      rewrite (does_not_reference_commutes_app1 _ URzQ_X).
      rewrite <- (app_nil_r (finalize _)) at 1.
      apply_app_congruence.
      unfold uc_equiv_l; simpl.
      rewrite SKIP_id_r.
      symmetry.
      rewrite <- (ID_equiv_SKIP dim n) by assumption.
      apply X_X_id.
      apply finalize_dnr.
      apply FSet.remove_1; auto.
    + rewrite (finalize_unfold n (FSet.add n qs)); auto.
      unfold X.
      rewrite (does_not_reference_commutes_app1 _ URzQ_X).
      apply_app_congruence.
      apply finalize_equal.
      apply FSetProps.remove_add; auto.
      apply finalize_dnr.
      apply FSet.remove_1; auto.
      apply FSet.add_1; auto.
  - (* Rz case *)
    bdestruct (FSet.mem n qs); rewrite IHl by assumption; simpl.
    + rewrite (cons_to_app _ l).
      apply_app_congruence_cong.
      specialize (@finalize_unfold dim n qs H) as unf.
      apply uc_equiv_cong_l in unf.
      rewrite unf.
      assert (@does_not_reference _ dim (finalize (FSet.remove n qs)) n = true).
      apply finalize_dnr.
      apply FSet.remove_1; auto.
      specialize (@does_not_reference_commutes_app1 dim (finalize (FSet.remove n qs)) (URzQ_Rz a) n H0) as comm.
      apply uc_equiv_cong_l in comm.
      rewrite <- app_assoc.
      rewrite <- comm.
      apply_app_congruence_cong.
      unfold uc_cong_l. simpl. 
      erewrite uc_seq_cong.
      2: { apply uc_equiv_cong.
           specialize (@invert_rotation_semantics dim a n) as tmp. 
           simpl in tmp. rewrite SKIP_id_r in tmp.
           apply tmp. }
      2: apply uc_equiv_cong; apply SKIP_id_r.      
      erewrite (uc_seq_cong _ _ (_ ; _)).
      2: reflexivity.
      2: apply uc_equiv_cong; apply SKIP_id_r.
      symmetry.
      apply X_comm_Rz.  
    + apply uc_equiv_cong_l.
      rewrite (cons_to_app _ l).
      apply_app_congruence.
      apply does_not_reference_commutes_app1.
      apply finalize_dnr; auto.
  - (* CNOT case *)
    rewrite IHl by assumption. 
    simpl.
    rewrite (cons_to_app _ l).
    apply uc_equiv_cong_l.
    apply_app_congruence.
    bdestruct (FSet.mem n qs).
    + bdestruct (FSet.mem n0 qs).
      * rewrite (finalize_unfold n0 qs) by assumption.
        rewrite (finalize_unfold n (FSet.remove n0 qs)).
        repeat rewrite <- app_assoc.
        rewrite <- does_not_reference_commutes_app2.
        apply_app_congruence.
        rewrite (uc_app_congruence [X n0] [X n0] _ ([CNOT n n0] ++ [X n] ++ [X n0])).
        2: reflexivity.
        2: { unfold_uc_equiv_l.
             apply X_comm_CNOT_control. }
        rewrite app_assoc.
        rewrite (uc_app_congruence ([X n0] ++ [CNOT n n0]) ([CNOT n n0] ++ [X n0]) _ ([X n] ++ [X n0])).
        2: { unfold_uc_equiv_l.
             apply X_comm_CNOT_target. }
        2: reflexivity.
        unfold X.
        rewrite does_not_reference_commutes_app1.
        rewrite <- (app_nil_r [CNOT n n0]) at 1.
        apply_app_congruence.
        unfold uc_equiv_l; simpl.
        rewrite SKIP_id_r.
        rewrite <- (ID_equiv_SKIP dim n0) by assumption.
        symmetry.
        apply X_X_id.
        simpl.
        apply andb_true_intro; split; auto.
        rewrite negb_true_iff. 
        apply eqb_neq; auto.
        apply finalize_dnr.
        apply FSet.remove_1; auto.
        apply finalize_dnr.
        intro contra.
        apply FSet.remove_3 in contra.
        contradict contra.
        apply FSet.remove_1; auto.
        apply FSet.remove_2; auto.
      * rewrite (finalize_unfold n0 (FSet.add n0 qs)); auto.
        erewrite finalize_equal.
        2: apply FSetProps.remove_add; auto.
        rewrite (finalize_unfold n qs); auto.
        rewrite <- app_assoc.
        rewrite <- does_not_reference_commutes_app2.
        apply_app_congruence.
        unfold X.
        rewrite (does_not_reference_commutes_app1 _ _ n0).     
        unfold_uc_equiv_l.
        symmetry.
        apply X_comm_CNOT_control.
        simpl.
        apply andb_true_intro; split; auto.
        rewrite negb_true_iff. 
        apply eqb_neq; auto.
        apply finalize_dnr.
        apply FSet.remove_1; auto.
        apply finalize_dnr.
        intro contra.
        apply FSet.remove_3 in contra.
        contradiction.
        apply FSet.add_1; auto.
    + bdestruct (FSet.mem n0 qs).
      * rewrite (finalize_unfold n0 qs) by assumption.
        rewrite <- app_assoc.
        rewrite <- does_not_reference_commutes_app2.
        apply_app_congruence.   
        unfold_uc_equiv_l.
        symmetry.
        apply X_comm_CNOT_target.
        apply finalize_dnr.
        intro contra.
        apply FSet.remove_3 in contra.
        contradiction.
        apply finalize_dnr.
        apply FSet.remove_1; auto.
      * apply does_not_reference_commutes_app2.
        apply finalize_dnr; auto.
        apply finalize_dnr; auto.
Qed.

Lemma not_propagation_sound : forall {dim} (l : RzQ_ucom_l dim), 
  uc_well_typed_l l -> not_propagation l ≅l≅ l.
Proof.
  intros.
  unfold not_propagation.
  rewrite not_propagation'_preserves_semantics; auto.
  rewrite finalize_empty.
  reflexivity.
Qed.

Lemma not_propagation_WT : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (not_propagation l).
Proof.
  intros dim l WT.
  specialize (not_propagation_sound l WT) as H.
  symmetry in H.
  apply uc_cong_l_implies_WT in H; assumption.
Qed.
