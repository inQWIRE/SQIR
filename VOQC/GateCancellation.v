Require Import SQIR.UnitarySem.
Require Export RzQGateSet.
Require Import List.
Require Import MappingConstraints.
Import RzQList.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.


(**********************************************************************)
(** Optimization: simple cancellation and combination w/ commutation **)
(**********************************************************************)

(* Cancel and combine gates, checking for cancellations across commuting 
   subcircuits. We determine whether a gate commutes through a subcircuit 
   using the following circuits identities from Nam et al.

   - Rz b ; H b ; CNOT a b ; H b ≡ H b ; CNOT a b ; H b ; Rz b
   - Rz b ; CNOT a b ; Rz' b ; CNOT a b ≡ CNOT a b ; Rz' b ; CNOT a b ; Rz b
   - Rz a ; CNOT a b ≡ CNOT a b ; Rz a
   - X b ; CNOT a b ≡ CNOT a b ; X b
   - CNOT a c ; CNOT b c ≡ CNOT b c ; CNOT a c
   - CNOT a c ; CNOT a b ≡ CNOT a b ; CNOT a c
   - CNOT a b; H b; CNOT b c; H b ≡ H b; CNOT b c; H b; CNOT a b

   This optimization should have the same behavior as Nam et al.'s single/
   two-qubit gate cancellation routines (with some added 'not propagation').
*)

(** Propagation rules for Rz **)
Definition Rz_commute_rule1 {dim} q (l : RzQ_ucom_l dim) :=
  match (next_single_qubit_gate l q) with
  | Some (l1, URzQ_H, l2) => 
      match (next_two_qubit_gate l2 q) with
      | Some (l3, URzQ_CNOT, q1, q2, l4) =>
          if q =? q2
          then match (next_single_qubit_gate l4 q) with
               | Some (l5, URzQ_H, l6) => Some (l1 ++ [H q] ++ l3 ++ [CNOT q1 q] ++ l5 ++ [H q], l6) 
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition Rz_commute_rule2 {dim} q (l : RzQ_ucom_l dim) :=
  match (next_two_qubit_gate l q) with
  | Some (l1, URzQ_CNOT, q1, q2, l2) => 
      if q =? q2
      then match (next_single_qubit_gate l2 q) with
           | Some (l3, URzQ_Rz _ as u, l4) =>
               match (next_two_qubit_gate l4 q) with
               | Some (l5, URzQ_CNOT, q3, q4, l6) => 
                   if (q =? q4) && (q1 =? q3) && (does_not_reference (l3 ++ l5) q3)
                   then Some (l1 ++ [CNOT q1 q] ++ l3 ++ [App1 u q] ++ l5 ++ [CNOT q1 q], l6)
                   else None 
               | _ => None
               end
           | _ => None
           end
      else None
  | _ => None
  end.


Definition Rz_commute_rule3 {dim} q (l : RzQ_ucom_l dim) :=
  match (next_two_qubit_gate l q) with
  | Some (l1, URzQ_CNOT, q1, q2, l2) => 
      if q =? q1
      then Some (l1 ++ [CNOT q1 q2], l2)
      else None
  | _ => None
  end.

Definition Rz_commute_rules {dim} q :=
  @Rz_commute_rule1 dim q :: Rz_commute_rule2 q :: Rz_commute_rule3 q :: [].

Definition Rz_cancel_rule {dim} q a (l : RzQ_ucom_l dim) :=
  match (next_single_qubit_gate l q) with
  | Some (l1, URzQ_Rz a', l2) =>
      Some ((combine_rotations a a' q) ++ l1 ++ l2)
  | _ => None
  end.

(** Propagation rules for H **)
(* (Currently no  rules for commuting.) *)

Definition H_cancel_rule {dim} q (l : RzQ_ucom_l dim)  :=
  match next_single_qubit_gate l q with
  | Some (l1, URzQ_H, l2) => Some (l1 ++ l2)
  | _ => None
  end.

(** Propagation rules for X **)

Definition X_commute_rule {dim} q (l : RzQ_ucom_l dim) :=
  match (next_two_qubit_gate l q) with
  | Some (l1, URzQ_CNOT, q1, q2, l2) => 
      if q =? q2
      then Some (l1 ++ [CNOT q1 q2], l2)
      else None
  | _ => None
  end.

Definition X_cancel_rule {dim} q (l : RzQ_ucom_l dim) :=
  match (next_single_qubit_gate l q) with
  | Some (l1, URzQ_X, l2) => Some (l1 ++ l2)
  | _ => None
  end.

(** Propagation rules for CNOT **)

Definition CNOT_commute_rule1 {dim} q1 (l : RzQ_ucom_l dim) : option (RzQ_ucom_l dim * RzQ_ucom_l dim) :=
  match (next_single_qubit_gate l q1) with
  | Some (l1, URzQ_Rz _ as u, l2) => Some ([App1 u q1], l1 ++ l2)
  | _ => None
  end.

Definition CNOT_commute_rule2 {dim} q1 q2 (l : RzQ_ucom_l dim) :=
  match (next_two_qubit_gate l q2) with
  | Some (l1, URzQ_CNOT, q1', q2', l2) => 
      if q2 =? q2'
      then if (does_not_reference l1 q1)
           then Some (l1 ++ [CNOT q1' q2], l2)
           else None
      else None
  | _ => None
  end.

Definition CNOT_commute_rule3 {dim} q1 q2 (l : RzQ_ucom_l dim) :=
  match (next_two_qubit_gate l q1) with
  | Some (l1, URzQ_CNOT, q1', q2', l2) => 
      if q1 =? q1'
      then if (does_not_reference l1 q2)
           then Some (l1 ++ [CNOT q1 q2'], l2)
           else None
      else None
  | _ => None
  end.

Definition CNOT_commute_rule4 {dim} q1 q2 (l : RzQ_ucom_l dim) :=
  match (next_single_qubit_gate l q2) with
  | Some (l1, URzQ_H, l2) => 
      match (next_two_qubit_gate l2 q2) with
      | Some (l3, URzQ_CNOT, q1', q2', l4) => 
          if (q2 =? q1') && (¬ (q1 =? q2')) && (does_not_reference (l1 ++ l3) q1)
          then match (next_single_qubit_gate l4 q2) with
               | Some (l5, URzQ_H, l6) => Some (l1 ++ [H q2] ++ l3 ++ [CNOT q2 q2'] ++ [H q2], l5 ++ l6)
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition CNOT_commute_rule5 {dim} q1 q2 (l : RzQ_ucom_l dim) :=
  match next_single_qubit_gate l q2 with
  | Some (l1, URzQ_Rz _ as u, l2) =>
      match next_two_qubit_gate l2 q2 with
      | Some (l3, URzQ_CNOT, q1', q2', l4) =>
          if (q1 =? q1') && (q2 =? q2') && (does_not_reference (l1 ++ l3) q1)
          then match next_single_qubit_gate l4 q2 with
               | Some (l5, URzQ_Rz _ as u', l6) =>
                   Some (l1 ++ [App1 u' q2] ++ l3 ++ [CNOT q1' q2'] ++ [App1 u q2], l5 ++ l6) 
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition CNOT_commute_rules {dim} q1 q2 :=
  @CNOT_commute_rule1 dim q1 :: CNOT_commute_rule2 q1 q2 :: CNOT_commute_rule3 q1 q2 :: CNOT_commute_rule4 q1 q2 :: CNOT_commute_rule5 q1 q2 :: [].

Definition CNOT_cancel_rule {dim} q1 q2 (l : RzQ_ucom_l dim) :=
  match next_two_qubit_gate l q1 with
  | Some (l1, URzQ_CNOT, q1', q2', l2) => 
      if (q1 =? q1') && (q2 =? q2') && (does_not_reference l1 q2)
      then Some (l1 ++ l2)
      else None
  | _ => None
  end.

(** Gate Cancellation Routines **)
Definition propagate_Rz {dim} a (l : RzQ_ucom_l dim) q :=
  propagate l (Rz_commute_rules q) [Rz_cancel_rule q a] (length l).

Definition propagate_H {dim} (l : RzQ_ucom_l dim) q :=
  propagate l [] [H_cancel_rule q] 1%nat.

Definition propagate_X {dim} (l : RzQ_ucom_l dim) q :=
  propagate l [X_commute_rule q] [X_cancel_rule q] (length l).

Definition propagate_CNOT {dim} (l : RzQ_ucom_l dim) (q1 q2 : nat) :=
  propagate l (CNOT_commute_rules q1 q2) [CNOT_cancel_rule q1 q2] (length l).

Fixpoint cancel_single_qubit_gates' {dim} (l : RzQ_ucom_l dim) (n: nat) acc : RzQ_ucom_l dim :=
  match n with
  | 0 => rev_append acc l
  | S n' => match l with
           | App1 (URzQ_Rz a) q :: t => 
               match propagate_Rz a t q with
               | None => cancel_single_qubit_gates' t n' (Rzq a q :: acc)
               | Some l' => cancel_single_qubit_gates' l' n' acc
               end
           | App1 URzQ_H q :: t => 
               match propagate_H t q with
               | None => cancel_single_qubit_gates' t n' (H q :: acc)
               | Some l' => cancel_single_qubit_gates' l' n' acc
               end
           | App1 URzQ_X q :: t => 
               match propagate_X t q  with
               | None => cancel_single_qubit_gates' t n' (X q :: acc)
               | Some l' => cancel_single_qubit_gates' l' n' acc
               end
           | u :: t => cancel_single_qubit_gates' t n' (u :: acc)
           | [] => rev_append acc []
           end
  end.

Definition cancel_single_qubit_gates {dim} (l : RzQ_ucom_l dim) := 
  cancel_single_qubit_gates' l (length l) [].

Fixpoint cancel_two_qubit_gates' {dim} (l : RzQ_ucom_l dim) (n: nat) acc : RzQ_ucom_l dim :=
  match n with
  | 0 => rev_append acc l
  | S n' => match l with
           | App2 URzQ_CNOT q1 q2 :: t => 
               match propagate_CNOT t q1 q2 with
               | None => cancel_two_qubit_gates' t n' (CNOT q1 q2 :: acc)
               | Some l' => cancel_two_qubit_gates' l' n' acc
               end
           | u :: t => cancel_two_qubit_gates' t n' (u :: acc)
           | [] => rev_append acc []
           end
  end.

Definition cancel_two_qubit_gates {dim} (l : RzQ_ucom_l dim) := 
  cancel_two_qubit_gates' l (length l) [].

(** semantics preservation **)

Lemma propagate_Rz_sound : forall {dim} a (l : RzQ_ucom_l dim) q l',
  q < dim ->
  propagate_Rz a l q = Some l' ->
  Rzq a q :: l =l= l'.
Proof.
  unfold propagate_Rz.
  intros dim a l q l' Hq res.
  apply (propagate_preserves_semantics l (Rz_commute_rules q) [Rz_cancel_rule q a] (length l)). 5: apply res.
  apply uc_equiv_l_rel.
  apply uc_app_mor_Proper.
  - clear l l' res.
    intros rules Hin l l' res.
    destruct_In; subst.
    unfold Rz_cancel_rule in res.
    destruct_list_ops.
    rewrite app_assoc.
    rewrite <- does_not_reference_commutes_app1 by assumption.
    rewrite combine_rotations_semantics by assumption.
    reflexivity.
  - clear l l' res Hq.
    intros rules Hin l l1 l2 res.
    destruct_In; subst.
    + unfold Rz_commute_rule1 in res.
      destruct_list_ops.
      rewrite cons_to_app. 
      rewrite (cons_to_app _ (g2 ++ _)).
      rewrite (cons_to_app _ (g4 ++ _)).
      repeat rewrite app_assoc.
      setoid_rewrite (does_not_reference_commutes_app1 g0 (URzQ_Rz a)); auto.
      rewrite <- (app_assoc _ _ g2).
      rewrite (does_not_reference_commutes_app1 g2 URzQ_H) by assumption.
      rewrite (app_assoc _ g2), <- (app_assoc _ _ g2).
      rewrite (does_not_reference_commutes_app1 g2 (URzQ_Rz a)) by assumption.
      rewrite <- (app_assoc _ g4).
      rewrite <- (does_not_reference_commutes_app1 g4 URzQ_H) by assumption.
      rewrite <- (app_assoc _ _ g2). 
      setoid_rewrite (does_not_reference_commutes_app1 g2 URzQ_H); auto.
      rewrite <- (app_assoc _ g4).
      setoid_rewrite <- (does_not_reference_commutes_app1 g4 URzQ_H); auto.
      rewrite <- 2 (app_assoc _ _ [Rzq a n]).
      setoid_rewrite <- (does_not_reference_commutes_app1 g4 (URzQ_Rz a)); auto.
      apply_app_congruence.
      unfold_uc_equiv_l.
      apply Rz_comm_H_CNOT_H.
    + unfold Rz_commute_rule2 in res.
      destruct_list_ops.
      destruct (does_not_reference (g2 ++ g3) n2) eqn:dnr; try discriminate.
      apply does_not_reference_app in dnr.
      apply andb_true_iff in dnr as [? ?].
      inversion res; clear res; subst.
      rewrite cons_to_app. 
      rewrite (cons_to_app _ (g2 ++ _)).
      rewrite (cons_to_app _ (g3 ++ _)).
      repeat rewrite app_assoc.
      setoid_rewrite (does_not_reference_commutes_app1 g0 (URzQ_Rz a)); auto.
      rewrite <- (app_assoc _ _ g2).
      rewrite does_not_reference_commutes_app2 by assumption.
      rewrite (app_assoc _ g2), <- (app_assoc _ _ g2).
      rewrite does_not_reference_commutes_app1 by assumption.
      rewrite <- (app_assoc _ g3).
      rewrite <- (does_not_reference_commutes_app2 g3) by assumption.
      rewrite <- (app_assoc _ _ g2).
      setoid_rewrite (does_not_reference_commutes_app2 g2); auto.
      rewrite <- (app_assoc _ g3).
      setoid_rewrite <- (does_not_reference_commutes_app2 g3); auto.
      rewrite <- (app_assoc _ (_ ++ g3) [Rzq a n1]), <- (app_assoc _ g3).
      setoid_rewrite <- (does_not_reference_commutes_app1 g3); auto.
      apply_app_congruence.
      unfold_uc_equiv_l.
      apply Rz_comm_CNOT_Rz_CNOT.
    + unfold Rz_commute_rule3 in res.
      destruct_list_ops.
      rewrite cons_to_app.
      repeat rewrite app_assoc.
      setoid_rewrite (does_not_reference_commutes_app1 g0); auto.
      apply_app_congruence.
      unfold_uc_equiv_l.
      apply Rz_comm_CNOT.
Qed.

Lemma propagate_Rz_WT : forall {dim} a (l : RzQ_ucom_l dim) q l',
  q < dim ->
  uc_well_typed_l l ->
  propagate_Rz a l q = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_Rz_sound a l q l' H H1) as H2.
  apply (uc_equiv_l_implies_WT _ _ H2).
  constructor; assumption.
Qed.

Lemma propagate_H_sound : forall {dim} (l : RzQ_ucom_l dim) q l',
  q < dim ->
  propagate_H l q = Some l' ->
  H q :: l =l= l'.
Proof. 
  unfold propagate_H.
  intros dim l q l' Hq res.
  eapply propagate_preserves_semantics; try apply res.
  apply uc_equiv_l_rel.
  apply uc_app_mor_Proper.
  - clear l l' res.
    intros rules Hin l l' res.
    destruct_In; subst.
    unfold H_cancel_rule in res.
    destruct_list_ops.
    rewrite app_assoc.
    rewrite <- does_not_reference_commutes_app1 by assumption.
    rewrite cons_to_app. 
    rewrite <- app_nil_l.
    apply_app_congruence.
    unfold_uc_equiv_l.
    rewrite <- (ID_equiv_SKIP dim q) by assumption.
    apply H_H_id.
  - clear l l' res.
    intros rules Hin l l' res.
    destruct_In.
Qed.

Lemma propagate_H_WT : forall {dim} (l : RzQ_ucom_l dim) q l',
  q < dim ->
  uc_well_typed_l l -> 
  propagate_H l q = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_H_sound l q l' H H1) as H2.
  apply (uc_equiv_l_implies_WT _ _ H2).
  constructor; assumption.
Qed.

Lemma propagate_X_sound : forall {dim} (l : RzQ_ucom_l dim) q l',
  q < dim ->
  propagate_X l q = Some l' ->
  X q :: l =l= l'.
Proof.
  unfold propagate_X.
  intros dim l q l' Hq res.
  eapply propagate_preserves_semantics; try apply res.
  apply uc_equiv_l_rel.
  apply uc_app_mor_Proper.
  - clear l l' res.
    intros rules Hin l l' res.
    destruct_In; subst.
    unfold X_cancel_rule in res.
    destruct_list_ops.
    rewrite app_assoc.
    rewrite <- does_not_reference_commutes_app1 by assumption.
    rewrite cons_to_app. 
    rewrite <- app_nil_l.
    apply_app_congruence.
    unfold_uc_equiv_l.
    rewrite <- (ID_equiv_SKIP dim q) by assumption.
    apply X_X_id.
  - clear l l' res Hq.
    intros rules Hin l l1 l2 res.
    destruct_In; subst.
    unfold X_commute_rule in res.
    destruct_list_ops.
    rewrite cons_to_app.
    repeat rewrite app_assoc.
    setoid_rewrite (does_not_reference_commutes_app1 g0); auto.
    apply_app_congruence.
    unfold_uc_equiv_l.
    apply X_comm_CNOT_target.
Qed.

Lemma propagate_X_WT : forall {dim} (l : RzQ_ucom_l dim) q l',
  q < dim ->
  uc_well_typed_l l ->
  propagate_X l q = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_X_sound l q l' H H1) as H2.
  apply (uc_equiv_l_implies_WT _ _ H2).
  constructor; assumption.
Qed.

Lemma propagate_CNOT_sound : forall {dim} (l : RzQ_ucom_l dim) q1 q2 l',
  q1 < dim ->
  q2 < dim -> 
  q1 <> q2 ->
  propagate_CNOT l q1 q2 = Some l' ->
  CNOT q1 q2 :: l =l= l'.
Proof.
  unfold propagate_CNOT.
  intros dim l q1 q2 l' Hq1 Hq2 Hq1q2 res.
  eapply propagate_preserves_semantics; try apply res.
  apply uc_equiv_l_rel.
  apply uc_app_mor_Proper.
  - clear l l' res.
    intros rules Hin l l' res.
    destruct_In; subst.
    unfold CNOT_cancel_rule in res.
    destruct_list_ops.
    destruct (does_not_reference g0 n) eqn:?; try discriminate.
    inversion res; subst; clear res.
    rewrite app_assoc.
    rewrite <- does_not_reference_commutes_app2 by assumption.
    rewrite cons_to_app. 
    rewrite <- app_nil_l.
    apply_app_congruence.
    unfold_uc_equiv_l.
    apply CNOT_CNOT_id; assumption.
  - clear l l' res.
    intros rules Hin l l1 l2 res.
    destruct_In; subst.
    + unfold CNOT_commute_rule1 in res.
      destruct_list_ops.
      rewrite app_assoc.
      rewrite <- does_not_reference_commutes_app1 by assumption.
      rewrite cons_to_app.
      apply_app_congruence.
      symmetry.
      unfold_uc_equiv_l.
      apply Rz_comm_CNOT.
    + unfold CNOT_commute_rule2 in res.
      destruct_list_ops.
      destruct (does_not_reference g0 q1) eqn:?; try discriminate.
      inversion res; subst; clear res.
      rewrite cons_to_app.
      repeat rewrite app_assoc.
      setoid_rewrite (does_not_reference_commutes_app2 g0); auto.
      apply_app_congruence.
      unfold_uc_equiv_l.
      apply CNOT_comm_CNOT_sharing_target.
    + unfold CNOT_commute_rule3 in res.
      destruct_list_ops.
      destruct (does_not_reference g0 q2) eqn:?; try discriminate.
      inversion res; subst; clear res.
      rewrite cons_to_app.
      repeat rewrite app_assoc.
      setoid_rewrite (does_not_reference_commutes_app2 g0); auto.
      apply_app_congruence.
      unfold_uc_equiv_l.
      apply CNOT_comm_CNOT_sharing_control.
    + unfold CNOT_commute_rule4 in res.
      destruct_list_ops; simpl in res.
      destruct (does_not_reference (g0 ++ g2) q1) eqn:dnr; try discriminate.
      destruct_list_ops.
      apply does_not_reference_app in dnr.
      apply andb_true_iff in dnr as [? ?].
      rewrite cons_to_app.
      rewrite (cons_to_app _ (g2 ++ _)).
      rewrite (cons_to_app _ [_]).
      repeat rewrite app_assoc.
      setoid_rewrite (does_not_reference_commutes_app2 g0); auto.
      rewrite <- (app_assoc _ _ g2).
      rewrite does_not_reference_commutes_app1 by assumption.
      rewrite <- (app_assoc _ _ (g2 ++ _)), (app_assoc _ g2).
      rewrite (does_not_reference_commutes_app2 g2) by assumption.
      rewrite <- (app_assoc _ g3).
      rewrite <- (does_not_reference_commutes_app1 g3) by assumption.
      rewrite <- (app_assoc _ _ g2).
      setoid_rewrite (does_not_reference_commutes_app1 g2); auto.
      apply_app_congruence.
      unfold_uc_equiv_l.
      apply CNOT_comm_H_CNOT_H. 
      assumption.
    + unfold CNOT_commute_rule5 in res.
      destruct_list_ops.
      destruct (does_not_reference (g0 ++ g2) n0) eqn:dnr; try discriminate.
      simpl in res.
      destruct_list_ops.
      apply does_not_reference_app in dnr.
      apply andb_true_iff in dnr as [? ?].
      rewrite cons_to_app.
      rewrite (cons_to_app _ (g2 ++ _)).
      rewrite (cons_to_app _ [_]).
      repeat rewrite app_assoc.
      setoid_rewrite (does_not_reference_commutes_app2 g0); auto.
      rewrite <- (app_assoc _ _ g2).
      rewrite does_not_reference_commutes_app1 by assumption.
      rewrite <- (app_assoc _ _ (g2 ++ _)), (app_assoc _ g2).
      rewrite (does_not_reference_commutes_app2 g2) by assumption.
      rewrite <- (app_assoc _ g3).
      rewrite <- (does_not_reference_commutes_app1 g3) by assumption.
      rewrite <- (app_assoc _ _ g2).
      setoid_rewrite (does_not_reference_commutes_app1 g2); auto.
      apply_app_congruence.
      symmetry.
      unfold_uc_equiv_l.
      apply Rz_comm_CNOT_Rz_CNOT.   
Qed.

Lemma propagate_CNOT_WT : forall {dim} (l : RzQ_ucom_l dim) q1 q2 l',
  q1 < dim ->
  q2 < dim -> 
  q1 <> q2 ->
  uc_well_typed_l l ->
  propagate_CNOT l q1 q2 = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_CNOT_sound l q1 q2 l' H H0 H1 H3) as H4.
  apply (uc_equiv_l_implies_WT _ _ H4).
  constructor; assumption.
Qed.

Lemma cancel_single_qubit_gates_sound : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> cancel_single_qubit_gates l =l= l.
Proof.
  intros dim l WT.
  assert (H: forall n acc, cancel_single_qubit_gates' l n acc =l= rev acc ++ l).
  { intros n.
    generalize dependent l.
    induction n; intros l WT acc; simpl. 
    rewrite rev_append_rev. reflexivity.
    destruct l; simpl.
    rewrite rev_append_rev. reflexivity.
    destruct g as [u | | u]; inversion WT; subst.
    - dependent destruction u.
      + destruct (propagate_H l n0) eqn:prop.
        rewrite (propagate_H_sound _ _ _ H1 prop).
        apply IHn.
        apply (propagate_H_WT _ _ _ H1 H3 prop).
        rewrite IHn; auto.
        simpl. rewrite <- app_assoc. reflexivity.
      + destruct (propagate_X l n0) eqn:prop.
        rewrite (propagate_X_sound _ _ _ H1 prop).
        apply IHn.
        apply (propagate_X_WT _ _ _ H1 H3 prop).
        rewrite IHn; auto.
        simpl. rewrite <- app_assoc. reflexivity.
      + destruct (propagate_Rz a l n0) eqn:prop.
        rewrite (propagate_Rz_sound _ _ _ _ H1 prop).
        apply IHn.
        apply (propagate_Rz_WT _ _ _ _ H1 H3 prop).
        rewrite IHn; auto.
        simpl. rewrite <- app_assoc. reflexivity.
    - rewrite IHn; auto. 
      simpl. rewrite <- app_assoc. reflexivity.
    - inversion u. }
  apply H.
Qed.

Lemma cancel_single_qubit_gates_WT: forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (cancel_single_qubit_gates l).
Proof.
  intros dim l WT.
  specialize (cancel_single_qubit_gates_sound l WT) as H.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H; assumption.
Qed.

Lemma cancel_two_qubit_gates_sound : forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> cancel_two_qubit_gates l =l= l.
Proof.
  intros dim l WT.
  assert (H : forall n acc, cancel_two_qubit_gates' l n acc =l= rev acc ++ l).
  { intros n.
    generalize dependent l.
    induction n; intros l WT acc; simpl. 
    rewrite rev_append_rev. reflexivity.
    destruct l; simpl.
    rewrite rev_append_rev. reflexivity.
    destruct g as [ | u | u]; inversion WT; subst.
    - rewrite IHn; auto. 
      simpl. rewrite <- app_assoc. reflexivity.
    - dependent destruction u.
      destruct (propagate_CNOT l n0 n1) eqn:prop.
      rewrite (propagate_CNOT_sound _ _ _ _ H3 H4 H5 prop).
      apply IHn.
      apply (propagate_CNOT_WT _ _ _ _ H3 H4 H5 H6 prop).
      rewrite IHn; auto. 
      simpl. rewrite <- app_assoc. reflexivity.
    - inversion u. }
  apply H.
Qed.

Lemma cancel_two_qubit_gates_WT: forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (cancel_two_qubit_gates l).
Proof.
  intros dim l WT.
  specialize (cancel_two_qubit_gates_sound l WT) as H.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H; assumption.
Qed.

(** mapping preservation **)

Lemma Rz_commute_rule1_respects_constraints: forall {dim} q  (in_l out_l1 out_l2 : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool) , 
  respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
  @Rz_commute_rule1 dim q in_l = Some (out_l1, out_l2) ->
  respects_constraints_directed is_in_graph URzQ_CNOT out_l1
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold Rz_commute_rule1 in H0.
  repeat destruct_matches. 
  assert_and_prove_next_gate.  
  destruct H1 as [respects_g0 respects_g].
  assert_and_prove_next_gate.
  destruct H1 as [respects_g2 [respects_g1 iiggn0n]].
  assert_and_prove_next_gate.
  destruct H1 as [respects_g4 respects_g3].    
  split.
  - inversion H0; subst.
    repeat (try apply respects_constraints_directed_app; auto; try constructor).
    symmetry in HeqH2.
    rewrite Nat.eqb_eq in HeqH2.
    subst.
    assumption.
  - inversion H0; subst.
    assumption. 
Qed.

Lemma Rz_commute_rule2_respects_constraints: forall {dim} q (in_l out_l1 out_l2 : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool), 
  respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
  @Rz_commute_rule2 dim q in_l = Some (out_l1, out_l2) ->
  respects_constraints_directed is_in_graph URzQ_CNOT out_l1
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof. 
  intros.
  unfold Rz_commute_rule2 in H0.
  repeat destruct_matches. 
  assert_and_prove_next_gate.
  destruct H1 as  [respects_g0 [respects_g iiggn0n]].
  assert_and_prove_next_gate.
  destruct H1 as [respects_g2 respects_g1].
  assert_and_prove_next_gate. 
  destruct H1 as  [respects_g4 [respects_g3 iiggn2n1]].
  symmetry in HeqH0.
  rewrite Nat.eqb_eq in HeqH0.
  subst.
  split; inversion H0; subst;
  repeat (try apply respects_constraints_directed_app; try constructor; auto).
Qed.   

Lemma Rz_commute_rule3_respects_constraints: forall {dim} q  (in_l out_l1 out_l2 : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool), 
  respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
  @Rz_commute_rule3 dim q in_l = Some (out_l1, out_l2) ->
  respects_constraints_directed is_in_graph URzQ_CNOT out_l1 
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold Rz_commute_rule3 in H0.
  repeat destruct_matches. 
  assert_and_prove_next_gate. 
  destruct H1 as  [respects_g4 [respects_g3 iiggn2n1]].
  split;
  inversion H0; subst; 
  repeat (try apply respects_constraints_directed_app; try constructor; auto).
Qed.

Lemma X_commute_rule_respects_constraints: forall {dim} q (in_l out_l1 out_l2 : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool), 
  respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
  @X_commute_rule dim q in_l = Some (out_l1, out_l2) ->
  respects_constraints_directed is_in_graph URzQ_CNOT out_l1 
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold X_commute_rule in H0.
  repeat destruct_matches. 
  assert_and_prove_next_gate.
  destruct H1 as  [respects_g4 [respects_g3 iiggn2n1]].
  split; inversion H0; subst;
  repeat (try apply respects_constraints_directed_app; auto; try constructor).
Qed.

Lemma CNOT_commute_rule1_respects_constraints: forall {dim} q (in_l out_l1 out_l2 : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool), 
  respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
  @CNOT_commute_rule1 dim q in_l = Some (out_l1, out_l2) ->
  respects_constraints_directed is_in_graph URzQ_CNOT out_l1 
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold CNOT_commute_rule1 in H0.
  repeat destruct_matches. 
  assert_and_prove_next_gate.
  destruct H1. 
  split;
    inversion H0; subst; 
      repeat (try apply respects_constraints_directed_app; auto; try constructor).
Qed.

Lemma CNOT_commute_rule2_respects_constraints: forall {dim} q1 q2 (in_l out_l1 out_l2 : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool), 
  respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
  @CNOT_commute_rule2 dim q1 q2 in_l = Some (out_l1, out_l2) ->
  respects_constraints_directed is_in_graph URzQ_CNOT out_l1 
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold CNOT_commute_rule2 in H0.
  repeat destruct_matches.
  assert_and_prove_next_gate. 
  destruct H1 as [respects_g0 [ respects_g is_in_graphn0n]].
  split;
    inversion H0; subst; 
      repeat (try apply respects_constraints_directed_app; auto; try constructor).  
  symmetry in HeqH0.
  rewrite Nat.eqb_eq in HeqH0.
  subst. 
  assumption.
Qed.

Lemma CNOT_commute_rule3_respects_constraints: forall {dim} q1 q2 (in_l out_l1 out_l2 : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool), 
  respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
  @CNOT_commute_rule3 dim q1 q2 in_l = Some (out_l1, out_l2) ->
  respects_constraints_directed is_in_graph URzQ_CNOT out_l1 
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold CNOT_commute_rule3 in H0.
  repeat destruct_matches.
  assert_and_prove_next_gate. 
  destruct H1 as [respects_g0 [ respects_g is_in_graphn0n]].
  split;
    inversion H0; subst; 
      repeat (try apply respects_constraints_directed_app; auto; try constructor).
  symmetry in HeqH0.
  rewrite Nat.eqb_eq in HeqH0.
  subst. 
  assumption.
Qed.

Lemma CNOT_commute_rule4_respects_constraints: forall {dim} q1 q2  (in_l out_l1 out_l2 : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool), 
  respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
  @CNOT_commute_rule4 dim q1 q2 in_l = Some (out_l1, out_l2) ->
  respects_constraints_directed is_in_graph URzQ_CNOT out_l1
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold CNOT_commute_rule4 in H0.
  repeat destruct_matches.
  assert_and_prove_next_gate. 
  destruct H1 as [respects_g0 respects_g].
  assert_and_prove_next_gate. 
  destruct H1 as [respects_g2  [respects_g1 is_in_n0_n]].
  assert_and_prove_next_gate. 
  destruct H1 as [respects_g4  respects_g3].
  split;
    inversion H0; subst; 
      repeat (try apply respects_constraints_directed_app; auto; try constructor).
  symmetry in HeqH2.
  rewrite <- andb_assoc in HeqH2. 
  apply andb_true_iff in HeqH2.
  destruct HeqH2 as [q2n0 q1ndnrf].
  apply andb_true_iff in q1ndnrf.
  destruct q1ndnrf as [q1n dnr].
  rewrite Nat.eqb_eq in q2n0.
  subst.
  assumption. 
Qed.

Lemma CNOT_commute_rule5_respects_constraints: forall {dim} q1 q2  (in_l out_l1 out_l2 : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool), 
  respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
  @CNOT_commute_rule5 dim q1 q2 in_l = Some (out_l1, out_l2) ->
  respects_constraints_directed is_in_graph URzQ_CNOT out_l1
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold CNOT_commute_rule5 in H0.
  repeat destruct_matches.
  assert_and_prove_next_gate. 
  destruct H1 as [respects_g0  respects_g].
  assert_and_prove_next_gate.
  destruct H1 as [respects_g2  [respects_g1 is_in_n0_n]].
  assert_and_prove_next_gate. 
  destruct H1 as [respects_g4  respects_g3].
  split;
    inversion H0; subst; 
      repeat (try apply respects_constraints_directed_app; auto; try constructor).
Qed.

Lemma Rz_cancel_rule_respects_constraints: forall {dim} (is_in_graph : nat -> nat -> bool) a q, 
  @cancel_rules_respect_constraints dim _ [Rz_cancel_rule q a] is_in_graph URzQ_CNOT.
Proof.
  intros.
  unfold cancel_rules_respect_constraints.
  intros. 
  unfold Rz_cancel_rule in H.
  destruct_In.
  rewrite <- H2 in H1.
  repeat destruct_matches.
  assert_and_prove_next_gate. 
  destruct H as [respects_g0  respects_g].
  inversion H1.
  apply respects_constraints_directed_app.
  unfold combine_rotations.
  destruct (Qeq_bool (bound (a + a0)) zero_Q); repeat constructor.
  apply respects_constraints_directed_app.
  assumption.
  assumption. 
Qed.

Lemma H_cancel_rule_respects_constraints: forall {dim} (is_in_graph : nat -> nat -> bool) q, 
  @cancel_rules_respect_constraints dim _ [H_cancel_rule q] is_in_graph URzQ_CNOT.
Proof.
  intros.
  unfold cancel_rules_respect_constraints.
  intros. 
  unfold H_cancel_rule in H.
  destruct_In.
  rewrite <- H2 in H1.
  repeat destruct_matches. 
  assert_and_prove_next_gate.
  destruct H as [respects_g0  respects_g].
  inversion H1.
  apply respects_constraints_directed_app.
  assumption.
  assumption. 
Qed.

Lemma X_cancel_rule_respects_constraints: forall {dim} (is_in_graph : nat -> nat -> bool) q, 
  @cancel_rules_respect_constraints dim _ [X_cancel_rule q] is_in_graph URzQ_CNOT.
Proof.
  intros.
  unfold cancel_rules_respect_constraints.
  intros. 
  unfold X_cancel_rule in H.
  destruct_In.
  rewrite <- H2 in H1.
  repeat destruct_matches. 
  assert_and_prove_next_gate.
  destruct H as [respects_g0  respects_g].
  inversion H1.
  apply respects_constraints_directed_app.
  assumption.
  assumption. 
Qed.

Lemma CNOT_cancel_rule_respects_constraints: forall {dim} (is_in_graph : nat -> nat -> bool) q1 q2, 
  @cancel_rules_respect_constraints dim _ [CNOT_cancel_rule q1 q2] is_in_graph URzQ_CNOT.
Proof.
  intros.
  unfold cancel_rules_respect_constraints.
  intros. 
  unfold CNOT_cancel_rule in H.
  destruct_In.
  rewrite <- H2 in H1.
  repeat destruct_matches.
  assert_and_prove_next_gate. 
  destruct H as [respects_g0 [ respects_g is_inn0n]].
  inversion H1.
  apply respects_constraints_directed_app. 
  assumption.
  assumption. 
Qed.

Lemma Rz_commute_rules_respect_constraints: forall {dim} n (is_in_graph : nat -> nat -> bool), 
  @commute_rules_respect_constraints dim _ (Rz_commute_rules n) is_in_graph URzQ_CNOT.
Proof.
  intros.
  unfold commute_rules_respect_constraints.
  intros. 
  unfold Rz_commute_rules in H.
  destruct_In.
  - rewrite <- H2 in H1.
    eapply Rz_commute_rule1_respects_constraints.
    apply H0.
    apply H1.
  - rewrite <- H in H1. 
    eapply Rz_commute_rule2_respects_constraints.
    apply H0.
    apply H1. 
  - rewrite <-  H2 in H1. 
    eapply Rz_commute_rule3_respects_constraints.
    apply H0.
    apply H1. 
Qed.

Lemma CNOT_commute_rules_respect_constraints: forall {dim} n1 n2 (is_in_graph : nat -> nat -> bool), 
  @commute_rules_respect_constraints dim _ (CNOT_commute_rules n1 n2) is_in_graph URzQ_CNOT.
Proof.
  intros.
  unfold commute_rules_respect_constraints.
  intros. 
  unfold CNOT_commute_rules in H.
  destruct_In.
  - rewrite <- H2 in H1.
    eapply CNOT_commute_rule1_respects_constraints.
    apply H0.
    apply H1.
  - rewrite <- H in H1. 
    eapply CNOT_commute_rule2_respects_constraints.
    apply H0.
    apply H1. 
  - rewrite <-  H2 in H1. 
    eapply CNOT_commute_rule3_respects_constraints.
    apply H0.
    apply H1. 
  - rewrite <-  H in H1. 
    eapply CNOT_commute_rule4_respects_constraints.
    apply H0.
    apply H1. 
  - rewrite <-  H2 in H1. 
    eapply CNOT_commute_rule5_respects_constraints.
    apply H0.
    apply H1. 
Qed.

Lemma propagate_Rz_respects_constraints : forall {dim} a (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool) (q : nat) l',
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  propagate_Rz a l q = Some l' ->
  respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros. 
  unfold propagate_Rz in H0.
  eapply propagate_respects_constraints.
  apply H.
  apply Rz_cancel_rule_respects_constraints.
  apply Rz_commute_rules_respect_constraints.
  apply H0. 
Qed.

Lemma propagate_H_respects_constraints : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool) (q : nat) l',
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  propagate_H l q = Some l' ->
  respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros. 
  unfold propagate_H in H0.
  eapply propagate_respects_constraints.
  apply H.
  apply H_cancel_rule_respects_constraints.
  assert (@commute_rules_respect_constraints dim _ [] is_in_graph URzQ_CNOT).
  unfold commute_rules_respect_constraints.
  intros.
  destruct_In.
  apply H1. 
  apply H0. 
Qed.   

Lemma propagate_X_respects_constraints : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool) (q : nat) l',
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  propagate_X l q = Some l' ->
  respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros. 
  unfold propagate_X in H0.
  eapply propagate_respects_constraints.
  apply H.
  apply X_cancel_rule_respects_constraints.
  assert (@commute_rules_respect_constraints dim _ [X_commute_rule q] is_in_graph URzQ_CNOT).
  unfold commute_rules_respect_constraints.
  intros.
  destruct_In.
  rewrite <- H4 in H3. 
  eapply X_commute_rule_respects_constraints.
  apply H2.
  apply H3.
  apply H1.
  apply H0. 
Qed.

Lemma propagate_CNOT_respects_constraints : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool) (q1 q2 : nat) l',
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  propagate_CNOT l q1 q2 = Some l' ->
  respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros. 
  unfold propagate_Rz in H0.
  eapply propagate_respects_constraints.
  apply H.
  apply CNOT_cancel_rule_respects_constraints.
  apply CNOT_commute_rules_respect_constraints.
  apply H0. 
Qed.

Lemma cancel_single_qubit_gates'_respects_constraints : forall {dim} (l acc : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool) (n : nat) ,
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT acc ->
  respects_constraints_directed is_in_graph URzQ_CNOT (cancel_single_qubit_gates' l n acc).
Proof.
  intros.
  generalize dependent acc.
  generalize dependent l.
  induction n. 
  - intros.
    unfold cancel_single_qubit_gates'. rewrite rev_append_rev.
    apply respects_constraints_directed_app.
    apply rev_respects_constraints.
    assumption.
    assumption.
  - intros.
    destruct l.
    + apply rev_append_respects_constraints; assumption. 
    + simpl. destruct g; dependent destruction r; inversion H; subst.
      * destruct (propagate_H l n0) eqn:pH.  
        eapply IHn; try reflexivity; auto.
        eapply propagate_H_respects_constraints; try apply pH; auto.
        eapply IHn; try reflexivity; auto.
        constructor; auto.
      * destruct (propagate_X l n0) eqn:pX.  
        eapply IHn; try reflexivity; auto.
        eapply propagate_X_respects_constraints; try apply pX; auto.
        eapply IHn; try reflexivity; auto.
        constructor; auto.
      * destruct (propagate_Rz a l n0) eqn:pRz.  
        eapply IHn; try reflexivity; auto.
        eapply propagate_Rz_respects_constraints; try apply pRz; auto.
        eapply IHn; try reflexivity; auto.
        constructor; auto.
      * eapply IHn; try reflexivity; auto. 
        constructor; auto.
Qed. 

Lemma cancel_single_qubit_gates_respects_constraints : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool) ,
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (cancel_single_qubit_gates l).
Proof.
  intros.
  eapply cancel_single_qubit_gates'_respects_constraints.
  assumption.
  constructor.
Qed. 

Lemma cancel_two_qubit_gates'_respects_constraints : forall {dim} (l acc : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool) (n : nat) ,
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT acc ->
  respects_constraints_directed is_in_graph URzQ_CNOT (cancel_two_qubit_gates' l n acc).
Proof.
  intros.
  generalize dependent acc.
  generalize dependent l.
  induction n. 
  - intros. 
    unfold cancel_two_qubit_gates'.
    apply rev_append_respects_constraints; assumption. 
  - intros.
    simpl.  
    destruct l.
    + subst.
      apply rev_append_respects_constraints; assumption. 
    + destruct g; dependent destruction r; inversion H; subst.
      * eapply IHn; try reflexivity; auto. 
        constructor; auto.
      * eapply IHn; try reflexivity; auto. 
        constructor; auto.
      * eapply IHn; try reflexivity; auto. 
        constructor; auto.
      * destruct (propagate_CNOT l n0 n1) eqn:pCX.  
        eapply IHn; try reflexivity; auto.
        eapply propagate_CNOT_respects_constraints; try apply pCX; auto.
        eapply IHn; try reflexivity; auto.
        constructor; auto.
Qed.         

Lemma cancel_two_qubit_gates_respects_constraints : forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph URzQ_CNOT l ->
  respects_constraints_directed is_in_graph URzQ_CNOT (cancel_two_qubit_gates l).
Proof.
  intros.
  eapply cancel_two_qubit_gates'_respects_constraints.
  assumption.
  constructor.
Qed. 
