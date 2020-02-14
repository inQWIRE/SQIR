Require Import UnitarySem.
Require Import Equivalences.
Require Export RzkGateSet.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.

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

Definition Rz_commute_rule1 {dim} q (l : Rzk_ucom_l dim) :=
  match (next_single_qubit_gate l q) with
  | Some (l1, URzk_H, l2) => 
      match (next_two_qubit_gate l2 q) with
      | Some (l3, URzk_CNOT, q1, q2, l4) =>
          if q =? q2
          then match (next_single_qubit_gate l4 q) with
               | Some (l5, URzk_H, l6) => Some (l1 ++ [H q] ++ l3 ++ [CNOT q1 q] ++ l5 ++ [H q], l6) 
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition Rz_commute_rule2 {dim} q (l : Rzk_ucom_l dim) :=
  match (next_two_qubit_gate l q) with
  | Some (l1, URzk_CNOT, q1, q2, l2) => 
      if q =? q2
      then match (next_single_qubit_gate l2 q) with
           | Some (l3, URzk_Rz _ as u, l4) =>
               match (next_two_qubit_gate l4 q) with
               | Some (l5, URzk_CNOT, q3, q4, l6) => 
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

Definition Rz_commute_rule3 {dim} q (l : Rzk_ucom_l dim) :=
  match (next_two_qubit_gate l q) with
  | Some (l1, URzk_CNOT, q1, q2, l2) => 
      if q =? q1
      then Some (l1 ++ [CNOT q1 q2], l2)
      else None
  | _ => None
  end.

Definition Rz_commute_rules {dim} q :=
  @Rz_commute_rule1 dim q :: Rz_commute_rule2 q :: Rz_commute_rule3 q :: [].

Definition Rz_cancel_rule {dim} q i (l : Rzk_ucom_l dim) :=
  match (next_single_qubit_gate l q) with
  | Some (l1, URzk_Rz i', l2) =>
      Some ((combine_rotations i i' q) ++ l1 ++ l2)
  | _ => None
  end.

(** Propagation rules for H **)
(* (Currently no  rules for commuting.) *)

Definition H_cancel_rule {dim} q (l : Rzk_ucom_l dim)  :=
  match next_single_qubit_gate l q with
  | Some (l1, URzk_H, l2) => Some (l1 ++ l2)
  | _ => None
  end.

(** Propagation rules for X **)

Definition X_commute_rule {dim} q (l : Rzk_ucom_l dim) :=
  match (next_two_qubit_gate l q) with
  | Some (l1, URzk_CNOT, q1, q2, l2) => 
      if q =? q2
      then Some (l1 ++ [CNOT q1 q2], l2)
      else None
  | _ => None
  end.

Definition X_cancel_rule {dim} q (l : Rzk_ucom_l dim) :=
  match (next_single_qubit_gate l q) with
  | Some (l1, URzk_X, l2) => Some (l1 ++ l2)
  | _ => None
  end.

(** Propagation rules for CNOT **)

Definition CNOT_commute_rule1 {dim} q1 (l : Rzk_ucom_l dim) : option (Rzk_ucom_l dim * Rzk_ucom_l dim) :=
  match (next_single_qubit_gate l q1) with
  | Some (l1, URzk_Rz _ as u, l2) => Some ([App1 u q1], l1 ++ l2)
  | _ => None
  end.

Definition CNOT_commute_rule2 {dim} q1 q2 (l : Rzk_ucom_l dim) :=
  match (next_two_qubit_gate l q2) with
  | Some (l1, URzk_CNOT, q1', q2', l2) => 
      if q2 =? q2'
      then if (does_not_reference l1 q1)
           then Some (l1 ++ [CNOT q1' q2], l2)
           else None
      else None
  | _ => None
  end.

Definition CNOT_commute_rule3 {dim} q1 q2 (l : Rzk_ucom_l dim) :=
  match (next_two_qubit_gate l q1) with
  | Some (l1, URzk_CNOT, q1', q2', l2) => 
      if q1 =? q1'
      then if (does_not_reference l1 q2)
           then Some (l1 ++ [CNOT q1 q2'], l2)
           else None
      else None
  | _ => None
  end.

Definition CNOT_commute_rule4 {dim} q1 q2 (l : Rzk_ucom_l dim) :=
  match (next_single_qubit_gate l q2) with
  | Some (l1, URzk_H, l2) => 
      match (next_two_qubit_gate l2 q2) with
      | Some (l3, URzk_CNOT, q1', q2', l4) => 
          if (q2 =? q1') && ¬ (q1 =? q2') && (does_not_reference (l1 ++ l3) q1)
          then match (next_single_qubit_gate l4 q2) with
               | Some (l5, URzk_H, l6) => Some (l1 ++ [H q2] ++ l3 ++ [CNOT q2 q2'] ++ [H q2], l5 ++ l6)
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition CNOT_commute_rule5 {dim} q1 q2 (l : Rzk_ucom_l dim) :=
  match next_single_qubit_gate l q2 with
  | Some (l1, URzk_Rz i, l2) =>
      match next_two_qubit_gate l2 q2 with
      | Some (l3, URzk_CNOT, q1', q2', l4) =>
          if (q1 =? q1') && (q2 =? q2') && (does_not_reference (l1 ++ l3) q1)
          then match next_single_qubit_gate l4 q2 with
               | Some (l5, URzk_Rz i', l6) =>
                   Some (l1 ++ [App1 (URzk_Rz i') q2] ++ l3 ++ [CNOT q1' q2'] ++ [App1 (URzk_Rz i) q2], l5 ++ l6) 
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition CNOT_commute_rules {dim} q1 q2 :=
  @CNOT_commute_rule1 dim q1 :: CNOT_commute_rule2 q1 q2 :: CNOT_commute_rule3 q1 q2 :: CNOT_commute_rule4 q1 q2 :: CNOT_commute_rule5 q1 q2 :: [].

Definition CNOT_cancel_rule {dim} q1 q2 (l : Rzk_ucom_l dim) :=
  match next_two_qubit_gate l q1 with
  | Some (l1, URzk_CNOT, q1', q2', l2) => 
      if (q1 =? q1') && (q2 =? q2') && (does_not_reference l1 q2)
      then Some (l1 ++ l2)
      else None
  | _ => None
  end.

(** Gate Cancellation Routines **)

Definition propagate_Rz {dim} k (l : Rzk_ucom_l dim) q n :=
  propagate l (Rz_commute_rules q) [Rz_cancel_rule q k] n.

Definition propagate_H {dim} (l : Rzk_ucom_l dim) q :=
  propagate l [] [H_cancel_rule q] 1%nat.

Definition propagate_X {dim} (l : Rzk_ucom_l dim) q n :=
  propagate l [X_commute_rule q] [X_cancel_rule q] n.

Definition propagate_CNOT {dim} (l : Rzk_ucom_l dim) (q1 q2 n : nat) :=
  propagate l (CNOT_commute_rules q1 q2) [CNOT_cancel_rule q1 q2] n.

Fixpoint cancel_single_qubit_gates' {dim} (l : Rzk_ucom_l dim) (n: nat) : Rzk_ucom_l dim :=
  match n with
  | 0 => l
  | S n' => match l with
           | App1 (URzk_Rz i) q :: t => 
               match propagate_Rz i t q (length t) with
               | None => (App1 (URzk_Rz i) q) :: cancel_single_qubit_gates' t n'
               | Some l' => cancel_single_qubit_gates' l' n'
               end
           | App1 URzk_H q :: t => 
               match propagate_H t q with
               | None => H q :: cancel_single_qubit_gates' t n'
               | Some l' => cancel_single_qubit_gates' l' n'
               end
           | App1 URzk_X q :: t => 
               match propagate_X t q (length t) with
               | None => X q :: cancel_single_qubit_gates' t n'
               | Some l' => cancel_single_qubit_gates' l' n'
               end
           | u :: t => u :: cancel_single_qubit_gates' t n'
           | [] => []
           end
  end.

Definition cancel_single_qubit_gates {dim} (l : Rzk_ucom_l dim) := 
  cancel_single_qubit_gates' l (length l).

Fixpoint cancel_two_qubit_gates' {dim} (l : Rzk_ucom_l dim) (n: nat) : Rzk_ucom_l dim :=
  match n with
  | 0 => l
  | S n' => match l with
           | App2 URzk_CNOT q1 q2 :: t => 
               match propagate_CNOT t q1 q2 (length t) with
               | None => CNOT q1 q2 :: cancel_two_qubit_gates' t n'
               | Some l' => cancel_two_qubit_gates' l' n'
               end
           | u :: t => u :: cancel_two_qubit_gates' t n'
           | [] => []
           end
  end.

Definition cancel_two_qubit_gates {dim} (l : Rzk_ucom_l dim) := 
  cancel_two_qubit_gates' l (length l).

(** Proofs **)

(* Basic gate equivalences *)

Lemma Rz_commutes_with_H_CNOT_H : forall {dim} i q1 q2,
  @Rz dim i q2 :: H q2 :: CNOT q1 q2 :: H q2 :: [] =l= H q2 :: CNOT q1 q2 :: H q2 :: Rz i q2 :: [].
Proof.
  intros.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  unfold uc_equiv; simpl.
  rewrite hadamard_rotation, phase_shift_rotation.
  autorewrite with eval_db.
  gridify.
  - rewrite (Mmult_assoc _ hadamard hadamard). 
    Qsimpl.
    repeat rewrite (Mmult_assoc _ _ hadamard).
    rewrite (Mmult_assoc _ hadamard).
    replace (hadamard × (σx × hadamard)) with σz by solve_matrix.
    rewrite <- phase_pi, 2 phase_mul.
    rewrite Rplus_comm.
    reflexivity.
  - rewrite (Mmult_assoc _ hadamard hadamard).
    Qsimpl.
    repeat rewrite (Mmult_assoc _ _ hadamard).
    rewrite (Mmult_assoc _ hadamard).
    replace (hadamard × (σx × hadamard)) with σz by solve_matrix.
    rewrite <- phase_pi, 2 phase_mul.
    rewrite Rplus_comm.
    reflexivity.
Qed.

Lemma Rz_commutes_with_CNOT_Rz_CNOT : forall {dim} i i' q1 q2,
  @Rz dim i q2 :: CNOT q1 q2 :: Rz i' q2 :: CNOT q1 q2 :: [] =l= CNOT q1 q2 :: Rz i' q2 :: CNOT q1 q2 :: Rz i q2 :: [].
Proof.
  intros.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  unfold uc_equiv; simpl.
  repeat rewrite phase_shift_rotation.
  autorewrite with eval_db.
  gridify.
  - Qsimpl. 
    rewrite 2 phase_mul. rewrite Rplus_comm.
    replace (σx × phase_shift (IZR i' * PI / IZR Rzk_k) × σx × phase_shift (IZR i * PI / IZR Rzk_k))
      with (phase_shift (IZR i * PI / IZR Rzk_k) × σx × phase_shift (IZR i' * PI / IZR Rzk_k) × σx) by
      solve_matrix.
    reflexivity.
  - Qsimpl.
    rewrite 2 phase_mul. rewrite Rplus_comm.
    replace (σx × phase_shift (IZR i' * PI / IZR Rzk_k) × σx × phase_shift (IZR i * PI / IZR Rzk_k))
      with (phase_shift (IZR i * PI / IZR Rzk_k) × σx × phase_shift (IZR i' * PI / IZR Rzk_k) × σx) by
      solve_matrix.      
    reflexivity.
Qed.

Lemma Rz_commutes_with_CNOT : forall {dim} i q1 q2,
  @Rz dim i q1 :: CNOT q1 q2 :: [] =l= CNOT q1 q2 :: Rz i q1 :: [].
Proof.
  intros.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  unfold uc_equiv; simpl.
  rewrite phase_shift_rotation.
  autorewrite with eval_db.
  gridify.
  - replace  (∣1⟩⟨1∣ × phase_shift (IZR i * PI / IZR Rzk_k))
      with (phase_shift (IZR i * PI / IZR Rzk_k) × ∣1⟩⟨1∣) by solve_matrix.
    replace  (∣0⟩⟨0∣ × phase_shift (IZR i * PI / IZR Rzk_k))
      with (phase_shift (IZR i * PI / IZR Rzk_k) × ∣0⟩⟨0∣) by solve_matrix.
    reflexivity.
  - replace  (∣1⟩⟨1∣ × phase_shift (IZR i * PI / IZR Rzk_k))
      with (phase_shift (IZR i * PI / IZR Rzk_k) × ∣1⟩⟨1∣) by solve_matrix.
    replace  (∣0⟩⟨0∣ × phase_shift (IZR i * PI / IZR Rzk_k))
      with (phase_shift (IZR i * PI / IZR Rzk_k) × ∣0⟩⟨0∣) by solve_matrix.
    reflexivity.
Qed.

Lemma H_H_cancel : forall {dim} q, 
  q < dim -> @H dim q :: H q :: [] =l= [].
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  rewrite hadamard_rotation.
  autorewrite with eval_db; try lia.
  gridify. Qsimpl. reflexivity.
Qed.

Lemma X_X_cancel : forall {dim} q, 
  q < dim -> @X dim q :: X q :: [] =l= [].
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  rewrite pauli_x_rotation.
  autorewrite with eval_db; try lia.
  gridify. Qsimpl. reflexivity.
Qed.

Lemma X_commutes_with_CNOT : forall {dim} q1 q2,
  @X dim q2 :: CNOT q1 q2 :: [] =l= CNOT q1 q2 :: X q2 :: [].
Proof.
  intros.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r. 
  apply X_CNOT_comm.
Qed.

Lemma CNOT_CNOT_cancel : forall {dim} q1 q2, 
  q1 < dim -> q2 < dim -> q1 <> q2 -> 
  @App2 _ dim URzk_CNOT q1 q2 :: App2 URzk_CNOT q1 q2 :: [] =l= [].
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db; try lia.
  gridify; Qsimpl.
  all: repeat rewrite <- kron_plus_distr_r;
       repeat rewrite <- kron_plus_distr_l.
  all: replace (∣1⟩ × ∣1⟩† .+ ∣0⟩ × ∣0⟩†) with (I 2) by solve_matrix.
  all: reflexivity.
Qed.  

Lemma CNOT_commutes_with_CNOT_sharing_target : forall {dim} q1 q2 q3,
  @CNOT dim q1 q3 :: CNOT q2 q3 :: [] =l= CNOT q2 q3 :: CNOT q1 q3 :: [].
Proof.
  intros.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify; reflexivity.
Qed.

Lemma CNOT_commutes_with_CNOT_sharing_control : forall {dim} q1 q2 q3,
  @CNOT dim q1 q3 :: CNOT q1 q2 :: [] =l= CNOT q1 q2 :: CNOT q1 q3 :: [].
Proof.
  intros.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify; Qsimpl; reflexivity.
Qed.

Lemma CNOT_commutes_with_H_CNOT_H : forall {dim} q1 q2 q3,
  q1 <> q3 ->
  @CNOT dim q1 q2 :: H q2 :: CNOT q2 q3 :: H q2 :: [] =l= H q2 :: CNOT q2 q3 :: H q2 :: CNOT q1 q2 :: [].
Proof.
  intros.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  unfold uc_equiv; simpl.
  rewrite hadamard_rotation.
  autorewrite with eval_db.
  gridify; try reflexivity. (* slow! *)
  all: replace (hadamard × ∣1⟩⟨1∣ × hadamard × σx) with
         (σx × hadamard × ∣1⟩⟨1∣ × hadamard) by solve_matrix;
       replace (hadamard × ∣0⟩⟨0∣ × hadamard × σx) with
         (σx × hadamard × ∣0⟩⟨0∣ × hadamard) by solve_matrix;
       reflexivity.
Qed.

(* Proofs about optimization *)

Lemma propagate_Rz_sound : forall {dim} i (l : Rzk_ucom_l dim) q n l',
  q < dim ->
  propagate_Rz i l q n = Some l' ->
  Rz i q :: l =l= l'.
Proof.
  unfold propagate_Rz.
  intros dim i l q n l' Hq res.
  eapply propagate_preserves_semantics; try apply res.
  apply uc_equiv_l_rel.
  apply uc_app_mor_Proper.
  - clear l l' res.
    intros rules Hin l l' res.
    destruct_In; subst.
    unfold Rz_cancel_rule in res.
    destruct (next_single_qubit_gate l q) eqn:nsqg; try discriminate.
    repeat destruct p; dependent destruction r; try discriminate.
    inversion res; subst.
    rewrite combine_rotations_semantics by assumption.
    rewrite (nsqg_commutes _ _ _ _ _ nsqg); rewrite app_comm_cons. 
    reflexivity.
  - clear l l' n res Hq.
    intros rules Hin l l1 l2 res.
    destruct_In; subst.
    + unfold Rz_commute_rule1 in res.
      destruct (next_single_qubit_gate l q) eqn:nsqg1; try discriminate.
      repeat destruct p; dependent destruction r; try discriminate.
      specialize (nsqg_l1_does_not_reference _ _ _ _ _ nsqg1) as dnrg0.
      apply nsqg_preserves_structure in nsqg1.
      destruct (next_two_qubit_gate g q) eqn:ntqg; try discriminate.
      repeat destruct p; dependent destruction r.
      specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as dnrg2.
      apply ntqg_preserves_structure in ntqg.
      bdestruct (q =? n); try discriminate.
      destruct (next_single_qubit_gate g1 q) eqn:nsqg2; try discriminate.
      repeat destruct p; dependent destruction r; try discriminate.
      specialize (nsqg_l1_does_not_reference _ _ _ _ _ nsqg2) as dnrg4.
      apply nsqg_preserves_structure in nsqg2.
      inversion res; subst.
      rewrite cons_to_app.
      rewrite (cons_to_app (H n)).
      rewrite (cons_to_app (CNOT n0 n)).
      repeat rewrite app_assoc.
      rewrite (does_not_reference_commutes_app1 _ (URzk_Rz i) _ dnrg0).
      repeat rewrite <- (app_assoc _ _ g2).
      rewrite 2 (does_not_reference_commutes_app1 _ URzk_H _ dnrg2).
      rewrite <- (app_assoc g0).
      rewrite (app_assoc _ g2).
      rewrite (does_not_reference_commutes_app1 _ (URzk_Rz i) _ dnrg2).
      repeat rewrite <- (app_assoc _ g4).
      rewrite <- 2 (does_not_reference_commutes_app1 _ URzk_H _ dnrg4).
      repeat rewrite <- (app_assoc _ _ [Rz i n]).
      rewrite <- (does_not_reference_commutes_app1 _ (URzk_Rz i) _ dnrg4).
      repeat rewrite <- app_assoc.  
      do 2 (apply uc_app_congruence; try reflexivity).
      repeat rewrite app_assoc.
      do 2 (apply uc_app_congruence; try reflexivity).
      simpl.
      apply Rz_commutes_with_H_CNOT_H.
    + unfold Rz_commute_rule2 in res.
      destruct (next_two_qubit_gate l q) eqn:ntqg1; try discriminate.
      repeat destruct p; dependent destruction r.
      specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg1) as dnrg0.
      apply ntqg_preserves_structure in ntqg1.
      bdestruct (q =? n); try discriminate.
      subst.
      destruct (next_single_qubit_gate g n) eqn:nsqg; try discriminate.
      repeat destruct p; dependent destruction r; try discriminate.
      specialize (nsqg_l1_does_not_reference _ _ _ _ _ nsqg) as dnrg2.
      apply nsqg_preserves_structure in nsqg.
      destruct (next_two_qubit_gate g1 n) eqn:ntqg2; try discriminate.
      repeat destruct p; dependent destruction r.
      specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg2) as dnrg4.
      apply ntqg_preserves_structure in ntqg2.
      bdestruct (n =? n1); try discriminate.
      bdestruct (n0 =? n2); try discriminate.
      destruct (does_not_reference (g2 ++ g4) n2) eqn:dnr; try discriminate.
      simpl in res.
      inversion res; subst. clear res.
      apply does_not_reference_app in dnr.
      apply andb_true_iff in dnr as [dnrg2' dnrg4'].
      rewrite cons_to_app.
      rewrite (cons_to_app (CNOT n2 n1)).
      rewrite (cons_to_app (Rz i0 n1) (g4 ++ _)).
      repeat rewrite app_assoc.
      rewrite (does_not_reference_commutes_app1 _ (URzk_Rz i) _ dnrg0).
      repeat rewrite <- (app_assoc _ _ g2).
      rewrite 2 (does_not_reference_commutes_app2 _ URzk_CNOT _ _ dnrg2' dnrg2).
      rewrite <- (app_assoc g0).
      rewrite (app_assoc _ g2).
      rewrite (does_not_reference_commutes_app1 _ (URzk_Rz i) _ dnrg2).
      repeat rewrite <- (app_assoc _ g4).
      rewrite <- 2 (does_not_reference_commutes_app2 _ URzk_CNOT _ _ dnrg4' dnrg4).
      repeat rewrite <- (app_assoc _ _ [Rz i n1]).
      rewrite <- (does_not_reference_commutes_app1 _ (URzk_Rz i) _ dnrg4).
      repeat rewrite <- app_assoc.  
      do 2 (apply uc_app_congruence; try reflexivity).
      repeat rewrite app_assoc.
      do 2 (apply uc_app_congruence; try reflexivity).
      simpl.
      apply Rz_commutes_with_CNOT_Rz_CNOT.
    + unfold Rz_commute_rule3 in res.
      destruct (next_two_qubit_gate l q) eqn:ntqg; try discriminate.
      repeat destruct p; dependent destruction r.
      specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as dnr.
      apply ntqg_preserves_structure in ntqg.
      bdestruct (q =? n0); try discriminate.
      subst.
      inversion res; subst.
      rewrite (cons_to_app (Rz i n0) (g0 ++ _)).
      repeat rewrite app_assoc.
      apply uc_app_congruence; try reflexivity. 
      rewrite (does_not_reference_commutes_app1 _ (URzk_Rz i) _ dnr).
      repeat rewrite <- app_assoc.
      apply uc_app_congruence; try reflexivity. 
      simpl.
      apply Rz_commutes_with_CNOT.
Qed.

Lemma propagate_Rz_WT : forall {dim} k (l : Rzk_ucom_l dim) q n l',
  q < dim ->
  uc_well_typed_l l ->
  propagate_Rz k l q n = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_Rz_sound k l q n l' H H1) as H2.
  apply (uc_equiv_l_implies_WT _ _ H2).
  constructor; assumption.
Qed.

Lemma propagate_H_sound : forall {dim} (l : Rzk_ucom_l dim) q l',
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
    destruct (next_single_qubit_gate l q) eqn:nsqg; try discriminate.
    repeat destruct p; dependent destruction r; try discriminate.
    inversion res; subst.
    rewrite (nsqg_commutes _ _ _ _ _ nsqg).
    rewrite app_comm_cons.
    rewrite H_H_cancel; try assumption; try reflexivity.
  - clear l l' res.
    intros rules Hin l l' res.
    destruct_In.
Qed.

Lemma propagate_H_WT : forall {dim} (l : Rzk_ucom_l dim) q l',
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

Lemma propagate_X_sound : forall {dim} (l : Rzk_ucom_l dim) q n l',
  q < dim ->
  propagate_X l q n = Some l' ->
  X q :: l =l= l'.
Proof.
  unfold propagate_X.
  intros dim l q n l' Hq res.
  eapply propagate_preserves_semantics; try apply res.
  apply uc_equiv_l_rel.
  apply uc_app_mor_Proper.
  - clear l l' res.
    intros rules Hin l l' res.
    destruct_In; subst.
    unfold X_cancel_rule in res.
    destruct (next_single_qubit_gate l q) eqn:nsqg; try discriminate.
    repeat destruct p; dependent destruction r; try discriminate.
    inversion res; subst.
    rewrite (nsqg_commutes _ _ _ _ _ nsqg).
    rewrite app_comm_cons.
    rewrite X_X_cancel; try assumption; try reflexivity.
  - clear l l' n res Hq.
    intros rules Hin l l1 l2 res.
    destruct_In; subst.
    unfold X_commute_rule in res.
    destruct (next_two_qubit_gate l q) eqn:ntqg; try discriminate.
    repeat destruct p; dependent destruction r.
    bdestruct (q =? n); try discriminate.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as dnr.
    apply ntqg_preserves_structure in ntqg.
    inversion res; subst.
    rewrite (cons_to_app (X n) (g0 ++_)).
    repeat rewrite app_assoc.
    rewrite (does_not_reference_commutes_app1 _ URzk_X _ dnr). 
    apply uc_app_congruence; try reflexivity.
    repeat rewrite <- app_assoc.
    apply uc_app_congruence; try reflexivity.
    simpl.
    apply X_commutes_with_CNOT.
Qed.

Lemma propagate_X_WT : forall {dim} (l : Rzk_ucom_l dim) q n l',
  q < dim ->
  uc_well_typed_l l ->
  propagate_X l q n = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_X_sound l q n l' H H1) as H2.
  apply (uc_equiv_l_implies_WT _ _ H2).
  constructor; assumption.
Qed.

Lemma propagate_CNOT_sound : forall {dim} (l : Rzk_ucom_l dim) q1 q2 n l',
  q1 < dim ->
  q2 < dim -> 
  q1 <> q2 ->
  propagate_CNOT l q1 q2 n = Some l' ->
  CNOT q1 q2 :: l =l= l'.
Proof.
  unfold propagate_CNOT.
  intros dim l q1 q2 n l' Hq1 Hq2 Hq1q2 res.
  eapply propagate_preserves_semantics; try apply res.
  apply uc_equiv_l_rel.
  apply uc_app_mor_Proper.
  - clear l l' res.
    intros rules Hin l l' res.
    destruct_In; subst.
    unfold CNOT_cancel_rule in res.
    destruct (next_two_qubit_gate l q1) eqn:ntqg; try discriminate.
    repeat destruct p; dependent destruction r.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as dnr1.
    apply ntqg_preserves_structure in ntqg.
    bdestruct (q1 =? n1); bdestruct (q2 =? n0); 
      destruct (does_not_reference g0 q2) eqn:dnr2;
      simpl in res; try discriminate.    
    inversion res; subst.
    rewrite app_comm_cons.
    rewrite cons_to_app.
    rewrite (does_not_reference_commutes_app2 _ URzk_CNOT _ _ dnr1 dnr2).
    rewrite app_assoc.
    rewrite <- (app_assoc g0).
    simpl.
    rewrite CNOT_CNOT_cancel; try assumption.
    rewrite app_nil_r. reflexivity.
  - clear l l' n res.
    intros rules Hin l l1 l2 res.
    destruct_In; subst.
    + unfold CNOT_commute_rule1 in res.
      destruct (next_single_qubit_gate l q1) eqn:nsqg; try discriminate.
      repeat destruct p; dependent destruction r; try discriminate.
      apply nsqg_commutes in nsqg.
      inversion res; subst.
      rewrite nsqg.
      rewrite app_comm_cons.
      repeat rewrite app_assoc.
      do 2 (apply uc_app_congruence; try reflexivity).
      simpl; symmetry.
      apply Rz_commutes_with_CNOT.
    + unfold CNOT_commute_rule2 in res.
      destruct (next_two_qubit_gate l q2) eqn:ntqg; try discriminate.
      repeat destruct p; dependent destruction r.
      specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as dnr1.
      apply ntqg_preserves_structure in ntqg.
      bdestruct (q2 =? n); try discriminate.
      destruct (does_not_reference g0 q1) eqn:dnr2; try discriminate.
      inversion res; subst.
      rewrite (cons_to_app (CNOT q1 n) (g0 ++ _)).
      repeat rewrite app_assoc.
      rewrite (does_not_reference_commutes_app2 _ URzk_CNOT _ _ dnr2 dnr1).
      apply uc_app_congruence; try reflexivity.
      repeat rewrite <- app_assoc.
      apply uc_app_congruence; try reflexivity.
      apply CNOT_commutes_with_CNOT_sharing_target.
    + unfold CNOT_commute_rule3 in res.
      destruct (next_two_qubit_gate l q1) eqn:ntqg; try discriminate.
      repeat destruct p; dependent destruction r.
      specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as dnr1.
      apply ntqg_preserves_structure in ntqg.
      bdestruct (q1 =? n0); try discriminate.
      destruct (does_not_reference g0 q2) eqn:dnr2; try discriminate.
      inversion res; subst.
      rewrite (cons_to_app (CNOT n0 q2) (g0 ++ _)).
      repeat rewrite app_assoc.
      rewrite (does_not_reference_commutes_app2 _ URzk_CNOT _ _ dnr1 dnr2).
      apply uc_app_congruence; try reflexivity.
      repeat rewrite <- app_assoc.
      apply uc_app_congruence; try reflexivity.
      apply CNOT_commutes_with_CNOT_sharing_control.
    + unfold CNOT_commute_rule4 in res.
      destruct (next_single_qubit_gate l q2) eqn:nsqg1; try discriminate.
      repeat destruct p; dependent destruction r; try discriminate.
      specialize (nsqg_l1_does_not_reference _ _ _ _ _ nsqg1) as dnrg0.
      apply nsqg_preserves_structure in nsqg1.     
      destruct (next_two_qubit_gate g q2) eqn:ntqg; try discriminate.
      repeat destruct p; dependent destruction r.
      specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as dnrg2.
      apply ntqg_preserves_structure in ntqg.      
      bdestruct (q2 =? n0); bdestruct (q1 =? n); try discriminate.
      destruct (does_not_reference (g0 ++ g2) q1) eqn:dnr; try discriminate.
      apply does_not_reference_app in dnr.
      apply andb_true_iff in dnr as [dnrg0' dnrg2'].
      simpl in res.
      destruct (next_single_qubit_gate g1 q2) eqn:nsqg2; try discriminate.
      repeat destruct p; dependent destruction r; try discriminate.
      specialize (nsqg_l1_does_not_reference _ _ _ _ _ nsqg2) as dnrg4.
      apply nsqg_preserves_structure in nsqg2.   
      inversion res; subst. clear res.
      rewrite cons_to_app.
      rewrite (cons_to_app (CNOT n0 n)).
      rewrite (cons_to_app (H n0) (g2 ++ _)).
      repeat rewrite app_assoc.
      rewrite (does_not_reference_commutes_app2 _ URzk_CNOT _ _ dnrg0' dnrg0).
      repeat rewrite <- (app_assoc _ _ g2).
      rewrite 2 (does_not_reference_commutes_app1 _ URzk_H _ dnrg2).
      rewrite <- (app_assoc g0).
      rewrite (app_assoc _ g2).
      rewrite (does_not_reference_commutes_app2 _ URzk_CNOT _ _ dnrg2' dnrg2).
      rewrite <- (app_assoc _ g4).
      rewrite <- (does_not_reference_commutes_app1 _ URzk_H _ dnrg4).
      repeat rewrite <- app_assoc.  
      do 2 (apply uc_app_congruence; try reflexivity).
      repeat rewrite app_assoc.
      do 2 (apply uc_app_congruence; try reflexivity).
      simpl.
      apply CNOT_commutes_with_H_CNOT_H.
      assumption.
    + unfold CNOT_commute_rule5 in res.
      destruct (next_single_qubit_gate l q2) eqn:nsqg1; try discriminate.
      repeat destruct p; dependent destruction r; try discriminate.
      specialize (nsqg_l1_does_not_reference _ _ _ _ _ nsqg1) as dnrg0.
      apply nsqg_preserves_structure in nsqg1.     
      destruct (next_two_qubit_gate g q2) eqn:ntqg; try discriminate.
      repeat destruct p; dependent destruction r.
      specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as dnrg2.
      apply ntqg_preserves_structure in ntqg.
      bdestruct (q1 =? n0); try discriminate.
      bdestruct (q2 =? n); try discriminate.
      destruct (does_not_reference (g0 ++ g2) q1) eqn:dnr; try discriminate.
      simpl in res.
      destruct (next_single_qubit_gate g1 q2) eqn:nsqg2; try discriminate.
      repeat destruct p; dependent destruction r; try discriminate.
      specialize (nsqg_l1_does_not_reference _ _ _ _ _ nsqg2) as dnrg4.
      apply nsqg_preserves_structure in nsqg2.     
      inversion res; subst. clear res.
      apply does_not_reference_app in dnr.
      apply andb_true_iff in dnr as [dnrg0' dnrg2'].
      rewrite cons_to_app.
      rewrite (cons_to_app (CNOT n0 n)).
      rewrite (cons_to_app (App1 (URzk_Rz i0) n) (g2 ++ _)).
      repeat rewrite app_assoc.
      rewrite (does_not_reference_commutes_app2 _ URzk_CNOT _ _ dnrg0' dnrg0).
      repeat rewrite <- (app_assoc _ _ g2).
      rewrite 2 (does_not_reference_commutes_app1 _ (URzk_Rz _) _ dnrg2).
      rewrite <- (app_assoc g0).
      rewrite (app_assoc _ g2).
      rewrite (does_not_reference_commutes_app2 _ URzk_CNOT _ _ dnrg2' dnrg2).
      repeat rewrite <- (app_assoc _ g4).
      rewrite <- (does_not_reference_commutes_app1 _ (URzk_Rz _) _ dnrg4).
      repeat rewrite <- app_assoc.  
      do 2 (apply uc_app_congruence; try reflexivity).
      repeat rewrite app_assoc.
      do 2 (apply uc_app_congruence; try reflexivity).
      simpl. symmetry.
      apply Rz_commutes_with_CNOT_Rz_CNOT. 
Qed.

Lemma propagate_CNOT_WT : forall {dim} (l : Rzk_ucom_l dim) q1 q2 n l',
  q1 < dim ->
  q2 < dim -> 
  q1 <> q2 ->
  uc_well_typed_l l ->
  propagate_CNOT l q1 q2 n = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_CNOT_sound l q1 q2 n l' H H0 H1 H3) as H4.
  apply (uc_equiv_l_implies_WT _ _ H4).
  constructor; assumption.
Qed.

Lemma cancel_single_qubit_gates_sound : forall {dim} (l : Rzk_ucom_l dim),
  uc_well_typed_l l -> cancel_single_qubit_gates l =l= l.
Proof.
  intros dim l WT.
  assert (forall n, cancel_single_qubit_gates' l n =l= l).
  { intros n.
    generalize dependent l.
    induction n; intros l WT; try reflexivity.
    simpl.
    destruct l; try reflexivity.
    destruct g as [u | | u]; inversion WT; subst.
    - dependent destruction u.
      + destruct (propagate_H l n0) eqn:prop.
        rewrite (propagate_H_sound _ _ _ H1 prop).
        apply IHn.
        apply (propagate_H_WT _ _ _ H1 H3 prop).
        rewrite IHn; try reflexivity; try assumption.
      + destruct (propagate_X l n0 (length l)) eqn:prop.
        rewrite (propagate_X_sound _ _ _ _ H1 prop).
        apply IHn.
        apply (propagate_X_WT _ _ _ _ H1 H3 prop).
        rewrite IHn; try reflexivity; try assumption.
      + destruct (propagate_Rz i l n0 (length l)) eqn:prop.
        rewrite (propagate_Rz_sound _ _ _ _ _ H1 prop).
        apply IHn.
        apply (propagate_Rz_WT _ _ _ _ _ H1 H3 prop).
        rewrite IHn; try reflexivity; try assumption.
    - rewrite IHn; try reflexivity; try assumption.
    - inversion u. }
  apply H.
Qed.

Lemma cancel_single_qubit_gates_WT: forall {dim} (l : Rzk_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (cancel_single_qubit_gates l).
Proof.
  intros dim l WT.
  specialize (cancel_single_qubit_gates_sound l WT) as H.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H; assumption.
Qed.

Lemma cancel_two_qubit_gates_sound : forall {dim} (l : Rzk_ucom_l dim),
  uc_well_typed_l l -> cancel_two_qubit_gates l =l= l.
Proof.
  intros dim l WT.
  assert (forall n, cancel_two_qubit_gates' l n =l= l).
  { intros n.
    generalize dependent l.
    induction n; intros l WT; try reflexivity.
    simpl.
    destruct l; try reflexivity.
    destruct g as [| u | u]; inversion WT; subst.
    - rewrite IHn; try reflexivity; try assumption.
    - dependent destruction u.
      destruct (propagate_CNOT l n0 n1 (length l)) eqn:prop.
      rewrite (propagate_CNOT_sound _ _ _ _ _ H3 H4 H5 prop).
      apply IHn.
      apply (propagate_CNOT_WT _ _ _ _ _ H3 H4 H5 H6 prop).
      rewrite IHn; try reflexivity; try assumption. 
    - inversion u. }
  apply H.
Qed.

Lemma cancel_two_qubit_gates_WT: forall {dim} (l : Rzk_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (cancel_two_qubit_gates l).
Proof.
  intros dim l WT.
  specialize (cancel_two_qubit_gates_sound l WT) as H.
  symmetry in H.
  apply uc_equiv_l_implies_WT in H; assumption.
Qed.
