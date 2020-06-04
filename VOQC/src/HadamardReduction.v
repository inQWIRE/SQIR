Require Import UnitarySem.
Require Export RzQGateSet.
Require Import List.
Open Scope ucom.

Local Close Scope Q_scope.

(*******************************************)
(** Optimization: hadamard gate reduction **)
(*******************************************)

(* This optimization pass reduces the number of H gates in a program
   using a variety of rewrite rules. *)

(* Hadamard Reduction Optimization
   
   Try to apply each the following equivalences to c. If one
   of the equivalences applies, then return the circuit resulting from
   the appropriate substitution.

   #1  - H q; P q; H q ≡ P† q; H q; P† q 
   #2  - H q; P† q; H q ≡ P q; H q; P q 
   #3  - H q1; H q2; CNOT q1 q2; H q1; H q2 ≡ CNOT q2 q1 
   #4  - H q2; P q2; CNOT q1 q2; P† q2; H q2 ≡ P† q2; CNOT q1 q2; P q2 
   #5  - H q2; P† q2; CNOT q1 q2; P q2; H q2 ≡ P q2; CNOT q1 q2; P† q2 
*)

Definition apply_H_equivalence1 {dim} q (l : RzQ_ucom_l dim) := 
  replace_pattern l (H q  :: P q :: H q :: []) (PDAG q :: H q :: PDAG q :: []).

Definition apply_H_equivalence2 {dim} q (l : RzQ_ucom_l dim) := 
  replace_pattern l (H q :: PDAG q :: H q :: []) (P q :: H q :: P q :: []).

Definition apply_H_equivalence3 {dim} q (l : RzQ_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
  | Some (l1, URzQ_H, l2) =>
      let l := l1 ++ l2 in
      match (next_two_qubit_gate l q) with
      | Some (l1, URzQ_CNOT, m, n, l2) => 
          if (q =? m) 
          then match (last_single_qubit_gate l1 n) with
               | Some (l1_1, URzQ_H, l1_2) => 
                   let l1 := l1_1 ++ l1_2 in
                   match (next_single_qubit_gate l2 q) with
                   | Some (l2_1, URzQ_H, l2_2) =>
                       let l2 := l2_1 ++ l2_2 in
                       match (next_single_qubit_gate l2 n) with
                       | Some (l2_1, URzQ_H, l2_2) => 
                           let l2 := l2_1 ++ l2_2 in
                           Some (l1 ++ [CNOT n q] ++ l2)
                       | _ => None
                       end
                   | _ => None
                   end
               | _ => None
               end
          else match (last_single_qubit_gate l1 m) with
               | Some (l1_1, URzQ_H, l1_2) => 
                   let l1 := l1_1 ++ l1_2 in
                   match (next_single_qubit_gate l2 q) with
                   | Some (l2_1, URzQ_H, l2_2) =>
                       let l2 := l2_1 ++ l2_2 in
                       match (next_single_qubit_gate l2 m) with
                       | Some (l2_1, URzQ_H, l2_2) => 
                           let l2 := l2_1 ++ l2_2 in
                           Some (l1 ++ [CNOT q m] ++ l2)
                       | _ => None
                       end
                   | _ => None
                   end
               | _ => None
               end
      | _ => None
      end
  | _ => None
  end.

Definition apply_H_equivalence4 {dim} q (l : RzQ_ucom_l dim) :=
  match (remove_prefix l (H q :: P q :: [])) with
  | None => None
  | Some l1 =>
      match (next_two_qubit_gate l1 q) with
      | Some (l2, URzQ_CNOT, q1, q2, l3) =>
          if q =? q2 
          then match (remove_prefix l3 (PDAG q :: H q :: [])) with
               | None => None
               | Some l4 =>
                   Some (l2 ++ (PDAG q2 :: CNOT q1 q2 :: P q2 :: []) ++ l4)
               end
          else None
      | _ => None
      end
  end.

Definition apply_H_equivalence5 {dim} q (l : RzQ_ucom_l dim) :=
  match (remove_prefix l (H q :: PDAG q :: [])) with
  | Some l1 =>
      match (next_two_qubit_gate l1 q) with
      | Some (l2, URzQ_CNOT, q1, q2, l3) =>
          if q =? q2 
          then match (remove_prefix l3 (P q :: H q :: [])) with
               | Some l4 =>
                   Some (l2 ++ (P q2 :: CNOT q1 q2 :: PDAG q2 :: []) ++ l4)
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition apply_H_equivalence {dim} (l : RzQ_ucom_l dim) (q : nat) : option (RzQ_ucom_l dim) :=
  try_rewrites l (apply_H_equivalence1 q :: apply_H_equivalence2 q :: apply_H_equivalence3 q :: apply_H_equivalence4 q :: apply_H_equivalence5 q :: []).

(* For each H gate, try to apply a rewrite rule. If some rewrite rule
   succeeds, then make the recursive call on the circuit returned by
   apply_equivalence. 
 
   The n argument is needed to convince Coq of termination. We start with
   n = 2 * (length l), which is an overapproximation of the necessary
   number of iterations. Note that the starting value of n is greater than
   (length l) because apply_equivalence will sometimes return a program
   of the same size as the input program.

   If we wanted to do a proper proof of termination, we would need to show
   that each call to apply_H_equivalence (strictly) reduces the number of H 
   gates in the program. *)
Fixpoint apply_H_equivalences' {dim} (l : RzQ_ucom_l dim) (n: nat) acc : RzQ_ucom_l dim :=
  match n with
  | 0 => rev_append acc l
  | S n' => 
      match l with
      | [] => rev_append acc []
      | (App1 URzQ_H q) :: t => 
          match apply_H_equivalence l q with
          | None => apply_H_equivalences' t n' (H q :: acc)
          | Some l' => apply_H_equivalences' l' n' acc
          end
      | g :: t => apply_H_equivalences' t n' (g :: acc)
      end
  end.

Definition hadamard_reduction {dim} (l : RzQ_ucom_l dim) := 
  apply_H_equivalences' l (2 * (length l)) [].

(* Small example - both tests are the same circuit, just with the
   gate list reordered. The output should contain 2 H gates. *)
Definition hadamard_reduction_test1 : RzQ_ucom_l 4 :=
  X 0 :: H 0 :: P 0 :: H 0 :: X 0 :: H 1 :: H 2 :: CNOT 2 1 :: H 1 :: H 2 :: H 3 :: P 3 :: CNOT 3 2 :: H 3 :: P 3 :: CNOT 2 3 :: PDAG 3 :: H 3 :: [].
Compute (hadamard_reduction hadamard_reduction_test1).

Definition hadamard_reduction_test2 : RzQ_ucom_l 4 :=
  H 2 :: H 3 :: X 0 :: H 1 :: CNOT 2 1 :: P 3 :: H 0 :: H 2 :: P 0 :: CNOT 3 2 :: H 3 :: P 3 :: CNOT 2 3 :: H 0 :: X 0 :: PDAG 3 :: H 1 :: H 3 :: [].
Compute (hadamard_reduction hadamard_reduction_test2).

Lemma P_simplifies : phase_shift (1 * / 2 * PI) = phase_shift (PI/2).
Proof. apply f_equal. lra. Qed.

Lemma PDAG_simplifies : phase_shift (3 * / 2 * PI) = phase_shift (-(PI/2)).
Proof.
  unfold phase_shift; solve_matrix.
  replace (3 * / 2 * PI)%R with (2 * PI + - / 2 * PI)%R by lra.
  rewrite Cexp_add, Cexp_2PI. 
  autorewrite with R_db C_db Cexp_db. 
  rewrite Rmult_comm; reflexivity.
Qed.

Lemma apply_H_equivalence1_sound : forall {dim} (l l' : RzQ_ucom_l dim) q,
  apply_H_equivalence1 q l = Some l' ->
  l ≅l≅ l'. 
Proof.
  intros.
  apply replace_pattern_sound in H; try assumption.
  exists (PI / 4)%R.
  destruct dim.
  simpl; unfold pad. gridify.
  simpl; autorewrite with eval_db; try lia. 
  gridify.  
  rewrite <- Mscale_kron_dist_l.
  rewrite <- Mscale_kron_dist_r.
  do 2 (apply f_equal2; trivial).
  rewrite hadamard_rotation.
  repeat rewrite phase_shift_rotation.
  unfold Qreals.Q2R; simpl.
  rewrite P_simplifies, PDAG_simplifies.
  solve_matrix; autorewrite with Cexp_db; C_field.
Qed.

Lemma apply_H_equivalence2_sound : forall {dim} (l l' : RzQ_ucom_l dim) q,
  apply_H_equivalence2 q l = Some l' ->
  l ≅l≅ l'.
Proof. 
  intros.
  eapply replace_pattern_sound; try apply H.
  exists (- PI / 4)%R.
  destruct dim.
  simpl; unfold pad. gridify.
  simpl; autorewrite with eval_db; try lia.
  gridify.  
  rewrite <- Mscale_kron_dist_l.
  rewrite <- Mscale_kron_dist_r.
  do 2 (apply f_equal2; trivial).
  rewrite hadamard_rotation.
  repeat rewrite phase_shift_rotation.
  unfold Qreals.Q2R; simpl.
  rewrite P_simplifies, PDAG_simplifies.
  solve_matrix; autorewrite with Cexp_db; C_field.
Qed.

Lemma apply_H_equivalence3_sound : forall {dim} (l l' : RzQ_ucom_l dim) q,
  apply_H_equivalence3 q l = Some l' ->
  l =l= l'.
Proof.
  intros dim l l' q res.
  unfold apply_H_equivalence3 in res.
  destruct_list_ops; simpl_dnr.
  - rewrite app_assoc.
    rewrite <- does_not_reference_commutes_app1 by assumption.
    rewrite <- app_assoc.
    setoid_rewrite H0; clear H0.
    rewrite (app_assoc g6).
    rewrite <- (does_not_reference_commutes_app1 g6) by assumption.
    rewrite <- (app_assoc _ g6).
    rewrite H; clear H.
    repeat rewrite app_assoc.
    rewrite (cons_to_app _ (_ ++ _)).
    rewrite does_not_reference_commutes_app1 by assumption.
    rewrite <- (app_assoc _ _ g3).
    rewrite (does_not_reference_commutes_app1 g3) by assumption.
    rewrite (app_assoc _ g3), <- (app_assoc _ _ g3).
    rewrite (does_not_reference_commutes_app1 g3) by assumption.
    rewrite <- (app_assoc _ g7).
    rewrite <- (does_not_reference_commutes_app1 g7) by assumption.
    apply_app_congruence.
    assert (H : [@H dim n0] ++ [H n] =l= [H n] ++ [H n0]).
    { simpl. unfold uc_equiv_l; simpl. 
      repeat rewrite <- useq_assoc. 
      rewrite U_V_comm. 
      reflexivity. lia. }
    rewrite H. 
    repeat rewrite app_assoc.
    rewrite H.
    unfold_uc_equiv_l. 
    apply H_swaps_CNOT.
  - destruct H2; try lia. subst.
    rewrite app_assoc.
    rewrite <- does_not_reference_commutes_app1 by assumption.
    rewrite <- app_assoc.
    setoid_rewrite H1; clear H1.
    rewrite (app_assoc g6).
    rewrite <- (does_not_reference_commutes_app1 g6) by assumption.
    rewrite <- (app_assoc _ g6).
    rewrite H0; clear H0.
    repeat rewrite app_assoc.
    rewrite (cons_to_app _ (_ ++ _)).
    rewrite does_not_reference_commutes_app1 by assumption.
    rewrite <- (app_assoc _ _ g3).
    rewrite (does_not_reference_commutes_app1 g3) by assumption.
    rewrite (app_assoc _ g3), <- (app_assoc _ _ g3).
    rewrite (does_not_reference_commutes_app1 g3) by assumption.
    rewrite <- (app_assoc _ g7).
    rewrite <- (does_not_reference_commutes_app1 g7) by assumption.
    apply_app_congruence.
    unfold_uc_equiv_l. 
    apply H_swaps_CNOT.
Qed.

Lemma apply_H_equivalence4_sound : forall {dim} (l l' : RzQ_ucom_l dim) q,
  apply_H_equivalence4 q l = Some l' ->
  l =l= l'.
Proof.
  intros. 
  unfold apply_H_equivalence4 in H.
  destruct (remove_prefix l (RzQGateSet.H q :: P q :: [])) eqn:rp; try discriminate.
  apply remove_prefix_correct in rp.
  rewrite rp; clear rp.
  destruct_list_ops.
  destruct (remove_prefix g0 (PDAG n :: RzQGateSet.H n :: [])) eqn:rp; try discriminate.
  apply remove_prefix_correct in rp.
  rewrite rp; clear rp.
  inversion H; subst; clear H.
  rewrite (cons_to_app (RzQGateSet.H n)).
  rewrite (cons_to_app (PDAG n)).
  rewrite 2 (cons_to_app _ (_ :: _)).
  rewrite (cons_to_app _ g).
  repeat rewrite app_assoc.
  rewrite <- (app_assoc [H n]).
  setoid_rewrite (does_not_reference_commutes_app1 g1); try assumption.
  rewrite app_assoc.
  setoid_rewrite (does_not_reference_commutes_app1 g1); try assumption.
  clear.
  apply_app_congruence.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  unfold uc_equiv; simpl.
  rewrite hadamard_rotation.
  repeat rewrite phase_shift_rotation.
  unfold Qreals.Q2R; simpl.
  rewrite P_simplifies, PDAG_simplifies.
  autorewrite with eval_db.
  gridify.
  - do 3 (apply f_equal2; trivial); solve_matrix;
      rewrite Cexp_neg; rewrite Cexp_PI2; repeat group_radicals; lca.
  - do 5 (apply f_equal2; trivial); solve_matrix; 
      rewrite Cexp_neg; rewrite Cexp_PI2; repeat group_radicals; lca.
Qed.    

Lemma apply_H_equivalence5_sound : forall {dim} (l l' : RzQ_ucom_l dim) q,
  apply_H_equivalence5 q l = Some l' ->
  l =l= l'.
Proof.
  intros. 
  unfold apply_H_equivalence5 in H.
  destruct (remove_prefix l (RzQGateSet.H q :: PDAG q :: [])) eqn:rp; try discriminate.
  apply remove_prefix_correct in rp.
  rewrite rp; clear rp.
  destruct_list_ops.
  destruct (remove_prefix g0 (P n :: RzQGateSet.H n :: [])) eqn:rp; try discriminate.
  apply remove_prefix_correct in rp.
  rewrite rp; clear rp.
  inversion H; subst; clear H.
  rewrite (cons_to_app (RzQGateSet.H n)).
  rewrite (cons_to_app (P n)).
  rewrite 2 (cons_to_app _ (_ :: _)).
  rewrite (cons_to_app _ g).
  repeat rewrite app_assoc.
  rewrite <- (app_assoc [H n]).
  setoid_rewrite (does_not_reference_commutes_app1 g1); try assumption.
  rewrite app_assoc.
  setoid_rewrite (does_not_reference_commutes_app1 g1); try assumption.
  clear.
  apply_app_congruence.
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  unfold uc_equiv; simpl.
  rewrite hadamard_rotation.
  repeat rewrite phase_shift_rotation.
  unfold Qreals.Q2R; simpl.
  rewrite P_simplifies, PDAG_simplifies.
  autorewrite with eval_db.
  gridify.
  - do 3 (apply f_equal2; trivial); solve_matrix;
      rewrite Cexp_neg; rewrite Cexp_PI2; repeat group_radicals; lca.
  - do 5 (apply f_equal2; trivial); solve_matrix; 
      rewrite Cexp_neg; rewrite Cexp_PI2; repeat group_radicals; lca.
Qed.    

Lemma apply_H_equivalence_sound : forall {dim} (l l' : RzQ_ucom_l dim) q,
  apply_H_equivalence l q = Some l' -> 
  l ≅l≅ l'.
Proof. 
  unfold apply_H_equivalence.
  intros dim l l' q.
  apply try_rewrites_preserves_property.
  intros.
  destruct_In.
  subst; apply (apply_H_equivalence1_sound _ _ _ H0).
  subst; apply (apply_H_equivalence2_sound _ _ _ H0). 
  apply uc_equiv_cong_l.
  subst; apply (apply_H_equivalence3_sound _ _ _ H0). 
  apply uc_equiv_cong_l.
  subst; apply (apply_H_equivalence4_sound _ _ _ H0). 
  apply uc_equiv_cong_l.
  subst; apply (apply_H_equivalence5_sound _ _ _ H0). 
Qed.

Lemma apply_H_equivalences_sound: forall {dim} (l : RzQ_ucom_l dim) n acc, 
  rev_append acc l ≅l≅ apply_H_equivalences' l n acc.
Proof. 
  intros dim l n acc.
  generalize dependent acc.
  generalize dependent l.
  induction n; try easy.
  intros l acc.
  destruct l; try reflexivity.
  destruct g as [u | | u]; simpl.
  - dependent destruction u.
    destruct (apply_H_equivalence (App1 URzQ_H n0 :: l) n0) eqn:res.
    all: rewrite <- IHn; simpl; try reflexivity.
    apply apply_H_equivalence_sound in res.
    rewrite 2 rev_append_rev. rewrite res. reflexivity.
  - rewrite <- IHn; simpl. reflexivity.
  - inversion u.
Qed.

Lemma hadamard_reduction_sound: forall {dim} (l : RzQ_ucom_l dim), 
  hadamard_reduction l ≅l≅ l.
Proof. 
  intros. symmetry. 
  unfold hadamard_reduction. 
  rewrite <- apply_H_equivalences_sound. 
  reflexivity.
Qed.

Lemma hadamard_reduction_WT: forall {dim} (l : RzQ_ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (hadamard_reduction l).
Proof.
  intros dim l WT.
  specialize (hadamard_reduction_sound l) as H.
  symmetry in H.
  apply uc_cong_l_implies_WT in H; assumption.
Qed.