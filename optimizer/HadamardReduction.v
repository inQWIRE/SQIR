Require Import UnitarySem.
Require Import Equivalences.
Require Import PI4GateSet.
Require Import optimizer.Utilities.
Require Import List.
Open Scope ucom.

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

Definition apply_H_equivalence1 {dim} q (l : PI4_ucom_l dim) := 
  replace_single_qubit_pattern l q 
    (UPI4_H  :: UPI4_P :: UPI4_H :: []) 
    (UPI4_PDAG :: UPI4_H :: UPI4_PDAG :: []).

Definition apply_H_equivalence2 {dim} q (l : PI4_ucom_l dim) := 
  replace_single_qubit_pattern l q 
    (UPI4_H :: UPI4_PDAG :: UPI4_H :: []) 
    (UPI4_P :: UPI4_H :: UPI4_P :: []).

Definition apply_H_equivalence3 {dim} q (l : PI4_ucom_l dim) := 
  match (next_single_qubit_gate l q) with
  | Some (l1, UPI4_H, l2) =>
      let l := l1 ++ l2 in
      match (next_two_qubit_gate l q) with
      | Some (l1, UPI4_CNOT, m, n, l2) => 
          if (q =? m) 
          then match (last_single_qubit_gate l1 n) with
               | Some (l1_1, UPI4_H, l1_2) => 
                   let l1 := l1_1 ++ l1_2 in
                   match (next_single_qubit_gate l2 q) with
                   | Some (l2_1, UPI4_H, l2_2) =>
                       let l2 := l2_1 ++ l2_2 in
                       match (next_single_qubit_gate l2 n) with
                       | Some (l2_1, UPI4_H, l2_2) => 
                           let l2 := l2_1 ++ l2_2 in
                           Some (l1 ++ [CNOT n q] ++ l2)
                       | _ => None
                       end
                   | _ => None
                   end
               | _ => None
               end
          else match (last_single_qubit_gate l1 m) with
               | Some (l1_1, UPI4_H, l1_2) => 
                   let l1 := l1_1 ++ l1_2 in
                   match (next_single_qubit_gate l2 q) with
                   | Some (l2_1, UPI4_H, l2_2) =>
                       let l2 := l2_1 ++ l2_2 in
                       match (next_single_qubit_gate l2 m) with
                       | Some (l2_1, UPI4_H, l2_2) => 
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

Definition apply_H_equivalence4 {dim} q (l : PI4_ucom_l dim) :=
  match (remove_single_qubit_pattern l q (UPI4_H :: UPI4_P :: [])) with
  | None => None
  | Some l1 =>
      match (next_two_qubit_gate l1 q) with
      | Some (l2, UPI4_CNOT, q1, q2, l3) =>
          if q =? q2 
          then match (remove_single_qubit_pattern l3 q (UPI4_PDAG :: UPI4_H :: [])) with
               | None => None
               | Some l4 =>
                   Some (l2 ++ (PDAG q2 :: CNOT q1 q2 :: P q2 :: []) ++ l4)
               end
          else None
      | _ => None
      end
  end.

Definition apply_H_equivalence5 {dim} q (l : PI4_ucom_l dim) :=
  match (remove_single_qubit_pattern l q (UPI4_H :: UPI4_PDAG :: [])) with
  | Some l1 =>
      match (next_two_qubit_gate l1 q) with
      | Some (l2, UPI4_CNOT, q1, q2, l3) =>
          if q =? q2 
          then match (remove_single_qubit_pattern l3 q (UPI4_P :: UPI4_H :: [])) with
               | Some l4 =>
                   Some (l2 ++ (P q2 :: CNOT q1 q2 :: PDAG q2 :: []) ++ l4)
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition apply_H_equivalence {dim} (l : PI4_ucom_l dim) (q : nat) : option (PI4_ucom_l dim) :=
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
Fixpoint apply_H_equivalences {dim} (l : PI4_ucom_l dim) (n: nat) : PI4_ucom_l dim :=
  match n with
  | 0 => l
  | S n' => 
      match l with
      | [] => []
      | (App1 UPI4_H q) :: t => 
          match apply_H_equivalence l q with
          | None => H q :: apply_H_equivalences t n'
          | Some l' => apply_H_equivalences l' n'
          end
      | g :: t => g :: apply_H_equivalences t n'
      end
  end.

Definition hadamard_reduction {dim} (l : PI4_ucom_l dim) := 
  apply_H_equivalences l (2 * (length l)).

(* Small example - both tests are the same circuit, just with the
   gate list reordered. The output should contain 2 H gates. *)
Definition hadamard_reduction_test1 : PI4_ucom_l 4 :=
  X 0 :: H 0 :: P 0 :: H 0 :: X 0 :: H 1 :: H 2 :: CNOT 2 1 :: H 1 :: H 2 :: H 3 :: P 3 :: CNOT 3 2 :: H 3 :: P 3 :: CNOT 2 3 :: PDAG 3 :: H 3 :: [].
Compute (hadamard_reduction hadamard_reduction_test1).

Definition hadamard_reduction_test2 : PI4_ucom_l 4 :=
  H 2 :: H 3 :: X 0 :: H 1 :: CNOT 2 1 :: P 3 :: H 0 :: H 2 :: P 0 :: CNOT 3 2 :: H 3 :: P 3 :: CNOT 2 3 :: H 0 :: X 0 :: PDAG 3 :: H 1 :: H 3 :: [].
Compute (hadamard_reduction hadamard_reduction_test2).

Lemma apply_H_equivalence1_sound : forall {dim} (l l' : PI4_ucom_l dim) q,
  apply_H_equivalence1 q l = Some l' ->
  l ≅l≅ l'. 
Proof.
  intros.
  apply replace_single_qubit_pattern_sound' in H; try assumption.
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
  solve_matrix; autorewrite with Cexp_db; C_field.
Qed.

Lemma apply_H_equivalence2_sound : forall {dim} (l l' : PI4_ucom_l dim) q,
  apply_H_equivalence2 q l = Some l' ->
  l ≅l≅ l'.
Proof. 
  intros.
  eapply replace_single_qubit_pattern_sound'; try apply H.
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
  solve_matrix; autorewrite with Cexp_db; C_field.
Qed.

Lemma apply_H_equivalence3_sound : forall {dim} (l l' : PI4_ucom_l dim) q,
  apply_H_equivalence3 q l = Some l' ->
  l =l= l'.
Proof.
  intros.
  unfold apply_H_equivalence3 in H.
  destruct (next_single_qubit_gate l q) eqn:nsqg1; try discriminate.
  repeat destruct p; dependent destruction p; try discriminate.
  destruct (next_two_qubit_gate (g0 ++ g) q) eqn:ntqg; try discriminate.
  repeat destruct p; dependent destruction p.
  bdestruct (q =? n0).
  - destruct (last_single_qubit_gate g2 n) eqn:lsqg; try discriminate.
    repeat destruct p; dependent destruction p; try discriminate.
    destruct (next_single_qubit_gate g1 q) eqn:nsqg2; try discriminate.
    repeat destruct p; dependent destruction p; try discriminate.
    destruct (next_single_qubit_gate (g6 ++ g5) n) eqn:nsqg3; try discriminate.
    repeat destruct p; dependent destruction p; try discriminate.
    inversion H; subst.
    clear H.
    apply nsqg_commutes in nsqg1; rewrite nsqg1.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as H.
    apply ntqg_preserves_structure in ntqg; rewrite ntqg.
    eapply does_not_reference_commutes_app1 in H.
    rewrite app_assoc.
    rewrite H.
    apply lsqg_commutes in lsqg; rewrite lsqg.
    apply nsqg_commutes in nsqg2; rewrite nsqg2.
    apply nsqg_commutes in nsqg3; rewrite nsqg3.
    clear.
    bdestruct (n =? n0).
    subst.
    unfold uc_equiv_l, uc_equiv. 
    repeat (try rewrite PI4_to_base_ucom_l_app;
            try rewrite list_to_ucom_append;
            simpl).
    unfold ueval_cnot. bdestruct_all. Msimpl_light. reflexivity.
    rewrite (cons_to_app (@CNOT dim n n0)).
    rewrite (app_assoc g4).
    rewrite <- 2 (app_assoc (g4 ++ g3)).
    apply uc_app_congruence; try reflexivity.
    repeat rewrite app_assoc.
    rewrite <- 2 (app_assoc _ _ g7).
    apply uc_app_congruence; try reflexivity.
    rewrite <- app_assoc.
    assert ([@App1 _ dim UPI4_H n0] ++ [App1 UPI4_H n] =l= [App1 UPI4_H n] ++ [App1 UPI4_H n0]).
    { simpl. unfold uc_equiv_l; simpl. 
      repeat rewrite <- useq_assoc. 
      rewrite U_V_comm. 
      reflexivity. lia. }
    rewrite H0.
    simpl.
    unfold uc_equiv_l; simpl.
    rewrite 2 SKIP_id_r.
    repeat rewrite <- useq_assoc. 
    apply H_swaps_CNOT.
  - destruct (last_single_qubit_gate g2 n0) eqn:lsqg; try discriminate.
    repeat destruct p; dependent destruction p; try discriminate.
    destruct (next_single_qubit_gate g1 q) eqn:nsqg2; try discriminate.
    repeat destruct p; dependent destruction p; try discriminate.
    destruct (next_single_qubit_gate (g6 ++ g5) n0) eqn:nsqg3; try discriminate.
    repeat destruct p; dependent destruction p; try discriminate.
    inversion H; subst.
    clear H.
    apply nsqg_commutes in nsqg1; rewrite nsqg1.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as H.
    specialize (ntqg_returns_two_qubit_gate _ _ _ _ _ _ _ ntqg) as H1.
    assert (q = n).
    { destruct H1. contradict H1; assumption. assumption. }
    subst. clear H0 H1.
    apply ntqg_preserves_structure in ntqg; rewrite ntqg.
    eapply does_not_reference_commutes_app1 in H.
    rewrite app_assoc.
    rewrite H.
    apply lsqg_commutes in lsqg; rewrite lsqg.
    apply nsqg_commutes in nsqg2; rewrite nsqg2.
    apply nsqg_commutes in nsqg3; rewrite nsqg3.
    clear.
    bdestruct (n =? n0).
    subst.
    unfold uc_equiv_l, uc_equiv. 
    repeat (try rewrite PI4_to_base_ucom_l_app;
            try rewrite list_to_ucom_append;
            simpl).
    unfold ueval_cnot. bdestruct_all. Msimpl_light. reflexivity.
    rewrite (cons_to_app (@CNOT dim n n0)).
    rewrite (app_assoc g4).
    rewrite <- 2 (app_assoc (g4 ++ g3)).
    apply uc_app_congruence; try reflexivity.
    repeat rewrite app_assoc.
    rewrite <- 2 (app_assoc _ _ g7).
    apply uc_app_congruence; try reflexivity.
    rewrite <- app_assoc.
    assert ([@App1 _ dim UPI4_H n0] ++ [App1 UPI4_H n] =l= [App1 UPI4_H n] ++ [App1 UPI4_H n0]).
    { simpl. unfold uc_equiv_l; simpl. 
      repeat rewrite <- useq_assoc. 
      rewrite U_V_comm. 
      reflexivity. lia. }
    rewrite H0.
    simpl.
    unfold uc_equiv_l; simpl.
    rewrite 2 SKIP_id_r.
    repeat rewrite <- useq_assoc. 
    apply H_swaps_CNOT.
Qed.

Lemma apply_H_equivalence4_sound : forall {dim} (l l' : PI4_ucom_l dim) q,
  apply_H_equivalence4 q l = Some l' ->
  l =l= l'.
Proof.
  intros. 
  unfold apply_H_equivalence4 in H.
  destruct (remove_single_qubit_pattern l q (UPI4_H :: UPI4_P :: [])) eqn:rsqp1; try discriminate.
  apply remove_single_qubit_pattern_correct in rsqp1.
  destruct (next_two_qubit_gate p q) eqn:ntqg; try discriminate.
  repeat destruct p0; dependent destruction p0.
  specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as dnr.
  apply ntqg_preserves_structure in ntqg; subst.
  bdestruct (q =? n); try discriminate.
  destruct (remove_single_qubit_pattern g q (UPI4_PDAG :: UPI4_H :: [])) eqn:rsqp2; try discriminate.
  apply remove_single_qubit_pattern_correct in rsqp2.
  inversion H; subst.
  simpl in *.
  rewrite rsqp1, rsqp2.
  repeat rewrite app_comm_cons.
  rewrite (cons_to_app (App1 UPI4_H n)).
  rewrite (cons_to_app (App1 UPI4_P n)).
  rewrite (does_not_reference_commutes_app1 _ UPI4_P _ dnr). 
  rewrite app_assoc.
  rewrite (does_not_reference_commutes_app1 _ UPI4_H _ dnr).
  clear.
  repeat rewrite <- app_assoc; simpl.
  rewrite <- (app_nil_l p).
  repeat rewrite app_comm_cons.
  do 2 (apply uc_app_congruence; try reflexivity).
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  unfold uc_equiv; simpl.
  rewrite hadamard_rotation.
  repeat rewrite phase_shift_rotation.
  autorewrite with eval_db.
  gridify.
  - do 3 (apply f_equal2; trivial); solve_matrix;
      rewrite Cexp_6PI4; rewrite Cexp_2PI4; repeat group_radicals; lca.
  - do 5 (apply f_equal2; trivial); solve_matrix; 
      rewrite Cexp_6PI4; rewrite Cexp_2PI4; repeat group_radicals; lca.
Qed.    

Lemma apply_H_equivalence5_sound : forall {dim} (l l' : PI4_ucom_l dim) q,
  apply_H_equivalence5 q l = Some l' ->
  l =l= l'.
Proof.
  intros. 
  unfold apply_H_equivalence5 in H.
  destruct (remove_single_qubit_pattern l q (UPI4_H :: UPI4_PDAG :: [])) eqn:rsqp1; try easy.
  apply remove_single_qubit_pattern_correct in rsqp1.
  destruct (next_two_qubit_gate p q) eqn:ntqg; try discriminate.
  repeat destruct p0; dependent destruction p0.
  specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as dnr.
  apply ntqg_preserves_structure in ntqg; subst.
  bdestruct (q =? n); try discriminate.
  destruct (remove_single_qubit_pattern g q (UPI4_P :: UPI4_H :: [])) eqn:rsqp2; try discriminate.
  apply remove_single_qubit_pattern_correct in rsqp2.
  inversion H; subst.
  simpl in *.
  rewrite rsqp1, rsqp2.
  repeat rewrite app_comm_cons.
  rewrite (cons_to_app (App1 UPI4_H n)).
  rewrite (cons_to_app (App1 UPI4_PDAG n)).
  rewrite (does_not_reference_commutes_app1 _ UPI4_PDAG _ dnr). 
  rewrite app_assoc.
  rewrite (does_not_reference_commutes_app1 _ UPI4_H _ dnr).
  clear.
  repeat rewrite <- app_assoc; simpl.
  rewrite <- (app_nil_l p).
  repeat rewrite app_comm_cons.
  do 2 (apply uc_app_congruence; try reflexivity).
  unfold uc_equiv_l; simpl.
  rewrite 2 SKIP_id_r.
  unfold uc_equiv; simpl.
  rewrite hadamard_rotation.
  repeat rewrite phase_shift_rotation.
  autorewrite with eval_db.
  gridify.
  - do 3 (apply f_equal2; trivial); solve_matrix;
      rewrite Cexp_6PI4; rewrite Cexp_2PI4; repeat group_radicals; lca.
  - do 5 (apply f_equal2; trivial); solve_matrix; 
      rewrite Cexp_6PI4; rewrite Cexp_2PI4; repeat group_radicals; lca.
Qed.    

Lemma apply_H_equivalence_sound : forall {dim} (l l' : PI4_ucom_l dim) q,
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

Lemma apply_H_equivalences_sound: forall {dim} (l : PI4_ucom_l dim) n, 
  l ≅l≅ apply_H_equivalences l n.
Proof. 
  intros.
  generalize dependent l.
  induction n; try easy.
  intros.
  destruct l; try easy.
  destruct g; simpl.
  - dependent destruction p.
    destruct (apply_H_equivalence (App1 UPI4_H n0 :: l) n0) eqn:res.
    all: rewrite <- IHn; try reflexivity.
    apply (apply_H_equivalence_sound _ _ _ res).
  - rewrite <- IHn; reflexivity.
  - inversion p.
Qed.

Lemma hadamard_reduction_sound: forall {dim} (l : PI4_ucom_l dim), 
  l ≅l≅ hadamard_reduction l.
Proof. intros. apply apply_H_equivalences_sound. Qed.

(* TODO: We should also be able to prove that the Hadamard reduction optimization 
   reduces the number of Hadamard gates in the program. *)
