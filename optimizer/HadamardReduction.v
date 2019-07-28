Require Import Phase.
Require Import UnitarySem.
Require Import Tactics.
Require Import ListRepresentation.
Require Import Equivalences.
Require Import Proportional.
Require Import List.
Open Scope ucom.

(*****************************************************************)
(** Optimization: rewrite w/ a single-qubit circuit equivalence **)
(*****************************************************************)

(* We restrict to single-qubit circuit equivalences for now because dealing
   with multi-qubit patterns is tedious with the list representation. For
   example, say that we are looking for the sub-circuit:
       C = [ H 0; H 2; CNOT 1 2; X 0 ]
   When searching for this sub-circuit, we need to keep in mind that these
   gates may be interspersed among other gates in the circuit in any order
   that respects dependence relationships. For example, the following program
   contains C, although it may not be obvious from casual inspection.
       [X 3; H 2; H 0; X 0; CNOT 0 3; CNOT 1 2]
*)

Definition single_qubit_pattern := list (fUnitary 1).

Fixpoint single_qubit_pattern_to_program {dim} (pat : single_qubit_pattern) q : gate_list dim :=
  match pat with
  | [] => []
  | u :: t => App1 u q :: (single_qubit_pattern_to_program t q)
  end. 

(* If the next sequence of gates applied to qubit q matches 'pat', then remove
   'pat' from the program. *)
Fixpoint remove_single_qubit_pattern {dim} (l : gate_list dim) (q : nat) (pat : single_qubit_pattern) : option (gate_list dim) :=
  match pat with
  | [] => Some l
  | u :: t =>
      match next_single_qubit_gate l q with
      | Some (u', l') =>
          if match_gate u u'
          then remove_single_qubit_pattern l' q t
          else None
      | _ => None
      end
  end.

(* If the next sequence of gates applied to qubit q matches 'pat', then replace
   'pat' with 'rep'. *)
Definition replace_single_qubit_pattern {dim} (l : gate_list dim) (q : nat) (pat rep : single_qubit_pattern) : option (gate_list dim) :=
  match (remove_single_qubit_pattern l q pat) with
  | Some l' => Some ((single_qubit_pattern_to_program rep q) ++ l')
  | None => None
  end.
     
(* Simple tests *)
Definition test : gate_list 4 := (_H 1) :: (_X 0) :: (_CNOT 2 3) :: (_Z 0) :: (_H 0) :: (_Z 1) :: (_Z 2) :: (_CNOT 0 2) :: [].
Compute (next_single_qubit_gate test 0).
Compute (next_single_qubit_gate test 1).
Compute (next_single_qubit_gate test 2).
Compute (next_two_qubit_gate test 2).
Compute (next_two_qubit_gate test 3).
Compute (next_single_qubit_gate test 4).
Compute (replace_single_qubit_pattern test 0 (fU_X :: fU_PI4 4 :: []) (fU_H :: fU_H :: [])).
Compute (replace_single_qubit_pattern test 0 (fU_X :: fU_H :: []) (fU_PI4 4:: fU_PI4 4 :: [])).

Lemma remove_single_qubit_pattern_correct : forall {dim} (l l' : gate_list dim) (q : nat) (pat : single_qubit_pattern),
  remove_single_qubit_pattern l q pat = Some l' ->
  l =l= (single_qubit_pattern_to_program pat q) ++ l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction pat; intros.
  - inversion H; subst. reflexivity.
  - simpl in H. 
    remember (next_single_qubit_gate l q) as next_gate.
    symmetry in Heqnext_gate.
    destruct next_gate; try easy.
    destruct p. 
    remember (match_gate a f) as gate_match.
    destruct gate_match; try easy.
    symmetry in Heqgate_match.
    rewrite match_gate_refl in Heqgate_match; subst.
    simpl.
    rewrite <- (IHpat _ _ H). 
    apply (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
Qed.

Lemma remove_single_qubit_pattern_correct' : forall {dim} (l l' : gate_list dim) (q : nat) (pat : single_qubit_pattern),
  remove_single_qubit_pattern l q pat = Some l' ->
  l ≅l≅ ((single_qubit_pattern_to_program pat q) ++ l').
Proof.
  exists 0%R. rewrite eulers0. rewrite Mscale_1_l.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction pat; intros.
  - inversion H; subst. reflexivity.
  - simpl in H. 
    remember (next_single_qubit_gate l q) as next_gate.
    symmetry in Heqnext_gate.
    destruct next_gate; try easy.
    destruct p. 
    remember (match_gate a f) as gate_match.
    destruct gate_match; try easy.
    symmetry in Heqgate_match.
    rewrite match_gate_refl in Heqgate_match; subst.
    simpl.
    rewrite <- (IHpat _ _ H). 
    apply (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
Qed.

Lemma replace_single_qubit_pattern_sound : forall {dim} (l l' : gate_list dim) (q : nat) (pat rep : single_qubit_pattern),
  @uc_equiv_l dim (single_qubit_pattern_to_program pat q) (single_qubit_pattern_to_program rep q) ->
  replace_single_qubit_pattern l q pat rep = Some l' ->
  l =l= l'.
Proof.
  intros.
  unfold replace_single_qubit_pattern in H0.
  remember (remove_single_qubit_pattern l q pat) as remove_pat.
  destruct remove_pat; try easy.
  symmetry in Heqremove_pat.
  apply remove_single_qubit_pattern_correct in Heqremove_pat.
  inversion H0; subst.
  rewrite Heqremove_pat.
  rewrite H.
  reflexivity.
Qed.

Lemma replace_single_qubit_pattern_sound' : forall {dim} (l l' : gate_list dim) (q : nat) (pat rep : single_qubit_pattern),
  @uc_cong_l dim (single_qubit_pattern_to_program pat q) (single_qubit_pattern_to_program rep q) ->
  replace_single_qubit_pattern l q pat rep = Some l' ->
  l ≅l≅ l'.
Proof.
  intros.
  unfold replace_single_qubit_pattern in H0.
  remember (remove_single_qubit_pattern l q pat) as remove_pat.
  destruct remove_pat; try easy.
  symmetry in Heqremove_pat.
  apply remove_single_qubit_pattern_correct' in Heqremove_pat.
  inversion H0; subst.
  rewrite Heqremove_pat. rewrite H. reflexivity.
Qed.

(* TODO: We might also want to prove something along the lines of: the resulting
   program contains 'rep'. *)

(* Given a list of rewrite rules, try to apply each rule until one succeeds. 
   Return None if no rewrite succeeds. *)
Fixpoint try_rewrites {dim} l (rules : list (gate_list dim -> option (gate_list dim))) :=
  match rules with
  | [] => None
  | h :: t => match (h l) with
            | Some l' => Some l'
            | None => try_rewrites l t
            end
  end.

Lemma try_apply_rewrites_sound : forall {dim} (l l' : gate_list dim) rules,
  (forall r, In r rules -> (forall l l', r l = Some l' -> l =l= l')) ->
  try_rewrites l rules = Some l' ->
  l =l= l'.
Proof.
  intros.
  induction rules.
  - inversion H0.
  - simpl in H0.
    remember (a l) as al. 
    destruct al; inversion H0; subst.
    + symmetry in Heqal.
      assert (In a (a :: rules)) by (apply in_eq).
      apply (H a H1 l l' Heqal).
    + apply IHrules; try assumption.
      intros.
      apply (H r).
      apply in_cons; assumption.
      assumption.
Qed.

Lemma try_apply_rewrites_sound_cong : forall {dim} (l l' : gate_list dim) rules,
  (forall r, In r rules -> (forall l l', r l = Some l' -> l ≅l≅ l')) ->
  try_rewrites l rules = Some l' ->
  l ≅l≅ l'.
Proof.
  intros.
  induction rules.
  - inversion H0.
  - simpl in H0.
    remember (a l) as al. 
    destruct al; inversion H0; subst.
    + symmetry in Heqal.
      assert (In a (a :: rules)) by (apply in_eq).
      apply (H a H1 l l' Heqal).
    + apply IHrules; try assumption.
      intros.
      apply (H r).
      apply in_cons; assumption.
      assumption.
Qed.


(*******************************************)
(** Optimization: hadamard gate reduction **)
(*******************************************)

(** CURRENTLY NOT VERIFIED **)

(* This optimization pass reduces the number of H gates in a program
   using a variety of rewrite rules. *)

(* Hadamard Reduction Optimization
   
   Try to apply each the following equivalences to c. If one
   of the equivalences applies, then return the circuit resulting from
   the appropriate substitution.

   #1  - H q; P q; H q ≡ P† q; H q; P† q 
   #2  - H q; P† q; H q ≡ P q; H q; P q 
   #3a - H q1; H q2; CNOT q1 q2; H q1; H q1 ≡ CNOT q2 q1 
   #3b - H q2; H q1; CNOT q1 q2; H q1; H q2 ≡ CNOT q2 q1 
   #4  - H q2; P q2; CNOT q1 q2; P† q2; H q2 ≡ P† q2; CNOT q1 q2; P q2 
   #5  - H q2; P† q2; CNOT q1 q2; P q2; H q2 ≡ P q2; CNOT q1 q2; P† q2 
*)

Definition apply_H_equivalence1 {dim} q (l : gate_list dim) := 
  replace_single_qubit_pattern l q 
    (fU_H  :: fU_P :: fU_H :: []) 
    (fU_PDAG :: fU_H :: fU_PDAG :: []).

Definition apply_H_equivalence2 {dim} q (l : gate_list dim) := 
  replace_single_qubit_pattern l q 
    (fU_H :: fU_PDAG :: fU_H :: []) 
    (fU_P :: fU_H :: fU_P :: []).

Definition apply_H_equivalence3 {dim} q (l : gate_list dim) := 
  match (next_single_qubit_gate l q) with
  | Some (fU_H, l1) =>
      match (next_two_qubit_gate l1 q) with
      | Some (l2, m, n, l3) => 
          match (next_single_qubit_gate l3 q) with
          | Some (fU_H, l4) =>
              if (q =? m)
              (* case 3a *)
              then match (next_single_qubit_gate (rev l2) n) with
                   | Some (fU_H, l5) => 
                       match (next_single_qubit_gate l4 n) with
                       | Some (fU_H, l6) => 
                           Some ((rev l5) ++ [_CNOT n m] ++ l6)
                       | _ => None
                       end
                   | _ => None
                   end
              (* case 3b *)
              else match (next_single_qubit_gate (rev l2) m) with
                   | Some (fU_H, l5) => 
                       match (next_single_qubit_gate l4 m) with
                       | Some (fU_H, l6) => 
                           Some ((rev l5) ++ [_CNOT n m] ++ l6)
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

Definition apply_H_equivalence4 {dim} q (l : gate_list dim) :=
  match (remove_single_qubit_pattern l q (fU_H :: fU_P :: [])) with
  | None => None
  | Some l1 =>
      match (next_two_qubit_gate l1 q) with
      | None => None
      | Some (l2, q1, q2, l3) =>
          if q =? q2 
          then match (remove_single_qubit_pattern l3 q (fU_PDAG :: fU_H :: [])) with
               | None => None
               | Some l4 =>
                   Some (l2 ++ (_PDAG q2 :: _CNOT q1 q2 :: _P q2 :: []) ++ l4)
               end
          else None
      end
  end.

Definition apply_H_equivalence5 {dim} q (l : gate_list dim) :=
  match (remove_single_qubit_pattern l q (fU_H :: fU_PDAG :: [])) with
  | Some l1 =>
      match (next_two_qubit_gate l1 q) with
      | Some (l2, q1, q2, l3) =>
          if q =? q2 
          then match (remove_single_qubit_pattern l3 q (fU_P :: fU_H :: [])) with
               | Some l4 =>
                   Some (l2 ++ (_P q2 :: _CNOT q1 q2 :: _PDAG q2 :: []) ++ l4)
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition apply_H_equivalence {dim} (l : gate_list dim) (q : nat) : option (gate_list dim) :=
  try_rewrites l ((apply_H_equivalence1 q) :: (apply_H_equivalence2 q) :: (apply_H_equivalence3 q) :: (apply_H_equivalence4 q) :: (apply_H_equivalence5 q) :: []).

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
Fixpoint apply_H_equivalences {dim} (l : gate_list dim) (n: nat) : gate_list dim :=
  match n with
  | 0 => l
  | S n' => 
      match l with
      | [] => []
      | (App1 fU_H q) :: t => 
          match apply_H_equivalence l q with
          | None => (_H q) :: (apply_H_equivalences t n')
          | Some l' => apply_H_equivalences l' n'
          end
      | g :: t => g :: (apply_H_equivalences t n')
      end
  end.

Definition hadamard_reduction {dim} (l : gate_list dim) : gate_list dim := 
  apply_H_equivalences l (2 * (length l)).

Lemma apply_H_equivalence1_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence1 q l = Some l' ->
  l ≅l≅ l'. 
Proof.
  intros.
  eapply replace_single_qubit_pattern_sound'.
  2 : { apply H. }
  exists (PI / 4)%R.
  unfold uc_eval, ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try (remove_zero_gates; trivial).
  Msimpl. 
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  assert (hadamard × phase_shift (2 * PI / 4) × hadamard = (Cexp (PI / 4)%R) .* (phase_shift (6 * PI / 4) × hadamard  × phase_shift (6 * PI / 4))).
  { solve_matrix. 
    all: autorewrite with Cexp_db.
    all: C_field_simplify; try nonzero.
  }
  rewrite H1.
  repeat rewrite Mscale_mult_dist_l.
  repeat rewrite Mscale_kron_dist_r.  
  rewrite Mscale_kron_dist_l.
  reflexivity.
  rewrite Mscale_0_r.
  reflexivity.
Qed.

Lemma apply_H_equivalence2_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence2 q l = Some l' ->
  l ≅l≅ l'.
Proof. 
  intros.
  eapply replace_single_qubit_pattern_sound'; try apply H.
  exists (- PI / 4)%R.
  unfold uc_eval, ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try (remove_zero_gates; trivial).
  - Msimpl.
    restore_dims_strong; repeat rewrite kron_mixed_product.
    Msimpl.
    assert (hadamard × phase_shift (6 * PI / 4) × hadamard = (Cexp (- PI / 4)%R) .* phase_shift (2 * PI / 4) × hadamard × phase_shift (2 * PI / 4)).
    { solve_matrix. 
      all: autorewrite with Cexp_db.
      all: C_field_simplify; try nonzero.
    }
    rewrite H1.
    repeat rewrite Mscale_mult_dist_l.
    repeat rewrite Mscale_kron_dist_r.
    rewrite Mscale_kron_dist_l.
    reflexivity.
  - rewrite Mscale_0_r. reflexivity.
Qed.

Lemma nsqg_preserves_semantics' : forall {dim} (l l' : gate_list dim) (q : nat) (u : fUnitary 1),
  next_single_qubit_gate l q = Some (u, l') -> 
  l = App1 u q :: l'.
Proof.
  intros.
  unfold next_single_qubit_gate in H.
  induction l.
  - inversion H.
  - destruct a.
Admitted.

Lemma ntqg_preserves_semantics' : forall {dim} (l l1 l2 : gate_list dim) (q m n : nat),
  next_two_qubit_gate l q = Some (l1, m, n, l2) ->
  l = l1 ++ [App2 fU_CNOT m n] ++ l2.
Proof.
Admitted.
  
Lemma H_reduction_basic : forall {dim} (n : nat), 
  (n + 1 <= dim)%nat -> @App1 dim fU_H n :: App1 fU_H n :: [] =l= [].
Proof.
  intros.
  unfold uc_equiv_l. simpl.
  unfold uc_equiv. simpl.
  rewrite Mmult_1_l by auto with wf_db.
  unfold ueval1, pad.
  bdestructΩ (n + 1 <=? dim).
  restore_dims_strong.
  repeat rewrite kron_mixed_product.
  repeat rewrite Mmult_1_l by auto with wf_db.
  replace (hadamard × hadamard) with (I 2) by solve_matrix.
  repeat rewrite id_kron.
  unify_matrices_light.
Qed.

Lemma apply_H_equivalence3_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence3 q l = Some l' ->
  l ≅l≅ l'.
Proof.
  intros.
  unfold apply_H_equivalence3 in H.
  remember (next_single_qubit_gate l q) as pat.
  destruct pat. symmetry in Heqpat.
  destruct p.
  2 : inversion H.
  apply nsqg_preserves_semantics' in Heqpat.
  rewrite Heqpat. clear Heqpat.
  dependent destruction f; inversion H. clear H1.
  remember (next_two_qubit_gate g q) as pat.
  symmetry in Heqpat.
  destruct pat.
  repeat destruct p.
  assert (does_not_reference g1 q = true) by (eapply ntqg_l1_does_not_reference; apply Heqpat).
  apply ntqg_preserves_semantics' in Heqpat.
  rewrite Heqpat. clear Heqpat.
  remember (next_single_qubit_gate g0 q) as pat.
  symmetry in Heqpat.
  destruct pat.
  destruct p.
  apply nsqg_preserves_semantics in Heqpat.
  apply uc_equiv_cong_l in Heqpat.
  rewrite Heqpat. clear Heqpat.
  dependent destruction f; try easy. 2 : inversion H. 2 : inversion H.
  bdestruct (q =? n0).
  - subst n0. remember (next_single_qubit_gate (rev g1) n) as pat.
    symmetry in Heqpat.
    destruct pat.
    destruct p.
    2 : inversion H.
    apply nsqg_preserves_semantics' in Heqpat.
    rewrite <- (rev_involutive g3) in Heqpat.
    rewrite <- rev_unit in Heqpat.
    apply (f_equal (@rev (gate_app dim))) in Heqpat.
    repeat rewrite rev_involutive in Heqpat.
    apply (does_not_reference_commutes_app1 _ fU_H _) in H0.
    apply uc_equiv_cong_l in H0.
    simpl in H0. 
    rewrite app_comm_cons.
    rewrite H0.
    subst g1.
    dependent destruction f; try easy.
    remember (next_single_qubit_gate g2 n) as pat.
    symmetry in Heqpat.
    destruct pat; try easy.
    destruct p.
    apply nsqg_preserves_semantics' in Heqpat.
    rewrite Heqpat. clear Heqpat.
    dependent destruction f; try easy.
    inversion H.
    simpl.
    repeat rewrite <- app_assoc. simpl.
    apply uc_cong_l_app_congruence; try reflexivity.
    rewrite <- (app_nil_l g1).
    repeat rewrite app_comm_cons.
    apply uc_cong_l_app_congruence; try reflexivity.
    admit.
  - remember (next_single_qubit_gate (rev g1) n0) as pat.
    symmetry in Heqpat.
    destruct pat.
    2 : inversion H.
    destruct p.
    apply nsqg_preserves_semantics' in Heqpat.
    rewrite <- (rev_involutive g3) in Heqpat.
    rewrite <- rev_unit in Heqpat.
    apply (f_equal (@rev (gate_app dim))) in Heqpat.
    repeat rewrite rev_involutive in Heqpat.
    apply (does_not_reference_commutes_app1 _ fU_H _) in H0.
    apply uc_equiv_cong_l in H0.
    simpl in H0. 
    rewrite app_comm_cons.
    rewrite H0.
    subst g1.
    dependent destruction f; try easy.
    remember (next_single_qubit_gate g2 n0) as pat.
    symmetry in Heqpat.
    destruct pat. 2 : inversion H.
    destruct p.
    apply nsqg_preserves_semantics' in Heqpat.
    rewrite Heqpat. clear Heqpat.
    dependent destruction f; try easy.
    inversion H.
    simpl.
    repeat rewrite <- app_assoc. simpl.
    apply uc_cong_l_app_congruence; try reflexivity.
    rewrite <- (app_nil_l g1).
    repeat rewrite app_comm_cons.
    apply uc_cong_l_app_congruence; try reflexivity.
    admit. 
Admitted.

Lemma apply_H_equivalence4_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence4 q l = Some l' ->
  l ≅l≅ l'.
Proof.
  intros. 
  unfold apply_H_equivalence4 in H.
  remember (remove_single_qubit_pattern l q (fU_H :: fU_P :: [])) as pat.
  symmetry in Heqpat.
  destruct pat.
  2 : { inversion H. }
  apply remove_single_qubit_pattern_correct in Heqpat.
  apply uc_equiv_cong_l in Heqpat.
  remember (next_two_qubit_gate g q) as pat2.
  symmetry in Heqpat2.
  destruct pat2.
  2 : { inversion H. }
  repeat destruct p.
  assert (does_not_reference g1 q = true) by (eapply ntqg_l1_does_not_reference; apply Heqpat2).
  apply ntqg_preserves_semantics in Heqpat2.
  apply uc_equiv_cong_l in Heqpat2.
  bdestruct (q =? n).
  2 : { inversion H. }
  remember (remove_single_qubit_pattern g0 q (fU_PDAG :: fU_H :: [])) as pat3.
  symmetry in Heqpat3.
  destruct pat3.
  2 : { inversion H. }
  apply remove_single_qubit_pattern_correct in Heqpat3.
  apply uc_equiv_cong_l in Heqpat3.
  inversion H.
  rewrite Heqpat.
  rewrite Heqpat2.
  rewrite Heqpat3.
  simpl.
  repeat rewrite app_comm_cons.
  rewrite <- (app_nil_l g1).
  rewrite app_comm_cons.
  assert (H0' := H0).
  apply (does_not_reference_commutes_app1 _ fU_P _) in H0.
  apply (does_not_reference_commutes_app1 _ fU_H _) in H0'.
  apply uc_equiv_cong_l in H0.
  apply uc_equiv_cong_l in H0'.
  rewrite H0.
  rewrite <- (app_nil_l g1).
  rewrite app_comm_cons.
  rewrite H0'.
  simpl.
  rewrite <- (app_nil_l g2).
  repeat rewrite app_comm_cons.
  repeat rewrite <- app_assoc.
  apply uc_cong_l_app_congruence; try reflexivity.
  repeat rewrite app_assoc.
  apply uc_cong_l_app_congruence; try reflexivity.
  simpl.
  exists 0. rewrite Cexp_0. rewrite Mscale_1_l.
  simpl.
Admitted.

Lemma apply_H_equivalence5_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence5 q l = Some l' ->
  l ≅l≅ l'.
Proof.
  intros.
  unfold apply_H_equivalence5 in H.
  remember (remove_single_qubit_pattern l q (fU_H :: fU_PDAG :: [])) as pat.
  symmetry in Heqpat.
  destruct pat.
  2 : { inversion H. }
  apply remove_single_qubit_pattern_correct in Heqpat.
  apply uc_equiv_cong_l in Heqpat.
  remember (next_two_qubit_gate g q) as pat2.
  symmetry in Heqpat2.
  destruct pat2.
  2 : { inversion H. }
  repeat destruct p.
  assert (does_not_reference g1 q = true) by (eapply ntqg_l1_does_not_reference; apply Heqpat2).
  apply ntqg_preserves_semantics in Heqpat2.
  apply uc_equiv_cong_l in Heqpat2.
  bdestruct (q =? n). 2 : { inversion H. }
  subst.
  remember (remove_single_qubit_pattern g0 n (fU_P :: fU_H ::[])) as pat3.
  symmetry in Heqpat3.
  destruct pat3; try inversion H.
  apply remove_single_qubit_pattern_correct in Heqpat3.
  apply uc_equiv_cong_l in Heqpat3.
  inversion H.
  rewrite Heqpat.
  rewrite Heqpat2.
  rewrite Heqpat3.
  simpl.
  repeat rewrite app_comm_cons.
  rewrite <- (app_nil_l g1).
  rewrite app_comm_cons.
  assert (H0' := H0).
  apply (does_not_reference_commutes_app1 _ fU_PDAG _) in H0.
  apply (does_not_reference_commutes_app1 _ fU_H _) in H0'.
  apply uc_equiv_cong_l in H0.
  apply uc_equiv_cong_l in H0'.
  rewrite H0.
  rewrite <- (app_nil_l g1). rewrite app_comm_cons.
  rewrite app_assoc. rewrite H0'.
  repeat rewrite <- app_assoc. simpl.
  apply uc_cong_l_app_congruence; try reflexivity.
  rewrite <- (app_nil_l g2).
  repeat rewrite app_comm_cons.
  apply uc_cong_l_app_congruence; try reflexivity.
  exists 0. rewrite Cexp_0. rewrite Mscale_1_l.
  simpl.
  
  unfold ueval_cnot, ueval1, ueval_unitary1, pad.
  gridify.
  - apply f_equal2.
    + apply f_equal2; trivial. apply f_equal2; trivial.
      solve_matrix; rewrite Cexp_6PI4; rewrite Cexp_2PI4;
      C_field_simplify; try nonzero; lca.
    + apply f_equal2; trivial. apply f_equal2; trivial.
      solve_matrix; rewrite Cexp_6PI4; rewrite Cexp_2PI4;
      C_field_simplify; try nonzero; lca.
  - apply f_equal2.
    + do 4 (apply f_equal2; trivial); 
      solve_matrix; rewrite Cexp_6PI4; rewrite Cexp_2PI4;
      C_field_simplify; try nonzero; try lca.
    + do 4 (apply f_equal2; trivial); 
      solve_matrix; rewrite Cexp_6PI4; rewrite Cexp_2PI4;
      C_field_simplify; try nonzero; try lca.
Qed.    


Lemma apply_H_equivalence_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence l q = Some l' -> 
  l ≅l≅ l'.
Proof. 
  unfold apply_H_equivalence.
  intros dim l l' q.
  apply try_apply_rewrites_sound_cong.
  intros. 
  inversion H.
  subst; apply (apply_H_equivalence1_sound _ _ _ H0).
  inversion H1. 
  subst; apply (apply_H_equivalence2_sound _ _ _ H0). 
  inversion H2. 
  subst; apply (apply_H_equivalence3_sound _ _ _ H0). 
  inversion H3. 
  subst; apply (apply_H_equivalence4_sound _ _ _ H0). 
  inversion H4. 
  subst; apply (apply_H_equivalence5_sound _ _ _ H0). 
  inversion H5.
Qed.

Lemma apply_H_equivalences_sound: forall {dim} (l : gate_list dim) n, 
  l ≅l≅ apply_H_equivalences l n.
Proof. 
  intros.
  generalize dependent l.
  induction n; try easy.
  intros.
  destruct l; try easy.
  destruct g; simpl.
  - dependent destruction f;
    remember (apply_H_equivalence (App1 fU_H n0 :: l) n0) as res; symmetry in Heqres;
    destruct res;
    rewrite <- IHn;
    try apply (apply_H_equivalence_sound _ _ _ Heqres);
    reflexivity.
  - rewrite <- IHn; reflexivity.
Qed.

Lemma hadamard_reduction_sound: forall {dim} (l : gate_list dim), 
  l ≅l≅ hadamard_reduction l.
Proof. intros. apply apply_H_equivalences_sound. Qed.

(* TODO: We should also be able to prove that the Hadamard reduction optimization 
   reduces the number of Hadamard gates in the program. *)
