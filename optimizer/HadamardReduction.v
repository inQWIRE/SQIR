Require Import UnitarySem.
Require Import Equivalences.
Require Import PI4GateSet.
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

Definition single_qubit_pattern := list (PI4_Unitary 1).

Fixpoint single_qubit_pattern_to_program dim (pat : single_qubit_pattern) q : PI4_ucom_l dim :=
  match pat with
  | [] => []
  | u :: t => App1 u q :: (single_qubit_pattern_to_program dim t q)
  end. 

(* If the next sequence of gates applied to qubit q matches 'pat', then remove
   'pat' from the program. *)
Fixpoint remove_single_qubit_pattern {dim} (l : PI4_ucom_l dim) (q : nat) (pat : single_qubit_pattern) : option (PI4_ucom_l dim) :=
  match pat with
  | [] => Some l
  | u :: t =>
      match next_single_qubit_gate l q with
      | Some (l1, u', l2) =>
          if match_gate u u'
          then remove_single_qubit_pattern (l1 ++ l2) q t
          else None
      | _ => None
      end
  end.

(* If the next sequence of gates applied to qubit q matches 'pat', then replace
   'pat' with 'rep'. *)
Definition replace_single_qubit_pattern {dim} (l : PI4_ucom_l dim) (q : nat) (pat rep : single_qubit_pattern) : option (PI4_ucom_l dim) :=
  match (remove_single_qubit_pattern l q pat) with
  | Some l' => Some ((single_qubit_pattern_to_program dim rep q) ++ l')
  | None => None
  end.
     
(* Simple tests *)
Definition test : PI4_ucom_l 4 := (App1 UPI4_H 1) :: (App1 UPI4_X 0) :: (App2 UPI4_CNOT 2 3) :: (App1 UPI4_Z 0) :: (App1 UPI4_H 0) :: (App1 UPI4_Z 1) :: (App1 UPI4_Z 2) :: (App2 UPI4_CNOT 0 2) :: [].
Compute (next_single_qubit_gate test 0).
Compute (next_single_qubit_gate test 1).
Compute (next_single_qubit_gate test 2).
Compute (next_two_qubit_gate test 2).
Compute (next_two_qubit_gate test 3).
Compute (next_single_qubit_gate test 4).
Compute (replace_single_qubit_pattern test 0 (UPI4_X :: UPI4_PI4 4 :: []) (UPI4_H :: UPI4_H :: [])).
Compute (replace_single_qubit_pattern test 0 (UPI4_X :: UPI4_H :: []) (UPI4_PI4 4:: UPI4_PI4 4 :: [])).

Lemma remove_single_qubit_pattern_correct : forall {dim} (l l' : PI4_ucom_l dim) (q : nat) (pat : single_qubit_pattern),
  remove_single_qubit_pattern l q pat = Some l' ->
  l =l= (single_qubit_pattern_to_program dim pat q) ++ l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction pat; intros.
  - inversion H; subst. reflexivity.
  - simpl in H. 
    destruct (next_single_qubit_gate l q) eqn:nsqg; try easy.
    repeat destruct p.
    destruct (match_gate a p) eqn:Hmatch; try easy.
    rewrite match_gate_refl in Hmatch; subst.
    simpl.
    rewrite <- (IHpat _ _ H). 
    apply (nsqg_commutes _ _ _ _ _ nsqg).
Qed.

Lemma replace_single_qubit_pattern_sound : forall {dim} (l l' : PI4_ucom_l dim) (q : nat) (pat rep : single_qubit_pattern),
  single_qubit_pattern_to_program dim pat q =l= single_qubit_pattern_to_program dim rep q ->
  replace_single_qubit_pattern l q pat rep = Some l' ->
  l =l= l'.
Proof.
  intros.
  unfold replace_single_qubit_pattern in H0.
  destruct (remove_single_qubit_pattern l q pat) eqn:rem; try easy.
  apply remove_single_qubit_pattern_correct in rem.
  inversion H0; subst.
  rewrite rem.
  rewrite H.
  reflexivity.
Qed.

(* Equivalence up to a phase. *)
Lemma replace_single_qubit_pattern_sound' : forall {dim} (l l' : PI4_ucom_l dim) (q : nat) (pat rep : single_qubit_pattern),
  single_qubit_pattern_to_program dim pat q ≅l≅ single_qubit_pattern_to_program dim rep q ->
  replace_single_qubit_pattern l q pat rep = Some l' ->
  l ≅l≅ l'.
Proof.
  intros.
  unfold replace_single_qubit_pattern in H0.
  destruct (remove_single_qubit_pattern l q pat) eqn:rem; try easy.
  apply remove_single_qubit_pattern_correct in rem.
  apply uc_equiv_cong_l in rem.
  inversion H0; subst.
  rewrite rem. 
  rewrite H. 
  reflexivity.
Qed.

(* TODO: We might also want to prove something along the lines of: the resulting
   program contains 'rep'. *)

(* Given a list of rewrite rules, try to apply each rule until one succeeds. 
   Return None if no rewrite succeeds. *)
Fixpoint try_rewrites {dim} l (rules : list (PI4_ucom_l dim -> option (PI4_ucom_l dim))) :=
  match rules with
  | [] => None
  | h :: t => match (h l) with
            | Some l' => Some l'
            | None => try_rewrites l t
            end
  end.

Lemma try_apply_rewrites_sound : forall {dim} (l l' : PI4_ucom_l dim) rules,
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

Lemma try_apply_rewrites_sound_cong : forall {dim} (l l' : PI4_ucom_l dim) rules,
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
          (* case 3a *)
          then match (last_single_qubit_gate l1 n) with
               | Some (l1_1, UPI4_H, l1_2) => 
                   let l1 := l1_1 ++ l1_2 in
                   match (next_single_qubit_gate l2 m) with
                   | Some (l2_1, UPI4_H, l2_2) =>
                       let l2 := l2_1 ++ l2_2 in
                       match (next_single_qubit_gate l2 n) with
                       | Some (l2_1, UPI4_H, l2_2) => 
                           let l2 := l2_1 ++ l2_2 in
                           Some (l1 ++ [App2 UPI4_CNOT n m] ++ l2)
                       | _ => None
                       end
                   | _ => None
                   end
               | _ => None
               end
          (* case 3b *)
          else match (last_single_qubit_gate l1 m) with
               | Some (l1_1, UPI4_H, l1_2) => 
                   let l1 := l1_1 ++ l1_2 in
                   match (next_single_qubit_gate l2 m) with
                   | Some (l2_1, UPI4_H, l2_2) =>
                       let l2 := l2_1 ++ l2_2 in
                       match (next_single_qubit_gate l2 n) with
                       | Some (l2_1, UPI4_H, l2_2) => 
                           let l2 := l2_1 ++ l2_2 in
                           Some (l1 ++ [App2 UPI4_CNOT n m] ++ l2)
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
                   Some (l2 ++ (App1 UPI4_PDAG q2 :: App2 UPI4_CNOT q1 q2 :: App1 UPI4_P q2 :: []) ++ l4)
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
                   Some (l2 ++ (App1 UPI4_P q2 :: App2 UPI4_CNOT q1 q2 :: App1 UPI4_PDAG q2 :: []) ++ l4)
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition apply_H_equivalence {dim} (l : PI4_ucom_l dim) (q : nat) : option (PI4_ucom_l dim) :=
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
Fixpoint apply_H_equivalences {dim} (l : PI4_ucom_l dim) (n: nat) : PI4_ucom_l dim :=
  match n with
  | 0 => l
  | S n' => 
      match l with
      | [] => []
      | (App1 UPI4_H q) :: t => 
          match apply_H_equivalence l q with
          | None => (App1 UPI4_H q) :: (apply_H_equivalences t n')
          | Some l' => apply_H_equivalences l' n'
          end
      | g :: t => g :: (apply_H_equivalences t n')
      end
  end.

Definition hadamard_reduction {dim} (l : PI4_ucom_l dim) : PI4_ucom_l dim := 
  apply_H_equivalences l (2 * (length l)).

(* Small example - both tests are the same circuit, just with the
   gate list reordered. The output should contain 2 H gates. *)
Definition hadamard_reduction_test1 : PI4_ucom_l 4 :=
  App1 UPI4_X 0 :: App1 UPI4_H 0 :: App1 UPI4_P 0 :: App1 UPI4_H 0 :: App1 UPI4_X 0 :: App1 UPI4_H 1 :: App1 UPI4_H 2 :: App2 UPI4_CNOT 2 1 :: App1 UPI4_H 1 :: App1 UPI4_H 2 :: App1 UPI4_H 3 ::App1 UPI4_P 3 :: App2 UPI4_CNOT 3 2 :: App1 UPI4_H 3 :: App1 UPI4_P 3 :: App2 UPI4_CNOT 2 3 :: App1 UPI4_PDAG 3 :: App1 UPI4_H 3 :: [].
Compute (hadamard_reduction hadamard_reduction_test1).

Definition hadamard_reduction_test2 : PI4_ucom_l 4 :=
  App1 UPI4_H 2 :: App1 UPI4_H 3 :: App1 UPI4_X 0 ::  App1 UPI4_H 1 :: App2 UPI4_CNOT 2 1 :: App1 UPI4_P 3 :: App1 UPI4_H 0 :: App1 UPI4_H 2 :: App1 UPI4_P 0  :: App2 UPI4_CNOT 3 2 :: App1 UPI4_H 3 :: App1 UPI4_P 3 :: App2 UPI4_CNOT 2 3 :: App1 UPI4_H 0 :: App1 UPI4_X 0 :: App1 UPI4_PDAG 3 :: App1 UPI4_H 1 :: App1 UPI4_H 3 :: [].
Compute (hadamard_reduction hadamard_reduction_test2).

Lemma apply_H_equivalence1_sound : forall {dim} (l l' : PI4_ucom_l dim) q,
  apply_H_equivalence1 q l = Some l' ->
  l ≅l≅ l'. 
Proof.
  intros.
  apply replace_single_qubit_pattern_sound' in H; try assumption.
  exists (PI / 4)%R.
  destruct dim.
  simpl; unfold pad. bdestruct_all. Msimpl_light; reflexivity.
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
  simpl; unfold pad. bdestruct_all. Msimpl_light; reflexivity.
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
    destruct (next_single_qubit_gate g1 n0) eqn:nsqg2; try discriminate.
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
    subst. unfold uc_equiv_l, uc_equiv.
    repeat (try rewrite PI4_to_base_ucom_l_app;
            try rewrite list_to_ucom_append;
            simpl). 
    (* get rid of dim = 0 case *)
    destruct dim. 
    unfold ueval_cnot, pad.
    bdestruct_all; Msimpl_light; reflexivity.
    autorewrite with eval_db; try lia.
    gridify.
    assert ([@App1 _ dim UPI4_H n0] ++ [App1 UPI4_H n] =l= [App1 UPI4_H n] ++ [App1 UPI4_H n0]).
    { simpl. unfold uc_equiv_l; simpl. 
      repeat rewrite <- useq_assoc. 
      rewrite U_V_comm. 
      reflexivity.
      apply not_eq_sym; assumption. }
    rewrite (app_assoc [App1 UPI4_H n0]).
    rewrite H0; clear.
    repeat rewrite <- app_assoc; simpl.
    replace (App2 UPI4_CNOT n n0 :: g8 ++ g7) with ([App2 UPI4_CNOT n n0] ++ g8 ++ g7) by easy.
    replace (App1 UPI4_H n :: App1 UPI4_H n0 :: App2 UPI4_CNOT n0 n :: App1 UPI4_H n :: App1 UPI4_H n0 :: g8 ++ g7) with ((App1 UPI4_H n :: App1 UPI4_H n0 :: App2 UPI4_CNOT n0 n :: App1 UPI4_H n :: App1 UPI4_H n0 :: []) ++ g8 ++ g7) by easy.
    unfold uc_equiv_l.
    repeat (try rewrite PI4_to_base_ucom_l_app;
            try rewrite list_to_ucom_append).
    do 3 (apply useq_congruence; try reflexivity).
    specialize (@H_swaps_CNOT dim n n0) as H.
    repeat rewrite useq_assoc in H.
    unfold uc_equiv in *. simpl in *.
    destruct dim.
    unfold ueval_cnot, pad. Msimpl_light; reflexivity.
    rewrite denote_SKIP; try lia.
    Msimpl_light.
    rewrite hadamard_rotation.
    repeat rewrite denote_H in H.
    repeat rewrite denote_cnot in H.
    apply H.
  - destruct (last_single_qubit_gate g2 n0) eqn:lsqg; try discriminate.
    repeat destruct p; dependent destruction p; try discriminate.
    destruct (next_single_qubit_gate g1 n0) eqn:nsqg2; try discriminate.
    repeat destruct p; dependent destruction p; try discriminate.
    destruct (next_single_qubit_gate (g6 ++ g5) n) eqn:nsqg3; try discriminate.
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
    + subst. unfold uc_equiv_l, uc_equiv.
      repeat (try rewrite PI4_to_base_ucom_l_app;
              try rewrite list_to_ucom_append;
              simpl). 
      (* get rid of dim = 0 case *)
      destruct dim. 
      unfold ueval_cnot, pad.
      bdestruct_all; Msimpl_light; reflexivity.
      autorewrite with eval_db; try lia.
      bdestruct_all; Msimpl_light; reflexivity.
    + assert ([@App1 _ dim UPI4_H n0] ++ [App1 UPI4_H n] =l= [App1 UPI4_H n] ++ [App1 UPI4_H n0]).
      { simpl. unfold uc_equiv_l; simpl. 
        repeat rewrite <- useq_assoc. 
        rewrite U_V_comm. 
        reflexivity.
        apply not_eq_sym; assumption. }
      rewrite (app_assoc [App1 UPI4_H n0]).
      rewrite <- (app_assoc g4).
      rewrite <- (app_assoc g3).
      rewrite H0; clear.
      repeat rewrite <- app_assoc; simpl.
      replace (App2 UPI4_CNOT n n0 :: g8 ++ g7) with ([App2 UPI4_CNOT n n0] ++ g8 ++ g7) by easy.
      replace (App1 UPI4_H n :: App1 UPI4_H n0 :: App2 UPI4_CNOT n0 n :: App1 UPI4_H n :: App1 UPI4_H n0 :: g8 ++ g7) with ((App1 UPI4_H n :: App1 UPI4_H n0 :: App2 UPI4_CNOT n0 n :: App1 UPI4_H n :: App1 UPI4_H n0 :: []) ++ g8 ++ g7) by easy.
      unfold uc_equiv_l.
      repeat (try rewrite PI4_to_base_ucom_l_app;
              try rewrite list_to_ucom_append).
      do 3 (apply useq_congruence; try reflexivity).
      specialize (@H_swaps_CNOT dim n n0) as H.
      repeat rewrite useq_assoc in H.
      unfold uc_equiv in *. simpl in *.
      destruct dim.
      unfold ueval_cnot, pad. Msimpl_light; reflexivity.
      rewrite denote_SKIP; try lia.
      Msimpl_light.
      rewrite hadamard_rotation.
      repeat rewrite denote_H in H.
      repeat rewrite denote_cnot in H.
      apply H. 
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
  specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as H1.
  apply ntqg_preserves_structure in ntqg; subst.
  bdestruct (q =? n); try discriminate.
  destruct (remove_single_qubit_pattern g q (UPI4_PDAG :: UPI4_H :: [])) eqn:rsqp2; try discriminate.
  apply remove_single_qubit_pattern_correct in rsqp2.
  inversion H; subst.
  simpl in *.
  rewrite rsqp1, rsqp2.
  repeat rewrite app_comm_cons.
  replace (App1 UPI4_H n :: App1 UPI4_P n :: g0) with ([App1 UPI4_H n] ++ [App1 UPI4_P n] ++ g0) by easy.
  specialize (does_not_reference_commutes_app1 _ UPI4_P _ H1) as H2. 
  rewrite H2.
  rewrite app_assoc.
  specialize (does_not_reference_commutes_app1 _ UPI4_H _ H1) as H3. 
  rewrite H3.
  clear.
  repeat rewrite <- app_assoc; simpl.
  rewrite <- (app_nil_l p).
  repeat rewrite app_comm_cons.
  do 2 (apply uc_app_congruence; try reflexivity).
  unfold uc_equiv_l, uc_equiv; simpl.
  rewrite hadamard_rotation.
  repeat rewrite phase_shift_rotation.
  destruct dim.
  unfold pad; bdestruct_all; Msimpl_light; trivial.
  autorewrite with eval_db; try lia.
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
  destruct (next_two_qubit_gate p q) eqn:ntqg; try easy.
  repeat destruct p0; dependent destruction p0.
  specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as H1.
  apply ntqg_preserves_structure in ntqg; subst.
  bdestruct (q =? n); try easy.
  destruct (remove_single_qubit_pattern g q (UPI4_P :: UPI4_H :: [])) eqn:rsqp2; try easy.
  apply remove_single_qubit_pattern_correct in rsqp2.
  inversion H; subst.
  simpl in *.
  rewrite rsqp1, rsqp2.
  repeat rewrite app_comm_cons.
  replace (App1 UPI4_H n :: App1 UPI4_PDAG n :: g0) with ([App1 UPI4_H n] ++ [App1 UPI4_PDAG n] ++ g0) by easy.
  specialize (does_not_reference_commutes_app1 _ UPI4_PDAG _ H1) as H2. 
  rewrite H2.
  rewrite app_assoc.
  specialize (does_not_reference_commutes_app1 _ UPI4_H _ H1) as H3. 
  rewrite H3.
  clear.
  repeat rewrite <- app_assoc; simpl.
  rewrite <- (app_nil_l p).
  repeat rewrite app_comm_cons.
  do 2 (apply uc_app_congruence; try reflexivity).
  unfold uc_equiv_l, uc_equiv; simpl.
  rewrite hadamard_rotation.
  repeat rewrite phase_shift_rotation.
  destruct dim.
  unfold pad; bdestruct_all; Msimpl_light; trivial.
  autorewrite with eval_db; try lia.
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

Lemma apply_H_equivalence_sound : forall {dim} (l l' : PI4_ucom_l dim) q,
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
  apply uc_equiv_cong_l.
  subst; apply (apply_H_equivalence3_sound _ _ _ H0). 
  inversion H3. 
  apply uc_equiv_cong_l.
  subst; apply (apply_H_equivalence4_sound _ _ _ H0). 
  inversion H4. 
  apply uc_equiv_cong_l.
  subst; apply (apply_H_equivalence5_sound _ _ _ H0). 
  inversion H5.
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
  - dependent destruction p;
    remember (apply_H_equivalence (App1 UPI4_H n0 :: l) n0) as res; symmetry in Heqres;
    destruct res;
    rewrite <- IHn;
    try apply (apply_H_equivalence_sound _ _ _ Heqres);
    reflexivity.
  - rewrite <- IHn; reflexivity.
  - inversion p.
Qed.

Lemma hadamard_reduction_sound: forall {dim} (l : PI4_ucom_l dim), 
  l ≅l≅ hadamard_reduction l.
Proof. intros. apply apply_H_equivalences_sound. Qed.

(* TODO: We should also be able to prove that the Hadamard reduction optimization 
   reduces the number of Hadamard gates in the program. *)
