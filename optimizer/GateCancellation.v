Require Import Phase.
Require Import UnitarySem.
Require Import Tactics.
Require Import ListRepresentation.
Require Import Equivalences.
Require Import Proportional.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.

(*******************************************************)
(** Optimization: simple cancellation and combination **)
(*******************************************************)

(* 'cancel_gates_simple' is my first pass at the full one- and two-qubit 
   gate cancellation routines. This function cancels unitaries adjacent to 
   their inverses and combines adjacent z-rotation gates. It does not
   consider any commutation relationships. 

   The extra n argument is to help Coq recognize termination.
   We start with n = (length l). *)

Fixpoint cancel_gates_simple' {dim} (l acc : gate_list dim) (n: nat) : gate_list dim :=
  match n with
  | 0 => (rev acc) ++ l
  | S n' => match l with
           | [] => rev acc
           | App1 fU_H q :: t => 
               match next_single_qubit_gate t q with
               | Some (fU_H, t') => cancel_gates_simple' t' acc n'
               | _ => cancel_gates_simple' t (_H q :: acc) n'
               end
           | App1 fU_X q :: t => 
               match next_single_qubit_gate t q with
               | Some (fU_X, t') => cancel_gates_simple' t' acc n'
               | _ => cancel_gates_simple' t (_X q :: acc) n'
               end
           | App1 (fU_PI4 k) q :: t => 
               match next_single_qubit_gate t q with
               | Some (fU_PI4 k', t') => 
                 let k'' := (k + k')%Z in
                 if (k'' =? 8)%Z then cancel_gates_simple' t' acc n' else 
                 if (k'' <? 8)%Z then cancel_gates_simple' (_PI4 k'' q :: t') acc n'
                 else cancel_gates_simple' (_PI4 (k'' - 8)%Z q :: t') acc n' 
               | _ => cancel_gates_simple' t (_PI4 k q :: acc) n'
               end
           | App2 fU_CNOT q1 q2 :: t => 
               match next_two_qubit_gate t q1 with
               | Some (l1, q1', q2', l2) => 
                   if (q1 =? q1') && (q2 =? q2') && (does_not_reference l1 q2)
                   then cancel_gates_simple' (l1 ++ l2) acc n'
                   else cancel_gates_simple' t (_CNOT q1 q2 :: acc) n'
               | _ => cancel_gates_simple' t (_CNOT q1 q2 :: acc) n'
               end
           | _ => [] (* impossible case for well-formed gate_list *)
           end
  end.

Definition cancel_gates_simple {dim} (l : gate_list dim) : gate_list dim := 
  cancel_gates_simple' l [] (List.length l).


(* Useful identities. *)
   
(* TODO: These proofs are all just copied & pasted from each other, so
   there is definitely some cleaning that needs to be done. Once they're
   cleaned up, they should be moved to Equivalences.v *)

Lemma H_H_cancel : forall {dim} (l : gate_list dim) q, 
  q < dim -> _H q :: _H q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l. 
  rewrite (list_to_ucom_append (_H q :: _H q :: []) l). 
  simpl.
  rewrite uskip_id_r.
  rewrite <- (@H_H_id dim q).
  apply uskip_id_l.
  apply uc_well_typed_H; assumption.
Qed.

Lemma X_X_cancel : forall {dim} (l : gate_list dim) q, 
  q < dim -> _X q :: _X q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l. 
  rewrite (list_to_ucom_append (_X q :: _X q :: []) l). 
  simpl.
  rewrite uskip_id_r.
  rewrite <- (@X_X_id dim q).
  apply uskip_id_l.
  apply uc_well_typed_X; assumption.
Qed.

Lemma PI4_PI4_combine : forall {dim} (l : gate_list dim) q k k', 
  _PI4 k q :: _PI4 k' q :: l =l= _PI4 (k+k') q :: l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db; simpl.
  bdestruct (q + 1 <=? dim); try (remove_zero_gates; trivial).
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite phase_mul. 
  repeat rewrite <- Rmult_div_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite plus_IZR.
  rewrite Rplus_comm.
  reflexivity.
Qed.

Lemma PI4_PI4_m8_combine : forall {dim} (l : gate_list dim) q k k', 
  _PI4 k q :: _PI4 k' q :: l =l= _PI4 (k+k'-8) q :: l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db; simpl.
  bdestruct (q + 1 <=? dim); try (remove_zero_gates; trivial).
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite phase_mul. 
  repeat rewrite <- Rmult_div_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- plus_IZR.
  repeat rewrite Rmult_div_assoc.
  rewrite phase_PI4_m8.
  rewrite Zplus_comm.
  reflexivity.
Qed.
  
Lemma PI4_PI4_cancel : forall {dim} (l : gate_list dim) q k k', 
  q < dim -> 
  (k + k' = 8)%Z ->
  _PI4 k q :: _PI4 k' q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db; simpl.
  repad.
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite phase_mul. 
  repeat rewrite <- Rmult_div_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- plus_IZR.
  repeat rewrite Rmult_div_assoc.
  rewrite Zplus_comm, H0.
  replace (8 * PI / 4)%R with (2 * PI)%R by lra.
  rewrite phase_2pi.
  Msimpl. 
  replace (2 ^ q * 2 * 2 ^ d)%nat with (2^dim) by unify_pows_two.
  Msimpl.
  reflexivity.
Qed.
  
Lemma CNOT_CNOT_cancel : forall {dim} (l1 l2 : gate_list dim) q1 q2, 
  q1 < dim -> q2 < dim -> q1 <> q2 -> l1 ++ [_CNOT q1 q2] ++ [_CNOT q1 q2] ++ l2 =l= l1 ++ l2.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  rewrite list_to_ucom_append; simpl.
  autorewrite with eval_db; simpl.

  repad.
  - rewrite (Mmult_assoc (uc_eval (list_to_ucom l2))). 
    rewrite (Mmult_assoc (uc_eval (list_to_ucom l2))). 
    restore_dims_fast; repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite Mmult_plus_distr_r. 
    repeat rewrite Mmult_plus_distr_l.
    restore_dims_fast; repeat rewrite kron_mixed_product.
    Msimpl.
    replace (∣1⟩⟨1∣ × ∣1⟩⟨1∣) with (∣1⟩⟨1∣) by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
    remove_zero_gates.
    rewrite Mplus_0_l. 
    rewrite Mplus_0_r.
    replace (σx × σx) with (I 2) by solve_matrix.
    repeat rewrite kron_assoc.
    repeat rewrite id_kron.
    unify_pows_two.
    restore_dims_fast.
    rewrite <- kron_plus_distr_r.
    replace (∣1⟩⟨1∣ .+ ∣0⟩⟨0∣) with (I 2) by solve_matrix.
    Msimpl.
    restore_dims_fast.
    replace (2 ^ q1 * (2 * 2 ^ (d + 1) * 2 ^ d0)) with (2^dim) by unify_pows_two.
    Msimpl.
    rewrite list_to_ucom_append; reflexivity.
  - rewrite (Mmult_assoc (uc_eval (list_to_ucom l2))). 
    rewrite (Mmult_assoc (uc_eval (list_to_ucom l2))). 
    restore_dims_fast; repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite Mmult_plus_distr_r. 
    repeat rewrite Mmult_plus_distr_l.
    restore_dims_fast; repeat rewrite kron_mixed_product.
    Msimpl.
    replace (∣1⟩⟨1∣ × ∣1⟩⟨1∣) with (∣1⟩⟨1∣) by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
    remove_zero_gates.
    rewrite Mplus_0_l. 
    rewrite Mplus_0_r.
    replace (σx × σx) with (I 2) by solve_matrix.
    repeat rewrite id_kron.
    restore_dims_fast.
    rewrite <- kron_plus_distr_l.
    replace (∣1⟩⟨1∣ .+ ∣0⟩⟨0∣) with (I 2) by solve_matrix.
    repeat rewrite id_kron.
    replace (2 ^ q2 * (2 * 2 ^ d * 2) * 2 ^ d0) with (2^dim) by unify_pows_two.
    Msimpl.
    rewrite list_to_ucom_append; reflexivity.
Qed.  

Lemma cancel_gates_simple'_sound : forall {dim} (l acc : gate_list dim) n,
  uc_well_typed_l l -> (rev acc) ++ l =l= cancel_gates_simple' l acc n.
Proof.
  intros.
  generalize dependent acc.
  generalize dependent l.
  induction n; try easy.
  intros l WT; simpl.
  destruct l; intros; try (rewrite app_nil_r; reflexivity).
  destruct g.
  - dependent destruction f;
    remember (next_single_qubit_gate l n0) as next_gate;
    symmetry in Heqnext_gate; inversion WT.
    + (* H *)
      destruct next_gate.
      2: { rewrite <- IHn; try assumption.
           simpl; rewrite <- app_assoc. 
           reflexivity. }
      destruct p; dependent destruction f; rewrite <- IHn;
      try (simpl; rewrite <- app_assoc; reflexivity);
      try assumption.
      rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
      apply app_congruence; try reflexivity.
      apply H_H_cancel; assumption.
      apply (nsqg_WT _ _ _ _ Heqnext_gate H3).
    + (* X *)
      destruct next_gate.
      2: { rewrite <- IHn; try assumption.
           simpl; rewrite <- app_assoc. 
           reflexivity. }
      destruct p; dependent destruction f; rewrite <- IHn;
      try (simpl; rewrite <- app_assoc; reflexivity);
      try assumption.
      rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
      apply app_congruence; try reflexivity.
      apply X_X_cancel; assumption.
      apply (nsqg_WT _ _ _ _ Heqnext_gate H3).
    + (* PI4 *)
      destruct next_gate.
      2: { rewrite <- IHn; try assumption.
           simpl; rewrite <- app_assoc. 
           reflexivity. }
      destruct p; dependent destruction f;
      [| | destruct (k + k0 =? 8)%Z eqn:E; [|destruct (k + k0 <? 8)%Z]];
      try rewrite <- IHn;
      try rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate);
      try (simpl; rewrite <- app_assoc; reflexivity);
      try constructor;
      try apply (nsqg_WT _ _ _ _ Heqnext_gate);
      try assumption;
      try apply app_congruence; try reflexivity.
      apply Z.eqb_eq in E.
      apply PI4_PI4_cancel; lia.
      apply PI4_PI4_combine.
      apply PI4_PI4_m8_combine.
  - (* CNOT *)
    dependent destruction f.
    remember (next_two_qubit_gate l n0) as next_gate;
    symmetry in Heqnext_gate; 
    inversion WT.
    destruct next_gate.
    2: { rewrite <- IHn; try assumption.
         simpl; rewrite <- app_assoc. 
         reflexivity. }
    destruct p; destruct p; destruct p.
    bdestruct (n0 =? n4); bdestruct (n1 =? n3); simpl;
    try (rewrite <- IHn; try assumption; simpl; rewrite <- app_assoc; reflexivity).
    subst.
    remember (does_not_reference g0 n3) as dnr; symmetry in Heqdnr.
    destruct dnr; simpl; 
    try (rewrite <- IHn; try assumption; simpl; rewrite <- app_assoc; reflexivity).
    specialize (ntqg_preserves_semantics _ _ _ _ _ _ Heqnext_gate) as H7.
    rewrite H7.
    rewrite <- IHn.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ Heqnext_gate) as H8.
    rewrite app_comm_cons.
    rewrite app_assoc.
    rewrite (does_not_reference_commutes_app2 g0 fU_CNOT n4 n3 H8 Heqdnr).
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity.
    apply CNOT_CNOT_cancel; assumption.
    specialize (ntqg_WT _ _ _ _ _ _ Heqnext_gate H6) as [H8 H9].
    apply uc_well_typed_l_app; assumption.
Qed.

Lemma cancel_gates_simple_sound : forall {dim} (l : gate_list dim),
  uc_well_typed_l l -> l =l= cancel_gates_simple l.
Proof. 
  intros. 
  unfold cancel_gates_simple.
  rewrite <- cancel_gates_simple'_sound.
  reflexivity. 
  assumption. 
Qed.

(* Small test *)
Definition test1 : gate_list 4 := (_H 1) :: (_P 0) :: (_CNOT 2 3) :: (_P 0) :: (_H 1) :: (_Z 1) :: (_PDAG 0) :: (_CNOT 2 3) :: (_T 0) :: [].
Compute (cancel_gates_simple test1).

(**********************************************************************)
(** Optimization: simple cancellation and combination w/ commutation **)
(**********************************************************************)

(* Cancel and combine gates, as above, but also check for cancellations
   across commuting subcircuits. We will determine whether a gate
   commutes through a subcircuit using the following circuits identities
   from Nam et al.

   - X b; CNOT a b ≡ CNOT a b; X b
   - Rz b ; H b ; CNOT a b ; H b ≡ H b ; CNOT a b ; H b ; Rz b
   - Rz b ; CNOT a b ; Rz' b ; CNOT a b ≡ CNOT a b ; Rz' b ; CNOT a b ; Rz b
   - Rz a ; CNOT a b ≡ CNOT a b ; Rz a

   Not currently verified:
   - CNOT a c ; CNOT b c ≡ CNOT b c ; CNOT a c
   - CNOT a c ; CNOT a b ≡ CNOT a b ; CNOT a c
   - CNOT a b; H b; CNOT b c; H b ≡ H b; CNOT b c; H b; CNOT a b

   This optimization is similar to Nam et al.'s single/two-qubit gate
   cancellation and not propagation.
*)

(* Commutativity rule for X *)

Definition search_for_commuting_X_pat {dim} (l : gate_list dim) q :=
  match next_two_qubit_gate l q with
  | Some (l1, q1, q2, l2) =>
      if q =? q2
      then Some (l1 ++ [_CNOT q1 q2], l2)
      else None
  | _ => None
  end.

(* Commutativity rules for Rz *)

Definition search_for_Rz_pat1 {dim} (l : gate_list dim) q :=
  match (next_single_qubit_gate l q) with
  | Some (fU_H, l') => 
      match (next_two_qubit_gate l' q) with
      | Some (l1, q1, q2, l2) =>
          if q =? q2
          then match (next_single_qubit_gate l2 q) with
               | Some (fU_H, l2') => Some ([_H q] ++ l1 ++ [_CNOT q1 q] ++ [ _H q], l2') 
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition search_for_Rz_pat2 {dim} (l : gate_list dim) q :=
  match (next_two_qubit_gate l q) with
  | Some (l1, q1, q2, l2) => 
      if q =? q2
      then match (next_single_qubit_gate l2 q) with
           | Some (fU_PI4 k as u, l2') =>
               match (next_two_qubit_gate l2' q) with
               | Some (l3, q3, q4, l4) => 
                   if (q =? q4) && (q1 =? q3) && (does_not_reference l3 q3)
                   then Some (l1 ++ [_CNOT q1 q] ++ [App1 u q] ++ l3 ++ [_CNOT q1 q], l4)
                   else None 
               | _ => None
               end
           | _ => None
           end
      else None
  | _ => None
  end.

Definition search_for_Rz_pat3 {dim} (l : gate_list dim) q :=
  match (next_two_qubit_gate l q) with
  | Some (l1, q1, q2, l2) => 
      if q =? q1
      then Some (l1 ++ [_CNOT q1 q2], l2)
      else None
  | _ => None
  end.

Definition search_for_commuting_Rz_pat {dim} (l : gate_list dim) q :=
  match search_for_Rz_pat1 l q with
  | Some (l1, l2) => Some (l1, l2)
  | None => match search_for_Rz_pat2 l q with
           | Some (l1, l2) => Some (l1, l2)
           | None => match search_for_Rz_pat3 l q with
                    | Some (l1, l2) => Some (l1, l2)
                    | None => None
                    end
           end
  end.

(* Commutativity rules for CNOT *)

Definition search_for_CNOT_pat1 {dim} (l : gate_list dim) (q1 q2 : nat) : option (gate_list dim * gate_list dim) :=
  match (next_single_qubit_gate l q1) with
  | Some (fU_PI4 k, l') => Some ([_PI4 k q1], l')
  | _ => None
  end.

Definition search_for_CNOT_pat2 {dim} (l : gate_list dim) q1 q2 :=
  match (next_two_qubit_gate l q2) with
  | Some (l1, q1', q2', l2) => 
      if q2 =? q2'
      then if (does_not_reference l1 q1) && (does_not_reference l1 q1')
           then Some (l1 ++ [_CNOT q1' q2], l2)
           else None
      else None
  | _ => None
  end.

Definition search_for_CNOT_pat3 {dim} (l : gate_list dim) q1 q2 :=
  match (next_two_qubit_gate l q1) with
  | Some (l1, q1', q2', l2) => 
      if q1 =? q1'
      then if (does_not_reference l1 q2) && (does_not_reference l1 q2')
           then Some (l1 ++ [_CNOT q1 q2'], l2)
           else None
      else None
  | _ => None
  end.

Definition search_for_CNOT_pat4 {dim} (l : gate_list dim) q1 q2 :=
  match (next_single_qubit_gate l q2) with
  | Some (fU_H, l') => 
      match (next_two_qubit_gate l' q2) with
      | Some (l1, q1', q2', l2) => 
          if (q2 =? q1') && ¬ (q1 =? q2') && (does_not_reference l1 q1)
          then match (next_single_qubit_gate l2 q2) with
               | Some (fU_H, l2') => Some ([_H q2] ++ l1 ++ [_CNOT q2 q2'] ++ [_H q2], l2')
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition search_for_commuting_CNOT_pat {dim} (l : gate_list dim) q1 q2 :=
  match search_for_CNOT_pat1 l q1 q2 with
  | Some (l1, l2) => Some (l1, l2)
  | None => match search_for_CNOT_pat2 l q1 q2 with
           | Some (l1, l2) => Some (l1, l2)
           | None => match search_for_CNOT_pat3 l q1 q2 with
                    | Some (l1, l2) => Some (l1, l2)
                    | None =>  match search_for_CNOT_pat4 l q1 q2 with
                              | Some (l1, l2) => Some (l1, l2)
                              | None => None
                              end
                    end
           end
  end.

(* Propagation functions for each gate type *)

Fixpoint propagate_PI4 {dim} k (l : gate_list dim) (q n : nat) : option (gate_list dim) :=
  match n with
  | O => None
  | S n' => 
      match next_single_qubit_gate l q with
      | Some (fU_PI4 k', l') => 
                 let k'' := (k + k')%Z in
                 (* Cancel *)
                 if (k'' =? 8)%Z then Some l' else 
                 (* Combine *)
                 if (k'' <? 8)%Z then Some (_PI4 k'' q :: l')
                 else Some (_PI4 (k'' - 8)%Z q :: l') 
      (* Commute *)
      | _ =>
          match search_for_commuting_Rz_pat l q with
          | Some (l1, l2) => match (propagate_PI4 k l2 q n') with
                            | Some l' => Some (l1 ++ l')
                            | None => None
                            end
          | None =>  None
          end
      end
  end.

Definition propagate_H {dim} (l : gate_list dim) (q : nat) : option (gate_list dim) :=
  match next_single_qubit_gate l q with
  (* Cancel *)
  | Some (fU_H, l') => Some l'
  (* Currently no rules for commuting H gates *)
  | _ => None
  end.

Fixpoint propagate_X {dim} (l : gate_list dim) (q n : nat) : option (gate_list dim) :=
  match n with
  | O => None
  | S n' => 
      match next_single_qubit_gate l q with
      (* Cancel *)
      | Some (fU_X, l') => Some l'
      (* Commute *)
      | _ =>
          match search_for_commuting_X_pat l q with
          | Some (l1, l2) => match (propagate_X l2 q n') with
                            | Some l' => Some (l1 ++ l')
                            | None => None
                            end
          | None =>  None
          end
      end
  end.

Definition propagate_CNOT {dim} (l : gate_list dim) (q1 q2 n : nat) : option (gate_list dim) :=
  match n with
  | O => None
  | S n' => 
      match next_two_qubit_gate l q1 with
      (* Cancel *)
      | Some (l1, q1', q2', l2) => 
          if (q1 =? q1') && (q2 =? q2') && (does_not_reference l1 q2)
          then Some (l1 ++ l2)
          else None
      (* Commute -- commented out to avoid unverified code *)
      (*| _ =>
          match search_for_commuting_CNOT_pat l q1 q2 with
          | Some (l1, l2) => match (propagate_CNOT l2 q1 q2 n') with
                            | Some l' => Some (l1 ++ l')
                            | None => None
                            end
          | None =>  None
          end
      end*)
      | _ => None
      end
  end.

Fixpoint cancel_gates' {dim} (l : gate_list dim) (n: nat) : gate_list dim :=
  match n with
  | 0 => l
  | S n' => match l with
           | App1 (fU_PI4 k) q :: t => 
               match propagate_PI4 k t q (length t) with
               | None => (_PI4 k q) :: (cancel_gates' t n')
               | Some l' => cancel_gates' l' n'
               end
           | App1 fU_H q :: t => 
               match propagate_H t q with
               | None => (_H q) :: (cancel_gates' t n')
               | Some l' => cancel_gates' l' n'
               end
           | App1 fU_X q :: t => 
               match propagate_X t q (length t) with
               | None => (_X q) :: (cancel_gates' t n')
               | Some l' => cancel_gates' l' n'
               end
           | App2 fU_CNOT q1 q2 :: t => 
               match propagate_CNOT t q1 q2 (length t) with
               | None => (_CNOT q1 q2) :: (cancel_gates' t n')
               | Some l' => cancel_gates' l' n'
               end
           | _ => []
           end
  end.

Definition cancel_gates {dim} (l : gate_list dim) := 
  cancel_gates' l (length l).


(* Proofs about commutativity *)

Lemma commuting_X_pat : forall {dim} (l : gate_list dim) q l1 l2, 
  search_for_commuting_X_pat l q = Some (l1, l2) ->
  _X q :: l =l= l1 ++ [_X q] ++ l2.
Proof.
  intros.
  unfold search_for_commuting_X_pat in H.
  remember (next_two_qubit_gate l q) as next_gate; symmetry in Heqnext_gate.
  destruct next_gate; try easy.
  do 3 destruct p.
  bdestruct (q =? n); try easy.
  inversion H; subst.
  rewrite (ntqg_preserves_semantics _ _ _ _ _ _ Heqnext_gate).
  assert (does_not_reference g0 n = true).
  { apply (ntqg_l1_does_not_reference _ _ _ _ _ _ Heqnext_gate). }
  rewrite app_comm_cons.
  rewrite (does_not_reference_commutes_app1 _ fU_X _ H0).
  repeat rewrite <- app_assoc.
  rewrite (app_assoc _ _ l2).
  rewrite (app_assoc _ [_X n] l2).
  assert (@uc_equiv_l dim ([_X n] ++ [_CNOT n0 n]) ([_CNOT n0 n] ++ [_X n])).
  { unfold uc_equiv_l; simpl.
    do 2 rewrite uskip_id_r.
    apply X_CNOT_comm. }
  rewrite H1.
  reflexivity.  
Qed.

Lemma app_cons_app : forall {A} (a : A) (l1 l2 : list A), a :: l1 ++ l2 = [a] ++ l1 ++ l2.
Proof. reflexivity. Qed.


Lemma commuting_Rz_pat : forall {dim} k (l : gate_list dim) q l1 l2,
  search_for_commuting_Rz_pat l q = Some (l1, l2) ->
  _PI4 k q :: l =l= l1 ++ [_PI4 k q] ++ l2.
Proof.
(* Will require lemmas about search_for_Rz_pat1, 2, and 3. *)
  intros.
  unfold search_for_commuting_Rz_pat in H.
  destruct (search_for_Rz_pat1 l q) eqn:HS; 
  [|destruct (search_for_Rz_pat2 l q) eqn:HS2;
  [|destruct (search_for_Rz_pat3 l q) eqn:HS3]]; try discriminate.
  - unfold search_for_Rz_pat1 in HS.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_single_qubit_gate l q) eqn:HN1; try discriminate.
    destruct p.
    apply nsqg_preserves_semantics in HN1.
    destruct (next_two_qubit_gate g q) eqn:HN2; try discriminate.
    2:{ dependent destruction f; discriminate. }
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_semantics in HN2.
    dependent destruction f; try discriminate.
    bdestruct (q =? n); try easy.
    destruct (next_single_qubit_gate g0 q) eqn:HN1'; try discriminate.
    destruct p.
    apply nsqg_preserves_semantics in HN1'.
    dependent destruction f; try discriminate.
    inversion HS; subst.
    rewrite HN1, HN2, HN1'.
    rewrite app_comm_cons.
    rewrite (does_not_reference_commutes_app1 _ fU_H _ NoRef).
    repeat rewrite <- app_assoc.
    rewrite 2 app_comm_cons.
    rewrite (does_not_reference_commutes_app1 _ (fU_PI4 k) _ NoRef).
    rewrite (does_not_reference_commutes_app1 _ fU_H _ NoRef).    
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity.
    replace ( App1 fU_H n :: l2) with ([App1 fU_H n] ++ l2) by easy.
    repeat rewrite app_assoc.
    apply app_congruence; try reflexivity.
    unfold uc_equiv_l; simpl.
    unfold uc_equiv; simpl.
    autorewrite with eval_db.
    gridify.
    + rewrite (Mmult_assoc _ hadamard hadamard).
      replace (hadamard × hadamard) with (I 2) by solve_matrix.
      repeat rewrite (Mmult_assoc _ _ hadamard).
      rewrite (Mmult_assoc _ hadamard).
      replace (hadamard × (σx × hadamard)) with σz by solve_matrix.
      rewrite <- phase_pi, 2 phase_mul.
      Msimpl.
      rewrite Rplus_comm.
      reflexivity.
    + rewrite (Mmult_assoc _ hadamard hadamard).
      replace (hadamard × hadamard) with (I 2) by solve_matrix.
      repeat rewrite (Mmult_assoc _ _ hadamard).
      rewrite (Mmult_assoc _ hadamard).
      replace (hadamard × (σx × hadamard)) with σz by solve_matrix.
      rewrite <- phase_pi, 2 phase_mul.
      Msimpl.
      rewrite Rplus_comm.
      reflexivity.
  - unfold search_for_Rz_pat2 in HS2.
    destruct p.
    inversion H; subst. clear H HS.
    destruct (next_two_qubit_gate l q) eqn:HN2; try discriminate.
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_semantics in HN2.
    bdestruct (q =? n); try discriminate.
    subst.
    destruct (next_single_qubit_gate g n) eqn:HN1; try discriminate.
    repeat destruct p.
    dependent destruction f; try discriminate.
    apply nsqg_preserves_semantics in HN1.
    destruct (next_two_qubit_gate g1 n) eqn:HN2'; try discriminate.
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ HN2') as NoRef'.
    apply ntqg_preserves_semantics in HN2'.
    bdestruct (n =? n1); try discriminate.
    bdestruct (n0 =? n2); try discriminate.
    destruct (does_not_reference g3 n2) eqn:NoRef''; try discriminate.
    simpl in HS2.
    inversion HS2; subst. clear HS2.
    rewrite HN2, HN1, HN2'.
    rewrite app_comm_cons.
    rewrite (does_not_reference_commutes_app1 _ (fU_PI4 k) _ NoRef).
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity. 
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    apply app_congruence; try reflexivity. 
    repeat rewrite <- app_assoc.    
    rewrite <- (does_not_reference_commutes_app2 _ fU_CNOT _ _ NoRef'' NoRef').
    rewrite (app_assoc g3).
    rewrite <- (does_not_reference_commutes_app2 _ fU_CNOT _ _ NoRef'' NoRef').
    rewrite <- app_assoc.
    rewrite <- (does_not_reference_commutes_app1 _ (fU_PI4 k) _ NoRef').
    repeat rewrite app_assoc.    
    apply app_congruence; try reflexivity.
    unfold uc_equiv_l; simpl.
    unfold uc_equiv; simpl.
    autorewrite with eval_db.
    gridify.
    + replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
      replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
      remove_zero_gates.
      rewrite 2 phase_mul. rewrite Rplus_comm.
      replace (σx × phase_shift (IZR k0 * PI / 4) × σx × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × σx × phase_shift (IZR k0 * PI / 4) × σx) by
        solve_matrix.
      reflexivity.
    + replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
      replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
      remove_zero_gates.      
      rewrite 2 phase_mul. rewrite Rplus_comm.
      replace (σx × phase_shift (IZR k0 * PI / 4) × σx × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × σx × phase_shift (IZR k0 * PI / 4) × σx) by
        solve_matrix.      
      reflexivity.
  - clear HS HS2.
    unfold search_for_Rz_pat3 in HS3. 
    destruct p.
    inversion H; subst. clear H.
    destruct (next_two_qubit_gate l q) eqn:HN2; try discriminate.
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_semantics in HN2.
    bdestruct (q =? n0); try discriminate.
    subst.
    inversion HS3. subst.
    rewrite HN2.
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    apply app_congruence; try reflexivity. 
    rewrite (does_not_reference_commutes_app1 _ (fU_PI4 k) _ NoRef).
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity. 
    (* simple slide lemma: should exist already? *)
    unfold uc_equiv_l; simpl.
    unfold uc_equiv; simpl. 
    rewrite 2 Mmult_1_l; auto with wf_db.
    autorewrite with eval_db.
    gridify.
    + replace  (∣1⟩⟨1∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣1⟩⟨1∣) by solve_matrix.
      replace  (∣0⟩⟨0∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣0⟩⟨0∣) by solve_matrix.
      reflexivity.
    + replace  (∣1⟩⟨1∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣1⟩⟨1∣) by solve_matrix.
      replace  (∣0⟩⟨0∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣0⟩⟨0∣) by solve_matrix.
      reflexivity.
Qed.

(* Slow *)
(* Should add/use lemmas for ∣0⟩⟨0∣ × ∣1⟩⟨1∣ and the like. *)
Lemma commuting_CNOT_pat : forall {dim} (l : gate_list dim) q1 q2 l1 l2,
  search_for_commuting_CNOT_pat l q1 q2 = Some (l1, l2) ->
  _CNOT q1 q2 :: l =l= l1 ++ [_CNOT q1 q2] ++ l2.
Proof.
(* Will require lemmas about search_for_CNOT_pat1, 2, 3, and 4. *)
  intros.
  unfold search_for_commuting_CNOT_pat in H.
  destruct (search_for_CNOT_pat1 l q1 q2) eqn:HS; 
  [|clear HS; destruct (search_for_CNOT_pat2 l q1 q2) eqn:HS;
  [|clear HS; destruct (search_for_CNOT_pat3 l q1 q2) eqn:HS; 
  [|clear HS; destruct (search_for_CNOT_pat4 l q1 q2) eqn:HS]]]; try discriminate.
  - unfold search_for_CNOT_pat1 in HS.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_single_qubit_gate l q1) eqn:HN1; try discriminate.
    destruct p.
    apply nsqg_preserves_semantics in HN1.
    dependent destruction f; try discriminate.
    inversion HS; subst. clear HS.
    rewrite HN1. (* Wasn't this the last case of Rz *)
    repeat rewrite app_cons_app.
    replace (_CNOT q1 q2 :: App1 (fU_PI4 k) q1 :: l2) with
        ([_CNOT q1 q2] ++ [_PI4 k q1] ++ l2) by reflexivity.
    repeat rewrite app_assoc.
    apply app_congruence; try reflexivity.
    unfold uc_equiv_l; simpl.
    unfold uc_equiv; simpl. 
    Msimpl.
    autorewrite with eval_db.
    gridify.
    + replace  (∣1⟩⟨1∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣1⟩⟨1∣) by solve_matrix.
      replace  (∣0⟩⟨0∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣0⟩⟨0∣) by solve_matrix.
      reflexivity.
    + replace  (∣1⟩⟨1∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣1⟩⟨1∣) by solve_matrix.
      replace  (∣0⟩⟨0∣ × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × ∣0⟩⟨0∣) by solve_matrix.
      reflexivity.
  - unfold search_for_CNOT_pat2 in HS.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_two_qubit_gate l q2) eqn:HN2; try discriminate.
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_semantics in HN2.
    bdestruct (q2 =? n); try discriminate. subst.   
    destruct (does_not_reference g0 q1) eqn:NoRef'; try discriminate. 
    destruct (does_not_reference g0 n0) eqn:NoRef''; try discriminate.
    simpl in HS. inversion HS; subst. clear HS.
    rewrite HN2. 
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    rewrite (does_not_reference_commutes_app2 _ fU_CNOT _ _ NoRef' NoRef).
    apply app_congruence; try reflexivity.
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity.
    unfold uc_equiv_l; simpl.
    unfold uc_equiv; simpl. 
    Msimpl.
    autorewrite with eval_db.
    gridify; reflexivity.
  - unfold search_for_CNOT_pat3 in HS.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_two_qubit_gate l q1) eqn:HN2; try discriminate.
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_semantics in HN2.
    bdestruct (q1 =? n0); try discriminate. subst.   
    destruct (does_not_reference g0 q2) eqn:NoRef'; try discriminate. 
    destruct (does_not_reference g0 n) eqn:NoRef''; try discriminate.
    simpl in HS. inversion HS; subst. clear HS.
    rewrite HN2. 
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    rewrite (does_not_reference_commutes_app2 _ fU_CNOT _ _ NoRef NoRef').
    apply app_congruence; try reflexivity.
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity.
    unfold uc_equiv_l; simpl.
    unfold uc_equiv; simpl. 
    Msimpl.
    autorewrite with eval_db.
    gridify; try reflexivity.
    all: replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix;
         replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix;
         reflexivity.
  - unfold search_for_CNOT_pat4 in HS.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_single_qubit_gate l q2) eqn:HN1; try discriminate.
    destruct p.
    apply nsqg_preserves_semantics in HN1.
    dependent destruction f; try discriminate.
    destruct (next_two_qubit_gate g q2) eqn:HN2; try discriminate.
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_semantics in HN2.
    bdestruct (q2 =? n0); try discriminate; subst.
    bdestruct (q1 =? n); try discriminate; subst.
    destruct (does_not_reference g1 q1) eqn:NoRef'; try discriminate.
    simpl in HS.
    destruct (next_single_qubit_gate g0 n0) eqn:HN1'; try discriminate.
    destruct p.
    apply nsqg_preserves_semantics in HN1'.
    dependent destruction f; try discriminate.
    inversion HS; subst; clear HS.
    rewrite HN1, HN2, HN1'.
    repeat rewrite app_cons_app.
    replace (App1 fU_H n0 :: l2) with ([App1 fU_H n0] ++ l2) by reflexivity.
    repeat rewrite app_assoc.
    rewrite (does_not_reference_commutes_app1 _ fU_H _ NoRef).
    rewrite <- (app_assoc _ _ g1).
    rewrite (does_not_reference_commutes_app1 _ fU_H _ NoRef).
    rewrite app_assoc.
    rewrite (does_not_reference_commutes_app2 _ fU_CNOT _ _ NoRef' NoRef).
    apply app_congruence; try reflexivity.
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity.
    unfold uc_equiv_l; simpl.
    unfold uc_equiv; simpl. 
    Msimpl.
    autorewrite with eval_db.
    gridify; try reflexivity.
    all: replace (hadamard × ∣1⟩⟨1∣ × hadamard × σx) with
          (σx × hadamard × ∣1⟩⟨1∣ × hadamard) by
          solve_matrix;
         replace (hadamard × ∣0⟩⟨0∣ × hadamard × σx) with
          (σx × hadamard × ∣0⟩⟨0∣ × hadamard) by
          solve_matrix;
         reflexivity.
Qed.
      
(* Proofs about propagation functions *)

Lemma propagate_H_sound : forall {dim} (l : gate_list dim) q l',
  q < dim ->
  propagate_H l q = Some l' ->
  _H q :: l =l= l'.
Proof. 
  intros.
  unfold propagate_H in H0; simpl in H0.
  remember (next_single_qubit_gate l q) as next_gate; symmetry in Heqnext_gate.
  destruct next_gate; try easy.
  destruct p; dependent destruction f; try easy.
  inversion H0; subst.
  rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
  apply H_H_cancel; assumption.
Qed.

Lemma propagate_H_WT : forall {dim} (l : gate_list dim) q l',
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

Lemma propagate_X_sound : forall {dim} (l : gate_list dim) q n l',
  q < dim ->
  propagate_X l q n = Some l' ->
  _X q :: l =l= l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction n; try easy.
  simpl.
  intros.
  remember (next_single_qubit_gate l q) as next_gate; symmetry in Heqnext_gate.
  destruct next_gate.
  - destruct p.
    dependent destruction f. 
    2: { (* Cancel case *)
         inversion H0; subst.
         rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
         apply X_X_cancel; assumption. }
    (* Commute cases *)
    + (* copy & paste #1 *)
      remember (search_for_commuting_X_pat l q) as pat; symmetry in Heqpat.
      destruct pat; try easy.
      destruct p.    
      remember (propagate_X g0 q n) as prop; symmetry in Heqprop.
      destruct prop; try easy.    
      inversion H0; subst.
      rewrite (commuting_X_pat _ _ _ _ Heqpat).
      rewrite (IHn _ _ Heqprop).
      reflexivity.
    + (* copy & paste #2 *)
      remember (search_for_commuting_X_pat l q) as pat; symmetry in Heqpat.
      destruct pat; try easy.
      destruct p.    
      remember (propagate_X g0 q n) as prop; symmetry in Heqprop.
      destruct prop; try easy.    
      inversion H0; subst.
      rewrite (commuting_X_pat _ _ _ _ Heqpat).
      rewrite (IHn _ _ Heqprop).
      reflexivity.
  - (* copy & paste #3 *)
    remember (search_for_commuting_X_pat l q) as pat; symmetry in Heqpat.
    destruct pat; try easy.
    destruct p.    
    remember (propagate_X g q n) as prop; symmetry in Heqprop.
    destruct prop; try easy.    
    inversion H0; subst.
    rewrite (commuting_X_pat _ _ _ _ Heqpat).
    rewrite (IHn _ _ Heqprop).
    reflexivity.
Qed.

Lemma propagate_X_WT : forall {dim} (l : gate_list dim) q n l',
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

Lemma propagate_PI4_sound : forall {dim} k (l : gate_list dim) q n l',
  q < dim ->
  propagate_PI4 k l q n = Some l' ->
  _PI4 k q :: l =l= l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction n; try easy.
  simpl.
  intros.
  remember (next_single_qubit_gate l q) as next_gate; symmetry in Heqnext_gate.
  destruct next_gate.
  - destruct p.
    dependent destruction f. 
    3: { (* Cancel/combine case *)
         remember (k + k0 =? 8)%Z as k_k0_8.
         destruct k_k0_8; symmetry in Heqk_k0_8.
         apply Z.eqb_eq in Heqk_k0_8.
         inversion H0; subst.
         rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
         apply PI4_PI4_cancel; assumption. 
         destruct (k + k0 <? 8)%Z; inversion H0; subst;
         rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
         apply PI4_PI4_combine.
         apply PI4_PI4_m8_combine. }
    (* Commute cases *)
    + (* copy & paste #1 *)
      remember (search_for_commuting_Rz_pat l q) as pat; symmetry in Heqpat.
      destruct pat; try easy.
      destruct p.    
      remember (propagate_PI4 k g0 q n) as prop; symmetry in Heqprop.
      destruct prop; try easy.    
      inversion H0; subst.
      rewrite (commuting_Rz_pat _ _ _ _ _ Heqpat).
      rewrite (IHn _ _ Heqprop).
      reflexivity.
    + (* copy & paste #2 *)
      remember (search_for_commuting_Rz_pat l q) as pat; symmetry in Heqpat.
      destruct pat; try easy.
      destruct p.    
      remember (propagate_PI4 k g0 q n) as prop; symmetry in Heqprop.
      destruct prop; try easy.    
      inversion H0; subst.
      rewrite (commuting_Rz_pat _ _ _ _ _ Heqpat).
      rewrite (IHn _ _ Heqprop).
      reflexivity.
  - (* copy & paste #3 *)
    remember (search_for_commuting_Rz_pat l q) as pat; symmetry in Heqpat.
    destruct pat; try easy.
    destruct p.    
    remember (propagate_PI4 k g q n) as prop; symmetry in Heqprop.
    destruct prop; try easy.    
    inversion H0; subst.
    rewrite (commuting_Rz_pat _ _ _ _ _ Heqpat).
    rewrite (IHn _ _ Heqprop).
    reflexivity.
Qed.

Lemma propagate_PI4_WT : forall {dim} k (l : gate_list dim) q n l',
  q < dim ->
  uc_well_typed_l l ->
  propagate_PI4 k l q n = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_PI4_sound k l q n l' H H1) as H2.
  apply (uc_equiv_l_implies_WT _ _ H2).
  constructor; assumption.
Qed.

Lemma propagate_CNOT_sound : forall {dim} (l : gate_list dim) q1 q2 n l',
  q1 < dim ->
  q2 < dim -> 
  q1 <> q2 ->
  propagate_CNOT l q1 q2 n = Some l' ->
  _CNOT q1 q2 :: l =l= l'.
Proof. 
  intros.
  unfold propagate_CNOT in H2; simpl in H2.
  remember (next_two_qubit_gate l q1) as next_gate; symmetry in Heqnext_gate.
  destruct next_gate; destruct n; try easy.
  destruct p; destruct p; destruct p. 
  remember (does_not_reference g0 q2) as DNR; symmetry in HeqDNR.
  destruct DNR; bdestruct (q1 =? n1); bdestruct (q2 =? n0); 
  simpl in H2; inversion H2; subst.
  rewrite (ntqg_preserves_semantics _ _ _ _ _ _ Heqnext_gate).
  specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ Heqnext_gate) as H3.
  rewrite app_cons_app.
  rewrite (app_assoc _ _ g).
  rewrite <- (does_not_reference_commutes_app2 _ fU_CNOT _ _ H3 HeqDNR).
  simpl.
  specialize (CNOT_CNOT_cancel [] (g0 ++ g) _ _ H H0 H1) as H4.
  simpl in H4.
  assumption.
Qed.

Lemma propagate_CNOT_WT : forall {dim} (l : gate_list dim) q1 q2 n l',
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

Lemma cancel_gates'_sound : forall {dim} (l : gate_list dim) n,
  uc_well_typed_l l -> cancel_gates' l n =l= l.
Proof.
  intros.
  generalize dependent l.
  induction n; intros; try reflexivity.
  destruct l; try reflexivity.
  destruct g.
  - inversion H; subst. 
    dependent destruction f.
    + (* fU_H *) 
      simpl.
      remember (propagate_H l n0) as prop; symmetry in Heqprop.
      destruct prop; rewrite IHn; try reflexivity; try assumption.
      rewrite (propagate_H_sound _ _ _ H2 Heqprop).
      reflexivity.
      apply (propagate_H_WT _ _ _ H2 H4 Heqprop).
    + (* fU_X *)
      simpl.
      remember (propagate_X l n0 (length l)) as prop; symmetry in Heqprop.
      destruct prop; rewrite IHn; try reflexivity; try assumption.
      rewrite (propagate_X_sound _ _ _ _ H2 Heqprop).
      reflexivity.
      apply (propagate_X_WT _ _ _ _ H2 H4 Heqprop).
    + (* fU_PI4 *)
      simpl.
      remember (propagate_PI4 k l n0 (length l)) as prop; symmetry in Heqprop.
      destruct prop; rewrite IHn; try reflexivity; try assumption.
      rewrite (propagate_PI4_sound _ _ _ _ _ H2 Heqprop).
      reflexivity.
      apply (propagate_PI4_WT _ _ _ _ _ H2 H4 Heqprop).
  - (* fU_CNOT *)
    dependent destruction f; simpl.
    inversion H; subst. 
    remember (propagate_CNOT l n0 n1 (length l)) as prop; symmetry in Heqprop.
    destruct prop; rewrite IHn; try reflexivity; try assumption.
    rewrite (propagate_CNOT_sound _ _ _ _ _ H4 H5 H6 Heqprop).
    reflexivity.
    apply (propagate_CNOT_WT _ _ _ _ _ H4 H5 H6 H7 Heqprop).
Qed.

Lemma cancel_gates_sound : forall {dim} (l : gate_list dim), 
  uc_well_typed_l l -> cancel_gates l =l= l.
Proof. intros. apply cancel_gates'_sound; assumption. Qed.
