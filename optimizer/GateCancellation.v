Require Import UnitarySem.
Require Import Equivalences.
Require Import PI4GateSet.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.

(*******************************************************)
(** Optimization: simple cancellation and combination **)
(*******************************************************)

(* A first pass at the full one- and two-qubit gate cancellation routines. 
   This function cancels unitaries adjacent to their inverses and combines 
   adjacent z-rotation gates. It does not consider any commutation relationships. 

   The extra n argument is to help Coq recognize termination.
   We start with n = (length l). *)

Fixpoint cancel_gates_simple' {dim} (l acc : PI4_ucom_l dim) (n: nat) : PI4_ucom_l dim :=
  match n with
  | 0 => (rev acc) ++ l
  | S n' => match l with
           | [] => rev acc
           | App1 UPI4_H q :: t => 
               match next_single_qubit_gate t q with
               | Some (l1, UPI4_H, l2) => cancel_gates_simple' (l1 ++ l2) acc n'
               | _ => cancel_gates_simple' t (App1 UPI4_H q :: acc) n'
               end
           | App1 UPI4_X q :: t => 
               match next_single_qubit_gate t q with
               | Some (l1, UPI4_X, l2) => cancel_gates_simple' (l1 ++ l2) acc n'
               | _ => cancel_gates_simple' t (App1 UPI4_X q :: acc) n'
               end
           | App1 (UPI4_PI4 k) q :: t => 
               match next_single_qubit_gate t q with
               | Some (l1, UPI4_PI4 k', l2) => 
                 let k'' := (k + k')%Z in
                 if (k'' =? 8)%Z then cancel_gates_simple' (l1 ++ l2) acc n' else 
                 if (k'' <? 8)%Z then cancel_gates_simple' (App1 (UPI4_PI4 k'') q :: (l1 ++ l2)) acc n'
                 else cancel_gates_simple' (App1 (UPI4_PI4 (k'' - 8)%Z) q :: (l1 ++ l2)) acc n' 
               | _ => cancel_gates_simple' t (App1 (UPI4_PI4 k) q :: acc) n'
               end
           | App2 UPI4_CNOT q1 q2 :: t => 
               match next_two_qubit_gate t q1 with
               | Some (l1, _, q1', q2', l2) => 
                   if (q1 =? q1') && (q2 =? q2') && (does_not_reference l1 q2)
                   then cancel_gates_simple' (l1 ++ l2) acc n'
                   else cancel_gates_simple' t (App2 UPI4_CNOT q1 q2 :: acc) n'
               | _ => cancel_gates_simple' t (App2 UPI4_CNOT q1 q2 :: acc) n'
               end
           | _ => [] (* impossible case for well-formed gate_list *)
           end
  end.

Definition cancel_gates_simple {dim} (l : PI4_ucom_l dim) : PI4_ucom_l dim := 
  cancel_gates_simple' l [] (List.length l).

Lemma H_H_cancel : forall {dim} (l : PI4_ucom_l dim) q, 
  q < dim -> App1 UPI4_H q :: App1 UPI4_H q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l. 
  replace (App1 UPI4_H q :: App1 UPI4_H q :: l) with ((App1 UPI4_H q :: App1 UPI4_H q :: []) ++ l) by reflexivity.
  rewrite PI4_to_base_ucom_l_app.
  simpl.
  rewrite <- useq_assoc.
  autorewrite with eval_db.
  specialize (@H_H_id dim q) as HH.
  Local Transparent SQIR.H.
  unfold SQIR.H in HH.
  rewrite HH.
  apply ucom_id_l. 
  apply uc_well_typed_ID; assumption.
Qed.

Lemma X_X_cancel : forall {dim} (l : PI4_ucom_l dim) q, 
  q < dim -> App1 UPI4_X q :: App1 UPI4_X q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l. 
  replace (App1 UPI4_X q :: App1 UPI4_X q :: l) with ((App1 UPI4_X q :: App1 UPI4_X q :: []) ++ l) by reflexivity.
  rewrite PI4_to_base_ucom_l_app.
  simpl.
  rewrite <- useq_assoc. 
  specialize (@X_X_id dim q) as XX.
  Local Transparent X.
  unfold X in XX.
  rewrite XX.
  apply ucom_id_l. 
  apply uc_well_typed_ID; assumption.
Qed.

Lemma PI4_PI4_combine : forall {dim} (l : PI4_ucom_l dim) q k k', 
  App1 (UPI4_PI4 k) q :: App1 (UPI4_PI4 k') q :: l =l= App1 (UPI4_PI4 (k+k')) q :: l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db; simpl.
  repeat rewrite phase_shift_rotation.
  bdestruct (q + 1 <=? dim); try (Msimpl_light; trivial).
  rewrite Mmult_assoc.
  restore_dims; repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite phase_mul. 
  repeat rewrite <- Rmult_div_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite plus_IZR.
  rewrite Rplus_comm.
  reflexivity.
Qed.

Lemma PI4_PI4_m8_combine : forall {dim} (l : PI4_ucom_l dim) q k k', 
  App1 (UPI4_PI4 k) q :: App1 (UPI4_PI4 k') q :: l =l= App1 (UPI4_PI4 (k+k'-8)) q :: l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db; simpl.
  repeat rewrite phase_shift_rotation.
  repad.
  rewrite Mmult_assoc.
  restore_dims; repeat rewrite kron_mixed_product.
  Msimpl_light.
  rewrite phase_mul. 
  repeat rewrite <- Rmult_div_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- plus_IZR.
  repeat rewrite Rmult_div_assoc.
  rewrite phase_PI4_m8.
  rewrite Zplus_comm.
  reflexivity.
Qed.
  
Lemma PI4_PI4_cancel : forall {dim} (l : PI4_ucom_l dim) q k k', 
  q < dim -> 
  (k + k' = 8)%Z ->
  App1 (UPI4_PI4 k) q :: App1 (UPI4_PI4 k') q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  autorewrite with eval_db; simpl.
  repeat rewrite phase_shift_rotation.
  repad.
  rewrite Mmult_assoc.
  restore_dims; repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite phase_mul. 
  repeat rewrite <- Rmult_div_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- plus_IZR.
  repeat rewrite Rmult_div_assoc.
  rewrite Zplus_comm, H0.
  replace (8 * PI / 4)%R with (2 * PI)%R by lra.
  rewrite phase_2pi.
  repeat rewrite id_kron.
  restore_dims.
  Msimpl. 
  reflexivity.
Qed.
  
Lemma CNOT_CNOT_cancel : forall {dim} (l1 l2 : PI4_ucom_l dim) q1 q2, 
  q1 < dim -> q2 < dim -> q1 <> q2 -> l1 ++ [App2 UPI4_CNOT q1 q2] ++ [App2 UPI4_CNOT q1 q2] ++ l2 =l= l1 ++ l2.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  rewrite PI4_to_base_ucom_l_app, list_to_ucom_append; simpl.
  autorewrite with eval_db; simpl.
  bdestruct_all; Msimpl_light; try reflexivity;
  remember_differences; subst. (* maybe restore old repad *)
  - rewrite (Mmult_assoc (uc_eval (list_to_ucom (PI4_to_base_ucom_l l2)))). 
    rewrite (Mmult_assoc (uc_eval (list_to_ucom (PI4_to_base_ucom_l l2)))). 
    restore_dims; repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite Mmult_plus_distr_r. 
    repeat rewrite Mmult_plus_distr_l.
    restore_dims; repeat rewrite kron_mixed_product.
    Qsimpl.
    repeat rewrite kron_assoc.
    repeat rewrite id_kron.
    unify_pows_two.
    restore_dims.
    rewrite <- kron_plus_distr_r.
    Qsimpl.
    repeat rewrite id_kron.
    Msimpl_light.
    rewrite PI4_to_base_ucom_l_app, list_to_ucom_append; reflexivity.
  - rewrite (Mmult_assoc (uc_eval (list_to_ucom (PI4_to_base_ucom_l l2)))). 
    rewrite (Mmult_assoc (uc_eval (list_to_ucom (PI4_to_base_ucom_l l2)))). 
    restore_dims; repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite Mmult_plus_distr_r. 
    repeat rewrite Mmult_plus_distr_l.
    restore_dims; repeat rewrite kron_mixed_product.
    Qsimpl.
    repeat rewrite kron_assoc.
    repeat rewrite id_kron.
    restore_dims.
    rewrite <- 2 kron_plus_distr_l.
    Qsimpl.
    repeat rewrite id_kron.
    Msimpl_light.
    rewrite PI4_to_base_ucom_l_app, list_to_ucom_append; reflexivity.
Qed.  

Lemma cancel_gates_simple'_sound : forall {dim} (l acc : PI4_ucom_l dim) n,
  uc_well_typed_l l -> (rev acc) ++ l =l= cancel_gates_simple' l acc n.
Proof.
  intros.
  generalize dependent acc.
  generalize dependent l.
  induction n; try easy.
  intros l WT; simpl.
  destruct l; intros; try (rewrite app_nil_r; reflexivity).
  destruct g.
  - dependent destruction p;
    inversion WT;
    destruct (next_single_qubit_gate l n0) eqn:nsqg;
    try (rewrite <- IHn; try assumption;
         simpl; rewrite <- app_assoc; 
         reflexivity);
    do 2 destruct p.
    + (* H *)
      dependent destruction p; rewrite <- IHn;
      try (simpl; rewrite <- app_assoc; reflexivity);
      try assumption.
      rewrite (nsqg_commutes _ _ _ _ _ nsqg).
      apply uc_app_congruence; try reflexivity.
      apply H_H_cancel; assumption.
      apply uc_well_typed_l_app. 
      apply (nsqg_WT _ _ _ _ _ nsqg); assumption.
    + (* X *)
      dependent destruction p; rewrite <- IHn;
      try (simpl; rewrite <- app_assoc; reflexivity);
      try assumption.
      rewrite (nsqg_commutes _ _ _ _ _ nsqg).
      apply uc_app_congruence; try reflexivity.
      apply X_X_cancel; assumption.
      apply uc_well_typed_l_app. 
      apply (nsqg_WT _ _ _ _ _ nsqg); assumption.
    + (* PI4 *)
      dependent destruction p;
      [| | destruct (k + k0 =? 8)%Z eqn:E; [|destruct (k + k0 <? 8)%Z]];
      try rewrite <- IHn;
      try rewrite (nsqg_commutes _ _ _ _ _ nsqg);
      try (simpl; rewrite <- app_assoc; reflexivity);
      try constructor;
      try apply uc_well_typed_l_app;
      try apply (nsqg_WT _ _ _ _ _ nsqg);
      try assumption;
      apply uc_app_congruence;
      try reflexivity.
      apply Z.eqb_eq in E.
      apply PI4_PI4_cancel; lia.
      apply PI4_PI4_combine.
      apply PI4_PI4_m8_combine.
  - (* CNOT *)
    dependent destruction p.
    destruct (next_two_qubit_gate l n0) eqn:ntqg;
    inversion WT.
    2: { rewrite <- IHn; try assumption.
         simpl; rewrite <- app_assoc. 
         reflexivity. }
    do 4 destruct p.
    bdestruct (n0 =? n4); bdestruct (n1 =? n3); simpl;
    try (rewrite <- IHn; try assumption; simpl; rewrite <- app_assoc; reflexivity).
    subst.
    destruct (does_not_reference g0 n3) eqn:dnr; simpl;
    try (rewrite <- IHn; try assumption; simpl; rewrite <- app_assoc; reflexivity).
    rewrite (ntqg_preserves_structure _ _ _ _ _ _ _ ntqg).
    rewrite <- IHn.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as H8.
    rewrite app_comm_cons.
    rewrite app_assoc.
    rewrite (does_not_reference_commutes_app2 g0 UPI4_CNOT n4 n3 H8 dnr).
    repeat rewrite <- app_assoc.
    apply uc_app_congruence; try reflexivity.
    dependent destruction p.
    apply CNOT_CNOT_cancel; assumption.
    apply uc_well_typed_l_app.
    apply (ntqg_WT _ _ _ _ _ _ _ ntqg H6).
  - inversion p.
Qed.

Lemma cancel_gates_simple_sound : forall {dim} (l : PI4_ucom_l dim),
  uc_well_typed_l l -> l =l= cancel_gates_simple l.
Proof. 
  intros. 
  unfold cancel_gates_simple.
  rewrite <- cancel_gates_simple'_sound.
  reflexivity. 
  assumption. 
Qed.

(* Small test *)
Definition test1 : PI4_ucom_l 4 := (App1 UPI4_H 1) :: (App1 UPI4_P 0) :: (App2 UPI4_CNOT 2 3) :: (App1 UPI4_P 0) :: (App1 UPI4_H 1) :: (App1 UPI4_Z 1) :: (App1 UPI4_PDAG 0) :: (App2 UPI4_CNOT 2 3) :: (App1 UPI4_T 0) :: [].
Compute (cancel_gates_simple test1).

(**********************************************************************)
(** Optimization: simple cancellation and combination w/ commutation **)
(**********************************************************************)

(* Cancel and combine gates, as above, but also check for cancellations
   across commuting subcircuits. We will determine whether a gate
   commutes through a subcircuit using the following circuits identities
   from Nam et al.

   - X b ; CNOT a b ≡ CNOT a b ; X b
   - X a ; Rz a ≡ Rz† ; X a         (up to a global phase)
   - Rz b ; H b ; CNOT a b ; H b ≡ H b ; CNOT a b ; H b ; Rz b
   - Rz b ; CNOT a b ; Rz' b ; CNOT a b ≡ CNOT a b ; Rz' b ; CNOT a b ; Rz b
   - Rz a ; CNOT a b ≡ CNOT a b ; Rz a
   - CNOT a c ; CNOT b c ≡ CNOT b c ; CNOT a c
   - CNOT a c ; CNOT a b ≡ CNOT a b ; CNOT a c
   - CNOT a b; H b; CNOT b c; H b ≡ H b; CNOT b c; H b; CNOT a b

   This optimization is similar to Nam et al.'s single/two-qubit gate
   cancellation and not propagation.
*)

(* Commutativity rule for X *)

Definition search_for_X_pat1 {dim} (l : PI4_ucom_l dim) q :=
  match next_two_qubit_gate l q with
  | Some (l1, UPI4_CNOT, q1, q2, l2) =>
      if q =? q2
      then Some (l1 ++ [App2 UPI4_CNOT q1 q2], l2)
      else None
  | _ => None
  end.

Definition search_for_X_pat2 {dim} (l : PI4_ucom_l dim) q :=
  match next_single_qubit_gate l q with
  | Some (l1, UPI4_PI4 k, l2) => Some (l1 ++ [App1 (UPI4_PI4 (8 - k)%Z) q], l2)
  | _ => None
  end.

Definition search_for_commuting_X_pat {dim} (l : PI4_ucom_l dim) q :=
  match search_for_X_pat1 l q with
  | Some (l1, l2) => Some (l1, l2)
  | None => match search_for_X_pat2 l q with
           | Some (l1, l2) => Some (l1, l2)
           | None => None
           end
  end.

(* Commutativity rules for Rz *)

Definition search_for_Rz_pat1 {dim} (l : PI4_ucom_l dim) q :=
  match (next_single_qubit_gate l q) with
  | Some (l1, UPI4_H, l2) => 
      match (next_two_qubit_gate (l1 ++ l2) q) with
      | Some (l1, UPI4_CNOT, q1, q2, l2) =>
          if q =? q2
          then match (next_single_qubit_gate l2 q) with
               | Some (l2_1, UPI4_H, l2_2) => Some ([App1 UPI4_H q] ++ l1 ++ [App2 UPI4_CNOT q1 q] ++ [App1 UPI4_H q], l2_1 ++ l2_2) 
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition search_for_Rz_pat2 {dim} (l : PI4_ucom_l dim) q :=
  match (next_two_qubit_gate l q) with
  | Some (l1, UPI4_CNOT, q1, q2, l2) => 
      if q =? q2
      then match (next_single_qubit_gate l2 q) with
           | Some (l2_1, UPI4_PI4 k as u, l2_2) =>
               match (next_two_qubit_gate (l2_1 ++ l2_2) q) with
               | Some (l3, UPI4_CNOT, q3, q4, l4) => 
                   if (q =? q4) && (q1 =? q3) && (does_not_reference l3 q3)
                   then Some (l1 ++ [App2 UPI4_CNOT q1 q] ++ [App1 u q] ++ l3 ++ [App2 UPI4_CNOT q1 q], l4)
                   else None 
               | _ => None
               end
           | _ => None
           end
      else None
  | _ => None
  end.

Definition search_for_Rz_pat3 {dim} (l : PI4_ucom_l dim) q :=
  match (next_two_qubit_gate l q) with
  | Some (l1, UPI4_CNOT, q1, q2, l2) => 
      if q =? q1
      then Some (l1 ++ [App2 UPI4_CNOT q1 q2], l2)
      else None
  | _ => None
  end.

Definition search_for_commuting_Rz_pat {dim} (l : PI4_ucom_l dim) q :=
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

Definition search_for_CNOT_pat1 {dim} (l : PI4_ucom_l dim) (q1 q2 : nat) : option (PI4_ucom_l dim * PI4_ucom_l dim) :=
  match (next_single_qubit_gate l q1) with
  | Some (l1, UPI4_PI4 k as u, l2) => Some ([App1 u q1], l1 ++ l2)
  | _ => None
  end.

Definition search_for_CNOT_pat2 {dim} (l : PI4_ucom_l dim) q1 q2 :=
  match (next_two_qubit_gate l q2) with
  | Some (l1, UPI4_CNOT, q1', q2', l2) => 
      if q2 =? q2'
      then if (does_not_reference l1 q1) && (does_not_reference l1 q1')
           then Some (l1 ++ [App2 UPI4_CNOT q1' q2], l2)
           else None
      else None
  | _ => None
  end.

Definition search_for_CNOT_pat3 {dim} (l : PI4_ucom_l dim) q1 q2 :=
  match (next_two_qubit_gate l q1) with
  | Some (l1, UPI4_CNOT, q1', q2', l2) => 
      if q1 =? q1'
      then if (does_not_reference l1 q2) && (does_not_reference l1 q2')
           then Some (l1 ++ [App2 UPI4_CNOT q1 q2'], l2)
           else None
      else None
  | _ => None
  end.

Definition search_for_CNOT_pat4 {dim} (l : PI4_ucom_l dim) q1 q2 :=
  match (next_single_qubit_gate l q2) with
  | Some (l1, UPI4_H, l2) => 
      match (next_two_qubit_gate (l1 ++ l2) q2) with
      | Some (l1, UPI4_CNOT, q1', q2', l2) => 
          if (q2 =? q1') && ¬ (q1 =? q2') && (does_not_reference l1 q1)
          then match (next_single_qubit_gate l2 q2) with
               | Some (l2_1, UPI4_H, l2_2) => Some ([App1 UPI4_H q2] ++ l1 ++ [App2 UPI4_CNOT q2 q2'] ++ [App1 UPI4_H q2], l2_1 ++ l2_2)
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition search_for_commuting_CNOT_pat {dim} (l : PI4_ucom_l dim) q1 q2 :=
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

Fixpoint propagate_PI4 {dim} k (l : PI4_ucom_l dim) (q n : nat) : option (PI4_ucom_l dim) :=
  match n with
  | O => None
  | S n' => 
      match next_single_qubit_gate l q with
      | Some (l1, UPI4_PI4 k', l2) => 
                 let k'' := (k + k')%Z in
                 (* Cancel *)
                 if (k'' =? 8)%Z then Some (l1 ++ l2) else 
                 (* Combine *)
                 if (k'' <? 8)%Z then Some (App1 (UPI4_PI4 k'') q :: (l1 ++ l2))
                 else Some (App1 (UPI4_PI4 (k'' - 8)%Z) q :: (l1 ++ l2)) 
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

Definition propagate_H {dim} (l : PI4_ucom_l dim) (q : nat) : option (PI4_ucom_l dim) :=
  match next_single_qubit_gate l q with
  (* Cancel *)
  | Some (l1, UPI4_H, l2) => Some (l1 ++ l2)
  (* Currently no rules for commuting H gates *)
  | _ => None
  end.

Fixpoint propagate_X {dim} (l : PI4_ucom_l dim) (q n : nat) : option (PI4_ucom_l dim) :=
  match n with
  | O => None
  | S n' => 
      match next_single_qubit_gate l q with
      (* Cancel *)
      | Some (l1, UPI4_X, l2) => Some (l1 ++ l2)
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

Fixpoint propagate_CNOT {dim} (l : PI4_ucom_l dim) (q1 q2 n : nat) : option (PI4_ucom_l dim) :=
  match n with
  | O => None
  | S n' => 
      match next_two_qubit_gate l q1 with
      (* Cancel *)
      | Some (l1, UPI4_CNOT, q1', q2', l2) => 
          if (q1 =? q1') && (q2 =? q2') && (does_not_reference l1 q2)
          then Some (l1 ++ l2)
          else None
      (* Commute *)
      | _ =>
          match search_for_commuting_CNOT_pat l q1 q2 with
          | Some (l1, l2) => match (propagate_CNOT l2 q1 q2 n') with
                            | Some l' => Some (l1 ++ l')
                            | None => None
                            end
          | None =>  None
          end
      end
  end.

Fixpoint cancel_gates' {dim} (l : PI4_ucom_l dim) (n: nat) : PI4_ucom_l dim :=
  match n with
  | 0 => l
  | S n' => match l with
           | App1 (UPI4_PI4 k) q :: t => 
               match propagate_PI4 k t q (length t) with
               | None => (App1 (UPI4_PI4 k) q) :: (cancel_gates' t n')
               | Some l' => cancel_gates' l' n'
               end
           | App1 UPI4_H q :: t => 
               match propagate_H t q with
               | None => (App1 UPI4_H q) :: (cancel_gates' t n')
               | Some l' => cancel_gates' l' n'
               end
           | App1 UPI4_X q :: t => 
               match propagate_X t q (length t) with
               | None => (App1 UPI4_X q) :: (cancel_gates' t n')
               | Some l' => cancel_gates' l' n'
               end
           | App2 UPI4_CNOT q1 q2 :: t => 
               match propagate_CNOT t q1 q2 (length t) with
               | None => (App2 UPI4_CNOT q1 q2) :: (cancel_gates' t n')
               | Some l' => cancel_gates' l' n'
               end
           | _ => []
           end
  end.

Definition cancel_gates {dim} (l : PI4_ucom_l dim) := 
  cancel_gates' l (length l).

(* Proofs about commutativity *)

Lemma commuting_X_pat : forall {dim} (l : PI4_ucom_l dim) q l1 l2, 
  search_for_commuting_X_pat l q = Some (l1, l2) ->
  (App1 UPI4_X q :: l) ≅l≅ (l1 ++ [App1 UPI4_X q] ++ l2).
Proof.
  intros.
  unfold search_for_commuting_X_pat in H.
  destruct (search_for_X_pat1 l q) eqn:HS; 
  [|destruct (search_for_X_pat2 l q) eqn:HS2]; try discriminate.
  - unfold search_for_X_pat1 in HS.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_two_qubit_gate l q) eqn:ntqg; try easy.
    do 4 destruct p.
    dependent destruction p.
    bdestruct (q =? n); try easy.
    inversion H; subst.
    rewrite (ntqg_preserves_structure _ _ _ _ _ _ _ ntqg).
    apply ntqg_l1_does_not_reference in ntqg.
    rewrite app_comm_cons.
    apply uc_equiv_cong_l.
    rewrite (does_not_reference_commutes_app1 _ UPI4_X _ ntqg).
    inversion HS; subst.
    repeat rewrite <- app_assoc.
    apply uc_app_congruence; try reflexivity.
    repeat rewrite app_assoc.
    apply uc_app_congruence; try reflexivity.
    unfold uc_equiv_l; simpl.
    destruct dim.
    + unfold uc_equiv; simpl.
      unfold pad.
      bdestruct_all. 
      Msimpl_light; reflexivity.
    + repeat rewrite <- useq_assoc.
      unfold SKIP.
      do 2 (rewrite ucom_id_r; try apply uc_well_typed_ID; try lia).
      apply X_CNOT_comm.
  - unfold search_for_X_pat2 in HS2.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_single_qubit_gate l q) eqn:nsqg; try easy.
    repeat destruct p.
    dependent destruction p; try discriminate.
    remember (8 - k)%Z as k'.
    inversion HS2. subst l1 l2.
    specialize (nsqg_commutes _ _ _ _ _ nsqg) as H.
    apply uc_equiv_cong_l in H.
    rewrite H; clear H.
    apply nsqg_l1_does_not_reference in nsqg.
    specialize (does_not_reference_commutes_app1 g0 (UPI4_PI4 k') q nsqg) as H.
    apply uc_equiv_cong_l in H.
    rewrite <- H; clear H.
    rewrite <- (app_assoc _ g0).
    rewrite (app_assoc g0).
    specialize (does_not_reference_commutes_app1 g0 UPI4_X q nsqg) as H.
    apply uc_equiv_cong_l in H.
    rewrite <- H; clear H.
    rewrite app_comm_cons.
    repeat rewrite app_assoc.
    do 2 (apply uc_cong_l_app_congruence; try reflexivity).
    exists (IZR k * PI / 4)%R.
    simpl.
    destruct dim. (* get rid of dim = 0 case *)
    unfold pad; bdestruct_all; Msimpl_light; reflexivity.
    autorewrite with eval_db; try lia.
    bdestruct_all; try Msimpl_light; trivial.
    repeat rewrite kron_mixed_product.
    Msimpl_light.
    rewrite <- Mscale_kron_dist_l.
    rewrite <- Mscale_kron_dist_r.
    do 2 (apply f_equal2; try reflexivity).
    do 2 rewrite phase_shift_rotation.    
    rewrite pauli_x_rotation.
    solve_matrix.
    rewrite <- Cexp_add.
    subst.
    rewrite <- 2 Rmult_div_assoc.
    rewrite <- Rmult_plus_distr_r.
    rewrite <- plus_IZR.
    replace (k + (8 - k))%Z with 8%Z by lia.
    replace (8 * (PI / 4))%R with (2 * PI)%R by lra.
    rewrite Cexp_2PI.
    reflexivity.
Qed.

Lemma app_cons_app : forall {A} (a : A) (l1 l2 : list A), a :: l1 ++ l2 = [a] ++ l1 ++ l2.
Proof. reflexivity. Qed.

Lemma commuting_Rz_pat : forall {dim} k (l : PI4_ucom_l dim) q l1 l2,
  search_for_commuting_Rz_pat l q = Some (l1, l2) ->
  App1 (UPI4_PI4 k) q :: l =l= l1 ++ [App1 (UPI4_PI4 k) q] ++ l2.
Proof.
  intros.
  unfold search_for_commuting_Rz_pat in H.
  destruct (search_for_Rz_pat1 l q) eqn:HS; 
  [|destruct (search_for_Rz_pat2 l q) eqn:HS2;
  [|destruct (search_for_Rz_pat3 l q) eqn:HS3]]; try discriminate.
  - unfold search_for_Rz_pat1 in HS.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_single_qubit_gate l q) eqn:HN1; try discriminate.
    repeat destruct p.
    dependent destruction p; try discriminate.
    apply nsqg_commutes in HN1.
    destruct (next_two_qubit_gate (g0 ++ g) q) eqn:HN2; try discriminate.
    repeat destruct p.
    dependent destruction p; try discriminate.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_structure in HN2.
    bdestruct (q =? n); try easy.
    destruct (next_single_qubit_gate g1 q) eqn:HN1'; try discriminate.
    repeat destruct p.
    dependent destruction p; try discriminate.
    apply nsqg_commutes in HN1'.
    inversion HS; subst.
    rewrite HN1, HN2, HN1'.
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    rewrite <- (app_assoc _ _ g2).
    rewrite (does_not_reference_commutes_app1 _ UPI4_H _ NoRef).
    rewrite (app_assoc _ g2).
    rewrite (does_not_reference_commutes_app1 _ (UPI4_PI4 k) _ NoRef).
    repeat rewrite <- app_assoc.  
    apply uc_app_congruence; try reflexivity.
    repeat rewrite app_assoc.
    do 2 (apply uc_app_congruence; try reflexivity).
    unfold uc_equiv_l, uc_equiv; simpl.
    destruct dim. (* get rid of dim = 0 case *)
    unfold pad; bdestruct_all; Msimpl_light; reflexivity.
    rewrite hadamard_rotation, phase_shift_rotation.
    autorewrite with eval_db; try lia.
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
    dependent destruction p; try discriminate.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_structure in HN2.
    bdestruct (q =? n); try discriminate.
    subst.
    destruct (next_single_qubit_gate g n) eqn:HN1; try discriminate.
    repeat destruct p.
    dependent destruction p; try discriminate.
    apply nsqg_commutes in HN1.
    destruct (next_two_qubit_gate (g2 ++ g1) n) eqn:HN2'; try discriminate.
    repeat destruct p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ HN2') as NoRef'.
    apply ntqg_preserves_structure in HN2'.
    dependent destruction p; try discriminate.
    bdestruct (n =? n1); try discriminate.
    bdestruct (n0 =? n2); try discriminate.
    destruct (does_not_reference g4 n2) eqn:NoRef''; try discriminate.
    simpl in HS2.
    inversion HS2; subst. clear HS2.
    rewrite HN1, HN2'.
    rewrite app_comm_cons.
    rewrite (does_not_reference_commutes_app1 _ (UPI4_PI4 k) _ NoRef).
    repeat rewrite <- app_assoc.
    apply uc_app_congruence; try reflexivity. 
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    apply uc_app_congruence; try reflexivity. 
    repeat rewrite <- app_assoc.    
    rewrite <- (does_not_reference_commutes_app2 _ UPI4_CNOT _ _ NoRef'' NoRef').
    rewrite (app_assoc g4).
    rewrite <- (does_not_reference_commutes_app2 _ UPI4_CNOT _ _ NoRef'' NoRef').
    rewrite <- app_assoc.
    rewrite <- (does_not_reference_commutes_app1 _ (UPI4_PI4 k) _ NoRef').
    repeat rewrite app_assoc.    
    apply uc_app_congruence; try reflexivity.
    unfold uc_equiv_l, uc_equiv; simpl.
    destruct dim. (* get rid of dim = 0 case *)
    unfold pad; bdestruct_all; Msimpl_light; reflexivity.
    repeat rewrite phase_shift_rotation.
    autorewrite with eval_db; try lia.
    gridify.
    + replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
      replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
      Msimpl_light.
      rewrite 2 phase_mul. rewrite Rplus_comm.
      replace (σx × phase_shift (IZR k0 * PI / 4) × σx × phase_shift (IZR k * PI / 4))
        with (phase_shift (IZR k * PI / 4) × σx × phase_shift (IZR k0 * PI / 4) × σx) by
        solve_matrix.
      reflexivity.
    + replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
      replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
      Msimpl_light.      
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
    dependent destruction p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_structure in HN2.
    bdestruct (q =? n0); try discriminate.
    subst.
    inversion HS3. subst.
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    apply uc_app_congruence; try reflexivity. 
    rewrite (does_not_reference_commutes_app1 _ (UPI4_PI4 k) _ NoRef).
    repeat rewrite <- app_assoc.
    apply uc_app_congruence; try reflexivity. 
    (* simple slide lemma: should exist already? *)
    unfold uc_equiv_l, uc_equiv; simpl.
    destruct dim. (* get rid of dim = 0 case *)
    unfold pad; bdestruct_all; Msimpl_light; reflexivity.
    rewrite phase_shift_rotation.
    autorewrite with eval_db; try lia.
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
Lemma commuting_CNOT_pat : forall {dim} (l : PI4_ucom_l dim) q1 q2 l1 l2,
  search_for_commuting_CNOT_pat l q1 q2 = Some (l1, l2) ->
  App2 UPI4_CNOT q1 q2 :: l =l= l1 ++ [App2 UPI4_CNOT q1 q2] ++ l2.
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
    repeat destruct p.
    dependent destruction p; try discriminate.
    apply nsqg_commutes in HN1.
    inversion HS; subst. clear HS.
    rewrite HN1. (* Wasn't this the last case of Rz *)
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    do 2 (apply uc_app_congruence; try reflexivity).
    unfold uc_equiv_l, uc_equiv; simpl.
    destruct dim. (* get rid of dim = 0 case *)
    unfold pad; bdestruct_all; Msimpl_light; reflexivity.
    rewrite phase_shift_rotation.
    autorewrite with eval_db; try lia.
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
    dependent destruction p; try discriminate.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_structure in HN2.
    bdestruct (q2 =? n); try discriminate. subst.   
    destruct (does_not_reference g0 q1) eqn:NoRef'; try discriminate. 
    destruct (does_not_reference g0 n0) eqn:NoRef''; try discriminate.
    simpl in HS. inversion HS; subst. clear HS.
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    rewrite (does_not_reference_commutes_app2 _ UPI4_CNOT _ _ NoRef' NoRef).
    apply uc_app_congruence; try reflexivity.
    repeat rewrite <- app_assoc.
    apply uc_app_congruence; try reflexivity.
    unfold uc_equiv_l, uc_equiv; simpl.
    destruct dim. (* get rid of dim = 0 case *)
    unfold pad; bdestruct_all; Msimpl_light; reflexivity.
    autorewrite with eval_db; try lia.
    gridify; reflexivity.
  - unfold search_for_CNOT_pat3 in HS.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_two_qubit_gate l q1) eqn:HN2; try discriminate.
    repeat destruct p.
    dependent destruction p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_structure in HN2.
    bdestruct (q1 =? n0); try discriminate. subst.   
    destruct (does_not_reference g0 q2) eqn:NoRef'; try discriminate. 
    destruct (does_not_reference g0 n) eqn:NoRef''; try discriminate.
    simpl in HS. inversion HS; subst. clear HS.
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    rewrite (does_not_reference_commutes_app2 _ UPI4_CNOT _ _ NoRef NoRef').
    apply uc_app_congruence; try reflexivity.
    repeat rewrite <- app_assoc.
    apply uc_app_congruence; try reflexivity.
    unfold uc_equiv_l, uc_equiv; simpl.
    destruct dim. (* get rid of dim = 0 case *)
    unfold pad; bdestruct_all; Msimpl_light; reflexivity.
    autorewrite with eval_db; try lia.
    gridify; try reflexivity.
    all: replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix;
         replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix;
         reflexivity.
  - unfold search_for_CNOT_pat4 in HS.
    destruct p.
    inversion H; subst. clear H.
    destruct (next_single_qubit_gate l q2) eqn:HN1; try discriminate.
    repeat destruct p.
    dependent destruction p; try discriminate.
    apply nsqg_commutes in HN1.
    destruct (next_two_qubit_gate (g0 ++ g) q2) eqn:HN2; try discriminate.
    repeat destruct p.
    dependent destruction p.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ HN2) as NoRef.
    apply ntqg_preserves_structure in HN2.
    bdestruct (q2 =? n0); try discriminate; subst.
    bdestruct (q1 =? n); try discriminate; subst.
    destruct (does_not_reference g2 q1) eqn:NoRef'; try discriminate.
    simpl in HS.
    destruct (next_single_qubit_gate g1 n0) eqn:HN1'; try discriminate.
    repeat destruct p.
    apply nsqg_commutes in HN1'.
    dependent destruction p; try discriminate.
    inversion HS; subst; clear HS.
    rewrite HN1, HN2, HN1'.
    repeat rewrite app_cons_app.
    repeat rewrite app_assoc.
    rewrite (does_not_reference_commutes_app1 _ UPI4_H _ NoRef).
    rewrite <- (app_assoc _ _ g2).
    rewrite (does_not_reference_commutes_app1 _ UPI4_H _ NoRef).
    rewrite app_assoc.
    rewrite (does_not_reference_commutes_app2 _ UPI4_CNOT _ _ NoRef' NoRef).
    do 2 (apply uc_app_congruence; try reflexivity).
    repeat rewrite <- app_assoc.
    apply uc_app_congruence; try reflexivity.
    unfold uc_equiv_l, uc_equiv; simpl.
    destruct dim. (* get rid of dim = 0 case *)
    unfold pad; bdestruct_all; Msimpl_light; reflexivity.
    rewrite hadamard_rotation.
    autorewrite with eval_db; try lia.
    clear - H.
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

Lemma propagate_H_sound : forall {dim} (l : PI4_ucom_l dim) q l',
  q < dim ->
  propagate_H l q = Some l' ->
  App1 UPI4_H q :: l =l= l'.
Proof. 
  intros.
  unfold propagate_H in H0; simpl in H0.
  destruct (next_single_qubit_gate l q) eqn:nsqg; try discriminate.
  repeat destruct p; dependent destruction p; try discriminate.
  inversion H0; subst.
  rewrite (nsqg_commutes _ _ _ _ _ nsqg).
  apply H_H_cancel; assumption.
Qed.

Lemma propagate_H_WT : forall {dim} (l : PI4_ucom_l dim) q l',
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

Lemma propagate_X_sound : forall {dim} (l : PI4_ucom_l dim) q n l',
  q < dim ->
  propagate_X l q n = Some l' ->
  (App1 UPI4_X q :: l) ≅l≅ l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction n; try easy.
  simpl.
  intros.
  destruct (next_single_qubit_gate l q) eqn:nsqg;
  repeat destruct p;
  try dependent destruction p.
  2: (* Cancel case *)
     inversion H0; subst;
     apply uc_equiv_cong_l;
     rewrite (nsqg_commutes _ _ _ _ _ nsqg);
     apply X_X_cancel; assumption.
  all: (* Commute cases *)
     destruct (search_for_commuting_X_pat l q) eqn:pat; try discriminate;
     destruct p.
  1, 2: destruct (propagate_X g1 q n) eqn:prop; try discriminate.
  3: destruct (propagate_X g q n) eqn:prop; try discriminate.
  all: inversion H0; subst;
     rewrite (commuting_X_pat _ _ _ _ pat);
     rewrite (IHn _ _ prop);
     reflexivity.
Qed.

Lemma propagate_X_WT : forall {dim} (l : PI4_ucom_l dim) q n l',
  q < dim ->
  uc_well_typed_l l ->
  propagate_X l q n = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  specialize (propagate_X_sound l q n l' H H1) as H2.
  apply (uc_cong_l_implies_WT _ _ H2).
  constructor; assumption.
Qed.

Lemma propagate_PI4_sound : forall {dim} k (l : PI4_ucom_l dim) q n l',
  q < dim ->
  propagate_PI4 k l q n = Some l' ->
  App1 (UPI4_PI4 k) q :: l =l= l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction n; try easy.
  simpl.
  intros.
  destruct (next_single_qubit_gate l q) eqn:nsqg;
  repeat destruct p;
  try dependent destruction p. 
  3: { (* Cancel/combine case *)
        destruct (k + k0 =? 8)%Z eqn:k_k0_8.
        apply Z.eqb_eq in k_k0_8.
        inversion H0; subst.
        rewrite (nsqg_commutes _ _ _ _ _ nsqg).
        apply PI4_PI4_cancel; assumption. 
        destruct (k + k0 <? 8)%Z; inversion H0; subst;
        rewrite (nsqg_commutes _ _ _ _ _ nsqg).
        apply PI4_PI4_combine.
        apply PI4_PI4_m8_combine. }
  all: (* Commute cases *)
     destruct (search_for_commuting_Rz_pat l q) eqn:pat; try discriminate;
     destruct p;
     destruct (propagate_PI4 k l1 q n) eqn:prop; try discriminate;
     inversion H0; subst;
     rewrite (commuting_Rz_pat _ _ _ _ _ pat);
     rewrite (IHn _ _ prop);
     reflexivity.
Qed.

Lemma propagate_PI4_WT : forall {dim} k (l : PI4_ucom_l dim) q n l',
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

Lemma propagate_CNOT_sound : forall {dim} (l : PI4_ucom_l dim) q1 q2 n l',
  q1 < dim ->
  q2 < dim -> 
  q1 <> q2 ->
  propagate_CNOT l q1 q2 n = Some l' ->
  App2 UPI4_CNOT q1 q2 :: l =l= l'.
Proof. 
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction n; try easy.
  simpl.
  intros.
  destruct (next_two_qubit_gate l q1) eqn:ntqg;
  repeat destruct p.
  dependent destruction p.
  (* Cancel case *)
  destruct (does_not_reference g0 q2) eqn:dnr;
  bdestruct (q1 =? n1); bdestruct (q2 =? n0);
  simpl in H2; inversion H2; subst.
  rewrite (ntqg_preserves_structure _ _ _ _ _ _ _ ntqg).
  apply ntqg_l1_does_not_reference in ntqg.
  rewrite app_cons_app.
  rewrite (app_assoc _ _ g).
  rewrite <- (does_not_reference_commutes_app2 _ UPI4_CNOT _ _ ntqg dnr).
  simpl.
  specialize (CNOT_CNOT_cancel [] (g0 ++ g) _ _ H H0 H1) as H3.
  simpl in H3.
  assumption.
  (* Commute case *)
  destruct (search_for_commuting_CNOT_pat l q1 q2) eqn:pat; try discriminate;
  destruct p.
  destruct (propagate_CNOT p0 q1 q2 n) eqn:prop; try discriminate.
  inversion H2; subst.
  rewrite (commuting_CNOT_pat _ _ _ _ _ pat).
  rewrite (IHn _ _ prop).
  reflexivity.
Qed.

Lemma propagate_CNOT_WT : forall {dim} (l : PI4_ucom_l dim) q1 q2 n l',
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

Lemma cancel_gates'_sound : forall {dim} (l : PI4_ucom_l dim) n,
  uc_well_typed_l l -> cancel_gates' l n ≅l≅ l.
Proof.
  intros.
  generalize dependent l.
  induction n; intros; try reflexivity.
  destruct l; try reflexivity.
  destruct g.
  - inversion H; subst. 
    dependent destruction p.
    + (* UPI4_H *) 
      simpl.
      remember (propagate_H l n0) as prop; symmetry in Heqprop.
      destruct prop; rewrite IHn; try reflexivity; try assumption.
      apply uc_equiv_cong_l.
      rewrite (propagate_H_sound _ _ _ H2 Heqprop).
      reflexivity.
      apply (propagate_H_WT _ _ _ H2 H4 Heqprop).
    + (* UPI4_X *)
      simpl.
      remember (propagate_X l n0 (length l)) as prop; symmetry in Heqprop.
      destruct prop; rewrite IHn; try reflexivity; try assumption.
      rewrite (propagate_X_sound _ _ _ _ H2 Heqprop).
      reflexivity.
      apply (propagate_X_WT _ _ _ _ H2 H4 Heqprop).
    + (* UPI4_PI4 *)
      simpl.
      remember (propagate_PI4 k l n0 (length l)) as prop; symmetry in Heqprop.
      destruct prop; rewrite IHn; try reflexivity; try assumption.
      apply uc_equiv_cong_l.
      rewrite (propagate_PI4_sound _ _ _ _ _ H2 Heqprop).
      reflexivity.
      apply (propagate_PI4_WT _ _ _ _ _ H2 H4 Heqprop).
  - (* UPI4_CNOT *)
    dependent destruction p; simpl.
    inversion H; subst. 
    remember (propagate_CNOT l n0 n1 (length l)) as prop; symmetry in Heqprop.
    destruct prop; rewrite IHn; try reflexivity; try assumption.
    apply uc_equiv_cong_l.
    rewrite (propagate_CNOT_sound _ _ _ _ _ H4 H5 H6 Heqprop).
    reflexivity.
    apply (propagate_CNOT_WT _ _ _ _ _ H4 H5 H6 H7 Heqprop).
  - inversion p.
Qed.

Lemma cancel_gates_sound : forall {dim} (l : PI4_ucom_l dim), 
  uc_well_typed_l l -> cancel_gates l ≅l≅ l.
Proof. intros. apply cancel_gates'_sound; assumption. Qed.
