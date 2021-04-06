Require Import DensitySem.
Require Import RzQGateSet.

Module RzQProps := NonUListRepresentationProps RzQGateSet.
Export RzQProps.

Local Open Scope com_scope.

(* This optimization removes z-rotations (RzQ gates) that occur immediately before measurement. *)

(** Basic equivalences. **)

Lemma skip_id_r : forall dim (c : base_com dim),
  c; skip ≡ c.
Proof.
  intros.
  unfold c_equiv; simpl.
  unfold compose_super; reflexivity.
Qed.
 
Lemma Rz_mif : forall dim θ n (c1 c2 : base_com dim), 
  SQIR.Rz θ n ; mif n then c1 else c2 ≡ mif n then c1 else c2.
Proof.
  intros.
  unfold c_equiv; simpl.
  intros.
  unfold compose_super, Splus, super.
  autorewrite with eval_db.
  repad. subst. clear.
  Msimpl.
  repeat rewrite Mmult_assoc.
  Msimpl.
  repeat (restore_dims; rewrite <- Mmult_assoc).
  Qsimpl.
  replace (phase_shift (- θ) × ∣0⟩) with ∣0⟩ by solve_matrix.
  replace (phase_shift (- θ) × ∣1⟩) with (Cexp (- θ) .* ∣1⟩) by solve_matrix.
  repeat (restore_dims; rewrite Mmult_assoc).
  replace (⟨0∣ × phase_shift θ) with ⟨0∣ by solve_matrix.
  replace (⟨1∣ × phase_shift θ) with (Cexp θ .* ⟨1∣) by solve_matrix.
  apply f_equal2; trivial.
  distribute_scale.  
  rewrite Cexp_mul_neg_r.
  rewrite Mscale_1_l.
  reflexivity.
Qed. 

(* list version of the equivalence above *)
Lemma RzQ_Meas : forall {dim} i n (l1 l2 : RzQ_com_l dim), 
  (UC [Rz i n]) :: [Meas n l1 l2] =l= [Meas n l1 l2].
Proof.
  intros.
  unfold c_equiv_l; simpl.
  rewrite instr_to_com_UC, instr_to_com_Meas. 
  simpl.
  rewrite skip_id_r.
  rewrite <- Rz_mif with (θ:=(Qreals.Q2R i * PI)%R) at 2.
  apply seq_congruence; try reflexivity.
  unfold c_equiv; simpl.
  intros.
  rewrite phase_shift_rotation.
  unfold super.
  autorewrite with eval_db; try assumption.
  bdestruct (n + 1 <=? dim); Msimpl; reflexivity.
Qed. 

(* Not currently used, but could be useful for non-unitary X propagation. *)
Lemma X_mif : forall dim n (c1 c2 : base_com dim), 
  SQIR.X n ; mif n then c1 else c2 ≡ 
    mif n then (SQIR.X n ; c2) else (SQIR.X n ; c1).
Proof.
  intros.
  unfold c_equiv; simpl.
  intros.
  unfold compose_super, Splus, super.
  autorewrite with eval_db.
  repad. subst. clear.
  Msimpl.
  repeat rewrite Mmult_assoc.
  Msimpl.
  repeat (restore_dims; rewrite <- Mmult_assoc).
  Qsimpl.
  rewrite Mplus_comm; reflexivity.
  rewrite Mplus_comm; reflexivity.
Qed. 

(** Remove phase shifts before measurement. **)

(* Note that this will only remove one Rz gate per UC block. To remove multiple
   Rz gates per UC block, the function below could be modified - or just run multiple times. *)

(* Get the next rotation gate on any qubit. *)
Fixpoint next_Rz_gate {dim} (l : RzQ_ucom_l dim)
             : option (RzQ_ucom_l dim * Q * nat * RzQ_ucom_l dim) :=
  match l with
  | [] => None
  | (App1 (URzQ_Rz i) n) :: t => Some ([], i, n, t) 
  | g :: t => match (next_Rz_gate t) with
            | None => None
            | Some (l1, i, n, l2) => Some (g :: l1, i, n, l2)
            end
  end.

(* Perform the optimization. *)
Fixpoint remove_Rz_before_meas' {dim} (l : RzQ_com_l dim) n :=
  match n with
  | O => l
  | S n' =>
      match l with
      | [] => []
      | UC u :: t => 
          match next_Rz_gate u with
          | None => UC u :: remove_Rz_before_meas' t n'
          | Some (l1, _, n, l2) => 
              match next_measurement (UC l2 :: t) n with
              | Some _ => UC (l1 ++ l2) :: remove_Rz_before_meas' t n'
              | None => UC u :: remove_Rz_before_meas' t n'
              end
          end
      | Meas n l1 l2 :: t =>
          let l1' := remove_Rz_before_meas' l1 n' in
          let l2' := remove_Rz_before_meas' l2 n' in
          Meas n l1' l2' :: remove_Rz_before_meas' t n'
      end
  end.
Definition remove_Rz_before_meas {dim} (l : RzQ_com_l dim) :=
  remove_Rz_before_meas' l (count_ops l).

(** Examples **)

Definition test1 : RzQ_com_l 3 := UC (X 2 :: Z 0 :: CNOT 1 2 :: []) :: Meas 0 [] [] :: [].
Compute (count_ops test1).
Compute (remove_Rz_before_meas test1).
Definition test2 : RzQ_com_l 3 := UC (X 2 :: Z 0 :: CNOT 1 2 :: []) :: Meas 0 (UC [P 1] :: Meas 1 [] [] :: []) [] :: [].
Compute (count_ops test2).
Compute (remove_Rz_before_meas test2).
Definition test3 : RzQ_com_l 3 := UC (X 2 :: Z 0 :: CNOT 1 2 :: []) :: UC (H 2 :: []) :: Meas 2 [] [UC [H 1]] :: Meas 0 (UC [P 1] :: Meas 0 [] [] :: Meas 1 [] [] :: []) [UC (X 2 :: CNOT 1 2 :: [])] :: [].
Compute (count_ops test3).
Compute (remove_Rz_before_meas test3).

(** Proofs **)

Lemma next_Rz_gate_preserves_structure : forall dim (l : RzQ_ucom_l dim) l1 i n l2,
  next_Rz_gate l = Some (l1, i, n, l2) ->
  l = l1 ++ [Rz i n] ++ l2.
Proof.
  intros.
  generalize dependent l1.
  induction l; intros l1 H.
  - inversion H.
  - simpl in H.
    destruct a as [u | u | u]; dependent destruction u.
    all: try (destruct (next_Rz_gate l) eqn:Hnext; 
              try discriminate;
              do 3 destruct p; 
              inversion H; subst;
              rewrite IHl with (l1:=r0); 
              reflexivity).
    inversion H; subst. reflexivity.
Qed.

Lemma remove_Rz_before_meas_sound : forall dim (l : RzQ_com_l dim),
  remove_Rz_before_meas l =l= l.
Proof.
  intros.
  unfold remove_Rz_before_meas. 
  remember (count_ops l) as n; clear Heqn.
  generalize dependent l.
  induction n; try reflexivity.
  intros; simpl.
  destruct l; try reflexivity.
  destruct i; simpl.
  - destruct (next_Rz_gate g) eqn:ng.
    do 3 destruct p.
    destruct (does_not_reference r n0) eqn:dnr.
    destruct (next_measurement l n0) eqn:nm.
    repeat destruct p.
    all: try (rewrite IHn; reflexivity).
    apply next_Rz_gate_preserves_structure in ng.
    specialize (next_measurement_l1_does_not_reference _ _ _ _ _ _ nm) as dnr_c.
    apply next_measurement_preserves_structure in nm.
    rewrite IHn.
    rewrite cons_to_app.
    rewrite (cons_to_app _ l).
    rewrite c_app_congruence.
    2: apply UC_append.
    2: reflexivity.
    rewrite (c_app_congruence [UC g]).
    2: { rewrite ng. 
         rewrite UC_append.
         rewrite c_app_congruence. 
         2: reflexivity. 
         2: apply uc_equiv_l_implies_c_equiv_l; 
            apply does_not_reference_commutes_app1;
            assumption. 
         rewrite c_app_congruence. 
         2: reflexivity. 
         2: apply UC_append. 
         reflexivity. }
    2: reflexivity.
    rewrite nm.
    repeat rewrite <- app_assoc.
    do 2 (apply c_app_congruence; try reflexivity).
    repeat rewrite app_assoc.
    apply c_app_congruence; try reflexivity.
    rewrite (c_app_congruence ([UC [Rz q n0]] ++ l2)).
    2: apply does_not_reference_c_commutes_app1; assumption.
    2: reflexivity.
    rewrite <- app_assoc.
    apply c_app_congruence; try reflexivity.
    simpl.
    symmetry. apply RzQ_Meas.
  - rewrite IHn with (l:=l).
    unfold c_equiv_l, c_equiv; intros.
    apply Meas_cons_congruence; unfold c_eval_l, project_onto; simpl.
    1,2: intros; apply IHn. 
    all: auto with wf_db.
    reflexivity.
Qed.
