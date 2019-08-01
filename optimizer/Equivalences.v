Require Export UnitarySem.
Require Import Tactics.
Require Import Phase.

Local Open Scope ucom_scope.
Local Close Scope C_scope.
Local Close Scope R_scope.

(** Example equivalences of unitary circuits. **)

Lemma uskip_id_l : forall {dim} (c : ucom dim),
   (uskip ; c) ≡ c.
Proof.
  intros dim c. 
  unfold uc_equiv.
  simpl; Msimpl; reflexivity.
Qed.

Lemma uskip_id_r : forall {dim} (c : ucom dim),
   (c ; uskip) ≡ c.
Proof.
  intros dim c.
  unfold uc_equiv.
  simpl; Msimpl; reflexivity.
Qed.

Lemma X_X_id : forall {dim} q, 
  @uc_well_typed dim (X q) -> 
  @uc_equiv dim uskip (X q; X q).
Proof. 
  intros dim q WT. 
  unfold uc_equiv.
  simpl; unfold ueval1, pad. 
  inversion WT; subst.
  gridify.
  replace (σx × σx) with (I 2) by solve_matrix.
  repeat rewrite id_kron.
  reflexivity.
Qed.

Lemma X_CNOT_comm : forall {dim} c t, 
  @uc_equiv dim (X t; CNOT c t) (CNOT c t ; X t).
Proof.
  intros dim c t.
  unfold uc_equiv.
  simpl; unfold ueval1, ueval_cnot, pad.
  gridify; reflexivity.
Qed.

Lemma H_H_id : forall {dim} q, 
  @uc_well_typed dim (H q) -> 
  @uc_equiv dim uskip (H q; H q).
Proof. 
  intros dim q WT. 
  unfold uc_equiv.
  simpl; unfold ueval1, pad. 
  inversion WT; subst. 
  gridify.
  replace (hadamard × hadamard) with (I 2) by solve_matrix.
  repeat rewrite id_kron.
  reflexivity.
Qed.

Lemma Rz_Rz_add : forall {dim} q θ θ', 
   @uc_equiv dim ((Rz θ) q; (Rz θ') q) ((Rz (θ + θ')) q).
Proof.
  intros.
  unfold uc_equiv.
  simpl; unfold ueval1, pad. 
  gridify. 
  rewrite phase_mul.
  rewrite Rplus_comm. 
  reflexivity.
Qed.

Lemma Rz_0_add : forall {dim} q, 
  @uc_well_typed dim ((Rz 0) q) -> 
  @uc_equiv dim ((Rz 0) q) uskip.
Proof.
  intros dim q WT. 
  unfold uc_equiv.
  simpl; unfold ueval1, pad, ueval_unitary1. 
  inversion WT; subst. 
  bdestruct (q + 1 <=? dim); try lia.
  rewrite phase_0. 
  repeat rewrite id_kron.
  unify_matrices.
Qed.

Lemma U_V_comm : forall {dim} (m n : nat) (U V : Unitary 1),
  m <> n ->
  @uc_equiv dim (uapp1 U m ; uapp1 V n) (uapp1 V n ; uapp1 U m). 
Proof.
  intros dim m n U V NE.
  unfold uc_equiv; simpl.
  simpl in *.
  unfold ueval1, pad.
  gridify; reflexivity.
Qed.

(* A bit slow, due to six valid subcases *)
Lemma U_CNOT_comm : forall {dim} (q n1 n2 : nat) (U : Unitary 1),
  q <> n1 ->
  q <> n2 ->
  @uc_equiv dim (uapp1 U q ; CNOT n1 n2) (CNOT n1 n2 ; uapp1 U q). 
Proof.
  intros dim q n1 n2 U NE1 NE2.
  unfold uc_equiv.
  simpl.
  unfold ueval_cnot.
  unfold ueval1, pad.
  gridify; reflexivity.
Qed.

(* 24 valid subcases, excruciatingly slow *)
Lemma CNOT_CNOT_comm : forall {dim} (n1 n2 n1' n2' : nat),
  n1' <> n1 ->
  n1' <> n2 ->
  n2' <> n1 ->
  n2' <> n2 ->
  @uc_equiv dim (CNOT n1 n2 ; CNOT n1' n2') (CNOT n1' n2' ; CNOT n1 n2). 
Proof.
  intros.
  unfold uc_equiv.
  simpl; unfold ueval_cnot, pad.
  gridify; reflexivity.
Qed.  
  
