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

Lemma U_V_comm : forall {dim} (m n : nat) θ ϕ λ θ' ϕ' λ',
  m <> n ->
  @uc_equiv dim (uapp_R θ ϕ λ m ; uapp_R θ' ϕ' λ' n) (uapp_R θ' ϕ' λ' n ; uapp_R θ ϕ λ m). 
Proof.
  intros.
  unfold uc_equiv; simpl.
  simpl in *.
  autorewrite with eval_db.
  gridify; reflexivity.
Qed.

(* A bit slow, due to six valid subcases *)
Lemma U_CNOT_comm : forall {dim} (q n1 n2 : nat) θ ϕ λ,
  q <> n1 ->
  q <> n2 ->
  @uc_equiv dim (uapp_R θ ϕ λ q ; CNOT n1 n2) (CNOT n1 n2 ; uapp_R θ ϕ λ q). 
Proof.
  intros.
  unfold uc_equiv.
  simpl.
  autorewrite with eval_db.
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
  simpl.
  autorewrite with eval_db.
  gridify; reflexivity.
Qed.  
  
Lemma X_X_id : forall {dim} q, 
  @uc_well_typed dim (X q) -> 
  @uc_equiv dim uskip (X q; X q).
Proof. 
  intros dim q WT. 
  unfold uc_equiv.
  simpl; autorewrite with eval_db. 
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
  simpl; autorewrite with eval_db.
  gridify; reflexivity.
Qed.

Lemma H_H_id : forall {dim} q, 
  @uc_well_typed dim (H q) -> 
  @uc_equiv dim uskip (H q; H q).
Proof. 
  intros dim q WT. 
  unfold uc_equiv.
  simpl; autorewrite with eval_db. 
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
  simpl; autorewrite with eval_db. 
  gridify. 
  rewrite phase_mul.
  rewrite Rplus_comm. 
  reflexivity.
Qed.

Local Transparent Rz.
Lemma Rz_0_add : forall {dim} q, 
  @uc_well_typed dim ((Rz 0) q) -> 
  @uc_equiv dim ((Rz 0) q) uskip.
Proof.
  intros dim q WT. 
  unfold uc_equiv.
  autorewrite with eval_db; simpl. 
  inversion WT; subst.
  bdestruct (q + 1 <=? dim); try lia.
  rewrite phase_0. 
  Msimpl.
  apply f_equal.
  unify_pows_two.
Qed.