Require Import Compose.
Require Import QWIRE.Dirac.
Require Import Tactics.

Local Open Scope nat_scope.
Local Open Scope ucom_scope.

Fixpoint GHZ (n : nat) : ucom n :=
  match n with
  | 0    => uskip
  | S n' => (* n = n' + 1 *)
           match n' with 
           | 0     => (* n = 1 *) H 0
           | S n'' => (* n = n'' + 2 *)
                     cast (GHZ n' ; CNOT n'' n') n
           end         
end.

(* Maybe just define as big_kron (repeat n ψ)? *)
Fixpoint nket (n : nat) (ψ : Matrix 2 1) : Matrix (2^n) 1 :=
  match n with
  | 0 => I 1
  | S n' => (nket n' ψ) ⊗ ψ
  end.

Local Open Scope R_scope.
Local Open Scope C_scope.

Definition ghz (n : nat) : Matrix (2^n) 1 :=
  match n with 
  | 0 => I 1 
  | S n' => 1/ √2 .* (nket n ∣0⟩) .+ 1/ √2 .* (nket n ∣1⟩)
  end.

Lemma WF_nket : forall (n : nat)(ψ : Matrix 2 1), WF_Matrix ψ -> WF_Matrix (nket n ψ).
Proof.
  intros n ψ H. induction n; simpl; auto with wf_db. (* <- use this! *)
Qed.

Hint Resolve WF_nket : wf_db.

Lemma WF_ghz : forall n : nat, WF_Matrix (ghz n).
Proof.
  induction n; simpl; auto with wf_db.
Qed.

Lemma typed_GHZ : forall n, uc_well_typed (GHZ n).
Proof.
  intros. induction n.
  - simpl. apply WT_uskip.
  - simpl. destruct n. 
    + apply uc_well_typed_H; lia.
    + apply WT_seq.
      replace (S (S n)) with ((S n) + 1)%nat by lia. 
      apply typed_pad; assumption.
      apply uc_well_typed_CNOT; lia.
Qed.      

(* Move to Dirac.v or somewhere convenient *)
Lemma braket00 : ⟨0∣ × ∣0⟩ = I 1. Proof. solve_matrix. Qed.
Lemma braket01 : ⟨0∣ × ∣1⟩ = Zero. Proof. solve_matrix. Qed.
Lemma braket10 : ⟨1∣ × ∣0⟩ = Zero. Proof. solve_matrix. Qed.
Lemma braket11 : ⟨1∣ × ∣1⟩ = I 1. Proof. solve_matrix. Qed.

Theorem GHZ_correct : forall n : nat, uc_eval (GHZ n) × nket n ∣0⟩ = ghz n.
Proof.
  intros. induction n.
  - simpl. solve_matrix.
  - simpl. destruct n.
    + simpl; autorewrite with eval_db.
      bdestructΩ (0 + 1 <=? 1). 
      solve_matrix.
    + Opaque GHZ. Transparent CNOT. 
      simpl. 
      replace (S (S n)) with ((S n) + 1)%nat by lia.
      rewrite <- pad_dims_r by apply typed_GHZ.
      rewrite Mmult_assoc.
      restore_dims_strong.
      replace (2 ^ n * 2)%nat with (2 ^ S n)%nat by unify_pows_two.
      rewrite kron_mixed_product.
      simpl in *.
      rewrite IHn.
      autorewrite with eval_db. 
      repad.
      replace d with 0%nat in * by lia.
      replace d0 with 0%nat in * by lia. 
      simpl. Msimpl. clear.
      setoid_rewrite cnot_decomposition.
      autorewrite with ket_db.
      restore_dims_strong.
      rewrite 3 kron_assoc. 
      rewrite <- Mscale_plus_distr_r.
      restore_dims_fast.
      repeat rewrite Mscale_mult_dist_r.
      distribute_plus.
      rewrite 2 kron_mixed_product.
      autorewrite with ket_db; auto with wf_db.
(* alternative:
      gridify.
      replace d with 0%nat in * by lia.
      replace d0 with 0%nat in * by lia. 
      simpl. Msimpl. clear.
      restore_dims_fast.
      repeat rewrite kron_mixed_product.
      repeat rewrite Mscale_mult_dist_r.
      repeat rewrite kron_mixed_product.
      Msimpl.
      repeat rewrite Mmult_assoc.
      rewrite braket00, braket01, braket10, braket11.
      Msimpl.
      remove_zero_gates. rewrite Mscale_0_r. remove_zero_gates.
      rewrite Mplus_0_l, Mplus_0_r.
      rewrite Mplus_comm.
      repeat rewrite Mscale_kron_dist_l.
      reflexivity.
*)
Qed.


