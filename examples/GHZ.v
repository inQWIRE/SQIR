Require Import Compose.
Require Import QWIRE.Dirac.

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
    + apply WT_app1; lia.
    + apply WT_seq.
      replace (S (S n)) with ((S n) + 1)%nat by lia. 
      apply typed_pad; assumption.
      apply WT_app2; lia.
Qed.      

Theorem GHZ_correct : forall n : nat, uc_eval (GHZ n) × nket n ∣0⟩ = ghz n.
Proof.
  intros. induction n.
  - simpl. solve_matrix.
  - simpl. destruct n.
    + simpl. unfold ueval1, pad. 
      bdestructΩ (0 + 1 <=? 1). 
      solve_matrix.
    + simpl uc_eval. 
      replace (S (S n)) with ((S n) + 1)%nat by lia.
      rewrite <- pad_dims_r by (apply typed_GHZ).
      rewrite Mmult_assoc.
      restore_dims_strong.
      rewrite kron_mixed_product.
      simpl in *.
      rewrite IHn.
      unfold ueval_cnot, pad. 
      bdestruct (n <? S n); try lia.
      bdestruct (n + (1 + (S n - n - 1) + 1) <=? S (n + 1)); try lia.
      clear.
      replace (S n - n)%nat with 1%nat by lia.
      simpl.
      replace (n + 1 - 1 - n)%nat with O by lia.
      simpl.
      Msimpl.
      setoid_rewrite cnot_decomposition.
      autorewrite with ket_db.
      restore_dims_strong.
      replace ((2 ^ n) + 0)%nat with (2 ^ n)%nat by lia.
      replace (((2 ^ n) + (2 ^ n)) * 2)%nat with ((2 ^ n) * (2 * 2))%nat by lia. 
      rewrite Mmult_plus_distr_l. 
      autorewrite with ket_db.
      rewrite 3 kron_assoc. 
      rewrite 2 kron_mixed_product.
      autorewrite with ket_db; auto with wf_db.
      restore_dims.  
      rewrite CNOT00_spec.
      rewrite CNOT10_spec.
      reflexivity.
Qed.


