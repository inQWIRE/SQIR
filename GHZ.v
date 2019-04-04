Require Export SQIMP.
Require Import UnitarySem.
Require Import Dirac.

Close Scope R_scope.
Open Scope nat_scope.

Fixpoint GHZ (n : nat) : ucom :=
  match n with
  | 0 => uskip
  | 1 => H 0
  | S n' => GHZ n'; CNOT (n'-1) n'
end.

(* Maybe just define as big_kron (repeat n ψ)? *)
Fixpoint nket (n : nat) (ψ : Matrix 2 1) : Matrix (2^n) 1 :=
  match n with
  | 0 => I 1
  | S n' => (nket n' ψ) ⊗ ψ
  end.

Open Scope R_scope.

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

Lemma typed_GHZ : forall n : nat, uc_well_typed n (GHZ n).
Proof.
  intros. induction n as [| [| n']].
  - simpl. apply WT_uskip.
  - simpl. apply WT_app. easy.
    unfold in_bounds. intros. inversion H. rewrite H0. lia.
    inversion H0. constructor. intro. inversion H. constructor.
  - remember (S n') as k. simpl. destruct k. 
    + apply WT_app. easy. easy. constructor. easy. constructor.
    + apply WT_seq. apply (typed_pad _ 1 _). assumption.
      simpl. rewrite <- minus_n_O.
      apply WT_app. 
      * easy. 
      * unfold in_bounds. intros. inversion H. rewrite H0. lia.
        inversion H0. rewrite H1. lia. inversion H1. 
      * constructor. intro. inversion H. lia.
        inversion H0. constructor. intro. inversion H. constructor.
Qed.      

Theorem ghz_correct : forall n : nat, uc_eval n (GHZ n) × nket n ∣0⟩ = ghz n.
Proof.
  intros.
  induction n as [| [| n']].
  - simpl. solve_matrix.
  - simpl. solve_matrix. unfold ueval1. unfold pad. simpl.
    rewrite kron_1_r. rewrite kron_1_l. reflexivity. auto with wf_db.
  - remember (S n') as k.
    simpl. destruct k. inversion Heqk.
    remember (S k) as m.
    simpl.
    replace (uc_eval (S m) (GHZ m)) with (uc_eval (m + 1) (GHZ m)) by (rewrite plus_comm; reflexivity).
    rewrite <- pad_dims by (apply typed_GHZ).
    rewrite Mmult_assoc.
    restore_dims_strong.
    rewrite kron_mixed_product.
    rewrite IHn.
    unfold ueval_cnot. simpl.
    bdestructΩ (m - 1 <? m).
    unfold pad.
    bdestructΩ (m - 1 + S (m - (m - 1) - 1 + 1) <=? S m).
    clear H H0.
    replace (m - (m - 1))%nat with 1%nat by lia. simpl.
    rewrite Nat.sub_diag. simpl.
    Msimpl.
    setoid_rewrite cnot_decomposition.
    unfold ghz.
    rewrite Heqm. simpl. rewrite Nat.sub_0_r.
    autorewrite with ket_db.
    restore_dims_strong.
    rewrite (Mmult_plus_distr_l _ _ _  (I (2 ^ k) ⊗ cnot) (1 / √ 2 .* (nket k ∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩))
      (1 / √ 2 .* (nket k ∣1⟩ ⊗ ∣1⟩ ⊗ ∣0⟩))).
    restore_dims_strong.
    rewrite 2 kron_assoc. restore_dims.
    restore_dims_strong.
    setoid_rewrite (Mscale_mult_dist_r _ _ _ (1 / √ 2) (I (2 ^ k) ⊗ cnot) (nket k ∣0⟩ ⊗ (∣0⟩ ⊗ ∣0⟩))).
    setoid_rewrite (Mscale_mult_dist_r _ _ _ (1 / √ 2) (I (2 ^ k) ⊗ cnot) (nket k ∣1⟩ ⊗ (∣1⟩ ⊗ ∣0⟩))).
    rewrite 2 kron_mixed_product.
    replace (∣0⟩) with ∣ 0 ⟩ by reflexivity. 
    replace (∣1⟩) with ∣ 1 ⟩ by reflexivity. 
    rewrite CNOT00_spec, CNOT10_spec.
    Msimpl.
    rewrite kron_assoc.
    reflexivity.
Qed.


