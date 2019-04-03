Require Export SQIMP.
Require Import UnitarySem.

Fixpoint ghzc (n : nat) : ucom :=
  match n with
  | 0 => uskip
  | 1 => H 0
  | S n' => ghzc n'; CNOT (n'-1) n'
end.

Fixpoint nket (n : nat) (ψ : Matrix 2 1) : Matrix (2^n) 1 :=
  match n with
  | 0 => I 1
  | S n' => (nket n' ψ) ⊗ ψ
  end.

Open Scope R_scope.

Definition ghzs (n : nat) : Matrix (2^n) 1 :=
  match n with 
  | 0 => I 1 
  | S n' => 1/ √2 .* (nket n ∣0⟩) .+ 1/ √2 .* (nket n ∣1⟩)
end.

(* Move somewhere. *)
Ltac prove_wf :=
  repeat match goal with
         | |- context [ WF_Matrix _ _ (?a .+ ?b) ] => apply WF_plus
         | |- context [ WF_Matrix _ _ (?a × ?b) ] => apply WF_mult
         | |- context [ WF_Matrix _ _ (?a ⊗ ?b) ] => apply WF_kron
         | |- context [ WF_Matrix _ _ (?a .* ?b) ] => apply WF_scale
         | |- context [ WF_Matrix _ _ (?a)† ] => apply WF_adjoint
         | |- context [ WF_Matrix _ _ (I ?n) ] => apply WF_I
         | |- context [ WF_Matrix _ _ ∣0⟩ ] => apply WF_qubit0
         | |- context [ WF_Matrix _ _ ∣1⟩ ] => apply WF_qubit1
         | |- context [ WF_Matrix _ _ σx ] => apply WF_σx
         | |- context [ WF_Matrix _ _ (outer_product ?u ?v) ] => apply WF_outer_product
         end; auto.

Lemma WF_nket : forall (n : nat)(ψ : Matrix 2 1), WF_Matrix _ _ ψ -> WF_Matrix _ _ (nket n ψ).
Proof.
  intros n ψ H. induction n; simpl; prove_wf. unify_pows_two.
Qed.

Lemma WF_ghzs : forall n : nat, WF_Matrix _ _ (ghzs n).
Proof.
  induction n; simpl; prove_wf; unify_pows_two; apply WF_nket; prove_wf.
Qed.

Lemma typed_ghz : forall n : nat, uc_well_typed n (ghzc n).
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

Theorem ghz_correct : forall n : nat, uc_eval n (ghzc n) × nket n ∣0⟩ = ghzs n.
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
    replace (uc_eval (S m)%nat (ghzc m)) with (uc_eval (m + 1)%nat (ghzc m)) by (rewrite plus_comm; reflexivity).
    rewrite <- pad_dims by (apply typed_ghz).
    rewrite Mmult_assoc.
    replace (2 ^ 1)%nat with 2%nat by (simpl; reflexivity).
    replace (2 ^ S m)%nat with (2 ^ m * 2)%nat by unify_pows_two.
    replace (2 ^ m + (2 ^ m + 0))%nat with (2 ^ m * 2)%nat by lia.
    replace 1%nat with (1 * 1)%nat by lia.
    rewrite kron_mixed_product. simpl.
    rewrite IHn.
    rewrite Mmult_1_l by prove_wf.
    unfold ueval_cnot. simpl.
    replace (m-1 <? m) with true.
    2 : { symmetry. rewrite Nat.ltb_lt.
          rewrite Heqk. simpl. rewrite <- minus_n_O. lia. }
    replace (m - (m - 1))%nat with 1%nat by lia. 
    simpl.
    unfold pad.
    replace (m-1 + 2 <=? S m)%nat with true.
    2 : { rewrite plus_comm. simpl.
          destruct m. inversion Heqm.
          simpl. rewrite <- minus_n_O.
          symmetry. apply Nat.leb_refl. }
    simpl.
    rewrite Nat.sub_diag. simpl.
    repeat rewrite kron_1_r.
    unfold ghzs.
    rewrite Heqm.
    simpl.
    rewrite kron_plus_distr_r.
    replace (k-0)%nat with k by lia.
    replace (2^k + (2^k+0))%nat with (2 ^ k * 2)%nat by unify_pows_two. 
    remember (nket k ∣0⟩) as ψ0. remember (nket k ∣1⟩) as ψ1.
    replace 4%nat with (2*2)%nat by lia.
    rewrite Mmult_plus_distr_l.
    repeat rewrite <- kron_assoc.
    repeat rewrite Mscale_kron_dist_l.
    repeat rewrite Mscale_mult_dist_r.
    repeat apply f_equal2; try reflexivity.
    + show_dimensions.
      replace (kron' (2 ^ k * 2) 1 2 1 (kron' (2 ^ k) 1 2 1 ψ0 ∣0⟩) ∣0⟩) with (ψ0 ⊗ (∣0⟩ ⊗ ∣0⟩)).
      hide_dimensions.
      replace ((2 ^ k) * 2 * 2)%nat with ((2 ^ k) * (2 * 2))%nat by lia.
      rewrite kron_mixed_product.
      apply f_equal2.
      * rewrite Mmult_1_l. reflexivity. rewrite Heqψ0. apply WF_nket. prove_wf.
      * solve_matrix.
      * rewrite <- kron_assoc. simpl. reflexivity.
    + show_dimensions.
      replace (kron' (2 ^ k * 2) 1 2 1 (kron' (2 ^ k) 1 2 1 ψ1 ∣1⟩) ∣0⟩) with (ψ1 ⊗ (∣1⟩ ⊗ ∣0⟩)).
      replace (kron' (2 ^ k * 2) 1 2 1 (kron' (2 ^ k) 1 2 1 ψ1 ∣1⟩) ∣1⟩) with (ψ1 ⊗ (∣1⟩ ⊗ ∣1⟩)).
      hide_dimensions.
      replace ((2 ^ k) * 2 * 2)%nat with ((2 ^ k) * (2 * 2))%nat by lia.
      rewrite kron_mixed_product.
      apply f_equal2.
      * rewrite Mmult_1_l. reflexivity. rewrite Heqψ1. apply WF_nket. prove_wf.
      * solve_matrix.
      * rewrite <- kron_assoc. simpl. reflexivity.
      * rewrite <- kron_assoc. simpl. reflexivity.
Qed.


