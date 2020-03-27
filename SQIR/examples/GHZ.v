Require Import UnitarySem.
Require Import QWIRE.Dirac.

Local Open Scope nat_scope.
Local Open Scope ucom_scope.

Fixpoint GHZ (dim n : nat) : base_ucom dim :=
  match n with
  | 0        => SKIP
  | 1        => H 0
  | S (S n'' as n') => GHZ dim n' ; CNOT n'' n'      
  end.

Local Open Scope R_scope.
Local Open Scope C_scope.

Definition ghz (n : nat) : Matrix (2^n) (1^n) := (* 1^n for consistency with kron_n *)
  match n with 
  | 0 => I 1 
  | S n' => 1/ √2 .* (n ⨂ ∣0⟩) .+ 1/ √2 .* (n ⨂ ∣1⟩)
  end.

Lemma WF_ghz : forall n : nat, WF_Matrix (ghz n).
Proof.
  induction n; simpl; auto with wf_db. 
Qed.

Lemma typed_GHZ : forall dim n, (0 < dim)%nat -> (n <= dim)%nat -> uc_well_typed (GHZ dim n).
Proof.
  intros. induction n.
  - simpl. apply uc_well_typed_ID; assumption.
  - simpl. destruct n. 
    + apply uc_well_typed_H; assumption.
    + apply WT_seq.
      apply IHn; try lia.
      apply uc_well_typed_CNOT; lia.
Qed.      

Theorem GHZ_correct' : forall dim n : nat, 
  (0 < dim)%nat -> (n <= dim)%nat -> uc_eval (GHZ dim n) × dim ⨂ ∣0⟩ = ghz n ⊗ (dim - n) ⨂ ∣0⟩.
Proof.
  intros. induction n.
  - simpl. rewrite denote_SKIP; try assumption. 
    Msimpl. replace (dim - 0)%nat with dim by lia.
    reflexivity.
  - destruct dim; try lia.
    rewrite kron_n_assoc at 1; auto with wf_db.
    destruct n.
    + simpl; autorewrite with eval_db.
      bdestructΩ (0 + 1 <=? S dim). 
      Msimpl_light.
      replace (dim - 0)%nat with dim by lia.
      rewrite kron_mixed_product.
      Msimpl_light.
      apply f_equal2; try reflexivity.
      solve_matrix.
    + replace (uc_eval (GHZ (S dim) (S (S n)))) with (uc_eval (CNOT n (S n)) × uc_eval (GHZ (S dim) (S n))) by easy.
      rewrite <- kron_n_assoc.
      2: auto with wf_db.
      rewrite Mmult_assoc.
      setoid_rewrite IHn. 
      2: lia.
      (* annoyingly manual *)
      replace (S dim - S (S n))%nat with (dim - (S n))%nat by lia.
      replace (S dim - S n)%nat with (S (dim - (S n)))%nat by lia.
      rewrite kron_n_assoc.
      2: auto with wf_db.
      unfold ghz. 
      autorewrite with eval_db.
      clear IHn.
      bdestruct_all.
      clear H H1 H2. 
      apply Peano.le_S_n in H0.
      replace (S n - n - 1)%nat with O by lia.      
      replace (S dim - (n + (1 + 0 + 1)))%nat with (dim - S n)%nat by lia.
      simpl I.
      repeat rewrite kron_1_r.
      simpl kron_n.
      replace (2 ^ S (dim - S n))%nat with (2 * 2 ^ (dim - S n))%nat by unify_pows_two.
      replace (1 ^ S (dim - S n))%nat with (1 * 1 ^ (dim - S n))%nat by (repeat rewrite Nat.pow_1_l; lia).
      rewrite <- (kron_assoc _ (∣0⟩)).
      rewrite kron_plus_distr_l.
      rewrite (kron_plus_distr_r _ _ _ _ _ _ (∣0⟩)). 
      repeat rewrite Mscale_kron_dist_l.
      replace (2 ^ S n)%nat with (2 ^ n * 2)%nat by unify_pows_two.
      replace (1 ^ S n)%nat with (1 ^ n * 1)%nat by (repeat rewrite Nat.pow_1_l; lia).
      rewrite 2 (kron_assoc _ _ (∣0⟩)).
      replace (2 ^ (1 + 0 + 1))%nat with (2 * 2)%nat by reflexivity. 
      replace (2 ^ n * 2 * 2)%nat with (2 ^ n * (2 * 2))%nat by lia.
      replace (1 ^ n * 1 * 1)%nat with (1 ^ n * (1 * 1))%nat by lia.
      replace (2 ^ S dim)%nat with (2 ^ n * (2 * 2) * 2 ^ (dim - S n))%nat.
      2: simpl; unify_pows_two.
      replace (2 * 2 ^ 0)%nat with 2%nat by reflexivity.
      replace (1 ^ S dim)%nat with (1 ^ n * (1 * 1) * 1 ^ (dim - S n))%nat.
      2: repeat rewrite Nat.pow_1_l; reflexivity.
      rewrite kron_mixed_product.
      rewrite Mmult_plus_distr_r.
      repeat rewrite Mmult_plus_distr_l.
      repeat rewrite Mscale_mult_dist_r.
      repeat rewrite kron_mixed_product.
      repeat rewrite (Mmult_assoc _ (_)†). 
      Qsimpl.
      repeat rewrite <- kron_assoc.
      rewrite Mplus_comm.
      reflexivity.
Qed.

Theorem GHZ_correct : forall n : nat, 
  (0 < n)%nat -> uc_eval (GHZ n n) × n ⨂ ∣0⟩ = ghz n.
Proof.
  intros.
  rewrite GHZ_correct'; try lia.
  replace (n - n)%nat with O by lia.
  simpl.
  rewrite kron_1_r.
  reflexivity.
Qed.
