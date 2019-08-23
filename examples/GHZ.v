Require Import Compose.
Require Import QWIRE.Dirac.
Require Import Tactics.

(* Importing DJ to use kron_n. We should move kron_n to QWIRE instead. *)
Require Import examples.DeutschJozsa. 

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
  | S n' => 1/ √2 .* (kron_n n ∣0⟩) .+ 1/ √2 .* (kron_n n ∣1⟩)
  end.

(*
Fixpoint nket (n : nat) (ψ : Matrix 2 1) : Matrix (2^n) 1 :=
  match n with
  | 0 => I 1
  | S n' => (nket n' ψ) ⊗ ψ
  end.

Fixpoint kron_n n {m1 m2} (A : Matrix m1 m2) : Matrix (m1^n) (m2^n) :=
  match n with
  | 0    => I 1
  | S n' => kron (kron_n n' A) A
  end.

Lemma WF_kron_n : forall n {m1 m2} (A : Matrix m1 m2),
   WF_Matrix A ->  WF_Matrix (kron_n n A).
Hint Resolve WF_kron_n : wf_db.

Lemma kron_n_assoc :
  forall n {m1 m2} (A : Matrix m1 m2), WF_Matrix A -> kron_n (S n) A = A ⊗ kron_n n A.
*)

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

(* Move to Dirac.v or somewhere convenient *)
Lemma braket00 : ⟨0∣ × ∣0⟩ = I 1. Proof. solve_matrix. Qed.
Lemma braket01 : ⟨0∣ × ∣1⟩ = Zero. Proof. solve_matrix. Qed.
Lemma braket10 : ⟨1∣ × ∣0⟩ = Zero. Proof. solve_matrix. Qed.
Lemma braket11 : ⟨1∣ × ∣1⟩ = I 1. Proof. solve_matrix. Qed.

Theorem GHZ_correct' : forall dim n : nat, 
  (0 < dim)%nat -> (n <= dim)%nat -> uc_eval (GHZ dim n) × kron_n dim ∣0⟩ = ghz n ⊗ kron_n (dim - n) ∣0⟩.
Proof.
  intros. induction n.
  - simpl. rewrite denote_SKIP; try assumption. 
    Msimpl. replace (dim - 0)%nat with dim by lia.
    reflexivity.
  - simpl. 
    destruct dim; try lia. 
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
    + Opaque GHZ. 
      simpl.
      autorewrite with eval_db.
      rewrite <- kron_n_assoc; auto with wf_db.
      repeat rewrite Mmult_assoc.
      setoid_rewrite IHn; try lia.
      replace (S n - n - 1)%nat with O by lia.
      bdestruct_all.
      replace (S dim - (n + (1 + 0 + 1)))%nat with (dim - S n)%nat by lia.
      simpl.
      repeat rewrite kron_1_r. 
      setoid_rewrite cnot_decomposition.
      repeat rewrite kron_plus_distr_r.
      replace (dim - n)%nat with (S (dim - (S n)))%nat by lia.
      rewrite kron_n_assoc; auto with wf_db.
      repeat rewrite Mscale_kron_dist_l.
      
      restore_dims_fast.
      Set Printing All. rewrite <- kron_assoc.
      setoid_rewrite <- kron_assoc. 
      
      rewrite Mscae_plus_dist.
      restore_dims_fast.
      do 2 setoid_rewrite <- kron_assoc.
      Search ((_ .+ _) ⊗ _).

      gridify.
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
      Msimpl_light. rewrite Mscale_0_r. Msimpl_light.
      rewrite Mplus_0_l, Mplus_0_r.
      rewrite Mplus_comm.
      repeat rewrite Mscale_kron_dist_l.
      reflexivity.
*)
Qed.


