Require Import List.
Require Import Composition.

Open Scope ucom.
Local Close Scope C_scope.
Local Close Scope R_scope.

Inductive boolean : nat -> ucom -> Set :=
  | boolean_I : forall u, uc_well_typed 1 u -> u ≡ uskip -> boolean 1 u
  | boolean_X : forall u, uc_well_typed 1 u -> u ≡ (X 0) -> boolean 1 u
  | boolean_U : forall u u1 u2 dim,
                uc_well_typed dim u1 -> boolean dim u1 ->
                uc_well_typed dim u2 -> boolean dim u2 ->
                uc_eval (S dim) u = (uc_eval dim u1 ⊗ ∣0⟩⟨0∣) .+ (uc_eval dim u2 ⊗ ∣1⟩⟨1∣) ->
                uc_well_typed (S dim) u -> boolean (S dim) u.
  
Fixpoint count {dim : nat} {U : ucom} (P : boolean dim U) : C :=
  match P with
  | boolean_I _ _ _ => 0%R
  | boolean_X _ _ _ => 1%R
  | boolean_U u u1 u2 dim WT1 P1 WT2 P2 WT P => (count P1 + count P2)%C
  end.

Fixpoint nket (n : nat) (ψ : Matrix 2 1) : Matrix (2^n) 1 :=
  match n with
  | 0 => I 1
  | S n' => (nket n' ψ) ⊗ ψ
  end.

Notation "∣+⟩" := (/√2 .* ∣0⟩ .+ /√2 .* ∣1⟩)%C.
Notation "∣-⟩" := (/√2 .* ∣0⟩ .+ (-/√2) .* ∣1⟩)%C.

Definition balanced {dim : nat} {U : ucom} (P : boolean dim U) : Prop :=
  dim >= 2 /\ count P = (2%R ^ (dim - 2))%C.

Definition constant {dim : nat} {U : ucom} (P : boolean dim U) : Prop :=
  count P = 0%R \/ count P = (2%R ^ (dim - 1))%C.

Definition accept {dim : nat} {U : ucom} (P : boolean dim U) : Prop :=
    exists ψ : Matrix 2 1, ((ψ ⊗ nket dim ∣+⟩)† × (uc_eval (S dim) U × (∣-⟩ ⊗ nket dim ∣+⟩))) 0 0 = 1%R. 

Definition reject {dim : nat} {U : ucom} (P : boolean dim U) : Prop :=
    forall ψ : Matrix 2 1, ((ψ ⊗ nket dim ∣+⟩)† × (uc_eval (S dim) U × (∣-⟩ ⊗ nket dim ∣+⟩))) 0 0 = 0%R. 
 
Lemma deutsch_jozsa_count :
  forall {dim : nat} {U : ucom} (P : boolean dim U) (ψ : Matrix 2 1),
    (ψ ⊗ nket dim ∣+⟩)† × (uc_eval (S dim) U × (∣-⟩ ⊗ nket dim ∣+⟩)) = (1%R - 2%R * count P * /2%R ^ (dim - 1))%C .* (ψ† × ∣-⟩).
Proof.
  intros.
  remember ∣+⟩ as ψp. remember ∣-⟩ as ψm.
  induction P.
  - simpl. rewrite u1. simpl. 
    rewrite Mmult_1_l by (rewrite Heqψp; rewrite Heqψm; auto with wf_db).
    autorewrite with C_db. 
    rewrite kron_1_l by (rewrite Heqψp; auto with wf_db).
    rewrite (@kron_adjoint 2 1 2 1 _ _).
    rewrite (@kron_mixed_product 1 2 1 1 2 1 _ _ _ _).
    replace (ψp† × ψp) with (I 1) by (rewrite Heqψp; solve_matrix).
    rewrite kron_1_r. symmetry. 
    apply Mscale_1_l.
  - simpl. rewrite u1. unfold uc_eval. simpl. unfold ueval1, pad. simpl.
    rewrite kron_1_l by (rewrite Heqψp; auto with wf_db).
    rewrite kron_1_l by (auto with wf_db).
    autorewrite with C_db.
    rewrite (@kron_mixed_product 2 2 1 2 2 1 _ _ _ _).
    rewrite Mmult_1_l by (rewrite Heqψp; auto with wf_db).
    replace (σx × ψm) with ((-1)%R .* ψm) by (rewrite Heqψm; solve_matrix).
    rewrite Mscale_kron_dist_l. rewrite Mscale_mult_dist_r.
    rewrite (@kron_adjoint 2 1 2 1 _ _).
    rewrite (@kron_mixed_product 1 2 1 1 2 1 _ _ _ _).
    replace (ψp† × ψp) with (I 1) by (rewrite Heqψp; solve_matrix).
    rewrite kron_1_r.
    apply f_equal2. lca. reflexivity.
  - destruct dim. inversion P1.
    replace (nket (S dim) ψp) with (nket dim ψp ⊗ ψp) in * by reflexivity.
    replace (nket (S (S dim)) ψp) with (nket (S dim) ψp ⊗ ψp) by reflexivity.
    replace (S (S dim)) with (S dim + 1) in * by lia.
    replace (S (S (S dim))) with (S (S dim) + 1) by lia.
    replace (2 ^ (S dim + 1)) with (2 * 2 ^ dim * 2) in * by unify_pows_two.
    replace (2 ^ (S (S dim) + 1)) with (2 * 2 ^ (S dim) * 2) by unify_pows_two.
    replace (2 ^ S dim) with (2 ^ dim * 2) in IHP1 by unify_pows_two.
    replace (2 ^ S dim) with (2 ^ dim * 2) in IHP2 by unify_pows_two.
    replace (2 ^ S (S dim)) with (2 ^ (S dim) * 2) by unify_pows_two.
    repeat rewrite <- (@kron_assoc 2 1 (2 ^ dim) 1 2 1 _ _ _) in IHP1.
    repeat rewrite <- (@kron_assoc 2 1 (2 ^ dim) 1 2 1 _ _ _) in IHP2.
    repeat rewrite <- (@kron_assoc 2 1 (2 ^ (S dim)) 1 2 1 _ _ _).
    rewrite <- pad_dims_r in * by assumption.
    replace (2 ^ 1) with 2 in * by (simpl; reflexivity).
    rewrite kron_mixed_product in IHP1.
    rewrite kron_mixed_product in IHP2.
    rewrite kron_mixed_product.
    rewrite mult_assoc in *.
    rewrite (@kron_adjoint (2 * 2 ^ dim) 1 2 1 _ _) in IHP1.
    rewrite (@kron_adjoint (2 * 2 ^ dim) 1 2 1 _ _) in IHP2.
    rewrite (@kron_adjoint (2 * 2 ^ (S dim)) 1 2 1 _ _).
    rewrite kron_mixed_product in IHP1.
    rewrite kron_mixed_product in IHP2.
    rewrite kron_mixed_product.
    rewrite Mmult_1_l in * by (rewrite Heqψp; auto with wf_db).
    replace ((ψp) † × ψp) with (I 1) in * by (rewrite Heqψp; solve_matrix).
    rewrite kron_1_r in *.
    replace (nket (S dim) ψp) with (nket dim ψp ⊗ ψp) by reflexivity.
    replace (2 ^ S dim) with (2 ^ dim * 2) by unify_pows_two.
    repeat rewrite <- (@kron_assoc 2 1 (2 ^ dim) 1 2 1 _ _ _).
    replace (count (boolean_U u u1 u2 (S dim) u0 P1 u3 P2 e u4)) with (count P1 + count P2)%C by reflexivity.
    rewrite e.
    replace (2 ^ S dim) with (2 * 2 ^ dim) by unify_pows_two.
    rewrite mult_assoc.
    rewrite Mmult_plus_distr_r.
    rewrite (@kron_adjoint (2 * 2 ^ dim) 1 2 1 _ _).
    rewrite Mmult_plus_distr_l.
    repeat rewrite (@kron_mixed_product (2 * 2 ^ dim) (2 * 2 ^ dim) 1 2 2 1 _ _ _ _).
    repeat rewrite (@kron_mixed_product 1 (2 * 2 ^ dim) 1 1 2 1 _ _ _ _).
    replace ((ψp) † × (∣0⟩⟨0∣ × ψp)) with ((1/2)%R .* I 1) by (rewrite Heqψp; solve_matrix).
    replace ((ψp) † × (∣1⟩⟨1∣ × ψp)) with ((1/2)%R .* I 1) by (rewrite Heqψp; solve_matrix).
    repeat rewrite Mscale_kron_dist_r.
    repeat rewrite kron_1_r.
    rewrite <- Mscale_plus_distr_r.
    replace (S dim - 1) with dim in * by lia.
    replace (S (S dim) - 1) with (S dim) by lia.
    rewrite IHP1. rewrite IHP2.
    rewrite <- Mscale_plus_distr_l.
    rewrite Mscale_assoc.
    apply f_equal2. simpl.
    rewrite Cinv_mult_distr. lca. 
    apply C0_fst. simpl. lra.
    apply Cpow_nonzero. lra.
    reflexivity.
Qed.

Theorem deutsch_jozsa_constant_correct :
  forall (dim : nat) (U : ucom) (P : boolean dim U), constant P -> accept P.
Proof.
  intros. 
  unfold accept. destruct H.
  - exists ∣-⟩. rewrite (deutsch_jozsa_count P _). rewrite H. 
    destruct dim. inversion P.
    replace (S dim - 1) with dim in * by lia.
    autorewrite with C_db. rewrite Mscale_1_l. 
    replace (∣-⟩† × ∣-⟩) with (I 1) by solve_matrix.
    unfold I. simpl. reflexivity.
  - exists ((-1)%R .* ∣-⟩). rewrite (deutsch_jozsa_count P _). rewrite H.
    destruct dim. inversion P.
    replace (S dim - 1) with dim in * by lia.
    autorewrite with C_db. 
    rewrite <- Cmult_assoc. rewrite Cinv_r by (apply Cpow_nonzero; lra).
    rewrite Cmult_1_r.
    rewrite <- Cminus_unfold.
    replace (((-1)%R .* ∣-⟩)† × ∣-⟩) with ((-1)%R .* I 1).
    unfold I, scale. simpl. lca.
    solve_matrix. 
    rewrite Cconj_mult_distr. 
    rewrite Cconj_rad2.
    rewrite Cconj_R.
    group_radicals. lca.
Qed.

Theorem deutsch_jozsa_balanced_correct :
  forall (dim : nat) (U : ucom) (P : boolean dim U), balanced P -> reject P.
Proof.
  intros. unfold reject. intros. rewrite (deutsch_jozsa_count P _).
  destruct dim. inversion P.
  replace (S dim - 1) with dim in * by lia.
  unfold balanced in H. inversion H.
  destruct dim. inversion H0. inversion H3.
  replace (S (S dim) - 2) with dim in * by lia.
  rewrite H1. simpl. rewrite Cinv_r.
  autorewrite with C_db.
  rewrite Mscale_0_l. unfold Zero. reflexivity.
  Search Cmult eq.
  replace (2%R * 2%R ^ dim)%C with (2%R ^ S dim)%C.
  apply Cpow_nonzero. lra.
  simpl. reflexivity.
Qed.  


