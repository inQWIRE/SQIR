Require Import List.
Require Import Composition.

Open Scope ucom.
Local Close Scope C_scope.
Local Close Scope R_scope.

Inductive boolean : nat -> ucom -> Set :=
  | boolean_I : forall u, u ≡ uskip -> boolean 1 u
  | boolean_X : forall u, u ≡ X 0 -> boolean 1 u
  | boolean_U : forall u u1 u2 dim,
                boolean dim u1 -> boolean dim u2 ->
                uc_eval (S dim) u = (uc_eval dim u1 ⊗ ∣0⟩⟨0∣) .+ (uc_eval dim u2 ⊗ ∣1⟩⟨1∣) ->
                boolean (S dim) u.

Lemma boolean_WT : forall dim u, boolean dim u -> uc_well_typed dim u.
Proof.
  intros dim u H.
  apply WT_if_nonzero.
  induction H.
  - rewrite u0.
    simpl. intros F.
    apply (f_equal2_inv 0 0) in F.
    contradict F; nonzero.
  - rewrite u0.
    simpl. intros F.
    apply (f_equal2_inv 0 1) in F.
    contradict F; nonzero.
  - rewrite e. clear -IHboolean1.
    intros F.
    assert (Z1 : forall i j, i mod 2 = 0 -> j mod 2 = 0 -> (uc_eval dim u2 ⊗ ∣1⟩⟨1∣) i j = C0).
    { clear. intros. unfold kron. rewrite H, H0.  replace (∣1⟩⟨1∣ 0 0) with C0 by solve_matrix. lca. }
    assert (Z0 : forall i j, i mod 2 = 0 -> j mod 2 = 0 -> (uc_eval dim u1 ⊗ ∣0⟩⟨0∣) i j = C0).
    { intros.
      apply (f_equal2_inv i j) in F.      
      unfold Mplus in F. rewrite Z1 in F; trivial.
      rewrite Cplus_0_r in F.
      apply F.
    }
    contradict IHboolean1.
    prep_matrix_equality.
    specialize (Z0 (x*2) (y*2)).
    revert Z0. clear.
    unfold kron.
    rewrite 2 Nat.div_mul by lia.
    rewrite 2 Nat.mod_mul by lia.
    replace (∣0⟩⟨0∣ 0 0) with C1 by solve_matrix.
    rewrite Cmult_1_r.
    unfold Zero; simpl.
    auto.
Qed.          
  
Fixpoint count {dim : nat} {U : ucom} (P : boolean dim U) : C :=
  match P with
  | boolean_I _ _ => 0%R
  | boolean_X _ _ => 1%R
  | boolean_U _ _ _ _ P1 P2 _ => (count P1 + count P2)%C
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

Definition accept' {dim : nat} {U : ucom} (P : boolean dim U) : Prop :=
    exists ψ : Matrix 2 1, ((ψ ⊗ nket dim ∣+⟩)† × (uc_eval (S dim) U × (∣-⟩ ⊗ nket dim ∣+⟩))) 0 0 = 1%R. 

Definition reject' {dim : nat} {U : ucom} (P : boolean dim U) : Prop :=
    forall ψ : Matrix 2 1, ((ψ ⊗ nket dim ∣+⟩)† × (uc_eval (S dim) U × (∣-⟩ ⊗ nket dim ∣+⟩))) 0 0 = 0%R. 
 
Lemma deutsch_jozsa_count :
  forall {dim : nat} {U : ucom} (P : boolean dim U) (ψ : Matrix 2 1),
    (ψ ⊗ nket dim ∣+⟩)† × (uc_eval (S dim) U × (∣-⟩ ⊗ nket dim ∣+⟩)) = (1%R - 2%R * count P * /2%R ^ (dim - 1))%C .* (ψ† × ∣-⟩).
Proof.
  intros.
  remember ∣+⟩ as ψp. remember ∣-⟩ as ψm.
  specialize (boolean_WT _ _ P) as WTu.
  induction P.
  - simpl. rewrite u0. simpl.
    rewrite Mmult_1_l by (rewrite Heqψp; rewrite Heqψm; auto with wf_db).
    autorewrite with C_db. 
    rewrite kron_1_l by (rewrite Heqψp; auto with wf_db).
    rewrite (@kron_adjoint 2 1 2 1 _ _).
    rewrite (@kron_mixed_product 1 2 1 1 2 1 _ _ _ _).
    replace (ψp† × ψp) with (I 1) by (rewrite Heqψp; solve_matrix).
    rewrite kron_1_r. symmetry. 
    apply Mscale_1_l.
  - simpl. rewrite u0. unfold uc_eval. simpl. unfold ueval1, pad. simpl.
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
    specialize (boolean_WT _ _ P1) as WTu1.
    specialize (boolean_WT _ _ P2) as WTu2.
    rewrite <- pad_dims_r in *;
      try replace (S (S dim)) with (S dim + 1) by lia;
      try assumption.
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
    replace (count (boolean_U u u1 u2 (S dim) P1 P2 e)) with (count P1 + count P2)%C by reflexivity.
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
    rewrite (IHP1 WTu1). rewrite (IHP2 WTu2).
    rewrite <- Mscale_plus_distr_l.
    rewrite Mscale_assoc.
    apply f_equal2. simpl.
    rewrite Cinv_mult_distr. lca. 
    apply C0_fst. simpl. lra.
    apply Cpow_nonzero. lra.
    reflexivity.
Qed.

Theorem deutsch_jozsa_constant_correct' :
  forall (dim : nat) (U : ucom) (P : boolean dim U), constant P -> accept' P.
Proof.
  intros. 
  unfold accept'. destruct H.
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

Theorem deutsch_jozsa_balanced_correct' :
  forall (dim : nat) (U : ucom) (P : boolean dim U), balanced P -> reject' P.
Proof.
  intros. unfold reject'. intros. rewrite (deutsch_jozsa_count P _).
  destruct dim. inversion P.
  replace (S dim - 1) with dim in * by lia.
  unfold balanced in H. inversion H.
  destruct dim. inversion H0. inversion H3.
  replace (S (S dim) - 2) with dim in * by lia.
  rewrite H1. simpl. rewrite Cinv_r.
  autorewrite with C_db.
  rewrite Mscale_0_l. unfold Zero. reflexivity.
  replace (2%R * 2%R ^ dim)%C with (2%R ^ S dim)%C.
  apply Cpow_nonzero. lra.
  simpl. reflexivity.
Qed.  

Fixpoint cpar (n : nat) (u : nat -> ucom) : ucom :=
  match n with
  | 0 => uskip
  | S n' => cpar n' u ; u n'
  end.

Lemma well_typed_cpar_H : forall (n : nat), uc_well_typed n (cpar n H).
Proof.
  intros. induction n.
  - simpl. apply WT_uskip.
  - simpl. apply WT_seq.
    apply (typed_pad _ 1 _). assumption.
    apply WT_app. auto. 
    unfold in_bounds. intros. inversion H. rewrite <- H0. 
    lia. inversion H0. 
    constructor. intro. inversion H. constructor.
Qed.

Lemma WF_cpar_H : 
  forall (n : nat), WF_Matrix (uc_eval n (cpar n H)).
Proof.
  intros. induction n.
  - simpl. auto with wf_db.
  - simpl. unfold ueval1, pad. simpl.
    bdestructΩ (n + 1 <=? S n).
    apply WF_mult. auto with wf_db.
    replace (S n) with (n + 1) by lia.
    rewrite <- pad_dims_r.
    simpl. apply WF_kron; auto with wf_db.
    apply well_typed_cpar_H.
Qed.

Lemma WF_nket : forall (n : nat)(ψ : Matrix 2 1), WF_Matrix ψ -> WF_Matrix (nket n ψ).
Proof.
  intros n ψ H. induction n; simpl; auto with wf_db.
Qed.

Lemma cpar_correct_H : 
  forall (n : nat) (ψ : Matrix 2 1) (WF : WF_Matrix ψ), (uc_eval (S n) (cpar (S n) H)) × (ψ ⊗ nket n ∣0⟩) = (hadamard × ψ) ⊗ nket n ∣+⟩.
Proof.
  intros.
  remember ∣+⟩ as ψp.
  induction n.
  - simpl. unfold ueval1, pad. simpl. 
    rewrite kron_1_l; auto with wf_db. 
    repeat rewrite kron_1_r; auto with wf_db.
    rewrite Mmult_1_r; auto with wf_db.
  - replace (cpar (S (S n)) H) with (cpar (S n) H ; H (S n)) by reflexivity.
    replace (nket (S n) ψp) with (nket n ψp ⊗ ψp) by reflexivity.
    replace (nket (S n) ∣0⟩) with (nket n ∣0⟩ ⊗ ∣0⟩) by reflexivity.
    repeat replace (2 ^ S n) with (2 ^ n * 2) by unify_pows_two.
    repeat rewrite <- (@kron_assoc 2 1 (2 ^ n) 1 2 1 _ _ _).
    remember (cpar (S n) H) as c.
    simpl.
    replace (2 ^ n + (2 ^ n + 0) + (2 ^ n + (2 ^ n + 0) + 0)) with (2 * 2 ^ n * 2) by unify_pows_two.
    replace (2 ^ n + (2 ^ n + 0)) with (2 * 2 ^ n) by unify_pows_two.
    unfold ueval1, pad. simpl.
    bdestructΩ (n + 1 <=? S n).
    replace (2 ^ n + (2 ^ n + 0)) with (2 * 2 ^ n) by unify_pows_two.
    replace (n - n) with 0 by lia.
    replace (2 ^ 0) with 1 by auto.
    rewrite kron_1_r.
    replace (S (S n)) with (S n + 1) by lia.
    rewrite <- pad_dims_r.
    replace (2 ^ 1) with 2 by auto.
    rewrite kron_mixed_product.
    rewrite Mmult_1_l. rewrite Mmult_1_r by auto with wf_db.
    rewrite (@kron_mixed_product (2 * 2 ^ n) (2 * 2 ^ n) 1 2 2 1 _ _ _ _).
    replace (hadamard × ∣0⟩) with ψp by (rewrite Heqψp; solve_matrix).
    apply f_equal2. assumption. reflexivity.
    rewrite Heqc. 
    show_dimensions.
    replace (2 * 2 ^ n) with (2 ^ S n) by unify_pows_two.
    apply WF_cpar_H.
    rewrite Heqc. apply well_typed_cpar_H.
Qed.

Lemma cpar_H_self_adjoint :
  forall (n : nat), (uc_eval n (cpar n H))† = uc_eval n (cpar n H).
Proof.
  intros. induction n.
  - simpl. apply id_sa.
  - replace (cpar (S n) H) with (cpar n H ; H n) by reflexivity.
    remember (cpar n H) as c.
    replace (uc_eval (S n) (c; H n)) with (uc_eval (S n) (H n) × uc_eval (S n) c) by (simpl; reflexivity).
    rewrite Mmult_adjoint.
    replace (S n) with (n + 1) by lia.
    rewrite <- pad_dims_r by (rewrite Heqc; apply well_typed_cpar_H).
    (* replace (n + 1) with (S n) by lia. *)
    replace (uc_eval (n + 1) (H n)) with (I (2 ^ n) ⊗ hadamard).
    2 : { simpl. unfold ueval1, pad. bdestructΩ (n + 1 <=? n + 1).
    replace (n + 1 - 1 - n) with 0 by lia. simpl. rewrite kron_1_r. reflexivity. }
    replace (2 ^ 1) with 2 by (simpl; auto).
    replace (2 ^ (n + 1)) with (2 ^ n * 2) by unify_pows_two.
    repeat rewrite (@kron_adjoint (2 ^ n) (2 ^ n) 2 2 _ _).
    repeat rewrite id_sa. rewrite IHn.
    rewrite (@kron_mixed_product (2 ^ n) (2 ^ n) (2 ^ n) 2 2 2 _ _ _ _).
    symmetry.
    rewrite (@kron_mixed_product (2 ^ n) (2 ^ n) (2 ^ n) 2 2 2 _ _ _ _).
    rewrite Mmult_1_l. rewrite Mmult_1_r by auto with wf_db.
    symmetry.
    rewrite Mmult_1_l by auto with wf_db. 
    rewrite Mmult_1_r by auto with wf_db.
    apply f_equal. solve_matrix.
    rewrite Heqc. apply WF_cpar_H.
Qed.

Lemma nket_assoc :
  forall (n : nat) (ψ : Matrix 2 1), WF_Matrix ψ -> nket (S n) ψ = ψ ⊗ nket n ψ.
Proof.
  intros. induction n.
  - simpl. rewrite kron_1_l by auto with wf_db. rewrite kron_1_r. reflexivity.
  - replace (nket (S n) ψ) with (nket n ψ ⊗ ψ) by auto.
    replace (nket (S (S n)) ψ) with (nket (S n) ψ ⊗ ψ) by auto.
    replace (2 ^ S n) with (2 ^ n * 2) by unify_pows_two.
    rewrite <- (@kron_assoc 2 1 (2 ^ n) 1 2 1 _ _ _).
    rewrite IHn. reflexivity.
Qed.

Definition deutsch_jozsa (n : nat) (U : ucom) : ucom :=
  X 0 ; cpar n H ; U; cpar n H.

Lemma deutsch_jozsa_success_probability :
  forall {dim : nat} {U : ucom} (P : boolean dim U) (ψ : Matrix 2 1) (WF : WF_Matrix ψ),
    (ψ ⊗ nket dim ∣0⟩)† × ((uc_eval (S dim) (deutsch_jozsa (S dim) U)) × (nket (S dim) ∣0⟩)) = (1%R - 2%R * count P * /2%R ^ (dim - 1))%C .* (ψ† × ∣1⟩).
Proof.
  intros.
  unfold deutsch_jozsa. rewrite nket_assoc by auto with wf_db.
  replace (uc_eval (S dim) (((X 0; cpar (S dim) H); U); cpar (S dim) H))
  with (uc_eval (S dim) (cpar (S dim) H) × uc_eval (S dim) U × uc_eval (S dim) (cpar (S dim) H) × uc_eval (S dim) (X 0)).
  2 : { simpl. repeat rewrite Mmult_assoc. reflexivity. }
  rewrite Mmult_assoc.
  replace (uc_eval (S dim) (X 0)) with (σx ⊗ I (2 ^ dim)).
  2 : { simpl. unfold ueval1, pad. simpl. 
        replace (dim - 0 - 0) with dim by lia.
        rewrite kron_1_l. reflexivity. auto with wf_db. }
  rewrite (@kron_mixed_product 2 2 1 (2 ^ dim) (2 ^ dim) 1 _ _ _ _).
  rewrite Mmult_1_l by (apply WF_nket; auto with wf_db).
  replace (σx × ∣0⟩) with (∣1⟩) by solve_matrix.
  rewrite Mmult_assoc.
  rewrite cpar_correct_H by auto with wf_db.
  rewrite Mmult_assoc.
  rewrite <- (@Mmult_assoc 1 (2 * 2 ^ dim) _ _ _ _ _).
  rewrite <- cpar_H_self_adjoint.
  rewrite <- Mmult_adjoint.
  rewrite cpar_correct_H by auto with wf_db.
  replace (hadamard × ∣1⟩) with ∣-⟩ by solve_matrix.
  replace (2 ^ S dim) with (2 * 2 ^ dim) by unify_pows_two.
  assert (F : forall m n a b, @Mmult 1 m n a b = @Mmult (1 * 1) m n a b).
  { intros. simpl. reflexivity. } rewrite F.
  (* remember (hadamard × ψ) as ϕ. *)
  assert (forall ψ : Matrix 2 1,   
  (ψ ⊗ nket dim ∣+⟩)† × (uc_eval (S dim) U × (∣-⟩ ⊗ nket dim ∣+⟩)) = (1%R - 2%R * count P * /2%R ^ (dim - 1))%C .* (ψ† × ∣-⟩)).
  { intro. rewrite (deutsch_jozsa_count P). reflexivity. }
  rewrite H.
  rewrite Mmult_adjoint.
  rewrite Mmult_assoc.
  replace (hadamard† × ∣-⟩) with ∣1⟩ by solve_matrix.
  reflexivity.
Qed.

Definition accept {dim : nat} {U : ucom} (P : boolean dim U) : Prop :=
    exists (ψ : Matrix 2 1), WF_Matrix ψ -> ((ψ ⊗ nket dim ∣0⟩)† × (uc_eval (S dim) (deutsch_jozsa (S dim) U) × (nket (S dim) ∣0⟩))) 0 0 = 1%R. 

Definition reject {dim : nat} {U : ucom} (P : boolean dim U) : Prop :=
    forall (ψ : Matrix 2 1), WF_Matrix ψ -> ((ψ ⊗ nket dim ∣0⟩)† × (uc_eval (S dim) (deutsch_jozsa (S dim) U) × (nket (S dim) ∣0⟩))) 0 0 = 0%R. 

Theorem deutsch_jozsa_constant_correct :
  forall (dim : nat) (U : ucom) (P : boolean dim U), constant P -> accept P.
Proof.
  intros. 
  unfold accept. destruct H.
  - exists ∣1⟩.
    rewrite (deutsch_jozsa_success_probability P _) by auto with wf_db. 
    rewrite H. 
    destruct dim. inversion P.
    replace (S dim - 1) with dim in * by lia.
    autorewrite with C_db. rewrite Mscale_1_l. 
    replace (∣1⟩† × ∣1⟩) with (I 1) by solve_matrix.
    unfold I. simpl. reflexivity.
  - exists ((-1)%R .* ∣1⟩). intros.
    rewrite (deutsch_jozsa_success_probability P _) by auto with wf_db. 
    rewrite H.
    destruct dim. inversion P.
    replace (S dim - 1) with dim in * by lia.
    autorewrite with C_db. 
    rewrite <- Cmult_assoc. rewrite Cinv_r by (apply Cpow_nonzero; lra).
    rewrite Cmult_1_r.
    rewrite <- Cminus_unfold.
    replace (((-1)%R .* ∣1⟩)† × ∣1⟩) with ((-1)%R .* I 1).
    unfold I, scale. simpl. lca.
    solve_matrix.
Qed.

Theorem deutsch_jozsa_balanced_correct :
  forall (dim : nat) (U : ucom) (P : boolean dim U), balanced P -> reject P.
Proof.
  unfold reject. intros. 
  rewrite (deutsch_jozsa_success_probability P _) by auto with wf_db.
  destruct dim. inversion P.
  replace (S dim - 1) with dim in * by lia.
  unfold balanced in H. inversion H.
  destruct dim. inversion H1. inversion H4.
  replace (S (S dim) - 2) with dim in * by lia.
  rewrite H2. simpl. rewrite Cinv_r.
  autorewrite with C_db.
  rewrite Mscale_0_l. unfold Zero. reflexivity.
  replace (2%R * 2%R ^ dim)%C with (2%R ^ S dim)%C.
  apply Cpow_nonzero. lra.
  simpl. reflexivity.
Qed.  


