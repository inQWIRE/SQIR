Require Import List.
Require Import Compose.
Require Import Dirac.
Require Import Tactics.

Open Scope ucom.
Local Close Scope C_scope.
Local Close Scope R_scope.

Inductive boolean : forall n, ucom n -> Set :=
  | boolean_I : forall u, u ≡ uskip -> boolean 1 u
  | boolean_X : forall u, u ≡ X 0 -> boolean 1 u
  | boolean_U : forall dim (u : ucom (S dim)) (u1 u2 : ucom dim),
                boolean dim u1 -> boolean dim u2 ->
                uc_eval u = (uc_eval u1 ⊗ ∣0⟩⟨0∣) .+ (uc_eval u2 ⊗ ∣1⟩⟨1∣) ->
                boolean (S dim) u.

Lemma boolean_WT : forall dim u, boolean dim u -> uc_well_typed u.
Proof.
  intros dim u H.
  apply WT_if_nonzero.
  induction H.
  - rewrite u0.
    simpl. intros F.
    apply (f_equal2_inv 0 0) in F.
    inversion F. contradict H0. nonzero.
  - rewrite u0.
    simpl. intros F.
    apply (f_equal2_inv 0 1) in F.
    contradict F. unfold ueval1, pad.
    bdestruct_all. simpl.
    replace (@Zero 2 2 0 1) with C0 by solve_matrix.
    rewrite kron_1_l by auto with wf_db.
    rewrite kron_1_r by auto with wf_db.
    nonzero.
  - rewrite e. clear -IHboolean1.
    intros F.
    assert (Z1 : forall i j, i mod 2 = 0 -> j mod 2 = 0 -> (uc_eval u2 ⊗ ∣1⟩⟨1∣) i j = C0).
    { clear. intros. unfold kron. rewrite H, H0.  replace (∣1⟩⟨1∣ 0 0) with C0 by solve_matrix. lca. }
    assert (Z0 : forall i j, i mod 2 = 0 -> j mod 2 = 0 -> (uc_eval u1 ⊗ ∣0⟩⟨0∣) i j = C0).
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
  
(* Why not make this a function to nats? (Convert to R in DJ_count) *)
Fixpoint count {n : nat} {u : ucom n} (P : boolean n u) : C :=
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

Local Open Scope R_scope.
Local Open Scope C_scope.

Definition balanced {n : nat} {u : ucom n} (P : boolean n u) : Prop :=
  count P = (2%R ^ (n - 1))%C.

Definition constant {n : nat} {u : ucom n} (P : boolean n u) : Prop :=
  count P = 0%R \/ count P = (2%R ^ n)%C.

Lemma deutsch_jozsa_count :
  forall {dim : nat} {U : ucom (S dim)} (P : boolean (S dim) U) (ψ : Matrix 2 1),
    (ψ ⊗ nket dim ∣+⟩)† × (uc_eval U × (∣-⟩ ⊗ nket dim ∣+⟩)) = (1%R - 2%R * count P * /2%R ^ dim)%C .* (ψ† × ∣-⟩).
Proof.
  intros.
  remember ∣+⟩ as ψp. remember ∣-⟩ as ψm.
  induction dim; dependent destruction P.                                   
  - simpl. rewrite u0. simpl.
    repeat rewrite kron_1_r. rewrite Mmult_1_l by (subst; auto with wf_db). 
    autorewrite with C_db.
    symmetry. apply Mscale_1_l.
  - simpl. rewrite u0. unfold uc_eval. simpl. unfold ueval1, pad. simpl.
    simpl.
    repeat rewrite kron_1_r. rewrite kron_1_l by auto with wf_db.
    replace (σx × ψm) with ((-1)%R .* ψm) by (subst; solve_matrix).
    rewrite Mscale_mult_dist_r.
    apply f_equal2. lca. reflexivity.
  - inversion P1.
  - simpl.
    rewrite e.
    restore_dims_strong.
    repeat rewrite <- kron_assoc.
    restore_dims_strong.
    setoid_rewrite kron_adjoint.
    rewrite Mmult_plus_distr_r.
    restore_dims_strong.
    rewrite Mmult_plus_distr_l.
    repeat rewrite kron_mixed_product.
    setoid_rewrite (IHdim u1 P1).
    setoid_rewrite (IHdim u2 P2).
    replace ((ψp) † × (∣0⟩⟨0∣ × ψp)) with ((1/2)%R .* I 1) by (rewrite Heqψp; solve_matrix).
    replace ((ψp) † × (∣1⟩⟨1∣ × ψp)) with ((1/2)%R .* I 1) by (rewrite Heqψp; solve_matrix).
    repeat rewrite Mscale_kron_dist_r.
    restore_dims_strong.
    Msimpl.
    repeat rewrite Mscale_assoc.
    rewrite <- Mscale_plus_distr_l.
    apply f_equal2; trivial.
    field_simplify_eq. lca.
    split; try nonzero.
    apply Cpow_nonzero. lra.
Qed.    

Fixpoint cpar {dim : nat} (n : nat) (u : nat -> ucom dim) : ucom dim :=
  match n with
  | 0 => uskip
  | S n' => cpar n' u ; u n'
  end.

Lemma well_typed_cpar_H : forall (dim n : nat), (n <= dim)%nat -> @uc_well_typed dim (cpar n H).
Proof.
  intros. induction n.
  - simpl. apply WT_uskip.
  - simpl. apply WT_seq.
    apply IHn; lia.
    apply WT_app1; lia. 
Qed.

Lemma WF_cpar_H : 
  forall (dim n : nat), WF_Matrix (@uc_eval dim (cpar n H)).
Proof.
  intros. induction n.
  - simpl. auto with wf_db.
  - simpl. unfold ueval1, pad. simpl.
    bdestructΩ (n + 1 <=? dim).
    apply WF_mult. auto with wf_db.
    apply IHn.
    rewrite Mmult_0_l.
    apply WF_Zero.
Qed.

Lemma WF_nket : forall (n : nat)(ψ : Matrix 2 1), WF_Matrix ψ -> WF_Matrix (nket n ψ).
Proof.
  intros n ψ H. induction n; simpl; auto with wf_db.
Qed.

(*
Lemma cpar_correct_H_aux : 
  forall (dim n : nat) (ψ : Matrix 2 1) (WF : WF_Matrix ψ), 
  (n < dim)%nat ->
  (@uc_eval dim (cpar n H)) × (ψ ⊗ nket (dim - 1) ∣0⟩) 
  = (hadamard × ψ) ⊗ nket n ∣+⟩ ⊗ nket (dim - n - 1) ∣0⟩.
*)

Lemma cpar_correct_H : 
  forall (n : nat) (ψ : Matrix 2 1) (WF : WF_Matrix ψ), (@uc_eval (S n) (cpar (S n) H)) × (ψ ⊗ nket n ∣0⟩) = (hadamard × ψ) ⊗ nket n ∣+⟩.
Proof.
  intros.
  remember ∣+⟩ as ψp.
  induction n.
  - simpl. unfold ueval1, pad. simpl. 
    rewrite kron_1_l; auto with wf_db. 
    repeat rewrite kron_1_r; auto with wf_db.
    rewrite Mmult_1_r; auto with wf_db.
  - replace (@cpar (S (S n)) (S (S n)) H) with (@cpar (S (S n)) (S n) H ; H (S n)) by reflexivity.
    replace (nket (S n) ψp) with (nket n ψp ⊗ ψp) by reflexivity.
    replace (nket (S n) ∣0⟩) with (nket n ∣0⟩ ⊗ ∣0⟩) by reflexivity.
    repeat replace (2 ^ S n) with (2 ^ n * 2) by unify_pows_two.
    repeat rewrite <- (@kron_assoc 2 1 (2 ^ n) 1 2 1 _ _ _).
    simpl.
    unify_pows_two.
    unfold ueval1, pad.
    replace (S (S n) - 1 - S n)%nat with 0%nat by lia.
    replace (S (S n) - 1 - n)%nat with 1%nat by lia.
    simpl.
    bdestructΩ (n + 1 <=? S n).
    bdestructΩ (n + 1 <=? S (S n)).
    Msimpl.
    rewrite <- Mmult_assoc.
    replace (2 ^ n + (2 ^ n + 0))%nat with (2 * 2 ^ n)%nat by unify_pows_two.
    restore_dims_strong.
    rewrite (kron_mixed_product (I (2 * 2 ^ n)) hadamard (I (2 ^ n) ⊗ hadamard) (I 2)).
    Msimpl.
    Set Printing Implicit.
    simpl in IHn.
    rewrite 


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

Lemma cpar_correct_H : 
  forall (n : nat) (ψ : Matrix 2 1) (WF : WF_Matrix ψ), (@uc_eval (S n) (cpar (S n) H)) × (ψ ⊗ nket n ∣0⟩) = (hadamard × ψ) ⊗ nket n ∣+⟩.


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
    (ψ ⊗ nket dim ∣0⟩)† × ((uc_eval (S dim) (deutsch_jozsa (S dim) U)) × (nket (S dim) ∣0⟩)) = (1%R - 2%R * count P * /2%R ^ dim)%C .* (ψ† × ∣1⟩).
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
  (ψ ⊗ nket dim ∣+⟩)† × (uc_eval (S dim) U × (∣-⟩ ⊗ nket dim ∣+⟩)) = (1%R - 2%R * count P * /2%R ^ dim)%C .* (ψ† × ∣-⟩)).
  { intro. rewrite (deutsch_jozsa_count P). reflexivity. }
  rewrite H.
  rewrite Mmult_adjoint.
  rewrite Mmult_assoc.
  replace (hadamard† × ∣-⟩) with ∣1⟩ by solve_matrix.
  reflexivity.
Qed.

Definition accept {dim : nat} {U : ucom} (P : boolean dim U) : Prop :=
    exists (ψ : Matrix 2 1), ((ψ ⊗ nket dim ∣0⟩)† × (uc_eval (S dim) (deutsch_jozsa (S dim) U) × (nket (S dim) ∣0⟩))) 0 0 = 1%R. 

Definition reject {dim : nat} {U : ucom} (P : boolean dim U) : Prop :=
    forall (ψ : Matrix 2 1), WF_Matrix ψ -> ((ψ ⊗ nket dim ∣0⟩)† × (uc_eval (S dim) (deutsch_jozsa (S dim) U) × (nket (S dim) ∣0⟩))) 0 0 = 0%R. 

Theorem deutsch_jozsa_constant_correct :
  forall (dim : nat) (U : ucom) (P : boolean dim U), constant P -> accept P.
Proof.
  intros. 
  unfold accept.
  destruct H; [exists ∣1⟩ | exists ((-1)%R .* ∣1⟩) ];
  rewrite (deutsch_jozsa_success_probability P _) by auto with wf_db; rewrite H.
  - autorewrite with C_db. rewrite Mscale_1_l. solve_matrix.
  - rewrite <- Cmult_assoc.
    rewrite Cinv_r by (apply Cpow_nonzero; lra).
    solve_matrix.
Qed.

Theorem deutsch_jozsa_balanced_correct :
  forall (dim : nat) (U : ucom) (P : boolean dim U), balanced P -> reject P.
Proof.
  unfold reject. intros. 
  rewrite (deutsch_jozsa_success_probability P _) by auto with wf_db.
  destruct dim; inversion H.
  - inversion H1.
  - replace (S dim - 1) with dim in H2 by lia.
    rewrite H2.
    replace (2%R * 2%R ^ dim)%C with (2%R ^ S dim)%C by (simpl; reflexivity).
    autorewrite with C_db. rewrite Cinv_r by (apply Cpow_nonzero; lra).
    solve_matrix.
Qed.  


