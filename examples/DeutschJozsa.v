Require Import List.
Require Import Compose.
Require Import Dirac.

Open Scope ucom.
Local Close Scope C_scope.
Local Close Scope R_scope.

Inductive boolean : forall {n}, base_ucom (S n) -> Set :=
  | boolean_I : forall u, u ≡ SKIP -> @boolean 0 u
  | boolean_X : forall u, u ≡ X 0 -> @boolean 0 u
  | boolean_U : forall dim (u : base_ucom (S (S dim))) (u1 u2 : base_ucom (S dim)),
                boolean u1 -> boolean u2 ->
                uc_eval u = (uc_eval u1 ⊗ ∣0⟩⟨0∣) .+ (uc_eval u2 ⊗ ∣1⟩⟨1∣) ->
                boolean u.
  
(* Why not make this a function to nats? (Convert to R in DJ_count) *)
Fixpoint count {dim : nat} {u : base_ucom (S dim)} (P : boolean u) : C :=
  match P with
  | boolean_I _ _ => 0%R
  | boolean_X _ _ => 1%R
  | boolean_U _ _ _ _ P1 P2 _ => (count P1 + count P2)%C
  end.

Local Open Scope R_scope.
Local Open Scope C_scope.

Definition balanced {dim : nat} {u : base_ucom (S dim)} (P : boolean u) : Prop :=
  (dim > 0)%nat /\ count P = (2%R ^ (dim - 1))%C.

Definition constant {dim : nat} {u : base_ucom (S dim)} (P : boolean u) : Prop :=
  count P = 0%R \/ count P = (2%R ^ dim)%C.

Lemma deutsch_jozsa_count :
  forall {dim : nat} {U : base_ucom (S dim)} (P : boolean U) (ψ : Matrix 2 1),
    (ψ ⊗ kron_n dim ∣+⟩)† × (uc_eval U × (∣-⟩ ⊗ kron_n dim ∣+⟩)) = (1%R - 2%R * count P * /2%R ^ dim)%C .* (ψ† × ∣-⟩).
Proof.
  intros.
  remember ∣+⟩ as ψp. remember ∣-⟩ as ψm.
  induction dim; dependent destruction P.                                   
  - simpl. rewrite u0. 
    rewrite denote_SKIP; try lia.
    repeat rewrite kron_1_r. rewrite Mmult_1_l by (subst; auto with wf_db). 
    autorewrite with C_db.
    symmetry. apply Mscale_1_l.
  - simpl. rewrite u0.
    autorewrite with eval_db.
    simpl.
    repeat rewrite kron_1_r. rewrite kron_1_l by auto with wf_db.
    replace (σx × ψm) with ((-1)%R .* ψm) by (subst; solve_matrix).
    rewrite Mscale_mult_dist_r.
    apply f_equal2. lca. reflexivity.
  - simpl.
    rewrite e.
    restore_dims.
    repeat rewrite <- kron_assoc.
    restore_dims.
    setoid_rewrite kron_adjoint.
    rewrite Mmult_plus_distr_r.
    restore_dims.
    rewrite Mmult_plus_distr_l.
    repeat rewrite kron_mixed_product.
    setoid_rewrite (IHdim u1 P1).
    setoid_rewrite (IHdim u2 P2).
    replace ((ψp) † × (∣0⟩⟨0∣ × ψp)) with ((1/2)%R .* I 1) by (rewrite Heqψp; solve_matrix).
    replace ((ψp) † × (∣1⟩⟨1∣ × ψp)) with ((1/2)%R .* I 1) by (rewrite Heqψp; solve_matrix).
    repeat rewrite Mscale_kron_dist_r.
    restore_dims.
    Msimpl.
    repeat rewrite Mscale_assoc.
    rewrite <- Mscale_plus_distr_l.
    apply f_equal2; trivial.
    field_simplify_eq. lca.
    split; try nonzero.
    apply Cpow_nonzero. lra.
Qed.    

Fixpoint cpar {dim : nat} (n : nat) (u : nat -> base_ucom dim) : base_ucom dim :=
  match n with
  | 0 => SKIP
  | S n' => cpar n' u ; u n'
  end.

Lemma well_typed_cpar_H : forall (dim n : nat), (0 < dim)%nat -> (n <= dim)%nat -> uc_well_typed (@cpar dim n H).
Proof.
  intros. induction n.
  - simpl. apply uc_well_typed_ID; assumption.
  - simpl. apply WT_seq.
    apply IHn. lia. 
    apply uc_well_typed_H. lia.
Qed.

Lemma WF_cpar_H : 
  forall (dim n : nat), WF_Matrix (@uc_eval dim (cpar n H)).
Proof.
  intros. induction n.
  - simpl. auto with wf_db.
  - simpl.
    autorewrite with eval_db.
    bdestruct (n + 1 <=? dim).
    apply WF_mult. auto with wf_db.
    apply IHn.
    rewrite Mmult_0_l.
    apply WF_Zero.
Qed.

Lemma cpar_correct_H : forall dim n,
  (0 < dim)%nat -> (n <= dim)%nat -> uc_eval (@cpar dim n H) = (kron_n n hadamard) ⊗ I (2 ^ (dim - n)).
Proof.
  intros.
  induction n.
  - replace (dim - 0)%nat with dim by lia. 
    Msimpl_light. simpl. rewrite denote_SKIP; try assumption.
    reflexivity.
  - simpl.
    autorewrite with eval_db.
    bdestruct_all. 
    rewrite IHn; try lia.
    replace (dim - (n + 1))%nat with (dim - (S n))%nat by lia.
    replace (2 ^ (dim - n))%nat with (2 * 2 ^ (dim - (S n)))%nat by unify_pows_two.
    rewrite <- id_kron.
    rewrite <- kron_assoc.
    restore_dims.
    repeat rewrite kron_mixed_product.
    Msimpl_light. 
    reflexivity.
Qed.

Lemma kron_n_H : forall n,
  kron_n n hadamard × kron_n n ∣0⟩ = kron_n n ∣+⟩.
Proof.
  intros.
  induction n; simpl.
  - Msimpl_light. reflexivity.
  - restore_dims. 
    rewrite kron_mixed_product.
    rewrite <- IHn.
    apply f_equal_gen; try reflexivity.
    solve_matrix.
Qed.

Lemma cpar_H_self_adjoint :
  forall (n : nat), (uc_eval (@cpar n n H))† = uc_eval (@cpar n n H).
Proof.
  intros.
  destruct n. 
  (* weird n = 0 case *)
  simpl; unfold SKIP; rewrite denote_ID.
  unfold pad; bdestruct_all.
  apply zero_adjoint_eq.
  (* now n > 0 *)
  rewrite cpar_correct_H; try lia. 
  induction n.
  - simpl. Msimpl_light. apply hadamard_sa.
  - simpl in *; replace (n - n)%nat with O in * by lia. 
    simpl in *.
    repeat rewrite kron_1_r in *. 
    restore_dims. 
    rewrite kron_adjoint. 
    rewrite hadamard_sa. 
    setoid_rewrite IHn.
    reflexivity.
Qed.

Definition deutsch_jozsa {n} (U : base_ucom n) : base_ucom n :=
  X 0 ; cpar n H ; U; cpar n H.

Lemma deutsch_jozsa_success_probability :
  forall {dim : nat} {U : base_ucom (S dim)} (P : boolean U) (ψ : Matrix 2 1) (WF : WF_Matrix ψ),
    (ψ ⊗ kron_n dim ∣0⟩)† × ((uc_eval (deutsch_jozsa U)) × (kron_n (S dim) ∣0⟩)) = (1%R - 2%R * count P * /2%R ^ dim)%C .* (ψ† × ∣1⟩).
Proof.
  intros.
  unfold deutsch_jozsa. 
  rewrite kron_n_assoc by auto with wf_db.
  Opaque cpar. 
  simpl uc_eval.
  rewrite <- cpar_H_self_adjoint at 1.
  rewrite cpar_correct_H by lia.
  replace (S dim - S dim)%nat with O by lia.
  autorewrite with eval_db.
  bdestruct_all.
  simpl I.
  Msimpl_light.
  replace (dim - 0)%nat with dim by lia.
  rewrite kron_n_assoc by auto with wf_db.
  restore_dims. 
  repeat rewrite Mmult_assoc.
  restore_dims. 
  rewrite 2 kron_mixed_product.
  replace (σx × ∣0⟩) with (∣1⟩) by solve_matrix.
  replace (hadamard × ∣1⟩) with ∣-⟩ by solve_matrix.
  rewrite Mmult_1_l by auto with wf_db.
  rewrite kron_n_H. 
  rewrite <- Mmult_assoc.
  rewrite <- Mmult_adjoint.
  rewrite kron_mixed_product.
  remember (hadamard × ψ) as ϕ.
  rewrite kron_n_H.
  rewrite (deutsch_jozsa_count P).
  subst.
  Msimpl.
  rewrite hadamard_sa.
  rewrite Mmult_assoc.
  replace (hadamard × ∣-⟩) with ∣1⟩ by solve_matrix.
  reflexivity.
Qed.

Definition accept {dim : nat} {U : base_ucom (S dim)} (P : boolean U) : Prop :=
    exists (ψ : Matrix 2 1), ((ψ ⊗ kron_n dim ∣0⟩)† × (uc_eval (deutsch_jozsa U) × (kron_n (S dim) ∣0⟩))) 0%nat 0%nat = 1. 

Definition reject {dim : nat} {U : base_ucom (S dim)} (P : boolean U) : Prop :=
    forall (ψ : Matrix 2 1), WF_Matrix ψ -> ((ψ ⊗ kron_n dim ∣0⟩)† × (uc_eval (deutsch_jozsa U) × (kron_n (S dim) ∣0⟩))) 0%nat 0%nat = 0. 

Theorem deutsch_jozsa_constant_correct :
  forall (dim : nat) (U : base_ucom (S dim)) (P : boolean U), constant P -> accept P.
Proof.
  intros. 
  unfold accept.
  destruct H; [exists ∣1⟩ | exists (-1 .* ∣1⟩) ];
  rewrite (deutsch_jozsa_success_probability P) by auto with wf_db; rewrite H.
  - autorewrite with C_db. rewrite Mscale_1_l. solve_matrix.
  - rewrite <- Cmult_assoc.
    rewrite Cinv_r by (apply Cpow_nonzero; lra).
    solve_matrix.
Qed.

Theorem deutsch_jozsa_balanced_correct :
  forall (dim : nat) (U : base_ucom (S dim)) (P : boolean U), 
    balanced P -> reject P.
Proof.
  unfold reject. intros dim U P [H1 H2] ψ WF. 
  rewrite (deutsch_jozsa_success_probability P) by auto with wf_db.
  rewrite H2.
  replace (2 * 2 ^ (dim - 1)) with (2 ^ dim).
  2: { replace dim with (1 + (dim - 1))%nat at 1 by lia. reflexivity. }
  autorewrite with C_db. 
  rewrite Cinv_r by (apply Cpow_nonzero; lra).
  solve_matrix.
Qed.  


