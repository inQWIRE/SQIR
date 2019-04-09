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
  
Fixpoint count {dim : nat} {U : ucom} (P : boolean dim U)  : nat :=
  match P with
  | boolean_I _ _ _ => 0
  | boolean_X _ _ _ => 1
  | boolean_U u u1 u2 dim WT1 P1 WT2 P2 WT P => count P1 + count P2
  end.

Definition balanced {dim : nat} {U : ucom} (P : boolean dim U) : Prop :=
  dim >= 2 /\ count P = (2 ^ (dim - 2))%nat.

Definition constant {dim : nat} {U : ucom} (P : boolean dim U) : Prop :=
  count P = 0%nat \/ count P = (2 ^ (dim - 1))%nat.

Fixpoint cpar1 (n : nat) (u : nat -> ucom) : ucom :=
  match n with
  | 0 => uskip
  | S n' => cpar1 n' u ; u n'
  end.

Definition deutsch_jozsa (dim : nat) {U : ucom} (P : boolean dim U) : ucom := 
  cpar1 (S dim) H; U ; cpar1 (S dim) H.

Fixpoint nket (n : nat) (ψ : Matrix 2 1) : Matrix (2^n) 1 :=
  match n with
  | 0 => I 1
  | S n' => (nket n' ψ) ⊗ ψ
  end.

Lemma aux : forall a b : nat, (a + b = 0 <-> a = 0 /\ b = 0)%nat.
Proof. intros. lia. Qed.

Notation "∣+⟩" := (/√2 .* ∣0⟩ .+ /√2 .* ∣1⟩)%C.
Notation "∣-⟩" := (/√2 .* ∣0⟩ .+ (-/√2) .* ∣1⟩)%C.
 
Lemma aux2 : forall {m n : nat}(ψ1 ψ2 : Matrix m n), 
    ψ1 ⊗ ∣+⟩ = ψ2 ⊗ ∣+⟩ -> ψ1 = ψ2.
Proof. Admitted.

Lemma aux3 : forall {m n : nat}(ψ1 ψ2 : Matrix m n), 
    ψ1 ⊗ ∣-⟩ = ψ2 ⊗ ∣-⟩ -> ψ1 = ψ2.
Proof. Admitted.

Lemma WT_boolean : forall (dim : nat) (U : ucom), boolean dim U -> uc_well_typed dim U.
Proof. intros. inversion H; assumption. Qed.

Lemma cpar_correct :
  forall (dim : nat), (uc_eval (S dim) (cpar1 (S dim) H)) × (∣1⟩ ⊗ (nket dim ∣0⟩)) = ∣-⟩ ⊗ (nket dim ∣+⟩).
Proof.
  remember (∣+⟩) as plus.
  remember (∣-⟩) as minus.
  induction dim as [| dim'].
  - unfold cpar1. simpl. unfold ueval1, pad. simpl. 
    rewrite Heqminus. solve_matrix.
  - replace (cpar1 (S (S dim')) H) with (cpar1 (S dim') H ; H (S dim')) by (simpl; reflexivity).
    remember (cpar1 (S dim') H) as c. simpl.
    unfold ueval1, pad. replace (S dim' + 1)%nat with (S (S dim')) by lia. 
    bdestructΩ (S (S dim') <=? S (S dim')).
    rewrite Nat.sub_diag. 
    rewrite kron_1_r.
    replace (S (S dim'))%nat with (S dim' + 1)%nat by lia.
    rewrite <- pad_dims_r.
    remember (uc_eval (S dim') c) as u. 
    replace (2 ^ dim' + (2 ^ dim' + 0))%nat with (2 ^ S dim') by unify_pows_two.
    replace (2 ^ 1)%nat with 2%nat by (simpl; reflexivity).
    replace (2 ^ S dim' + (2 ^ S dim' + 0))%nat with (2 ^ S dim' * 2)%nat by unify_pows_two.
    rewrite kron_mixed_product.
    rewrite Mmult_1_r by auto with wf_db. 
    rewrite Mmult_1_l.
    remember (nket dim' ∣0⟩) as k0.
    remember (nket dim' plus) as kp.
    show_dimensions.
    replace 
      (kron' 2 1 (2 ^ S dim') 1 ∣1⟩ (kron' (2 ^ dim') 1 2 1 k0 ∣0⟩))
    with
      (kron' 2 1 (2 ^ dim' * 2) (1 * 1) ∣1⟩ (kron' (2 ^ dim') 1 2 1 k0 ∣0⟩)) by (unify_pows_two; rewrite plus_comm; reflexivity).
    replace 
      (kron' 2 1 (2 ^ S dim') 1 minus (kron' (2 ^ dim') 1 2 1 kp plus))
    with
      (kron' 2 1 (2 ^ dim' * 2) (1 * 1) minus (kron' (2 ^ dim') 1 2 1 kp plus)) by (unify_pows_two; rewrite plus_comm; reflexivity).
    repeat rewrite <- kron_assoc.
    hide_dimensions. show_dimensions.
    replace
      (Mmult' (2 ^ S dim' * 2) (2 ^ S dim' * 2) 1
              (kron' (2 ^ S dim') (2 ^ S dim') 2 2 u hadamard)
              (kron' (2 * 2 ^ dim') (1 * 1) 2 1 (kron' 2 1 (2 ^ dim') 1 ∣1⟩ k0) ∣0⟩)) 
    with
      (Mmult' (2 ^ S dim' * 2) (2 ^ S dim' * 2) (1 * 1 * 1)
              (kron' (2 ^ S dim') (2 ^ S dim') 2 2 u hadamard)
              (kron' (2 * 2 ^ dim') (1 * 1) 2 1 (kron' 2 1 (2 ^ dim') 1 ∣1⟩ k0) ∣0⟩)) by (simpl; reflexivity).
    hide_dimensions.
    rewrite kron_mixed_product.
    replace (2 * 2 ^ dim') with (2 ^ S dim') by unify_pows_two.
    rewrite IHdim'.
    rewrite Heqplus.
    replace (hadamard × ∣0⟩) with ∣+⟩ by solve_matrix. reflexivity.
Admitted.      

Lemma deutsch_jozsa_constant0 : 
  forall (dim : nat) (U : ucom) (P : boolean dim U),
  (count P = 0)%nat -> 
  ((uc_eval (S dim) U) × (∣-⟩ ⊗ (nket dim ∣+⟩))) = (∣-⟩ ⊗ (nket dim ∣+⟩)).
Proof.
  intros. 
  induction P; intros.
  - rewrite u1.
    simpl; Msimpl; reflexivity.
  - simpl in H. lia.
  - 
    remember (/√2 .* ∣0⟩ .+ /√2 .* ∣1⟩)%C as plus.
    remember (/√2 .* ∣0⟩ .+ (-/√2) .* ∣1⟩)%C as minus.
    intros. inversion H.
    apply aux in H1. inversion H1. 
    rewrite H0. rewrite H2.
    apply IHP1 in H0. 
    apply IHP2 in H2. 
    clear H1. clear H. clear IHP1. clear IHP2.
    replace (S (S dim))%nat with (S dim + 1)%nat by lia.
    rewrite <- pad_dims_r by apply u4.
    rewrite e. clear e. 
    replace (S dim) with (dim + 1)%nat in H0 by lia.
    replace (S dim) with (dim + 1)%nat in H2 by lia.
    rewrite <- pad_dims_r in H0 by apply u0.
    rewrite <- pad_dims_r in H2 by apply u3.
    destruct dim.
    + inversion P1.
    + clear P1. clear P2.
      replace (nket (S dim) plus) with (nket dim plus ⊗ plus) in * by reflexivity.
      show_dimensions.
      replace (2 ^ (S dim))%nat with (2 ^ dim * 2)%nat in * by unify_pows_two. 
      replace (2 ^ 1)%nat with 2%nat in * by (simpl; reflexivity).
      replace (kron' 2 1 (2 ^ dim * 2) 1 minus (kron' (2 ^ dim) 1 2 1 (nket dim plus) plus)) with (kron' 2 1 (2 ^ dim * 2) (1 * 1) minus (kron' (2 ^ dim) 1 2 1 (nket dim plus) plus)) in * by reflexivity.
(* Kesha: commented out because it was causing compiler errors

      rewrite <- kron_assoc in *.
      hide_dimensions. 
      show_dimensions.
      replace (2 ^ (S dim + 1))%nat with (2 * 2 ^ dim * 2)%nat in * by unify_pows_two.
      replace
        (Mmult' (2 * 2 ^ dim * 2) (2 * 2 ^ dim * 2) (1 * 1)
         (kron' (2 ^ dim * 2) (2 ^ dim * 2) 2 2 (uc_eval (S dim) u1) (I 2))
         (kron' (2 * 2 ^ dim) (1 * 1) 2 1 (kron' 2 1 (2 ^ dim) 1 minus (nket dim plus))
            plus))
      with
        (Mmult' (2 * 2 ^ dim * 2) (2 * 2 ^ dim * 2) (1 * 1 * 1)
         (kron' (2 ^ dim * 2) (2 ^ dim * 2) 2 2 (uc_eval (S dim) u1) (I 2))
         (kron' (2 * 2 ^ dim) (1 * 1) 2 1 (kron' 2 1 (2 ^ dim) 1 minus (nket dim plus))
            plus)) in * by (simpl; reflexivity).
      replace 
        (Mmult' (2 * 2 ^ dim * 2) (2 * 2 ^ dim * 2) (1 * 1)
         (kron' (2 ^ dim * 2) (2 ^ dim * 2) 2 2 (uc_eval (S dim) u2) (I 2))
         (kron' (2 * 2 ^ dim) (1 * 1) 2 1 (kron' 2 1 (2 ^ dim) 1 minus (nket dim plus))
            plus))
      with
        (Mmult' (2 * 2 ^ dim * 2) (2 * 2 ^ dim * 2) (1 * 1 * 1)
         (kron' (2 ^ dim * 2) (2 ^ dim * 2) 2 2 (uc_eval (S dim) u2) (I 2))
         (kron' (2 * 2 ^ dim) (1 * 1) 2 1 (kron' 2 1 (2 ^ dim) 1 minus (nket dim plus))
            plus)) in * by (simpl; reflexivity).
      hide_dimensions.
      replace (2 ^ S dim)%nat with (2 * 2 ^ dim)%nat in * by (simpl; reflexivity).
      replace (2 * 2 ^ dim)%nat with (2 ^ dim * 2)%nat in * by lia.
      rewrite kron_mixed_product in *.
      rewrite Mmult_1_l in H0. 2 : rewrite Heqplus; auto with wf_db.
      rewrite Mmult_1_l in H2. 2 : rewrite Heqplus; auto with wf_db.
      rewrite Heqplus in H0. apply aux2 in H0. rewrite <- Heqplus in H0.
      rewrite Heqplus in H2. apply aux2 in H2. rewrite <- Heqplus in H2.
      replace (S (0 + 0))%nat with 1%nat by (simpl; reflexivity).
      replace (minus ⊗ nket (S (S dim)) plus) with (minus ⊗ nket (S dim) plus ⊗ plus).
      2 : { 
        replace (nket (S (S dim)) plus) with (nket (S dim) plus ⊗ plus) by reflexivity.
        rewrite kron_assoc. simpl. 
        show_dimensions.
        repeat rewrite <- plus_n_O.
        rewrite double_mult. 
        replace ((2 ^ dim + 2 ^ dim) * 2)%nat with (2 * (2 ^ dim + 2 ^ dim))%nat by lia.
        reflexivity.
      }
      remember (∣1⟩ ⊗ nket (S dim) ∣0⟩ ) as ψ.
      replace (2 ^ (S (S dim) + 1))%nat with (2 ^ (S (S dim)) * 2)%nat by unify_pows_two.
      remember (uc_eval (S dim) u1) as M1.
      remember (uc_eval (S dim) u2) as M2.      
      remember (∣0⟩⟨0∣) as q0.
      remember (∣1⟩⟨1∣) as q1.
      
      show_dimensions.
      replace (2 ^ dim * 2)%nat with (2 ^ S dim)%nat by unify_pows_two.
      replace (2 ^ S (S dim))%nat with (2 ^ S dim * 2)%nat by unify_pows_two.
      replace (2 * 2 ^ S dim)%nat with (2 ^ S dim * 2)%nat by omega.
      remember (2 ^ S dim)%nat as d.
      replace 
      (Mmult' (d * 2 * 2) (d * 2 * 2) 1
             (kron' (d * 2) (d * 2) 2 2 (kron' d d 2 2 M1 q0 .+ kron' d d 2 2 M2 q1) (I 2)))
      with
      (Mmult' (d * 2 * 2) (d * 2 * 2) (1 * 1 * 1)
             (kron' (d * 2) (d * 2) 2 2 (kron' d d 2 2 M1 q0 .+ kron' d d 2 2 M2 q1) (I 2))) by (simpl; reflexivity).
      hide_dimensions.
      rewrite kron_mixed_product.
      rewrite Mmult_1_l. 2 : rewrite Heqplus; auto with wf_db.
      apply f_equal2; try reflexivity.
      rewrite Heqd, HeqM1, HeqM2, Heqq0, Heqq1 in *.
      (* rewrite Heqd, HeqM1, HeqM2, Heqψ, Heqq0, Heqq1 in *. *)
      replace (nket (S dim) plus) with (nket dim plus ⊗ plus) by reflexivity.
      show_dimensions.
      replace (2 ^ S dim)%nat with (2 ^ dim * 2)%nat by unify_pows_two.
      clear Heqd. clear HeqM1. clear HeqM2. clear Heqψ. clear Heqq0. clear Heqq1.
      clear q0. clear q1. clear ψ. clear M2. clear M1.
      replace 
        (kron' 2 1 (2 ^ dim * 2) 1 minus (kron' (2 ^ dim) 1 2 1 (nket dim plus) plus))
      with
        (kron' 2 1 (2 ^ dim * 2) (1 * 1) minus (kron' (2 ^ dim) 1 2 1 (nket dim plus) plus)) by (simpl; reflexivity).
      hide_dimensions.
      rewrite <- kron_assoc.
      rewrite Mmult_plus_distr_r.
      replace (2 ^ dim * 2)%nat with (2 * 2 ^ dim)%nat by unify_pows_two.
      repeat rewrite kron_mixed_product.
      replace (∣0⟩⟨0∣ × plus) with (/√2 .* ∣0⟩) by (rewrite Heqplus; solve_matrix).
      replace (∣1⟩⟨1∣ × plus) with (/√2 .* ∣1⟩)%nat by (rewrite Heqplus; solve_matrix).
      replace (2 ^ dim * 2)%nat with (2 * 2 ^ dim)%nat in * by unify_pows_two.
      rewrite H0. rewrite H2. 
      rewrite <- kron_plus_distr_l. 
      rewrite Heqplus. reflexivity.
Qed. *)
Admitted.

Lemma count_limit :
   forall (dim : nat) (U : ucom) (P : boolean dim U), count P <= 2 ^ (dim - 1).
Proof.
  intros. induction P.
  - simpl. lia.
  - simpl. lia.
  - simpl. 
    replace (2 ^ (dim - 0))%nat with (2 ^ (dim - 1) + 2 ^ (dim - 1))%nat.
    apply plus_le_compat; assumption.
    destruct dim.
    + inversion P1.
    + unify_pows_two. 
Qed.

Lemma aux4 : forall a b c d: nat, a <= c -> b <= d -> a + b = c + d -> a = c /\ b = d.
Proof.
  intros. split. lia. lia.
Qed.

Lemma constant_induction :
  forall u u1 u2 dim WT1 P1 WT2 P2 WT P, 
  count (boolean_U u u1 u2 dim WT1 P1 WT2 P2 WT P) = 2 ^ dim ->
  count P1 = 2 ^ (dim - 1) /\ count P2 = 2 ^ (dim - 1).
Proof.
  intros. inversion H.
  destruct dim. 
  - inversion P2.
  - replace (S dim - 1) with dim by lia.
    replace (2 ^ S dim) with (2 ^ dim + 2 ^ dim) in H1 by unify_pows_two.
    assert (count P1 <= 2 ^ dim).
    replace (2 ^ dim) with (2 ^ (S dim - 1)) by unify_pows_two. apply count_limit.
    assert (count P2 <= 2 ^ dim).
    replace (2 ^ dim) with (2 ^ (S dim - 1)) by unify_pows_two. apply count_limit.
    apply aux4; assumption.
Qed.    

Lemma deutsch_jozsa_constant1 : 
  forall (dim : nat) (U : ucom) (P : boolean dim U),
  (count P = 2 ^ (dim - 1))%nat -> 
  ((uc_eval (S dim) U) × (∣-⟩ ⊗ (nket dim ∣+⟩))) = (-1)%R .* (∣-⟩ ⊗ (nket dim ∣+⟩)).
Proof.  
  intros. induction P; intros.
  - inversion H.
  - rewrite u1. simpl. unfold ueval1, pad. simpl. 
    (* rewrite eulers_identity. *)
    solve_matrix.
  - replace (S dim - 1) with dim in H by lia.
    apply constant_induction in H.
    inversion H. apply IHP1 in H0. apply IHP2 in H1.
    remember ∣+⟩ as ψp. remember ∣-⟩ as ψm.
    replace (S (S dim)) with (S dim + 1) by lia. 
    rewrite <- pad_dims_r by apply u4.
    rewrite e.
    replace (S dim) with (dim + 1) in H0 by lia. 
    rewrite <- pad_dims_r in H0 by apply u0.
    replace (S dim) with (dim + 1) in H1 by lia. 
    rewrite <- pad_dims_r in H1 by apply u3.
    destruct dim. inversion P1.
    replace (nket (S dim) ψp) with (nket dim ψp ⊗ ψp) in * by reflexivity.
    replace (2 ^ 1) with 2 in * by (simpl; reflexivity).
    show_dimensions.
    replace (2 ^ S dim) with (2 ^ dim * 2) in * by unify_pows_two.
    replace  
       (kron' 2 1 (2 ^ dim * 2) 1 ψm (kron' (2 ^ dim) 1 2 1 (nket dim ψp) ψp))
    with 
       (kron' 2 1 (2 ^ dim * 2) (1 * 1) ψm (kron' (2 ^ dim) 1 2 1 (nket dim ψp) ψp)) in * by (simpl; reflexivity).
(*
    rewrite <- kron_assoc in *.
    replace (2 ^ (S dim + 1)) with (2 * 2 ^ dim * 2) in * by unify_pows_two.
    hide_dimensions. show_dimensions.
    replace
      (Mmult' (2 * 2 ^ dim * 2) (2 * 2 ^ dim * 2) (1 * 1)
         (kron' (2 ^ dim * 2) (2 ^ dim * 2) 2 2 (uc_eval (S dim) u1) (I 2))
         (kron' (2 * 2 ^ dim) (1 * 1) 2 1 (kron' 2 1 (2 ^ dim) 1 ψm (nket dim ψp))
            ψp))
    with
      (Mmult' (2 * 2 ^ dim * 2) (2 * 2 ^ dim * 2) (1 * 1 * 1)
         (kron' (2 * 2 ^ dim) (2 * 2 ^ dim) 2 2 (uc_eval (S dim) u1) (I 2))
         (kron' (2 * 2 ^ dim) (1 * 1) 2 1 (kron' 2 1 (2 ^ dim) 1 ψm (nket dim ψp))
            ψp)) in H0 by (simpl; reflexivity).
    replace
      (Mmult' (2 * 2 ^ dim * 2) (2 * 2 ^ dim * 2) (1 * 1)
         (kron' (2 ^ dim * 2) (2 ^ dim * 2) 2 2 (uc_eval (S dim) u2) (I 2))
         (kron' (2 * 2 ^ dim) (1 * 1) 2 1 (kron' 2 1 (2 ^ dim) 1 ψm (nket dim ψp))
            ψp))
    with
      (Mmult' (2 * 2 ^ dim * 2) (2 * 2 ^ dim * 2) (1 * 1 * 1)
         (kron' (2 * 2 ^ dim) (2 * 2 ^ dim) 2 2 (uc_eval (S dim) u2) (I 2))
         (kron' (2 * 2 ^ dim) (1 * 1) 2 1 (kron' 2 1 (2 ^ dim) 1 ψm (nket dim ψp))
            ψp)) in H1 by (simpl; reflexivity).
    rewrite kron_mixed_product in *.
    hide_dimensions.
    rewrite Mmult_1_l in *; try (rewrite Heqψp; auto with wf_db).
*)
Admitted.

Definition proportional {n : nat} (ψ ϕ : Vector n) := 
  exists θ, ψ = Cexp θ .* ϕ. 

Notation "ψ ∝ ϕ" := (proportional ψ ϕ) (at level 20).

Theorem deutsch_jozsa_constant_correct :
  forall (dim : nat) (U : ucom) (P : boolean dim U),
  constant P -> 
  ((uc_eval (S dim) U) × (∣-⟩ ⊗ (nket dim ∣+⟩))) ∝ (∣-⟩ ⊗ (nket dim ∣+⟩)).
Proof.
  intros. inversion H.
  - exists 0%R. rewrite eulers0. rewrite Mscale_1_l.
    apply (deutsch_jozsa_constant0 _ _ P). assumption.
  - exists PI. rewrite eulers_identity.
    apply (deutsch_jozsa_constant1 _ _ P). assumption.
Qed.   

Definition perpendicular {n : nat} (ψ ϕ : Vector n) :=
  dot ψ ϕ = 0%R.

Notation "ψ ⟂ ϕ" := (perpendicular ψ ϕ) (at level 20). 

Theorem deutsch_jozsa_balanced_correct : 
  forall (dim : nat) (U : ucom) (P : boolean dim U) (ψ : Vector 2),
  balanced P -> 
  ((uc_eval (S dim) U) × (∣-⟩ ⊗ (nket dim ∣+⟩))) ⟂ (ψ ⊗ (nket dim ∣+⟩)).
Proof.
Admitted.
