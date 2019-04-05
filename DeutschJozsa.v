Require Import Quantum.
Require Import List.
Require Import SQIMP.
Require Import UnitarySem.


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

Definition balanced (dim : nat) {U : ucom} (P : boolean dim U) : Prop :=
  count P = (2 ^ (dim - 1))%nat.

Definition constant (dim : nat) {U : ucom} (P : boolean dim U) : Prop :=
  count P = 0%nat \/ count P = (2 ^ dim)%nat.

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

Lemma aux2 : forall {m n : nat}(ψ1 ψ2 : Matrix m n), 
    ψ1 ⊗ ∣0⟩ = ψ2 ⊗ ∣0⟩ -> ψ1 = ψ2.
Proof. Admitted.

Lemma WT_boolean : forall (dim : nat) (U : ucom), boolean dim U -> uc_well_typed dim U.
Proof. intros. inversion H; assumption. Qed.
 
Lemma deutsch_jozsa_constant0 : 
  forall (dim : nat) (U : ucom) (P : boolean dim U),
  (count P = 0)%nat -> 
  ((uc_eval (S dim) U) × (∣1⟩ ⊗ (nket dim ∣0⟩))) = (∣1⟩ ⊗ (nket dim ∣0⟩)).
Proof.
  intros. 
  induction P; intros.
  - rewrite u1.
    simpl; Msimpl; reflexivity.
  - simpl in H. lia.
  - intros. inversion H.
    apply aux in H1. inversion H1. 
    rewrite H0. rewrite H2.
    apply IHP1 in H0. 
    apply IHP2 in H2. 
    clear H1. clear H. clear IHP1. clear IHP2.
    replace (S (S dim))%nat with (S dim + 1)%nat by lia.
    rewrite <- pad_dims by apply u4.
    rewrite e. clear e. 
    replace (S dim) with (dim + 1)%nat in H0 by lia.
    replace (S dim) with (dim + 1)%nat in H2 by lia.
    rewrite <- pad_dims in H0 by apply u0.
    rewrite <- pad_dims in H2 by apply u3.
    destruct dim.
    + inversion P1.
    + clear P1. clear P2.
      replace (nket (S dim) ∣0⟩) with (nket dim ∣0⟩ ⊗ ∣0⟩) in * by reflexivity.
      show_dimensions.
      replace (2 ^ (S dim))%nat with (2 ^ dim * 2)%nat in * by unify_pows_two. 
      replace (2 ^ 1)%nat with 2%nat in * by (simpl; reflexivity).
      replace (kron' 2 1 (2 ^ dim * 2) 1 ∣1⟩ (kron' (2 ^ dim) 1 2 1 (nket dim ∣0⟩) ∣0⟩)) with (kron' 2 1 (2 ^ dim * 2) (1 * 1) ∣1⟩ (kron' (2 ^ dim) 1 2 1 (nket dim ∣0⟩) ∣0⟩)) in * by reflexivity.
      rewrite <- kron_assoc in *.
      hide_dimensions. show_dimensions.
      replace (2 ^ (S dim + 1))%nat with (2 * 2 ^ dim * 2)%nat in * by unify_pows_two.
      replace
        (Mmult' (2 * 2 ^ dim * 2) (2 * 2 ^ dim * 2) 1
         (kron' (2 ^ dim * 2) (2 ^ dim * 2) 2 2 (uc_eval (S dim) u1) (I 2))
         (kron' (2 * 2 ^ dim) (1 * 1) 2 1 (kron' 2 1 (2 ^ dim) 1 ∣1⟩ (nket dim ∣0⟩))
            ∣0⟩))
      with
        (Mmult' (2 * 2 ^ dim * 2) (2 * 2 ^ dim * 2) (1 * 1 * 1)
         (kron' (2 ^ dim * 2) (2 ^ dim * 2) 2 2 (uc_eval (S dim) u1) (I 2))
         (kron' (2 * 2 ^ dim) (1 * 1) 2 1 (kron' 2 1 (2 ^ dim) 1 ∣1⟩ (nket dim ∣0⟩))
            ∣0⟩)) in * by (simpl; reflexivity).
      replace 
        (Mmult' (2 * 2 ^ dim * 2) (2 * 2 ^ dim * 2) 1
         (kron' (2 ^ dim * 2) (2 ^ dim * 2) 2 2 (uc_eval (S dim) u2) (I 2))
         (kron' (2 * 2 ^ dim) (1 * 1) 2 1 (kron' 2 1 (2 ^ dim) 1 ∣1⟩ (nket dim ∣0⟩))
            ∣0⟩))
      with
        (Mmult' (2 * 2 ^ dim * 2) (2 * 2 ^ dim * 2) (1 * 1 * 1)
         (kron' (2 ^ dim * 2) (2 ^ dim * 2) 2 2 (uc_eval (S dim) u2) (I 2))
         (kron' (2 * 2 ^ dim) (1 * 1) 2 1 (kron' 2 1 (2 ^ dim) 1 ∣1⟩ (nket dim ∣0⟩))
            ∣0⟩)) in * by (simpl; reflexivity).
      hide_dimensions.
      replace (2 ^ S dim)%nat with (2 * 2 ^ dim)%nat in * by (simpl; reflexivity).
      replace (2 * 2 ^ dim)%nat with (2 ^ dim * 2)%nat in * by omega.
      rewrite kron_mixed_product in *.
      rewrite Mmult_1_l in * by auto with wf_db.
      apply aux2 in H0. apply aux2 in H2.
      replace (S (0 + 0))%nat with 1%nat by (simpl; reflexivity).
      replace (∣1⟩ ⊗ nket (S (S dim)) ∣0⟩) with (∣1⟩ ⊗ nket (S dim) ∣0⟩ ⊗ ∣0⟩).
      2 : { 
        replace (nket (S (S dim)) ∣0⟩) with (nket (S dim) ∣0⟩ ⊗ ∣0⟩) by reflexivity.
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
      rewrite Mmult_1_l by auto with wf_db.
      apply f_equal2; try reflexivity.
      rewrite Heqd, HeqM1, HeqM2, Heqψ, Heqq0, Heqq1 in *.
      replace (nket (S dim) ∣0⟩) with (nket dim ∣0⟩ ⊗ ∣0⟩) by reflexivity.
      show_dimensions.
      replace (2 ^ S dim)%nat with (2 ^ dim * 2)%nat by unify_pows_two.
      clear Heqd. clear HeqM1. clear HeqM2. clear Heqψ. clear Heqq0. clear Heqq1.
      clear q0. clear q1. clear ψ. clear M2. clear M1.
      replace 
        (kron' 2 1 (2 ^ dim * 2) 1 ∣1⟩ (kron' (2 ^ dim) 1 2 1 (nket dim ∣0⟩) ∣0⟩))
      with
        (kron' 2 1 (2 ^ dim * 2) (1 * 1) ∣1⟩ (kron' (2 ^ dim) 1 2 1 (nket dim ∣0⟩) ∣0⟩)) by (simpl; reflexivity).
      hide_dimensions.
      rewrite <- kron_assoc.
      rewrite Mmult_plus_distr_r.
      replace (2 ^ dim * 2)%nat with (2 * 2 ^ dim)%nat by unify_pows_two.
      repeat rewrite kron_mixed_product.
      replace (∣0⟩⟨0∣ × ∣0⟩) with (∣0⟩) by solve_matrix.
      replace (∣1⟩⟨1∣ × ∣0⟩) with (@Zero 2 1)%nat by solve_matrix.
      replace (2 ^ dim * 2)%nat with (2 * 2 ^ dim)%nat in H0 by unify_pows_two.
      rewrite H0.
      rewrite kron_0_r.
      rewrite Mplus_0_r. reflexivity.
Qed.


Lemma deutsch_jozsa_constant1 : 
  forall (dim : nat) (U : ucom) (P : boolean dim U),
  (count P = 2 ^ dim)%nat -> 
  ((uc_eval (S dim) U) × (∣1⟩ ⊗ (nket dim ∣0⟩))) = (-1)%R .* (∣1⟩ ⊗ (nket dim ∣0⟩)).
Proof.
Admitted.

Definition proportional {n : nat} (ψ ϕ : Vector n) := 
  exists θ, ψ = Cexp θ .* ϕ. 

Notation "ψ ∝ ϕ" := (proportional ψ ϕ) (at level 20).

Theorem deutsch_jozsa_constant_correct :
  forall (dim : nat) (U : ucom) (P : boolean dim U),
  constant dim P -> 
  ((uc_eval (S dim) U) × (∣1⟩ ⊗ (nket dim ∣0⟩))) ∝ (∣1⟩ ⊗ (nket dim ∣0⟩)).
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
  balanced dim P -> 
  ((uc_eval (S dim) U) × (∣1⟩ ⊗ (nket dim ∣0⟩))) ⟂ (ψ ⊗ (nket dim ∣0⟩)).
Proof.
Admitted.


