Require Import Quantum.
Require Import List.
Require Import SQIMP.
Require Import UnitarySem.

Open Scope ucom.

(* Boolean functions {0,1} -> {0,1} *)
Definition c0 (q r : nat) : ucom := uskip.
Definition c1 (q r : nat) : ucom := X r.
Definition b0 (q r : nat) : ucom := CNOT q r.
Definition b1 (q r : nat) : ucom := CNOT q r; X r.

Inductive boolean : forall dim : nat, ucom -> Set :=
  | boolean_I : forall u, u ≡ uskip -> boolean 1 u
  | boolean_X : forall u, u ≡ (X 0) -> boolean 1 u
  | boolean_U : forall u u1 u2 dim, boolean dim u1 -> boolean dim u2 ->
                uc_eval (S dim) u = (∣0⟩⟨0∣ ⊗ uc_eval dim u1) .+ (∣1⟩⟨1∣ ⊗ uc_eval dim u2) ->
                boolean (S dim) u.
  
Fixpoint count {dim : nat} {U : ucom} (P : boolean dim U)  : nat :=
  match P with
  | boolean_I _ _ => 0
  | boolean_X _ _ => 1
  | boolean_U u u1 u2 dim P1 P2 P => count P1 + count P2
  end.

Definition deutsch1 (U : nat -> nat -> ucom) := (H 0; H 1; U 0 1; H 0)%nat.

Definition balanced1 (q r : nat) (U : nat -> nat -> ucom) := 
  uc_eval 2 (U q r) = uc_eval 2 (b0 q r) \/ uc_eval 2 (U q r) = uc_eval 2 (b1 q r). 

Definition constant1 (q r : nat) (U : nat -> nat -> ucom) := 
  uc_eval 2 (U q r) = uc_eval 2 (c0 q r) \/ uc_eval 2 (U q r) = uc_eval 2 (c1 q r). 

Notation "∣-⟩" := (/√2 .* ∣0⟩ .+ (-/√2) .* ∣1⟩)%C.

(* outer product *)
Definition op {n : nat} (ψ : Vector n) : Density n := ψ × ψ†.

(* Remove global phase. *)
Lemma global_phase : forall (n : nat) (ψ : Vector n), op ψ = op (-1 .* ψ).
Proof.
  intros. unfold op.
  rewrite Mscale_adj. rewrite Mscale_mult_dist_r. rewrite Mscale_mult_dist_l.
  rewrite Cconj_R. rewrite Mscale_assoc.
  symmetry. rewrite <- Mscale_1_l. apply f_equal2. lca. reflexivity.
Qed.

Definition proportional {n : nat} (ψ ϕ : Vector n) := 
  exists θ, ψ = Cexp θ .* ϕ. 

Notation "ψ ∝ ϕ" := (proportional ψ ϕ) (at level 20).

Lemma deutsch1_constant_correct :
  forall (U : nat -> nat -> ucom), (constant1 0 1 U) ->
     (uc_eval 2 (deutsch1 U) × (∣0⟩ ⊗ ∣1⟩)) ∝ (∣0⟩ ⊗ ∣-⟩).
Proof.
  intros.
  unfold constant in H.
  destruct H; unfold deutsch1; simpl; rewrite H.
  - exists 0. rewrite eulers0. unfold uc_eval, ueval1; simpl; unfold pad; simpl. 
    rewrite kron_1_l by (apply WF_hadamard). rewrite kron_1_r. 
    solve_matrix.
  - exists PI. rewrite eulers_identity. 
    unfold uc_eval, ueval1. simpl. unfold ueval1. unfold pad. simpl.
    solve_matrix. 
Qed.

Lemma deutsch1_balanced_correct :
  forall (U : nat -> nat -> ucom), (balanced1 0 1 U) -> 
     (uc_eval 2 (deutsch1 U) × (∣0⟩ ⊗ ∣1⟩)) ∝ (∣1⟩ ⊗ ∣-⟩).
Proof.
  intros. unfold balanced1 in H.
  destruct H; unfold deutsch1; simpl; rewrite H.
  - exists 0. rewrite eulers0. 
    unfold uc_eval, ueval1. simpl. unfold pad. simpl. unfold ueval_cnot. simpl.
    rewrite kron_1_l by (apply WF_hadamard). rewrite kron_1_r. 
    unfold pad. simpl.
    solve_matrix.
  - exists PI. rewrite eulers_identity. 
    unfold uc_eval, ueval1. simpl. unfold ueval_cnot, ueval1. simpl.
    unfold pad. simpl.
    repeat rewrite kron_1_l by (apply WF_hadamard). 
    repeat rewrite kron_1_r. 
    solve_matrix.
Qed.