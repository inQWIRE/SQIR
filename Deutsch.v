Require Import Quantum.
Require Import List.
Require Import SQIMP.
Require Import UnitarySem.

(* Boolean functions {0,1} -> {0,1} *)
Definition c0 (q r : nat) : ucom := uskip.
Definition c1 (q r : nat) : ucom := X r.
Definition b0 (q r : nat) : ucom := CNOT q r.
Definition b1 (q r : nat) : ucom := CNOT q r; X r.

Definition deutsch (U : nat -> nat -> ucom) := H 0; H 1; U 0 1; H 0.

Definition balanced (q r : nat) (U : nat -> nat -> ucom) := 
  uc_eval 2 (U q r) = uc_eval 2 (b0 q r) \/ uc_eval 2 (U q r) = uc_eval 2 (b1 q r). 

Definition constant (q r : nat) (U : nat -> nat -> ucom) := 
  uc_eval 2 (U q r) = uc_eval 2 (c0 q r) \/ uc_eval 2 (U q r) = uc_eval 2 (c1 q r). 

Open Scope R_scope.

Notation "∣-⟩" := (/√2 .* ∣0⟩ .+ (-/√2) .* ∣1⟩)%C.

(* outer product *)
Definition op {n : nat} (ψ : Vector n) : Density n := ψ × ψ†.

Open Scope C_scope.

(* Remove global phase. *)
Lemma global_phase : forall (n : nat)(ψ : Vector n), op ψ = op ((-1) .* ψ).
Proof.
  intros. unfold op.
  rewrite Mscale_adj. rewrite Mscale_mult_dist_r. rewrite Mscale_mult_dist_l.
  rewrite Cconj_R. rewrite Mscale_assoc.
  symmetry. rewrite <- Mscale_1_l. apply f_equal2. clra. reflexivity.
Qed.

Lemma deutsch_constant_correct : 
  forall (U : nat -> nat -> ucom), (constant 0 1 U) -> 
     op (uc_eval 2 (deutsch U) × (∣0⟩ ⊗ ∣1⟩)) = op (∣0⟩ ⊗ ∣-⟩).
Proof.
  intros.
  unfold constant in H.
  destruct H; unfold deutsch; simpl; rewrite H.
  - unfold uc_eval, ueval1; simpl; unfold pad; simpl. 
    rewrite kron_1_l by (apply WF_hadamard). rewrite kron_1_r. apply f_equal.
    solve_matrix.
  - unfold uc_eval, ueval1. simpl. unfold ueval1. unfold pad. simpl.
    rewrite global_phase. apply f_equal. solve_matrix.
Qed.

Lemma deutsch_balanced_correct :
  forall (U : nat -> nat -> ucom), (balanced 0 1 U) -> 
     op (uc_eval 2 (deutsch U) × (∣0⟩ ⊗ ∣1⟩)) = op (∣1⟩ ⊗ ∣-⟩).
Proof.
  intros. unfold balanced in H.
  destruct H; unfold deutsch; simpl; rewrite H.
  - unfold uc_eval, ueval1. simpl. unfold pad. simpl. unfold ueval_cnot. simpl.
    rewrite kron_1_l by (apply WF_hadamard). rewrite kron_1_r. apply f_equal.
    unfold pad. simpl.
    solve_matrix.
  - unfold uc_eval, ueval1. simpl. unfold ueval_cnot, ueval1. simpl.
    unfold pad. simpl.
    repeat rewrite kron_1_l by (apply WF_hadamard). 
    repeat rewrite kron_1_r. 
    rewrite global_phase. apply f_equal.
    solve_matrix.
Qed.


(* MOVE ELSEWHERE! *)
Fixpoint enumerate_bool_lists (len : nat) : list (list bool) :=
  match len with
  | 0 => []
  | S len' => map (cons true) (enumerate_bool_lists len') ++ map (cons false) (enumerate_bool_lists len')
  end.

Compute (enumerate_bool_lists 2%nat).

 (* Assumes f's domain is {t,f}^len *)
(* Returns the arity of {x | f x = b} *)
Definition count (len : nat) (f : list bool -> bool) (b : bool): nat :=
  length (filter (fun l => (bool_eq (f l) b)) (enumerate_bool_lists len)).


