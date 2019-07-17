Require Import UnitarySem.
Require Import QWIRE.Dirac.

Open Scope ucom.

(* Boolean functions {0,1} -> {0,1} *)
Definition f0 : ucom 2 := uskip.
Definition f1 : ucom 2 := X 1.
Definition f2 : ucom 2 := CNOT 0 1.
Definition f3 : ucom 2 := CNOT 0 1; X 1.

Definition deutsch (c : ucom 2) := H 0; H 1; c; H 0.

Definition constant (c : ucom 2) := c ≡ f0 \/ c ≡ f1. 

Definition balanced (c : ucom 2) := c ≡ f2 \/ c ≡ f3. 

(* Relation to ignore global phases. *)
Definition proportional {n : nat} (ψ ϕ : Vector n) := 
  exists θ, ψ = Cexp θ .* ϕ. 
Infix "∝" := proportional (at level 20).

Lemma deutsch_constant_correct :
  forall (c : ucom 2), constant c -> ((uc_eval (deutsch c)) × ∣0,1⟩) ∝ (∣0⟩ ⊗ ∣-⟩).
Proof.
  intros.
  unfold constant in H.
  destruct H; unfold deutsch; simpl; rewrite H.
  - exists 0. rewrite eulers0. 
    unfold uc_eval, ueval1, pad; simpl.
    solve_matrix. 
  - exists PI. rewrite eulers_identity. 
    unfold uc_eval, ueval1, pad; simpl.
    solve_matrix. 
Qed.

Lemma deutsch_balanced_correct :
  forall (c : ucom 2), balanced c -> ((uc_eval (deutsch c)) × ∣0,1⟩) ∝ (∣1⟩ ⊗ ∣-⟩).
Proof.
  intros. 
  unfold balanced in H.
  destruct H; unfold deutsch; simpl; rewrite H.
  - exists 0. rewrite eulers0. 
    unfold uc_eval, ueval1, ueval_cnot, pad; simpl.
    solve_matrix.
  - exists PI. rewrite eulers_identity. 
    unfold uc_eval, ueval1, ueval_cnot, pad; simpl. 
    solve_matrix.
Qed.