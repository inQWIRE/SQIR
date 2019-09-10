Require Import UnitarySem.
Require Import Proportional.
Require Import QWIRE.Dirac.

Open Scope ucom.

(* Boolean functions {0,1} -> {0,1} *)
Definition f0 : base_ucom 2 := SKIP.
Definition f1 : base_ucom 2 := X 1.
Definition f2 : base_ucom 2 := CNOT 0 1.
Definition f3 : base_ucom 2 := CNOT 0 1; X 1.

Definition deutsch (c : base_ucom 2) := H 0; H 1; c; H 0.

Definition constant (c : base_ucom 2) := c ≡ f0 \/ c ≡ f1. 

Definition balanced (c : base_ucom 2) := c ≡ f2 \/ c ≡ f3. 

Lemma deutsch_constant_correct :
  forall (c : base_ucom 2), constant c -> ((uc_eval (deutsch c)) × ∣0,1⟩) ∝ (∣0⟩ ⊗ ∣-⟩).
Proof.
  intros.
  unfold constant in H.
  destruct H; unfold deutsch; simpl; rewrite H.
  - exists 0. autorewrite with Cexp_db.
    autorewrite with eval_db; simpl; try lia.
    solve_matrix. 
  - exists PI. autorewrite with Cexp_db.
    unfold f1. 
    autorewrite with eval_db; simpl.
    solve_matrix. 
Qed.

Lemma deutsch_balanced_correct :
  forall (c : base_ucom 2), balanced c -> ((uc_eval (deutsch c)) × ∣0,1⟩) ∝ (∣1⟩ ⊗ ∣-⟩).
Proof.
  intros. 
  unfold balanced in H.
  destruct H; unfold deutsch; simpl; rewrite H.
  - exists 0. autorewrite with Cexp_db.
    unfold f2.
    autorewrite with eval_db; simpl.
    solve_matrix.
  - exists PI. autorewrite with Cexp_db.
    unfold f3; simpl.
    autorewrite with eval_db; simpl. 
    solve_matrix.
Qed.