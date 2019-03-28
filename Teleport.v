Require Import SQIMP.
Require Import UnitarySem.

Definition bell (c b : nat) : ucom := H c ; CNOT c b.
Definition alice (a c : nat) : ucom := CNOT a c ; H a.
Definition bob (a c b: nat) : ucom := CNOT c b; CZ a b.
Definition teleport (a c b : nat) : ucom := alice a c; bob a c b.


Open Scope R_scope.

Notation "∣+⟩" := (1/√2 .* ∣0⟩ .+ 1/√2 .* ∣1⟩)%C.

Definition epr00 : Vector 4 :=
  fun x y => match x, y with
             | 0, 0 => (1/√2)%C
             | 3, 0 => (1/√2)%C
             | _, _ => 0%C
             end.

Lemma epr_correct : 
  forall (ψ : Vector 2), WF_Matrix _ _ ψ -> (uc_eval 3 (bell 1 2)) × (ψ ⊗ ∣0⟩ ⊗ ∣0⟩) = ψ ⊗ epr00. 
Proof.
  intros.
  unfold bell. simpl. unfold ueval_cnot, ueval1. simpl. unfold pad. simpl.
  solve_matrix.
Qed.

Lemma teleport_correct : forall (ψ : Vector 2), 
    WF_Matrix _ _ ψ -> uc_eval 3 (teleport 0 1 2) × (ψ ⊗ epr00) = (∣+⟩ ⊗ ∣+⟩ ⊗ ψ).
Proof.
  intros.
  unfold teleport. simpl.
  unfold ueval1.
  unfold ueval_cnot, pad. simpl.
  solve_matrix;
  remember (ψ 0%nat 0%nat) as a; remember (ψ 1%nat 0%nat) as b.
  all : try rewrite (Cmult_comm a _); try rewrite (Cmult_comm b _).
  all : repeat rewrite Cmult_assoc.
  all : remember (/ √ 2 * / √ 2 * / √ 2 * b)%C as β.
  all : remember (/ √ 2 * / √ 2 * / √ 2 * a)%C as α.
  all : try rewrite (Copp_mult_distr_r (/√2)%C _).
  all : rewrite <- Cmult_plus_distr_l.
  all : repeat rewrite Cplus_assoc.
  all : try rewrite Copp_plus_distr; try rewrite Copp_involutive.
  all : try rewrite Cplus_assoc.
  all : try rewrite <- (Cplus_assoc α β α); try rewrite <- (Cplus_assoc α β (-α)). 
  all : rewrite (Cplus_comm β _); rewrite Cplus_assoc.
  all : autorewrite with C_db; try rewrite <- Cplus_assoc; autorewrite with C_db; rewrite Cdouble.
  all : try rewrite Heqα; try rewrite Heqβ.
  all : rewrite <- Cmult_plus_distr_l; repeat rewrite Cmult_assoc.
  all : autorewrite with C_db.
  all : rewrite <- (Cmult_assoc (/2) _ _); autorewrite with C_db.
  all : rewrite Cmult_assoc.
  all : rewrite <- (Cmult_assoc (/2) _ _); autorewrite with C_db; reflexivity.
Qed.

