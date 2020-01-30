Require Import SQIRE.
Require Import Quantum.

Definition eigenvalue {n} (A : Square n) (λ : C) := 
  exists (v : Vector n), A × v = λ .* v.

Lemma σz_eigenvalue_1 : eigenvalue σz C1.
Proof. exists ∣0⟩. solve_matrix. Qed.

Lemma σz_eigenvalue_m1 : eigenvalue σz (- C1).
Proof. exists ∣1⟩. solve_matrix. Qed.

Definition hermitian {n} (A : Square n) := A = A†.

(* In general, the trace norm of ρ is the sum of the singular values of ρ (i.e.
   the roots of the eigenvalues of ρρ†). When ρ is a Hermitian matrix, the trace
   norm is the sum of the absolute values of the eigenvalues of ρ. 

   --> How should you deal with eigenvalues with multiplicity > 1? *)
(*
Definition trace_norm {n} (A : Square n) (pf : hermitian A) :=
  Csum <some function that gets each eigenvalue> n 
*)

(* Simplest case: fidelity between two pure states *)
Definition fidelity {n} (ϕ ψ : Vector n) :=
  (ϕ ∘ ψ†) * (ϕ ∘ ψ†).

(* Utility for describing superposition states *)


(* Coset representation of modular integers. *)

Definition coset_repr r m : Vector (2^m) := Vsum (f : nat -> nat)