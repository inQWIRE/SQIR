Require DensitySem.
Require Import QWIRE.Dirac.

Import DensitySem.
Local Open Scope com.

(* The bit-flip code *)

Definition encode {n} (q a b : nat) : base_com n := CNOT q a; CNOT q b.
Definition error {n} (a : nat) : base_com n := X a.
Definition extraction {n} (q a b s1 s2 : nat) : base_com n := CNOT a s1; CNOT b s1; CNOT q s2; CNOT b s2; measure s1; measure s2.
Definition correction {n} (q a b s1 s2 : nat) : base_com n := meas s1 (meas s2 (X b) (X a)) (meas s2 (X q) skip).
Definition decode {n} (q a b : nat) : base_com n := encode q a b.

Definition q : nat := 0. 
Definition a : nat := 1. 
Definition b : nat := 2. 
Definition s1 : nat := 3.
Definition s2 : nat := 4.

Definition ec (y : nat): base_com 5 := encode q a b; error y; extraction q a b s1 s2; correction q a b s1 s2; decode q a b.

Definition syndrome (k : nat) : Matrix 4 4 :=
  match k with
  | 0 => ∣0⟩⟨0∣ ⊗ ∣1⟩⟨1∣
  | 1 => ∣1⟩⟨1∣ ⊗ ∣0⟩⟨0∣
  | 2 => ∣1⟩⟨1∣ ⊗ ∣1⟩⟨1∣
  | _ => Zero
  end.
                      
Lemma ec_correct : forall (ρ : Density 2) (k : nat),
    WF_Matrix ρ -> (k <= 2)%nat -> 
    c_eval (ec k) (ρ ⊗ ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣) = (ρ ⊗ ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣ ⊗ syndrome k).
Proof.
  intros ρ k WF H.
  destruct k as [| [| [| k']]]; unfold syndrome. 
  4 : lia.
  - simpl.
    repeat rewrite compose_super_eq.
    unfold compose_super.
    autorewrite with eval_db; simpl.
Admitted.


