Require Import SQIR.
Require DensitySem.
Require NDSem.
(*Require Import QWIRE.Dirac.*)

Local Open Scope com.

(** The 3-qubit bit-flip code **)

Definition q  : nat := 0. (* input qubit *)
Definition a1 : nat := 1. (* a1, a2 ancilla qubits to store encoding *)
Definition a2 : nat := 2.
Definition s1 : nat := 3. (* s1, s2 ancilla qubits to store syndrome *)
Definition s2 : nat := 4.

Definition encode : base_com 5 := CNOT q a1; CNOT q a2.
Definition error (k : nat) : base_com 5 := X k.
Definition extract : base_com 5 := 
  CNOT a1 s1; CNOT a2 s1; CNOT q s2; CNOT a2 s2; measure s1; measure s2.
Definition correct : base_com 5 := 
  meas s1 (meas s2 (X a2) (X a1)) (meas s2 (X q) skip).
Definition decode : base_com 5 := encode.
Definition ec (k : nat): base_com 5 := encode; error k; extract; correct; decode.

(* Proof with density matrix semantics *)
Module DensityQEC.
Import DensitySem.

Definition ρ0 := ∣0⟩⟨0∣.
Definition ρ1 := ∣1⟩⟨1∣.
Definition syndrome (k : nat) : Matrix 4 4 :=
  match k with
  | 0 => ρ0 ⊗ ρ1
  | 1 => ρ1 ⊗ ρ0
  | 2 => ρ1 ⊗ ρ1
  | _ => Zero
  end.
                   
Lemma ec_correct : forall (ρ : Density 2) (k : nat),
    WF_Matrix ρ -> (k <= 2)%nat -> 
    c_eval (ec k) (ρ ⊗ ρ0 ⊗ ρ0 ⊗ ρ0 ⊗ ρ0) = (ρ ⊗ ρ0 ⊗ ρ0 ⊗ syndrome k).
Proof.
  intros ρ k WF H.
  destruct k as [| [| [| ?]]]; unfold syndrome. 
  4 : lia.
  (* three cases depending on where the error occurred (k = 1,2,3) *)
  - simpl.
    unfold compose_super.
    repeat rewrite compose_super_eq.
    unfold compose_super.
    (* blah *)
Admitted.

End DensityQEC.

(* Proof with nondeterministic semantics *)
Module NDQEC.
Import NDSem.

(* Copied from Teleport.v -- move somewhere else *)
Definition proportional {m n : nat} (A B : Matrix m n) := 
  exists s, A = s .* B. 
Infix "∝" := proportional (at level 70).

Definition syndrome (k : nat) : Vector 4 :=
  match k with
  | 0 => ∣ 0 , 1 ⟩
  | 1 => ∣ 1 , 0 ⟩
  | 2 => ∣ 1 , 1 ⟩
  | _ => Zero
  end.
                   
Lemma ec_correct : forall (ψ ψ' : Vector 2) (k : nat),
  WF_Matrix ψ -> (k <= 2)%nat -> 
  ec k / (ψ  ⊗ ∣ 0 , 0 , 0 , 0 ⟩) ⇩ ψ' -> ψ' ∝ ψ  ⊗ ∣ 0 , 0 ⟩ ⊗ syndrome k.  
Proof.
  intros ψ ψ' k WF Hk H.
Admitted.

End NDQEC.
