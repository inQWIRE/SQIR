(* Unitary superdense coding example (in-progress *)

Require Import Dirac.
Require Import SQIMP.
Require Import UnitarySem.
Open Scope ucom_scope.

Require Import Complex.    

Definition a : nat := O.
Definition b : nat := S O.

Definition bell00_u : ucom :=
  H a;
  CNOT a b.

Definition encode_u (b1 b2 : bool): ucom :=
  (if b2 then X a else uskip);
  (if b1 then Z a else uskip).

Definition decode_u : ucom := (* note: this is the reverse of bell00 *)
  CNOT a b;
  H a.

Definition superdense_u (b1 b2 : bool) := bell00_u ; encode_u b1 b2; decode_u.

Close Scope ucom_scope.

(* Rewriting seems to be more cooperative with this definition of 
   kron_mixed_product *)
Lemma kron_mixed_prod2: forall (A : Matrix 2 2) (B : Matrix 2 2) x y,
    (A ⊗ B) × ∣ x,y ⟩ = (A × ∣ x ⟩) ⊗ (B × ∣ y ⟩).
Proof. intros. rewrite kron_mixed_product. reflexivity. Qed.
Hint Rewrite kron_mixed_prod2 : ket_db.

(*Set Printing All.*)

Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.
Coercion bool_to_nat : bool >-> nat.

Lemma superdense_correct : forall b1 b2, (uc_eval 2 (superdense_u b1 b2)) × ∣ 0,0 ⟩ = ∣ b1,b2 ⟩.
Proof.
  intros; simpl.
  replace (ueval_cnot 2 a b) with cnot.
  2:{ unfold ueval_cnot, pad; simpl. solve_matrix. } 
  unfold ueval1.
  unfold pad; Msimpl.
  destruct b1; destruct b2; unfold uc_eval; simpl;
    unfold ueval1, pad; simpl.
  - autorewrite with ket_db; auto with wf_db.
    setoid_rewrite CNOT00_spec.
    setoid_rewrite CNOT10_spec.
    autorewrite with ket_db C_db; auto with wf_db. (* wf_db shouldn't be req'd *)
    setoid_rewrite CNOT10_spec.
    autorewrite with ket_db C_db; auto with wf_db.
    replace (RtoC (-1)%R) with (- C1)%C by lca. (* There shouldn't be Rs here... *)
    autorewrite with C_db.
    rewrite <- Mplus_assoc.
    rewrite (Mplus_comm _ _ (_ .*  ∣ 0, 1 ⟩)).
    rewrite (Mplus_assoc _ _ (_ .*  ∣ 1, 1 ⟩)).    
    simpl_ket_2_qubit. 
    autorewrite with ket_db C_db.
    reflexivity.
  - solve_matrix.
  - solve_matrix.
  - solve_matrix.
Qed.    

(* Maybe a manual proof would be more illustrative? *)