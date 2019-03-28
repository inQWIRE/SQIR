(* Unitary superdense coding example (in-progress *)

Require Import Dirac.
Require Import SQIMP.
Require Import UnitarySem.
Open Scope ucom_scope.

Definition a : nat := O.
Definition b : nat := S O.

Definition bell00_u : ucom :=
  H a;
  CNOT a b.

Definition encode_u (b1 b2 : bool): ucom :=
    (if b2 then X a else uskip);
    (if b1 then X a else uskip).

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
Lemma superdense_correct : forall b1 b2, (uc_eval 2 (superdense_u b1 b2)) × ∣ 0,0 ⟩ = ∣ if b1 then S O else O,if b2 then S O else O ⟩.
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
    autorewrite with ket_db; auto with wf_db.
    
    (* What? This is |0,0⟩! *)

    Abort.
(*
    unify_pows_two.
    
    Set Printing All.

    repeat rewrite Mmult_assoc.
    
    

    Search (
    simpl.
    Search 
    Msimpl.


    autorewrite with ket_db C_db.
    replace (Init.Nat.mul (S (S O)) (S (S O))) with (S (S (S (S O)))) by easy.
    autorewrite with ket_db C_db. ; try show_wf.
    replace (Init.Nat.mul (S (S O)) (S (S O))) with (S (S (S (S O)))) by easy.
    autorewrite with ket_db C_db; try show_wf.
    (* need to use coqeulicot tactics to prove this *)
    replace (Cmult (Cmult (Cinv (RtoC (sqrt (IZR (Zpos (xO xH))))))
                          (RtoC (IZR (Zneg xH)))) 
                   (Cinv (RtoC (sqrt (IZR (Zpos (xO xH))))))) 
      with (Copp (Cinv (RtoC (IZR (Zpos (xO xH)))))) by admit.
    repeat (rewrite <- Mplus_assoc).
    replace (S (S (S (S O)))) with (Init.Nat.mul (S (S O)) (S (S O))) by easy.
    simpl_ket_2_qubit.
    autorewrite with ket_db C_db.
    reflexivity.
  - autorewrite with ket_db C_db; try show_wf.
    replace (Init.Nat.mul (S (S O)) (S (S O))) with (S (S (S (S O)))) by easy.
    autorewrite with ket_db C_db; try show_wf.
    replace (Init.Nat.mul (S (S O)) (S (S O))) with (S (S (S (S O)))) by easy.
    autorewrite with ket_db C_db; try show_wf.
Abort. *)
