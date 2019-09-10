Require Import QWIRE.Dirac.
Require Import UnitarySem.
Local Open Scope ucom.    

Definition a : nat := O.
Definition b : nat := S O.

Definition bell00_u : base_ucom 2 :=
  H a;
  CNOT a b.

Definition encode_u (b1 b2 : bool): base_ucom 2 :=
  (if b2 then X a else SKIP);
  (if b1 then Z a else SKIP).

Definition decode_u : base_ucom 2 := (* note: this is the reverse of bell00 *)
  CNOT a b;
  H a.

Definition superdense_u (b1 b2 : bool) := bell00_u ; encode_u b1 b2; decode_u.

Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.
Coercion bool_to_nat : bool >-> nat.

Lemma superdense_correct : forall b1 b2, (uc_eval (superdense_u b1 b2)) × ∣ 0,0 ⟩ = ∣ b1,b2 ⟩.
Proof.
  intros; simpl.
  autorewrite with eval_db.
  bdestructΩ (a + 1 <=? 2).
  Msimpl.
  simpl. replace 4%nat with (2*2)%nat by lia.
  replace (∣1⟩⟨1∣ ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 2) with cnot by solve_matrix.
  destruct b1; destruct b2; autorewrite with eval_db; simpl; try lia.
  (* At this point we have four cases corresponding to the values of b1 and b2. *)
  (* We'll do the first case (mostly) manually. *)
  - repeat rewrite kron_1_l; auto with wf_db.
    repeat rewrite Mmult_assoc.
    restore_dims; rewrite kron_mixed_product. 
    rewrite Mmult_1_l; auto with wf_db.
    rewrite H0_spec. 
    rewrite kron_plus_distr_r.
    repeat rewrite Mmult_plus_distr_l.
    repeat rewrite Mscale_kron_dist_l.
    repeat rewrite Mscale_mult_dist_r.
    rewrite CNOT00_spec.
    rewrite CNOT10_spec.
    repeat rewrite kron_mixed_product. 
    repeat rewrite Mmult_1_l; auto with wf_db.
    rewrite X0_spec; rewrite X1_spec.
    rewrite Z0_spec; rewrite Z1_spec.
    rewrite Mscale_kron_dist_l.
    repeat rewrite Mscale_mult_dist_r.
    rewrite CNOT10_spec.
    rewrite CNOT01_spec.
    repeat rewrite kron_mixed_product. 
    repeat rewrite Mmult_1_l; auto with wf_db.
    rewrite H0_spec. 
    rewrite H1_spec. 
    repeat rewrite kron_plus_distr_r.
    repeat rewrite Mscale_kron_dist_l.
    repeat rewrite Mscale_plus_distr_r.
    repeat rewrite Mscale_assoc.
    rewrite Mplus_assoc.
    rewrite (Mplus_comm _ _ (_ .* ∣ 1, 1 ⟩)).
    repeat rewrite <- Mplus_assoc.
    rewrite (Mplus_assoc _ _ _ (_ .* ∣ 1, 1 ⟩)).
    repeat rewrite <- Mscale_plus_distr_l.
    replace (RtoC (-1)%R) with (- C1)%C by lca.
    autorewrite with C_db.
    rewrite Mscale_0_l.
    rewrite Mplus_0_l.
    rewrite Mscale_1_l.
    reflexivity.
  (* We'll do the second case with a little more automation. *)
  - Msimpl. repeat rewrite Mmult_assoc.
    restore_dims; rewrite kron_mixed_product. 
    autorewrite with ket_db; auto with wf_db.
    repeat rewrite kron_mixed_product. 
    autorewrite with ket_db; auto with wf_db.
    repeat rewrite kron_mixed_product.
    autorewrite with ket_db; auto with wf_db.
    rewrite Mplus_assoc.
    rewrite (Mplus_comm _ _ (_ .* ∣ 1, 0 ⟩)).
    repeat rewrite <- Mplus_assoc.
    rewrite (Mplus_assoc _ _ _ (_ .* ∣ 1, 0 ⟩)).
    repeat rewrite <- Mscale_plus_distr_l.
    replace (RtoC (-1)%R) with (- C1)%C by lca.
    autorewrite with C_db.
    rewrite Mscale_0_l.
    rewrite Mplus_0_l.
    rewrite Mscale_1_l.
    reflexivity.
  (* We'll do the last two cases fully automatically. *)
  - solve_matrix.
  - solve_matrix.
Qed.    
