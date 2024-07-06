Require Export SQIR.UnitaryOps.
Require Import QuantumLib.Measurement.

Module ThreeQubitCode.

Open Scope ucom.

Definition Toffoli_false_fst {dim} (a b c : nat) : base_ucom dim :=
  X a;
CCX a b c;
  X a.


(* q at 0; encoding/decoding ancillae at 1 and 2; and recovery ancillae at 3 and 4. *)
Definition dim : nat := 5.

Module BitFlip.

Definition encode : base_ucom dim := 
  CNOT 0 1; CNOT 0 2.

Theorem encode_correct : forall (α β : C),
  (@uc_eval dim encode) × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ∣0,0,0,0⟩ )
= α .*∣0,0,0,0,0⟩ .+ β .* ∣1,1,1,0,0⟩.
Proof.
  intros.
  simpl.
  autorewrite with eval_db; simpl.
  Qsimpl.
replace (I 8) with (I 2 ⊗ I 2 ⊗ I 2).
  replace (I 4) with (I 2 ⊗ I 2).
  2,3: repeat rewrite id_kron; easy. 
  repeat (distribute_plus;
repeat rewrite <- kron_assoc by auto with wf_db;
          restore_dims).
  repeat rewrite kron_mixed_product.
  Qsimpl.
  autorewrite with ket_db.
rewrite Mplus_comm; easy.
Qed.

Inductive error : Set :=
  | NoError
| BitFlip0
| BitFlip1
  | BitFlip2.

Definition apply_error (e : error) : base_ucom dim :=
match e with
  | NoError => SKIP
  | BitFlip0 => X 0
  | BitFlip1 => X 1
  | BitFlip2 => X 2
  end.

Definition error_syndrome (e : error) : Vector 4 :=
  match e with
  | NoError => ∣0,0⟩
  | BitFlip0 => ∣0,1⟩
  | BitFlip1 => ∣1,0⟩
  | BitFlip2 => ∣1,1⟩
  end.


Definition recover : base_ucom dim := 
  CNOT 0 4; CNOT 1 4;
  CNOT 1 3; CNOT 2 3;
  CNOT 3 4;
  Toffoli_false_fst 3 4 0;
  Toffoli_false_fst 4 3 1;
  CCX 3 4 2.

Definition decode : base_ucom dim :=
  CNOT 0 1;
  CNOT 0 2.

Theorem decode_correct : forall (α β : C) (φ : Vector 4),
  WF_Matrix φ ->
  (@uc_eval dim decode) × ((α .* ∣0,0,0⟩ .+ β .* ∣1,1,1⟩) ⊗ φ)
  = ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ∣0,0⟩ ⊗ φ).
Proof.
  intros.
  simpl.
  autorewrite with eval_db; simpl; Qsimpl.
  rewrite Mmult_assoc.
  replace (I 8) with (I 2 ⊗ I 4) by (
    repeat rewrite id_kron;
    Qsimpl; easy
  ).
  repeat (distribute_plus;
          repeat rewrite <- kron_assoc by auto with wf_db;
          restore_dims).
  autorewrite with ket_db.
  apply Mplus_comm.
Qed.

Definition error_recover_correct (e : error) : forall (α β : C),
  (@uc_eval dim (apply_error e; recover)) × (α .* ∣0,0,0,0,0⟩ .+ β .* ∣1,1,1,0,0⟩) =
  (α .* ∣0,0,0⟩ .+ β .* ∣1,1,1⟩) ⊗ (error_syndrome e).
Proof.
  intros.
  destruct e.
  Local Opaque CCX.
  all : unfold apply_error; unfold recover; simpl.
  all : try rewrite denote_SKIP by (unfold dim; lia); Qsimpl.
  all : repeat rewrite Mmult_assoc.
  all : repeat rewrite Mmult_plus_distr_l.
  all : repeat rewrite Mscale_mult_dist_r.
  all : replace (∣0, 0, 0, 0, 0⟩) with (f_to_vec dim (fun _ => false)).
  all : replace (∣1, 1, 1, 0, 0⟩) with (f_to_vec dim (fun n => n <? 3)).
  10-12,14-16: (
    simpl f_to_vec;
    Qsimpl; easy
  ).
  
  all : repeat (
    first
    [ rewrite f_to_vec_CNOT
    | rewrite f_to_vec_CCX
    | rewrite f_to_vec_X
    ];
    unfold dim; try lia;
    simpl update (* simple `simpl` evaluates the vector *)
  ).

  all : simpl; Qsimpl; try reflexivity.
  all : repeat rewrite <- kron_assoc by auto with wf_db.
  all : solve_matrix.
Qed.


Definition bit_flip_recover (e : error) : base_ucom dim :=
  encode;
  apply_error e;
  recover;
  decode.


Theorem three_code_correct (e : error) : forall (α β : C),
  (@uc_eval dim (bit_flip_recover e) × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ∣0,0,0,0⟩)) = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ∣0,0⟩ ⊗ (error_syndrome e).
Proof.
  intros.
  unfold bit_flip_recover.
  Local Opaque encode apply_error recover decode.
  simpl uc_eval.
  repeat rewrite Mmult_assoc.
  rewrite encode_correct.
  rewrite <- Mmult_assoc with (B := uc_eval (apply_error e)).
  specialize (error_recover_correct e α β) as H.
  simpl in H.
  setoid_rewrite H.
  apply decode_correct.
  destruct e; simpl; auto with wf_db.
Qed.

End BitFlip.

Module PhaseFlip.

Definition encode : base_ucom dim := 
  BitFlip.encode;
  H 0; H 1; H 2.

Theorem encode_correct : forall (α β : C),
  (@uc_eval dim encode) × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ∣0,0,0,0⟩ )
  = α .* ∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣0,0⟩ .+ β .* ∣-⟩ ⊗ ∣-⟩ ⊗ ∣-⟩ ⊗ ∣0,0⟩.
Proof.
  intros.
  simpl.
  specialize (BitFlip.encode_correct α β) as H.
  simpl in H.
  repeat rewrite Mmult_assoc.
  rewrite <- Mmult_assoc with (B := uc_eval (CNOT 0 1)).
  rewrite H.
  autorewrite with eval_db; simpl.
  replace (I 16) with (I 4 ⊗ I 4).
  replace (I 8) with (I 4 ⊗ I 2).
  replace (I 4) with (I 2 ⊗ I 2).
  2,3,4: repeat rewrite id_kron; easy. 
  autorewrite with ket_db.
  repeat (distribute_plus;
          repeat rewrite <- kron_assoc by auto with wf_db;
          restore_dims).
  repeat rewrite kron_mixed_product.
  Qsimpl.

  replace (hadamard × ∣ 0 ⟩) with (∣+⟩).
  replace (hadamard × ∣ 1 ⟩) with (∣-⟩).
  reflexivity.
  all: solve_matrix.
Qed.

Inductive error : Set :=
  | NoError
  | PhaseFlip0
  | PhaseFlip1
  | PhaseFlip2.

Definition apply_error (e : error) : base_ucom dim :=
  match e with
  | NoError => SKIP
  | PhaseFlip0 => SQIR.Z 0
  | PhaseFlip1 => SQIR.Z 1
  | PhaseFlip2 => SQIR.Z 2
  end.

Definition error_syndrome (e : error) : Vector 4 :=
  match e with
  | NoError => ∣0,0⟩
  | PhaseFlip0 => ∣0,1⟩
  | PhaseFlip1 => ∣1,0⟩
  | PhaseFlip2 => ∣1,1⟩
  end.

Definition recover : base_ucom dim := 
  H 0; H 1; H 2;
  BitFlip.recover.

Definition decode := BitFlip.decode.

Definition decode_correct := BitFlip.decode_correct.

Theorem Hplus_spec' : hadamard × ∣+⟩ = ∣0⟩.
Proof.
  replace (∣+⟩) with (∣ + ⟩) by solve_matrix.
  apply Hplus_spec.
Qed.

Theorem Hminus_spec' : hadamard × ∣-⟩ = ∣1⟩.
Proof.
  replace (∣-⟩) with (∣ - ⟩) by solve_matrix.
  apply Hminus_spec.
Qed.

Definition error_recover_correct (e : error) : forall (α β : C),
  (@uc_eval dim (apply_error e; recover)) × (α .* ∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣0,0⟩ .+ β .* ∣-⟩ ⊗ ∣-⟩ ⊗ ∣-⟩ ⊗ ∣0,0⟩) =
  (α .* ∣0,0,0⟩ .+ β .* ∣1,1,1⟩) ⊗ (error_syndrome e).
Proof.
  intros.
  destruct e.

  Local Opaque CCX BitFlip.recover.
  all : simpl.
  all : repeat rewrite Mmult_assoc.
  all : autorewrite with ket_db eval_db; simpl.
  2 : unfold dim; lia.
  all : replace (I 16) with (I 4 ⊗ I 4) by (repeat rewrite id_kron; easy).
  all : replace (I 8) with (I 4 ⊗ I 2) by (repeat rewrite id_kron; easy).
  all : replace (I 4) with (I 2 ⊗ I 2) by (repeat rewrite id_kron; easy).
  all : repeat (
    repeat rewrite <- kron_assoc by auto with wf_db;
    restore_dims
  ).
  all : repeat rewrite kron_mixed_product.
  all : Qsimpl; replace (σz × ∣+⟩) with (∣-⟩) by solve_matrix; 
        replace (σz × ∣-⟩) with (∣+⟩) by solve_matrix. 
  all : repeat rewrite Hplus_spec', Hminus_spec'.
  all : replace (∣ 0 ⟩) with (∣0⟩) by solve_matrix.
  all : replace (∣0⟩) with (f_to_vec 1 (fun _ => false)) by solve_matrix.
  all : replace (∣1⟩) with (f_to_vec 1 (fun _ => true)) by solve_matrix.
  all : restore_dims.
  all : repeat rewrite kron_assoc by auto with wf_db.
  all : repeat (rewrite f_to_vec_merge; restore_dims).
  Local Transparent BitFlip.recover.
  all : simpl uc_eval.
  all : repeat rewrite Mmult_assoc; restore_dims.

  (* Faster that f_to_vec_simpl with 
     transparent CCX *)
  all : repeat (
    first
    [ rewrite f_to_vec_CNOT
    | rewrite f_to_vec_CCX
    | rewrite f_to_vec_X
    ];
    unfold dim; try lia;
    simpl update 
  ).
  all : simpl; Qsimpl.
  all : repeat rewrite <- kron_assoc by auto with wf_db.
  all : reflexivity.
Qed.

(** The rest of the circuit is the same as
    the BitFlip case. *)

Definition phase_flip_recover (e : error) : base_ucom dim :=
  encode;
  apply_error e;
  recover;
  decode.


Theorem three_code_correct (e : error) : forall (α β : C),
  (@uc_eval dim (phase_flip_recover e) × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ∣0,0,0,0⟩)) = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ∣0,0⟩ ⊗ (error_syndrome e).
Proof.
  intros.
  unfold phase_flip_recover.
  Local Opaque encode apply_error recover decode.
  simpl uc_eval.
  repeat rewrite Mmult_assoc.
  rewrite encode_correct.
  rewrite <- Mmult_assoc with (B := uc_eval (apply_error e)).
  specialize (error_recover_correct e α β) as H.
  simpl in H.
  setoid_rewrite H.
  apply decode_correct.
  destruct e; simpl; auto with wf_db.
Qed.

End PhaseFlip.

End ThreeQubitCode.
