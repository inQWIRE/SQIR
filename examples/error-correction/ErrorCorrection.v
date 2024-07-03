Require Export SQIR.UnitaryOps.
Require Import QuantumLib.Measurement.

Module ThreeQubitCode.

Open Scope ucom.

(* q at 0; encoding/decoding ancillae at 1 and 2; and recovery ancillae at 3 and 4. *)
Definition dim : nat := 5.

Definition encode : base_ucom dim := 
  CNOT 0 1; CNOT 0 2.

Theorem encode_correct : forall (α β : C),
  (@uc_eval dim encode) × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ∣0,0,0,0⟩ )
  = α .* ∣0,0,0,0,0⟩ .+ β .* ∣1,1,1,0,0⟩.
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

Definition Toffoli_false_fst {dim} (a b c : nat) : base_ucom dim :=
  X a;
  CCX a b c;
  X a.

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
  all : try rewrite denote_SKIP; Qsimpl.
  2 : unfold dim; lia.
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


End ThreeQubitCode.
