Require Import Vectors.Fin.
Require Export SQIR.UnitaryOps.

Module NineQubitCode.

Open Scope ucom.
Open Scope nat_scope.

Definition dim : nat := 9.

(** 
  Blocks
 *)

(* Encoded blocks *)
Definition block_no := Fin.t 3.

(* Qubits in a single block *)
Definition block_offset := Fin.t 3.

Definition block_to_qubit (n : block_no) (off : block_offset) : nat :=
  proj1_sig (Fin.to_nat n) * 3 + proj1_sig (Fin.to_nat off).

Compute block_to_qubit (@Fin.of_nat_lt 2 3 ltac:(lia)) (@Fin.of_nat_lt 2 3 ltac:(lia)).

(**
  Encoding
 *)

Definition encode_block (n : block_no) : base_ucom dim :=
  let q0 := proj1_sig (Fin.to_nat n) * 3 in
  let q1 := q0 + 1 in
  let q2 := q0 + 2 in
  CNOT q0 q1;
  CNOT q0 q2.

Definition encode : base_ucom dim :=
  CNOT 0 3; CNOT 0 6;
  H 0; H 3; H 6;
  encode_block (@Fin.of_nat_lt 0 3 ltac:(lia));
  encode_block (@Fin.of_nat_lt 1 3 ltac:(lia));
  encode_block (@Fin.of_nat_lt 2 3 ltac:(lia)).

Theorem encode_correct (α β : C) :
   (@uc_eval dim encode) × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ 8 ⨂ ∣0⟩ )
   = /C2 .* (/√ 2 .* (α .* 3 ⨂ (∣0,0,0⟩ .+            ∣1,1,1⟩)))
  .+ /C2 .* (/√ 2 .* (β .* 3 ⨂ (∣0,0,0⟩ .+  (-1)%R .* ∣1,1,1⟩))).
Proof.
  simpl. Qsimpl.

  replace (∣0⟩) with (f_to_vec 1 (fun _ => false)) by lma'.
  replace (∣1⟩) with (f_to_vec 1 (fun _ => true)) by lma'.
  restore_dims.
  replace (∣0,0,0⟩) with (f_to_vec 3 (fun _ => false)) by lma'.
  replace (∣1,1,1⟩) with (f_to_vec 3 (fun _ => true)) by lma'.

  repeat rewrite Mmult_assoc.
  rewrite kron_plus_distr_r.
  repeat rewrite Mmult_plus_distr_l.
  distribute_scale.
  repeat rewrite Mscale_mult_dist_r.
  restore_dims.
  repeat rewrite kron_assoc by auto 10 with wf_db.
  repeat (rewrite f_to_vec_merge; restore_dims).
  repeat rewrite f_to_vec_CNOT; try lia.
  simpl update.
  
  repeat  (
    rewrite f_to_vec_H; try lia;
    simpl update; simpl b2R;
    restore_dims;
    repeat rewrite Mmult_plus_distr_l;
    repeat rewrite Mscale_mult_dist_r
  ).
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mscale_mult_dist_r.
  
  repeat (rewrite f_to_vec_CNOT; try lia; try rewrite kron_1_l; simpl update).
  simpl. Qsimpl.

  replace (0 * PI)%R with 0%R by lra.
  replace (1 * PI)%R with PI by lra.
  autorewrite with Cexp_db.
  group_radicals.
  repeat rewrite Mscale_1_l.
  
  repeat rewrite <- Mscale_plus_distr_r.
  repeat rewrite kron_plus_distr_r.
  repeat rewrite kron_plus_distr_l.
  repeat rewrite Mplus_assoc.
  f_equal.
  - repeat rewrite Mscale_assoc.
    replace (α * / √ 2 * / √ 2 * / √ 2)%C with (/√ 2 * / C2 * α)%C.
    2: {
      (* why does lca not work here? *)
      rewrite Cmult_comm.
      do 2 rewrite <- Cmult_assoc.
      f_equal. f_equal.
      symmetry. apply Cinv_sqrt2_sqrt.
    }
    repeat (rewrite <- kron_assoc by auto 10 with wf_db; restore_dims).
    reflexivity.
  - do 2 (
      repeat rewrite Mscale_assoc;
      repeat rewrite (Cmult_comm (-1)%R _);
      repeat rewrite <- (Mscale_assoc _ _ _ (-1)%R _);
      repeat rewrite <- Mscale_plus_distr_r
    ).
    repeat rewrite Mscale_assoc.
    replace (β * / √ 2 * / √ 2 * / √ 2)%C with (/ √ 2 * / C2 * β)%C.
    2: {
      (* why does lca not work here? *)
      rewrite Cmult_comm.
      do 2 rewrite <- Cmult_assoc.
      f_equal. f_equal.
      symmetry. apply Cinv_sqrt2_sqrt.
    }
    f_equal.
    repeat rewrite Mscale_plus_distr_r.
    distribute_scale.
    repeat (rewrite <- kron_assoc by auto 10 with wf_db; restore_dims).
    repeat rewrite Mplus_assoc.
    reflexivity.
Qed.


(**
  Errors
 *)

Inductive phase_flip_error (n : block_no) : Set :=
  | OnePhaseFlip (off : block_offset)
  | MorePhaseFlip (e : phase_flip_error n) (off : block_offset).


Inductive bit_flip_error : Set :=
  | OneBitFlip (n : block_no) (off : block_offset)
  | TwoBitFlip (n₁ n₂ : block_no) (h : n₁ <> n₂) (off₁ off₂ : block_offset)
  | ThreeBitFlip (off₁ off₂ off₃ : block_offset).

Inductive error : Set :=
  | NoError
  | PhaseFlipError (n : block_no) (e : phase_flip_error n)
  | BitFlipError (e : bit_flip_error)
  | BothErrors (n : block_no) (e₁ : phase_flip_error n) (e₂ : bit_flip_error).

Fixpoint apply_phase_flip_error {n} (e : phase_flip_error n) : base_ucom dim :=
  match e with
  | OnePhaseFlip _ off => SQIR.Z (proj1_sig (Fin.to_nat off))
  | MorePhaseFlip _ e off => SQIR.Z (proj1_sig (Fin.to_nat off)); apply_phase_flip_error e
  end.

Definition apply_bit_flip_error (e : bit_flip_error) : base_ucom dim :=
  match e with
  | OneBitFlip n off => X (block_to_qubit n off)
  | TwoBitFlip n₁ n₂ _ off₁ off₂ => (X (block_to_qubit n₁ off₁)); (X (block_to_qubit n₂ off₂))
  | ThreeBitFlip off₁ off₂ off₃ => (
    let q1 := block_to_qubit (@Fin.of_nat_lt 0 3 ltac:(lia)) off₁ in
    let q2 := block_to_qubit (@Fin.of_nat_lt 1 3 ltac:(lia)) off₂ in
    let q3 := block_to_qubit (@Fin.of_nat_lt 2 3 ltac:(lia)) off₃ in
    X q1; X q2; X q3
  )
  end.

Definition apply_error (e : error) : base_ucom dim :=
  match e with
  | NoError => SKIP
  | PhaseFlipError _ e => apply_phase_flip_error e
  | BitFlipError e => apply_bit_flip_error e
  | BothErrors _ e₁ e₂ => apply_phase_flip_error e₁; apply_bit_flip_error e₂
  end.

End NineQubitCode.
