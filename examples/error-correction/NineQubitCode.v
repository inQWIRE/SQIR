Require Export SQIR.UnitaryOps.
Require Export QuantumLib.Measurement.

Require Import Common.
Import Common.

Module NineQubitCode.

Local Open Scope ucom.
Local Open Scope nat_scope.

Notation dim := 9%nat.
Notation block_dim := 3%nat.

Local Opaque CCX.

(**
  Utilities
  *)

Ltac compute_vec :=
  simpl uc_eval;
  repeat rewrite Mmult_assoc; restore_dims;
  repeat Common.f_to_vec_simpl_light;
  simpl;
  replace (0 * PI)%R with 0%R by lra;
  replace (1 * PI)%R with PI by lra;
  autorewrite with Cexp_db;
  repeat rewrite Mscale_1_l;
  restore_dims;
  autorewrite with ket_db.

Ltac correct_inPar well_typed :=
  try
  (replace (@uc_eval 9) with (@uc_eval (3 + 6)) by easy;
   rewrite inPar_correct by well_typed);
  try
  (replace (@uc_eval 6) with (@uc_eval (3 + 3)) by easy;
   rewrite inPar_correct by well_typed);
  restore_dims.

Ltac reorder_scalars :=
  repeat rewrite Mscale_assoc;
  repeat rewrite Cmult_comm with (x := ((-1)%R : C));
  repeat rewrite <- Mscale_assoc with (y := ((-1)%R : C));
  repeat rewrite <- Mscale_plus_distr_r.

Ltac normalize_kron_notation :=
  repeat rewrite <- kron_assoc by auto 8 with wf_db;
  try easy.

Lemma inv_sqrt2_cubed : (/ √ 2 * / √ 2 * / √ 2)%C = (/ C2 * /√ 2)%C.
Proof.
  now rewrite Cinv_sqrt2_sqrt.
Qed.

Lemma uc_well_typed_SKIP {d} {h : 0 < d} :
  @uc_well_typed _ d SKIP.
Proof.
  unfold SKIP.
  apply uc_well_typed_ID.
  assumption.
Qed.

Ltac simplify_sums :=
  match goal with
    | [ |- context [ (?A .+ ?B)
                    .+ (?A .+ RtoC (-1)%R .* ?B) ]
      ] => 
      replace (A .+ B
                .+ (A .+ RtoC (-1)%R .* B)) with (C2 .* A) by lma
    | [ |- context [?A .+ ?B
                      .+ RtoC (-1)%R .* (?A .+ RtoC (-1)%R .* ?B)]
      ] =>
        replace (A .+ B
                  .+ RtoC (-1)%R .* (A .+ RtoC (-1)%R .* B))
            with (C2 .* B) by lma
    | [ |- context [?A .+ ?B
                      .+ RtoC (-1)%R .* (
                          RtoC (-1)%R .* (?A .+ RtoC (-1)%R .* ?B))]
      ] =>
        replace (A .+ B
                  .+ RtoC (-1)%R .* (
                      RtoC (-1)%R .* (A .+ RtoC (-1)%R .* B)))
            with (C2 .* A) by lma
    | [ |- context [?A .+ RtoC (-1)%R .* ?B
                  .+ (?A .+ ?B)]
      ] => 
        replace (A .+ RtoC (-1)%R .* B
              .+ (A .+ B)) with (C2 .* A) by lma
    | [ |- context [RtoC (-1)%R .* ?A .+ ?B
                          .+ (?A .+ ?B)]
      ] => 
        replace (RtoC (-1)%R .* A .+ B
                          .+ (A .+ B)) 
                with (C2 .* B) by lma
    | [ |- context [(?A .+ ?B
                   .+ (RtoC (-1)%R .* ?A .+ ?B))]
      ] =>
        replace (A .+ B
                   .+ (RtoC (-1)%R .* A .+ B)) 
                 with (C2 .* B) by lma
  end.

Ltac pull_scalars :=
  distribute_scale;
  repeat rewrite Mscale_mult_dist_r;
  repeat rewrite Mscale_assoc.

Lemma collapse_scalar :
  (/ C2 * (/ √ 2 * (/ √ 2 * (C2 * (/ √ 2 * (C2 * (/ √ 2 * C2)))))))%C = C1.
Proof. C_field. Qed.

Ltac distribute_over_blocks :=
  repeat rewrite kron_1_l by auto 10 with wf_db;
  repeat rewrite kron_assoc by auto with wf_db;
  repeat rewrite Mmult_plus_distr_l;
  repeat rewrite Mscale_mult_dist_r;
  repeat rewrite Mmult_assoc;
  restore_dims;
  repeat rewrite kron_mixed_product;
  repeat rewrite Mmult_plus_distr_l;
  normalize_kron_notation;
  repeat rewrite Mscale_mult_dist_r.

Ltac flatten :=
  rewrite kron_plus_distr_r;
  rewrite 2 Mscale_kron_dist_l;
  rewrite ket0_equiv, ket1_equiv;
  repeat (rewrite <- kron_assoc by auto 9 with wf_db; restore_dims).

(** 
  Blocks
 *)

Inductive up_to_three :=
  | Zer0 
  | One
  | Two.

Definition t_to_nat (t : up_to_three) : nat :=
  match t with
  | Zer0 => 0
  | One  => 1
  | Two  => 2
  end.

Coercion t_to_nat : up_to_three >-> nat.

(* Encoded blocks *)
Definition block_no := up_to_three.

(* Qubits in a single block *)
Definition block_offset := up_to_three.


Definition block_to_qubit (n : block_no) (off : block_offset) : nat :=
  n * 3 + off.


(**
  Encoding
 *)

Definition encode_block : base_ucom block_dim :=
  H 0;
  CNOT 0 1;
  CNOT 0 2.

Theorem encode_block_zero :
  uc_eval encode_block × ∣ 0, 0, 0 ⟩
  = / √ 2 .* (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩).
Proof.
  rewrite Common.zero_3_f_to_vec.
  now compute_vec.
Qed.

Theorem encode_block_one :
  uc_eval encode_block × ∣ 1, 0 , 0 ⟩
  = / √ 2 .* (∣ 0, 0, 0 ⟩ .+ (-1)%R .* ∣ 1, 1, 1 ⟩).
Proof.
  rewrite Common.one_3_f_to_vec.
  now compute_vec.
Qed.

Theorem encode_block_well_typed :
  uc_well_typed encode_block.
Proof.
  unfold encode_block.
  auto.
  constructor.
  - constructor.
    + apply uc_well_typed_H; lia.
    + apply uc_well_typed_CNOT; lia.
  - apply uc_well_typed_CNOT; lia.
Qed.

Definition encode : base_ucom dim :=
  CNOT 0 3; CNOT 0 6;
  inPar encode_block (inPar encode_block encode_block).

Notation encoded α β := (
    α .* (/C2 .* (/√ 2 .* (3 ⨂ (∣0,0,0⟩ .+            ∣1,1,1⟩))))
 .+ β .* (/C2 .* (/√ 2 .* (3 ⨂ (∣0,0,0⟩ .+  (-1)%R .* ∣1,1,1⟩))))
).


Theorem encode_correct : forall (α β : C),
   (@uc_eval dim encode) × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ 8 ⨂ ∣0⟩)
   = encoded α β.
Proof.
  intros.
  Local Opaque inPar.
  simpl. Msimpl_light.
  replace (∣0⟩) with (f_to_vec 1 (fun _ => false)) by lma'.
  replace (∣1⟩) with (f_to_vec 1 (fun _ => true)) by lma'.
  restore_dims.

  repeat rewrite Mmult_assoc.
  rewrite kron_plus_distr_r.
  repeat rewrite Mmult_plus_distr_l.
  distribute_scale.
  repeat rewrite Mscale_mult_dist_r.
  restore_dims.
  repeat rewrite kron_assoc by auto 10 with wf_db.
  repeat (rewrite f_to_vec_merge; restore_dims).

  repeat Common.f_to_vec_simpl_light.
  simpl. Msimpl_light.
  restore_dims.
  correct_inPar ltac:(apply encode_block_well_typed).
  replace (∣0, 0, 0, 0, 0, 0, 0, 0, 0⟩) with (∣0, 0, 0⟩ ⊗ ∣0, 0, 0, 0, 0, 0⟩) by normalize_kron_notation.
  replace (∣0, 0, 0, 0, 0, 0⟩) with (∣0, 0, 0⟩ ⊗ ∣0, 0, 0⟩) by normalize_kron_notation.
  replace (∣1, 0, 0, 1, 0, 0, 1, 0, 0⟩) with (∣1, 0, 0⟩ ⊗ ∣1, 0, 0, 1, 0, 0⟩) by normalize_kron_notation.
  replace (∣1, 0, 0, 1, 0, 0⟩) with (∣1, 0, 0⟩ ⊗ ∣1, 0, 0⟩) by normalize_kron_notation.
  restore_dims.
  do 4 rewrite kron_mixed_product.
  rewrite encode_block_zero, encode_block_one.
  repeat rewrite Mscale_kron_dist_l.
  repeat rewrite Mscale_kron_dist_r.
  normalize_kron_notation.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- inv_sqrt2_cubed.
  repeat rewrite Cmult_assoc.
  repeat rewrite Mscale_assoc.
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
  | TwoBitFlip (safe_n : block_no) (off₁ off₂ : block_offset)
  | ThreeBitFlip (off₁ off₂ off₃ : block_offset).

Inductive error : Set :=
  | NoError
  | PhaseFlipError {n} (e : phase_flip_error n)
  | BitFlipError (e : bit_flip_error)
  | PhaseBitErrors {phase_n} (e₁ : phase_flip_error phase_n) (e₂ : bit_flip_error).

Definition apply_to_block (n : block_no) (uc : base_ucom block_dim) :=
  match n with
  | Zer0 => inPar uc   (inPar SKIP SKIP)
  | One  => inPar SKIP (inPar uc SKIP)
  | Two  => inPar SKIP (inPar SKIP uc)
  end.

Fixpoint apply_phase_flip_error {n} (e : phase_flip_error n) : base_ucom dim :=
  match e with
  | OnePhaseFlip _ off => apply_to_block n (SQIR.Z off)
  | MorePhaseFlip _ e off => 
      apply_to_block n (SQIR.Z off);
      apply_phase_flip_error e
  end.

Definition apply_bit_flip_error (e : bit_flip_error) : base_ucom (block_dim + (block_dim + block_dim)) :=
  match e with
  | OneBitFlip n off => apply_to_block n (X off)
  | TwoBitFlip safe_n off₁ off₂ =>
      match safe_n with
      | Zer0 => inPar SKIP (inPar (X off₁) (X off₂))
      | One => inPar (X off₁) (inPar SKIP (X off₂))
      | Two => inPar (X off₁) (inPar (X off₂) SKIP)
      end
  | ThreeBitFlip off₁ off₂ off₃ => (
    inPar (X off₁) (inPar (X off₂) (X off₃))
  )
  end.

Definition apply_error (e : error) : base_ucom dim :=
  match e with
  | NoError              => SKIP
  | PhaseFlipError    e  => apply_phase_flip_error e
  | BitFlipError      e  => apply_bit_flip_error e
  | PhaseBitErrors e₁ e₂ => apply_phase_flip_error e₁; apply_bit_flip_error e₂
  end.

Fixpoint list_to_map (l : list nat) : nat -> bool :=
  match l with
  | [] => fun _ => false
  | x :: l' => update (list_to_map l') x true
  end.

Fixpoint ancillae_for_phase_flip {n} (e : phase_flip_error n) : list nat :=
  match e with
  | MorePhaseFlip _ (OnePhaseFlip _ _) _ => []
  | MorePhaseFlip _ (MorePhaseFlip _ e _) _ => ancillae_for_phase_flip e
  | OnePhaseFlip _ _ => 
      match n with 
      | Zer0 => 2 :: [5]
      | One  => [2]
      | Two  => [5]
      end
  end.

Definition block_to_bit_syn (b : block_no) (off : block_offset) : list nat :=
  let left_edge := b * 3 in
  match off with
  | Zer0        => left_edge :: [left_edge + 1]
  | One         => [left_edge]
  | Two         => [left_edge + 1]
  end.

Definition ancillae_for_bit_flip (e : bit_flip_error) : list nat :=
  match e with
  | OneBitFlip n off => block_to_bit_syn n off
  | TwoBitFlip safe_n off₁ off₂ => 
      match safe_n with
      | Zer0 => (block_to_bit_syn One off₁) ++ (block_to_bit_syn Two off₂)
      | One => (block_to_bit_syn Zer0 off₁) ++ (block_to_bit_syn Two off₂)
      | Two => (block_to_bit_syn Zer0 off₁) ++ (block_to_bit_syn One off₂)
      end
  | ThreeBitFlip off₁ off₂ off₃ =>
      (block_to_bit_syn Zer0 off₁) ++
      (block_to_bit_syn One  off₂) ++
      (block_to_bit_syn Two  off₃)
  end.

Definition ancillae_for (e : error) : Vector (2 ^ 8) :=
  match e with
  | NoError              => 8 ⨂ ∣0⟩
  | PhaseFlipError e     => f_to_vec 8 (list_to_map (ancillae_for_phase_flip e))
  | BitFlipError e       => f_to_vec 8 (list_to_map (ancillae_for_bit_flip e))
  | PhaseBitErrors e₁ e₂ =>
      f_to_vec 8 (list_to_map (
        ancillae_for_phase_flip e₁ ++
        ancillae_for_bit_flip e₂
      ))
  end.

Lemma ancillae_for_two_phases_cancel {n}: 
  forall (e : phase_flip_error n) (off₁ off₂ : block_offset),
  ancillae_for (PhaseFlipError (MorePhaseFlip n (MorePhaseFlip n e off₁) off₂))
  = ancillae_for (PhaseFlipError e).
Proof. easy. Qed.

(**
  Decode
 *)
Definition decode_block : base_ucom block_dim :=
  CNOT 0 1;
  CNOT 0 2;
  CCX 1 2 0;
  H 0.

Theorem decode_block_well_typed : uc_well_typed decode_block.
Proof.
  repeat constructor.
  Local Transparent CCX.
  all : unfold CCX.
  Local Opaque CCX.
  3 : repeat constructor.
  all : unfold TDAG.
  all : try apply uc_well_typed_H; try lia.
  all : try apply uc_well_typed_CNOT; try lia.
  all : try apply uc_well_typed_Rz; lia.
Qed.

Lemma decode_block_zero :
  uc_eval decode_block × ∣0,0,0⟩ = / √ 2 .* (∣0,0,0⟩ .+ ∣1,0,0⟩).
Proof.
  rewrite Common.zero_3_f_to_vec.
  now compute_vec.
Qed.

Lemma decode_block_one :
  uc_eval decode_block × ∣1,0,0⟩ = / √ 2 .* (∣0,1,1⟩ .+ ∣1,1,1⟩).
Proof.
  rewrite Common.one_3_f_to_vec.
  now compute_vec.
Qed.

Lemma decode_block_two :
  uc_eval decode_block × ∣0,1,0⟩ = / √ 2 .* (∣0,1,0⟩ .+ ∣1,1,0⟩).
Proof.
  rewrite Common.two_3_f_to_vec.
  now compute_vec.
Qed.

Lemma decode_block_three :
  uc_eval decode_block × ∣1,1,0⟩ = / √ 2 .* (∣0,0,1⟩ .+ (-1)%R .* ∣1,0,1⟩).
Proof.
  rewrite Common.three_3_f_to_vec.
  now compute_vec.
Qed.

Lemma decode_block_four :
  uc_eval decode_block × ∣0,0,1⟩ = / √ 2 .* (∣0,0,1⟩ .+ ∣1,0,1⟩).
Proof.
  rewrite Common.four_3_f_to_vec.
  now compute_vec.
Qed.

Lemma decode_block_five :
  uc_eval decode_block × ∣1,0,1⟩ = / √ 2 .* (∣0,1,0⟩ .+ (-1)%R .* ∣1,1,0⟩).
Proof.
  rewrite Common.five_3_f_to_vec.
  now compute_vec.
Qed.

Lemma decode_block_six :
  uc_eval decode_block × ∣0,1,1⟩ = / √ 2 .* (∣0,1,1⟩ .+ (-1)%R .* ∣1,1,1⟩).
Proof.
  rewrite Common.six_3_f_to_vec.
  now compute_vec.
Qed.

Lemma decode_block_seven :
  uc_eval decode_block × ∣1,1,1⟩ = / √ 2 .* (∣0,0,0⟩ .+ (-1)%R .* ∣1,0,0⟩).
Proof.
  rewrite Common.seven_3_f_to_vec.
  now compute_vec.
Qed.

#[export] Hint Rewrite
  decode_block_zero
  decode_block_one
  decode_block_two
  decode_block_three
  decode_block_four
  decode_block_five
  decode_block_six
  decode_block_seven
  : decode_block_db.

Definition decode : base_ucom dim := 
  inPar decode_block (inPar decode_block decode_block);
  CNOT 0 3; CNOT 0 6;
  CCX 6 3 0.

Ltac compute_decoding := 
  repeat rewrite kron_1_l by auto with wf_db;
  repeat rewrite <- Mmult_assoc;
  rewrite Mmult_plus_distr_l;
  repeat rewrite Mscale_mult_dist_r;
  repeat rewrite Mmult_assoc;
  correct_inPar ltac:(apply decode_block_well_typed);
  restore_dims;
  distribute_over_blocks;
  restore_dims;
  
  autorewrite with decode_block_db;

  restore_dims;
  reorder_scalars;
  repeat simplify_sums;
  pull_scalars;
  rewrite Common.zero_3_f_to_vec;
  rewrite Common.one_3_f_to_vec;

  restore_dims;
  repeat rewrite kron_assoc by auto 10 with wf_db;
  repeat (rewrite f_to_vec_merge; restore_dims);
  repeat Common.f_to_vec_simpl_light;
  simpl; Qsimpl;
  repeat rewrite <- Cmult_assoc;
  rewrite collapse_scalar;
  autorewrite with C_db;

  now flatten.

(**
  Full circuit 
 *)
Definition shor (e : error) : base_ucom dim :=
  encode;
  apply_error e;
  (* Does not use the regular:
     `encode; apply_error e; recover; decode` 
     (because we do not recover the original encoding).
     Attempting to do so requires 8 additional
     qubits (really classical bits), 2 per block
     for bit flip, and 2 for phase flip.
     This makes the following analysis rougher.
  *)
  decode.


Theorem decode_correct :
  forall (α β : C),
  (@uc_eval dim decode) × encoded α β
  = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ 8 ⨂ ∣0⟩.
Proof.
  intros. simpl uc_eval.
  Qsimpl. simpl.
  now compute_decoding.
Qed.

(**
  Correctness
  *)

Theorem error_decode_correct_no_error :
  forall (α β : C),
  (@uc_eval dim (apply_error NoError; decode)) × (encoded α β)
  = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ancillae_for NoError.
Proof.
  intros.
  simpl ancillae_for. Msimpl_light.
  Local Opaque decode.
  simpl uc_eval. restore_dims.
  Local Transparent decode.
  repeat rewrite denote_SKIP; try lia.
  repeat rewrite Mmult_assoc; restore_dims.
  repeat rewrite Mmult_1_l by auto 10 with wf_db.
  rewrite decode_correct.
  simpl (_ ⨂  _).
  now rewrite kron_1_l by auto with wf_db.
Qed.

Lemma Z_block_zero :
  forall (off : block_offset), @uc_eval block_dim (SQIR.Z off) × ∣0,0,0⟩ = ∣0,0,0⟩.
Proof.
  intros.
  destruct off; rewrite denote_Z; lma'.
Qed.

Lemma Z_block_seven :
  forall (off : block_offset), @uc_eval block_dim (SQIR.Z off) × ∣1,1,1⟩ = (-1)%R .* ∣1,1,1⟩.
Proof.
  intros.
  destruct off; rewrite denote_Z; lma'.
Qed.

Definition post_one_phase_flip (α β : C) (n : block_no) :=
  match n with
  | Zer0 => (
      α .* (/C2 .* (/√ 2 .* (
          (∣0,0,0⟩ .+ (-1)%R .* ∣1,1,1⟩) ⊗ 2 ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩)))
        )
   .+ β .* (/C2 .* (/√ 2 .* (
           (∣0,0,0⟩ .+ ∣1,1,1⟩) ⊗ 2 ⨂ (∣0,0,0⟩ .+ (-1)%R .* ∣1,1,1⟩)))
        )
  )
  | One => (
      α .* (/C2 .* (/√ 2 .* (
          (∣0,0,0⟩ .+ ∣1,1,1⟩) ⊗ (∣0,0,0⟩ .+ (-1)%R .* ∣1,1,1⟩) ⊗ (∣0,0,0⟩ .+ ∣1,1,1⟩)))
        )
   .+ β .* (/C2 .* (/√ 2 .* (
        (∣0,0,0⟩ .+ (-1)%R .* ∣1,1,1⟩) ⊗ (∣0,0,0⟩ .+ ∣1,1,1⟩) ⊗ (∣0,0,0⟩ .+ (-1)%R .* ∣1,1,1⟩)))
        )
  )
  | Two => (
      α .* (/C2 .* (/√ 2 .* (
          (2 ⨂ (∣0,0,0⟩ .+ ∣1,1,1⟩) ⊗ (∣0,0,0⟩ .+ (-1)%R .* ∣1,1,1⟩)))
        ))
   .+ β .* (/C2 .* (/√ 2 .* (
           2 ⨂ (∣0,0,0⟩ .+ (-1)%R .* ∣1,1,1⟩) ⊗ (∣0,0,0⟩ .+ ∣1,1,1⟩)))
        )
  )
  end.

Theorem one_phase_flip_correct :
  forall (α β : C) {n} (off : block_offset), 
    uc_eval (apply_error (PhaseFlipError (OnePhaseFlip n off)))
    × encoded α β 
    = post_one_phase_flip α β n.
Proof.
  intros.
  simpl uc_eval.
  destruct n.
  all : simpl (_ ⨂ _).
  all : simpl apply_to_block.
  all : simpl post_one_phase_flip.
  all : correct_inPar ltac:(
    (destruct off;
      apply uc_well_typed_Z; simpl; lia)
    || apply (@uc_well_typed_SKIP block_dim); lia
  ).
  all : distribute_over_blocks.
  all : try rewrite denote_SKIP; try lia; Msimpl_light.
  all : rewrite Z_block_zero, Z_block_seven.
  all : repeat rewrite Mscale_assoc.
  all : restore_dims.
  all : replace ((-1)%R * (-1)%R)%C with C1 by lca.
  all : now rewrite Mscale_1_l.
Qed.

Theorem two_phase_flip_correct :
  forall (α β : C) {n} (off₁ off₂ : block_offset), 
    uc_eval (apply_error (PhaseFlipError (MorePhaseFlip n (OnePhaseFlip n off₁) off₂)))
    × encoded α β 
    = encoded α β.
Proof.
  intros.
  simpl uc_eval.
  destruct n.
  all : simpl (_ ⨂ _).
  all : simpl apply_to_block.
  all : do 2 correct_inPar ltac:(
    (destruct off₁; destruct off₂;
      apply uc_well_typed_Z; simpl; lia)
    || apply (@uc_well_typed_SKIP block_dim); lia
  ).
  all : distribute_over_blocks.
  all : try rewrite denote_SKIP; try lia; Msimpl_light.
  all : restore_dims.
  all : repeat rewrite Mmult_assoc.
  all : rewrite Z_block_zero, Z_block_seven.
  all : repeat rewrite Mscale_mult_dist_r.
  all : rewrite Z_block_zero, Z_block_seven.
  all : repeat rewrite Mscale_assoc.
  all : replace ((-1)%R * (-1)%R)%C with C1 by lca.
  all : rewrite <- Mscale_assoc with (y := C1).
  all : now rewrite Mscale_1_l.
Qed.

Theorem more_than_two_phase_flip_correct :
  forall (α β : C) {n} (off₁ off₂ : block_offset) (e : phase_flip_error n), 
    uc_eval (apply_error (PhaseFlipError (MorePhaseFlip n (MorePhaseFlip n e off₂) off₁)))
    × encoded α β 
    = uc_eval (apply_error (PhaseFlipError e)) × encoded α β.
Proof.
  intros.
  simpl uc_eval.
  destruct n.
  all : simpl (_ ⨂ _).
  all : simpl apply_to_block.
  all : do 2 correct_inPar ltac:(
    (destruct off₁; destruct off₂;
      apply uc_well_typed_Z; simpl; lia)
    || apply (@uc_well_typed_SKIP block_dim); lia
  ).
  all : distribute_over_blocks.
  all : try rewrite denote_SKIP; try lia; Msimpl_light.
  all : restore_dims.
  all : repeat rewrite Mmult_assoc.
  all : rewrite Z_block_zero, Z_block_seven.
  all : repeat rewrite Mscale_mult_dist_r.
  all : rewrite Z_block_zero, Z_block_seven.
  all : repeat rewrite Mscale_assoc.
  all : replace ((-1)%R * (-1)%R)%C with C1 by lca.
  all : rewrite <- Mscale_assoc with (y := C1).
  all : now rewrite Mscale_1_l.
Qed.

Theorem error_decode_correct_phase_flip :
  forall (α β : C) {n} (e : phase_flip_error n),
  (@uc_eval dim (apply_error (PhaseFlipError e); decode)) × (encoded α β)
  = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ancillae_for (PhaseFlipError e).
Proof.
  Local Opaque decode.
  intros.
  enough (
    (@uc_eval dim (apply_error (PhaseFlipError e); decode)) × (encoded α β)
      = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ancillae_for (PhaseFlipError e)
    /\
    forall off,
    (@uc_eval dim (apply_error (PhaseFlipError (MorePhaseFlip n e off)); decode)) × (encoded α β)
      = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ancillae_for (PhaseFlipError (MorePhaseFlip n e off))
  ).
  { destruct H; assumption. }
  induction e.
  - split.
    + intros.
      Local Opaque apply_error.
      Local Transparent decode.
      simpl uc_eval.
      Local Opaque decode.
      rewrite Mmult_assoc.
      rewrite one_phase_flip_correct.
      destruct n.
      all : simpl ancillae_for; simpl post_one_phase_flip.
      par : now compute_decoding.
    + intros.
      simpl uc_eval.
      rewrite Mmult_assoc.
      rewrite two_phase_flip_correct.
      apply decode_correct.
  - destruct IHe as [IHe IHme].
    split.
    + apply IHme.
    + intros off0.
      simpl uc_eval.
      rewrite Mmult_assoc.
      rewrite more_than_two_phase_flip_correct.
      rewrite ancillae_for_two_phases_cancel.
      simpl uc_eval in IHe.
      rewrite Mmult_assoc in IHe.
      apply IHe.
Qed.

Lemma X_0_block_zero :
  @uc_eval block_dim (X 0) × ∣0,0,0⟩ = ∣1,0,0⟩.
Proof.
  rewrite Common.zero_3_f_to_vec.
  now compute_vec.
Qed.

Lemma X_1_block_zero :
  @uc_eval block_dim (X 1) × ∣0,0,0⟩ = ∣0,1,0⟩.
Proof.
  rewrite Common.zero_3_f_to_vec.
  now compute_vec.
Qed.

Lemma X_2_block_zero :
  @uc_eval block_dim (X 2) × ∣0,0,0⟩ = ∣0,0,1⟩.
Proof.
  rewrite Common.zero_3_f_to_vec.
  now compute_vec.
Qed.

Lemma X_0_block_seven :
  @uc_eval block_dim (X 0) × ∣1,1,1⟩ = ∣0,1,1⟩.
Proof.
  rewrite Common.seven_3_f_to_vec.
  now compute_vec.
Qed.

Lemma X_1_block_seven :
  @uc_eval block_dim (X 1) × ∣1,1,1⟩ = ∣1,0,1⟩.
Proof.
  rewrite Common.seven_3_f_to_vec.
  now compute_vec.
Qed.

Lemma X_2_block_seven :
  @uc_eval block_dim (X 2) × ∣1,1,1⟩ = ∣1,1,0⟩.
Proof.
  rewrite Common.seven_3_f_to_vec.
  now compute_vec.
Qed.

#[export] Hint Rewrite
  X_0_block_zero
  X_1_block_zero
  X_2_block_zero
  X_0_block_seven
  X_1_block_seven
  X_2_block_seven
  : X_off_block_db.

Ltac post_offset_destruct :=
  autorewrite with X_off_block_db;
  autorewrite with decode_block_db;
  reorder_scalars; restore_dims;
  repeat simplify_sums;
  pull_scalars; restore_dims;
  autorewrite with f_to_vec_3_db;
  restore_dims;
  repeat rewrite kron_assoc by auto 10 with wf_db;
  repeat (rewrite f_to_vec_merge; restore_dims);
  repeat Common.f_to_vec_simpl_light;
  simpl f_to_vec; Msimpl_light;
  repeat rewrite <- Cmult_assoc;
  rewrite collapse_scalar; autorewrite with C_db;
  now flatten.

Theorem error_decode_correct_bit_flip :
  forall (α β : C) e,
  (@uc_eval dim (apply_error (BitFlipError e); decode)) × (encoded α β)
  = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ancillae_for (BitFlipError e).
Proof.
  intros.
  Local Transparent decode.
  Local Opaque decode_block.
  destruct e.
  all : repeat rewrite <- Mmult_assoc.
  all : rewrite Mmult_plus_distr_l.
  all : repeat rewrite Mscale_mult_dist_r.
  2 : destruct safe_n.
  1 : destruct n.
  Local Transparent apply_error.
  all : simpl uc_eval.
  all : simpl (_ ⨂ _).
  all : repeat rewrite Mmult_assoc; restore_dims.
  all : simpl apply_to_block.
  all : try rewrite kron_1_l by auto with wf_db.
  all : restore_dims.
  all : repeat rewrite kron_assoc by auto 10 with wf_db.
  all : correct_inPar ltac:(
    try apply decode_block_well_typed
  ).
  all : correct_inPar ltac:(
    try apply uc_well_typed_X;
    first [destruct off | destruct off₁; destruct off₂];
    try destruct off₃; simpl; lia 
    || apply (@uc_well_typed_SKIP block_dim); lia
  ).
  all : simpl (_ + _).
  all : distribute_over_blocks.
  all : try rewrite denote_SKIP; try lia; Msimpl_light.
  all : first [destruct off | destruct off₁; destruct off₂];
    try destruct off₃; simpl uc_eval; simpl ancillae_for.
  (* slow; around ~2m *)
  par : now post_offset_destruct.
Qed.

Lemma error_decode_correct_bit_one_phase_flip :
  forall (α β : C) e off {phase_n},
  (@uc_eval dim (apply_error (PhaseBitErrors (OnePhaseFlip phase_n off) e); decode)) × (encoded α β)
  = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ancillae_for (PhaseBitErrors (OnePhaseFlip phase_n off) e).
Proof.
  intros.
  simpl uc_eval.
  destruct phase_n; destruct e.
  all : repeat rewrite <- Mmult_assoc.
  all : rewrite Mmult_plus_distr_l.
  all : repeat rewrite Mscale_mult_dist_r.
  all : try destruct safe_n; try destruct n.
  all : simpl uc_eval.
  all : simpl (_ ⨂ _).
  all : repeat rewrite Mmult_assoc; restore_dims.
  all : simpl apply_to_block.
  all : try rewrite kron_1_l by auto with wf_db.
  all : restore_dims.
  all : repeat rewrite kron_assoc by auto 10 with wf_db.
  all : correct_inPar ltac:(
    try apply decode_block_well_typed
  ).
  all : correct_inPar ltac:(
    try apply uc_well_typed_X;
    first [destruct off0 | destruct off₁; destruct off₂];
    try destruct off₃; simpl; lia 
    || apply (@uc_well_typed_SKIP block_dim); lia
  ).
  all : correct_inPar ltac:(
    try apply uc_well_typed_Z;
    destruct off; simpl; lia 
    || apply (@uc_well_typed_SKIP block_dim); lia
  ).
  all : restore_dims.
  all : simpl (_ + _).
  all : distribute_over_blocks.
  all : try rewrite denote_SKIP; try lia; Msimpl_light.
  all : repeat rewrite Mmult_assoc.
  all : rewrite Z_block_zero, Z_block_seven.
  all : try rewrite denote_SKIP; try lia; Msimpl_light.
  all : repeat rewrite Mscale_mult_dist_r.
  all : restore_dims.
  all : try (destruct off0; simpl uc_eval; simpl ancillae_for).
  all : try post_offset_destruct.
  all : destruct off₁; destruct off₂; simpl uc_eval; simpl ancillae_for.
  1-81 : try post_offset_destruct.
  all : try destruct off₃; simpl uc_eval; simpl ancillae_for.
  all : now post_offset_destruct.
Qed.

Theorem error_decode_correct_bit_phase_flip :
  forall (α β : C) {phase_n} (e₁ : phase_flip_error phase_n) (e₂ : bit_flip_error),
  (@uc_eval dim (apply_error (PhaseBitErrors e₁ e₂); decode)) × (encoded α β)
  = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ancillae_for (PhaseBitErrors e₁ e₂).
Proof.
  Local Opaque decode.
  intros.
  enough (
    (@uc_eval dim (apply_error (PhaseBitErrors e₁ e₂); decode)) × (encoded α β)
      = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ancillae_for (PhaseBitErrors e₁ e₂)
    /\
    forall off,
    (@uc_eval dim (apply_error (PhaseBitErrors (MorePhaseFlip phase_n e₁ off) e₂); decode)) × (encoded α β)
      = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ancillae_for (PhaseBitErrors (MorePhaseFlip phase_n e₁ off) e₂)
  ).
  { destruct H; assumption. }
  induction e₁.
  - split.
    + apply error_decode_correct_bit_one_phase_flip.
    + intros.
      unfold apply_error.
      change (apply_phase_flip_error ?a) with (apply_error (PhaseFlipError a)).
      change (apply_bit_flip_error ?a) with (apply_error (BitFlipError a)).
      Local Opaque apply_error.
      simpl uc_eval.
      do 2 rewrite Mmult_assoc.
      rewrite two_phase_flip_correct.
      specialize (error_decode_correct_bit_flip α β e₂) as He.
      simpl uc_eval in He.
      rewrite Mmult_assoc in He.
      restore_dims.
      simpl in *.
      apply He.
  - destruct IHe₁ as [IHe IHme].
    split.
    + apply IHme.
    + intros off0.
      Local Transparent apply_error.
      unfold apply_error.
      change (apply_phase_flip_error ?a) with (apply_error (PhaseFlipError a)).
      change (apply_bit_flip_error ?a) with (apply_error (BitFlipError a)).
      Local Opaque apply_error.
      simpl uc_eval.
      do 2 rewrite Mmult_assoc.
      rewrite more_than_two_phase_flip_correct.
      change (apply_error (@PhaseBitErrors phase_n e₁ e₂)) with (apply_error (PhaseFlipError e₁); apply_error (BitFlipError e₂)) in IHe.
      simpl uc_eval in IHe.
      repeat rewrite Mmult_assoc in IHe.
      restore_dims.
      simpl in *.
      apply IHe.
Qed.


(**
  Main correctness proof for the discrete error case.
*)
Theorem shor_correct (e : error) : forall (α β : C),
  (@uc_eval dim (shor e)) × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ 8 ⨂ ∣0⟩)
  = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ancillae_for e.
Proof.
  intros.
  Local Opaque encode decode apply_error CCX.
  simpl uc_eval.
  repeat rewrite Mmult_assoc.
  rewrite encode_correct.

  destruct e; simpl ancillae_for.
  - specialize (error_decode_correct_no_error α β) as H.
    simpl uc_eval in H.
    simpl ancillae_for in H.
    rewrite Mmult_assoc in H.
    apply H.
  - specialize (error_decode_correct_phase_flip α β e) as H.
    simpl uc_eval in H.
    rewrite Mmult_assoc in H.
    apply H.
  - specialize (error_decode_correct_bit_flip α β e) as H.
    simpl uc_eval in H.
    rewrite Mmult_assoc in H.
    apply H.
  - specialize (error_decode_correct_bit_phase_flip α β e₁ e₂) as H.
    simpl uc_eval in H.
    rewrite Mmult_assoc in H.
    apply H.
Qed.

(**
  Generalized errors on single qubits
 *)

Lemma pauli_spans_2_by_2 : 
  forall (M : Square 2), WF_Matrix M ->
  exists λ₁ λ₂ λ₃ λ₄, 
  M = λ₁ .* (I 2) .+ λ₂ .* σx .+ λ₃ .* σy .+ λ₄ .* σz.
Proof.
  intros.
  exists ((M 0 0 + M 1 1) / C2)%C.
  exists ((M 0 1 + M 1 0) / C2)%C.
  exists (Ci * (M 0 1 - M 1 0) / C2)%C.
  exists ((M 0 0 - M 1 1) / C2)%C.
  solve_matrix.
Qed.

Lemma pauli_spans_unitary_2_by_2 :
  forall (M : Square 2), WF_Unitary M ->
  exists λ₁ λ₂ λ₃ λ₄, 
  M = λ₁ .* (I 2) .+ λ₂ .* σx .+ λ₃ .* σy .+ λ₄ .* σz
  /\ (Cmod λ₁ ^ 2 + Cmod λ₂ ^ 2 + Cmod λ₃ ^ 2 + Cmod λ₄ ^ 2)%C = C1.
Proof.
  intros ? [Hwf Hinv].
  specialize (pauli_spans_2_by_2 M Hwf) as [λ₁ [λ₂ [λ₃ [λ₄ Heq]]]].
  exists λ₁, λ₂, λ₃, λ₄.
  split.
  apply Heq.
  rewrite Heq in Hinv.

  repeat rewrite Mplus_adjoint in Hinv.
  repeat rewrite Mscale_adj in Hinv.
  repeat rewrite Mmult_plus_distr_l in Hinv.
  repeat rewrite Mmult_plus_distr_r in Hinv.
  repeat rewrite Mscale_mult_dist_r in Hinv.
  repeat rewrite Mscale_mult_dist_l in Hinv.
  specialize σx_unitary as [_ Hinvσx].
  specialize σy_unitary as [_ Hinvσy].
  specialize σz_unitary as [_ Hinvσz].
  rewrite Hinvσx in Hinv. clear Hinvσx.
  rewrite Hinvσy in Hinv. clear Hinvσy.
  rewrite Hinvσz in Hinv. clear Hinvσz.

  replace ((σx) †) with σx in Hinv by solve_matrix.
  replace ((σy) †) with σy in Hinv by solve_matrix.
  replace ((σz) †) with σz in Hinv by solve_matrix.

  autorewrite with M_db M_db_light in Hinv.
  replace (σx × σy) with (Ci .* σz) in Hinv by lma'.
  replace (σy × σx) with (-Ci .* σz) in Hinv by lma'.
  replace (σz × σx) with (Ci .* σy) in Hinv by lma'.
  replace (σx × σz) with (-Ci .* σy) in Hinv by lma'.
  replace (σy × σz) with (Ci .* σx) in Hinv by lma'.
  replace (σz × σy) with (-Ci .* σx) in Hinv by lma'.
  assert (H00 := Hinv).
  assert (H11 := Hinv).
  clear Hinv.
  apply (f_equal (fun m => m 0 0)) in H00.
  apply (f_equal (fun m => m 1 1)) in H11.
  unfold scale, Mplus, I, σx, σy, σz in H00, H11; simpl in H00, H11.
  specialize (Cplus_simplify _ _ _ _ H00 H11) as H.
  clear H00. clear H11.
  ring_simplify in H.
  repeat rewrite <- Cplus_assoc in H.
  repeat rewrite <- Cmult_assoc in H.
  repeat rewrite <- Cmult_plus_distr_l in H.

  replace (((R1 + R1)%R, (R0 + R0)%R)) with C2 in H.
  2 :{ 
      unfold C2.
      apply c_proj_eq; simpl.
      field.
      field.
  }
  apply Cmult_cancel_l with (a := C2); try nonzero.
  rewrite Cmult_1_r.

  repeat rewrite <- Cmod_sqr in H.
  rewrite Cmult_comm with (x := λ₁) in H.
  rewrite <- Cmod_sqr in H.
  repeat rewrite Cplus_assoc in H.

  exact H.
Qed.


Lemma YeqiXZ :
  σy = Ci .* σx × σz.
Proof. solve_matrix. Qed.

Definition ancillae_for_arbitrary
  (λ₁ λ₂ λ₃ λ₄ : C)
  (n : block_no)
  (off : block_offset) : Vector (2 ^ 8)
   := (
       λ₁ .* ancillae_for NoError
    .+ λ₂ .* ancillae_for (BitFlipError (OneBitFlip n off))
    .+ λ₃ * Ci .* ancillae_for (PhaseBitErrors (OnePhaseFlip n off) (OneBitFlip n off))
    .+ λ₄ .* ancillae_for (PhaseFlipError (OnePhaseFlip n off))
   ).

Lemma Cmod_Ci : Cmod Ci = 1%R.
Proof.
  unfold Ci, Cmod; simpl.
  rewrite Rmult_0_l.
  rewrite Rplus_0_l.
  do 2 rewrite Rmult_1_l.
  exact sqrt_1.
Qed.

Lemma ancillae_pure_vector_cond : 
  forall (λ₁ λ₂ λ₃ λ₄ : C) (n : block_no) (off : block_offset), 
  (Cmod λ₁ ^ 2 + Cmod λ₂ ^ 2 + Cmod λ₃ ^ 2 + Cmod λ₄ ^ 2)%C = C1 ->
  Pure_State_Vector (ancillae_for_arbitrary λ₁ λ₂ λ₃ λ₄ n off).
Proof.
  intros.
  unfold Pure_State_Vector.
  split.
  1: {
    destruct n; destruct off; unfold ancillae_for_arbitrary; simpl.
    all : auto 18 with wf_db.
  }
  destruct n; destruct off.
  all : unfold ancillae_for_arbitrary; simpl.
  all : repeat rewrite kron_1_l by auto with wf_db.
  all : repeat rewrite Mplus_adjoint.
  all : repeat rewrite Mscale_adj.
  all : restore_dims.
  all : rewrite <- ket0_equiv, <- ket1_equiv.
  all : repeat rewrite kron_adjoint.
  all : repeat rewrite Mmult_plus_distr_r.
  all : autorewrite with ket_db.
  all : repeat rewrite Mplus_assoc.
  all : repeat rewrite <- Mscale_plus_distr_l.
  all : repeat rewrite <- Cmod_sqr.
  all : rewrite Cmod_mult.
  all : rewrite Cmod_Ci.
  all : rewrite Rmult_1_r.
  all : repeat rewrite Cplus_assoc.
  all : rewrite H.
  all : now rewrite Mscale_1_l.
Qed.

Definition shor_arbitrary_unitary_matrix (M : Square 2) (n : block_no) (off : block_offset) :=
  uc_eval decode
  × pad_u dim (block_to_qubit n off) M 
  × uc_eval encode.

(**
  Main correctness proof for the continuous error case.
*)
Theorem shor_arbitrary_correct (M : Square 2) :
  WF_Unitary M ->
  forall (α β : C) (n : block_no) (off : block_offset),
  exists (φ : Vector (2^8)),
   Pure_State_Vector φ /\
   shor_arbitrary_unitary_matrix M n off × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ 8 ⨂ ∣0⟩)
  = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ φ.
Proof.
  intros.
  repeat rewrite Mmult_assoc.
  unfold shor_arbitrary_unitary_matrix.
  repeat rewrite Mmult_assoc.
  rewrite encode_correct.
  specialize (pauli_spans_unitary_2_by_2 M H) as Hpauli.
  destruct Hpauli as [λ₁ [λ₂ [λ₃ [λ₄ [Hpauli Hmod]]]]].
  rewrite Hpauli.
  exists (ancillae_for_arbitrary λ₁ λ₂ λ₃ λ₄ n off).
  split.
  1 : exact (ancillae_pure_vector_cond λ₁ λ₂ λ₃ λ₄ n off Hmod).
  destruct n; destruct off.
  all : cbn.
  all : repeat rewrite kron_1_l by auto with wf_db.
  all : try rewrite kron_1_r by auto with wf_db.
  1 : replace (I 256) with (I 4 ⊗ I 8 ⊗ I 8) by (repeat rewrite id_kron; easy).
  9 : replace (I 256) with (I 8 ⊗ I 8 ⊗ I 4) by (repeat rewrite id_kron; easy).
  2 : replace (I 128) with (I 2 ⊗ I 8 ⊗ I 8) by (repeat rewrite id_kron; easy).
  8 : replace (I 128) with (I 8 ⊗ I 8 ⊗ I 2) by (repeat rewrite id_kron; easy).
  3,7 : replace (I 64) with (I 8 ⊗ I 8) by (repeat rewrite id_kron; easy).
  7 : replace (I 32) with (I 8 ⊗ I 4) by (repeat rewrite id_kron; easy).
  5 : replace (I 32) with (I 4 ⊗ I 8) by (repeat rewrite id_kron; easy).
  6 : replace (I 16) with (I 8 ⊗ I 2) by (repeat rewrite id_kron; easy).
  
  all : restore_dims.
  all : repeat rewrite kron_assoc by auto 10 with wf_db.
  6 : replace (I 8 ⊗ I 2) with (I 2 ⊗ I 8) by (repeat rewrite id_kron; easy);
      restore_dims. 
  1-3 : repeat rewrite <- kron_assoc by auto 10 with wf_db.
  5-6 : rewrite <- kron_assoc with (C := I 8) by auto 10 with wf_db.
  6 : repeat (rewrite kron_assoc by auto 10 with wf_db; restore_dims).
  6 : repeat rewrite <- kron_assoc with (A := I 2) by auto 10 with wf_db.
  6 : repeat rewrite <- kron_assoc with (B := I 2) by auto 10 with wf_db.
  7 : repeat rewrite <- kron_assoc with (A := I 4) by auto 10 with wf_db.

  all : restore_dims.
  all : do 2 rewrite Mmult_plus_distr_l.
  all : pull_scalars; restore_dims.
  all : repeat rewrite kron_mixed_product.
  all : repeat rewrite Mmult_1_l by auto with wf_db.
  all : replace (I 4) with (I 2 ⊗ I 2) by (repeat rewrite id_kron; easy).
  all : do 2 rewrite Mmult_plus_distr_l.
  all : rewrite Mscale_mult_dist_r.
  all : restore_dims.
  all : repeat (rewrite kron_assoc by auto 10 with wf_db; restore_dims).
  all : repeat rewrite kron_mixed_product.
  all : repeat rewrite Mmult_plus_distr_r.
  all : repeat rewrite Mscale_mult_dist_l.
  all : rewrite ket0_equiv, ket1_equiv.
  all : restore_dims.
  all : repeat rewrite Mmult_1_l by auto with wf_db.
  all : rewrite X0_spec, X1_spec, Y0_spec, Y1_spec, Z0_spec, Z1_spec.
  Local Transparent decode.
  all : simpl uc_eval.
  all : repeat rewrite Mmult_assoc by auto 10 with wf_db.
  all : correct_inPar ltac:(apply decode_block_well_typed).
  all : repeat rewrite kron_mixed_product.
  all : repeat rewrite kron_plus_distr_r.
  all : repeat rewrite kron_plus_distr_l.
  all : repeat rewrite Mmult_plus_distr_l.
  all : repeat rewrite Mscale_mult_dist_r.
  all : repeat rewrite Mmult_plus_distr_l.
  all : repeat rewrite Mscale_kron_dist_l.
  all : repeat rewrite Mscale_mult_dist_r.
  all : repeat rewrite Mscale_kron_dist_r.
  all : repeat rewrite Mscale_mult_dist_r.
  all : restore_dims.
  all : repeat rewrite <- kron_assoc by auto 10 with wf_db.
  all : restore_dims.
  all : repeat rewrite Mscale_plus_distr_r with (x := ((-1)%R : C)).
  all : repeat rewrite Mscale_assoc.
  all : repeat rewrite Cmult_comm with (x := ((-1)%R : C)).
  all : repeat rewrite <- Mscale_assoc.
  all : repeat rewrite Mplus_assoc.
  all : repeat rewrite Mplus_comm with (A := λ₁ .* _).
  all : repeat rewrite Mplus_assoc.
  all : do 2 rewrite <- Mscale_plus_distr_r.
  all : repeat rewrite Mplus_comm with (A := λ₂ .* _).
  all : repeat rewrite Mplus_assoc.
  all : do 2 rewrite <- Mscale_plus_distr_r.
  all : repeat rewrite Mplus_comm with (A := λ₃ .* _).
  all : repeat rewrite Mplus_assoc.
  all : do 2 rewrite <- Mscale_plus_distr_r.
  all : repeat rewrite Mplus_comm with (A := λ₄ .* _).
  all : repeat rewrite Mplus_assoc.
  all : do 2 rewrite <- Mscale_plus_distr_r.
  all : autorewrite with decode_block_db.
  all : restore_dims.
  all : replace (-Ci) with (Ci * (-1)%R)%C by lca.
  all : reorder_scalars.
  all : repeat rewrite <- Cmult_assoc with (y := ((-1)%R : C)).
  all : rewrite Cmult_comm with (x := ((-1)%R : C)).
  all : reorder_scalars.
  all : repeat rewrite Cmult_assoc with (z := ((-1)%R : C)).
  all : repeat rewrite <- Mscale_assoc with (y := ((-1)%R : C)).
  all : reorder_scalars.
  all : pull_scalars.
  all : repeat rewrite Mscale_plus_distr_r with (x := ((-1)%R : C)).
  all : repeat rewrite Mscale_assoc.
  all : replace ((-1)%R * (-1)%R)%C with C1 by lca.
  all : repeat rewrite Mscale_1_l.
  all : restore_dims.
  all : repeat simplify_sums.
  all : autorewrite with f_to_vec_3_db.
  all : distribute_scale.
  all : distribute_plus.
  all : repeat rewrite Mscale_mult_dist_r.
  all : repeat rewrite Mmult_plus_distr_l.
  all : repeat rewrite Mscale_kron_dist_r.
  all : repeat rewrite Mscale_kron_dist_l.
  all : repeat rewrite Mscale_kron_dist_r.
  all : repeat rewrite kron_assoc by auto 10 with wf_db.
  all : repeat rewrite Mscale_assoc.
  all : repeat rewrite Mscale_mult_dist_r.
  all : restore_dims.
  all : repeat rewrite kron_assoc by auto 10 with wf_db.
  all : repeat (rewrite f_to_vec_merge; restore_dims).
  all : repeat f_to_vec_simpl_light.
  all : simpl.
  all : repeat rewrite kron_1_l by auto with wf_db.
  all : repeat rewrite kron_assoc by auto with wf_db.
  all : repeat rewrite <- Cmult_assoc.
  all : rewrite <- Mscale_assoc with (x := α);
        rewrite <- Mscale_assoc with (x := β).
  all : repeat rewrite Mscale_plus_distr_r.
  all : repeat rewrite Mscale_assoc.
  all : repeat rewrite <- Cmult_assoc.
  all : repeat rewrite Cmult_comm with (x := λ₁);
        repeat rewrite Cmult_comm with (x := λ₂);
        repeat rewrite Cmult_comm with (x := λ₃);
        repeat rewrite Cmult_comm with (x := λ₄).
  all : repeat rewrite Cmult_comm with (x := Ci).
  all : repeat rewrite Cmult_assoc.
  all : do 2 rewrite Cmult_comm with (y := λ₁);
        do 2 rewrite Cmult_comm with (y := λ₂);
        do 2 rewrite Cmult_comm with (y := λ₃);
        do 2 rewrite Cmult_comm with (y := λ₄).
  all : repeat rewrite Cmult_comm with (y := Ci).
  all : repeat rewrite <- Cmult_assoc.
  all : match goal with
  | [ |- context [
      ?λ * (?γ * (/ C2 * ?c)) .* _
      ]
    ] => replace (/ C2 * c)%C with (C1) by C_field
  end.
  all : repeat rewrite Cmult_1_r.
  all : unfold ancillae_for_arbitrary; simpl.
  all : repeat rewrite kron_1_l by auto with wf_db.
  all : rewrite ket0_equiv.
  all : repeat rewrite kron_plus_distr_l.
  all : repeat rewrite Mscale_kron_dist_r.
  all : repeat rewrite Mscale_plus_distr_r.
  all : restore_dims.
  all : repeat rewrite <- kron_assoc by auto 10 with wf_db.
  all : repeat rewrite Mscale_assoc.
  all : repeat rewrite Cmult_assoc.
  all : repeat rewrite Cmult_comm with (y := α);
        repeat rewrite Cmult_comm with (y := β).
  all : repeat rewrite Cmult_assoc.
  all : repeat rewrite Mplus_assoc.
  all : reflexivity.
Qed.

Theorem shor_arbitrary_correct_prob (M : Square 2) :
  WF_Unitary M ->
  forall (α β : C) (n : block_no) (off : block_offset),
   let r := shor_arbitrary_unitary_matrix M n off × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ 8 ⨂ ∣0⟩) in 
  @prob_partial_meas 1 (dim - 1) ∣0⟩ r = (Cmod α ^ 2)%R 
  /\ @prob_partial_meas 1 (dim - 1) ∣1⟩ r = (Cmod β ^ 2)%R.
Proof.
  intros.
  specialize (shor_arbitrary_correct M H α β n off) as [R [[HWFR HDag] HR]].
  subst r.
  rewrite HR.
  do 2 rewrite prob_partial_meas_alt.
  distribute_adjoint.
  Msimpl.
  autorewrite with ket_db.
  do 2 rewrite norm_scale.
  unfold norm.
  unfold inner_product.
  restore_dims.
  rewrite HDag.
  split; simpl; rewrite sqrt_1; repeat rewrite Rmult_1_r; easy.
Qed.

End NineQubitCode.
