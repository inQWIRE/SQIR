Require Export SQIR.UnitaryOps.

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

Definition t_eq (t₁ t₂ : up_to_three) : bool :=
  match t₁, t₂ with
  | Zer0, Zer0
  | One, One
  | Two, Two => true
  | _, _ => false
  end.

Coercion t_to_nat : up_to_three >-> nat.

Definition t_of_nat (n : nat) (h : n < 3) : up_to_three.
Proof.
  destruct n as [| [| [| n']]].
  - exact Zer0.
  - exact One.
  - exact Two.
  - lia.
Defined.

(* Encoded blocks *)
Definition block_no := up_to_three.

(* Qubits in a single block *)
Definition block_offset := up_to_three.

(**
  Encoding
 *)

Definition encode_block : base_ucom block_dim :=
  H 0;
  CNOT 0 1;
  CNOT 0 2.

Theorem encode_block_zero :
  uc_eval encode_block × ∣0,0,0⟩
  = / √ 2 .* (∣ 0, 0, 0 ⟩ .+ ∣ 1, 1, 1 ⟩).
Proof.
  rewrite Common.zero_3_f_to_vec.
  now compute_vec.
Qed.


Theorem encode_block_one :
  uc_eval encode_block × ∣1,0,0⟩
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

Ltac post_offset_destruct :=
  restore_dims;
  autorewrite with f_to_vec_3_db;
  try repeat rewrite f_to_vec_X; try lia; simpl f_to_vec;
  repeat rewrite kron_1_l by auto with wf_db;
  restore_dims;
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
  all : first [destruct off0 | destruct off₁; destruct off₂];
    try destruct off₃; simpl uc_eval; simpl ancillae_for.
  par : post_offset_destruct.
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
      Set Printing Implicit.
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


Definition shor_correct (e : error) : forall (α β : C),
  (@uc_eval dim (shor e)) × ((α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ 8 ⨂ ∣0⟩)
  = (α .* ∣0⟩ .+ β .* ∣1⟩) ⊗ ancillae_for e.
Proof.
  intros.
  Local Opaque encode decode apply_error CCX.
  simpl uc_eval.
  repeat rewrite Mmult_assoc.
  rewrite encode_correct.

  destruct e.
  - simpl ancillae_for.
    specialize (error_decode_correct_no_error α β) as H.
    simpl uc_eval in H.
    simpl ancillae_for in H.
    rewrite Mmult_assoc in H.
    apply H.
  - simpl ancillae_for.
    specialize (error_decode_correct_phase_flip α β e) as H.
    simpl uc_eval in H.
    rewrite Mmult_assoc in H.
    apply H.
  - simpl ancillae_for.
    specialize (error_decode_correct_bit_flip α β e) as H.
    simpl uc_eval in H.
    rewrite Mmult_assoc in H.
    apply H.
  - simpl ancillae_for.
    specialize (error_decode_correct_bit_phase_flip α β e₁ e₂) as H.
    simpl uc_eval in H.
    rewrite Mmult_assoc in H.
    apply H.
Qed.

End NineQubitCode.
