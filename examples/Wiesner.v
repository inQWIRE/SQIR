Require Import Lists.List.
Import ListNotations.

Notation bit_string := (list bool).
Notation combined_bit_string := (list (bool * bool * bool)).

Fixpoint zip {A} {B} (l1 : list A) (l2 : list B) :=
  match l1, l2 with
  | [], _ => []
  | _, []  => []
  | h1::t1, h2::t2 => (h1, h2) :: (zip t1 t2)
  end.


Lemma length_add: forall A (l1 : list A) n, length l1 = S n -> (exists l (a: A), length l = n /\ a::l = l1).
Proof.
  intros.
  induction l1.
  - contradict H.
    auto.
  - exists l1.
    exists a.
    split.
    + simpl in H.
      apply eq_add_S in H.
      assumption.
    + reflexivity.
Qed.

Theorem zip_same_length: forall A B (l1 : list A) (l2 : list B) n, length l1 = n -> length l2 = n -> length (zip l1 l2) = n.
Proof.
  intros.
  generalize dependent l1.
  generalize dependent l2.
  induction n.
  - intros.
    apply length_zero_iff_nil in H.
    apply length_zero_iff_nil in H0.
    subst.
    auto.
  - intros.
    apply length_add in H.
    destruct H.
    destruct H.
    destruct H.
    apply length_add in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    rewrite <- H1.
    rewrite <- H2.
    simpl.
    apply eq_S.
    apply IHn; assumption. 
Qed.


Require Import QWIRE.Dirac.
Require Import UnitarySem.
Require Import DensitySem.
Require Import SQIR.
Local Open Scope ucom.

Definition alice_bit_manip (base : bool) (data : bool) (n i : nat) : base_ucom n :=
  (if data then X i else SKIP);
  (if base then H i else SKIP).

Fixpoint alice_helper (state : list (bool * bool)) (i n : nat) :base_ucom n :=
  match state with
  | [] => SKIP
  | (b,d)::st' => alice_bit_manip b d n i; alice_helper st' (S i) n
  end.

Definition alice (state : list (bool * bool)) (n : nat) : base_ucom n :=
  alice_helper state 0 n.

Definition bob_bit_manip (base : bool) (n i : nat) : base_ucom n :=
  if base then H i else SKIP.


Fixpoint bob_helper (base : bit_string) (i n : nat) : base_ucom n :=
  match base with
  | [] => SKIP
  | b::base' => bob_bit_manip b n i ; bob_helper base' (S i) n
end.

Definition bob (base: bit_string) (n : nat) : base_ucom n := bob_helper base 0 n.

Definition circuit'_qubit_i_non_meas (ad ab bb : bool) (n i : nat) : base_ucom n := alice_bit_manip ab ad n i; bob_bit_manip bb n i.

Fixpoint circuit'_helper (l : combined_bit_string) (n : nat) (i : nat) : base_ucom n :=
  match l with
  | [] => SKIP
  | ((ad,ab),bb)::l' => circuit'_helper l' n (S i); circuit'_qubit_i_non_meas ad ab bb n i
end.

Local Open Scope com_scope.

Fixpoint bob_measure_helper {U} (n i : nat) : com U n := 
  match i with
  | 0 => measure 0
  | S i' => measure i; bob_measure_helper n i'
end.

Definition bob_measure {U} n : com U n := bob_measure_helper n n.

Definition circuit (alice_data alice_base bob_base : bit_string) (n : nat) :=
  alice (zip alice_base alice_data) n; bob bob_base n; bob_measure n.
(* The initial circuit layout turned out to be a bad design, since the interwoven pattern made inductive reasoning very challanging. Hence, this layout exists soely for documentation and as an example of what NOT to do. - See circuit' for a better definition *)

Local Close Scope com_scope.

Definition circuit' (alice_data alice_base bob_base : bit_string) (n : nat) :=
  circuit'_helper (zip (zip alice_data alice_base) bob_base) n 0.


Lemma MmultHHX: (hadamard × hadamard × σx) = σx.
Proof.
  solve_matrix.
Qed.


Lemma circuit'_individual_qubit_non_meas_same_base_false: forall base n i, (n > 0)%nat -> (i < n)%nat -> uc_eval (circuit'_qubit_i_non_meas false base base n i) = I (2 ^ n). 
Proof.
  intros.
  destruct base; simpl; try rewrite denote_H; try rewrite denote_X; try rewrite denote_SKIP.
  - rewrite Mmult_1_r.
    repeat rewrite pad_mult.
    + restore_dims.
      rewrite MmultHH.
      rewrite pad_id.
      * reflexivity.
      * assumption.
    + apply WF_pad.
      apply WF_hadamard.
  - assumption.
  - repeat rewrite Mmult_1_l; try apply WF_I. 
    reflexivity.
  - assumption.
Qed.

Lemma circuit'_individual_qubit_non_meas_same_base_true: forall base n i, (n > 0)%nat -> uc_eval (circuit'_qubit_i_non_meas true base base n i) = @pad 1 i n σx. 
Proof.
  intros.
  destruct base; simpl; try rewrite denote_H; try rewrite denote_X; try rewrite denote_SKIP.
  - repeat rewrite pad_mult.
    rewrite <- Mmult_assoc.
    restore_dims.
    rewrite MmultHHX.
    reflexivity.
  - repeat rewrite Mmult_1_l; try apply WF_pad; try apply WF_σx.
    reflexivity.
  - assumption.
Qed.


Lemma circuit'_individual_qubit_non_meas_diff_base_false: forall base_a base_b n i, base_a <> base_b -> (n > 0)%nat -> uc_eval (circuit'_qubit_i_non_meas false base_a base_b n i) = @pad 1 i n hadamard.
Proof.
  intros.
  destruct base_a, base_b; subst; try contradiction; simpl; try rewrite denote_H; try rewrite denote_X; try rewrite denote_SKIP.
  - rewrite Mmult_1_r; try apply WF_pad; try apply WF_hadamard.
    rewrite Mmult_1_l; try apply WF_pad; try apply WF_hadamard.
    reflexivity.
  - assumption.
  - repeat (rewrite Mmult_1_r; try apply WF_pad; try apply WF_I; try apply WF_hadamard).
    reflexivity.
  - assumption.
Qed.

Lemma circuit'_individual_qubit_non_meas_diff_base_true: forall base_a base_b n i, base_a <> base_b -> (n > 0)%nat -> uc_eval (circuit'_qubit_i_non_meas true base_a base_b n i) = @pad 1 i n (hadamard × σx).
Proof.
  intros.
  destruct base_a, base_b; subst; try contradiction; simpl; try rewrite denote_H; try rewrite denote_X; try rewrite denote_SKIP.
  - rewrite Mmult_1_l.
    + rewrite pad_mult.
      reflexivity.
    + rewrite pad_mult.
      apply WF_pad.
      apply WF_mult.
      * apply WF_hadamard.
      * apply WF_σx.
  - assumption.
  - rewrite Mmult_1_l; try apply WF_pad; try apply WF_σx.
    rewrite pad_mult.
    reflexivity.
  - assumption.
Qed.

Definition mat_data (b : bool) := if b then σx else I 2.

Fixpoint uc_eval_circuit_same_base data :=
  match data with
    | [] => I 1
    | d::data' => uc_eval_circuit_same_base data' ⊗ mat_data d
  end.

Lemma i_1_i_S: forall (i j: nat), i + 1 <=? i + S j = true.
  intros.
  induction j.
  apply Nat.leb_refl.
  apply leb_complete in IHj.
  apply leb_correct.
  eapply Nat.le_trans.
  apply IHj.
  apply plus_le_compat_l.
  constructor.
  constructor.
Qed.

Fixpoint initial_state n : Vector (2^n) :=
  match n with
  | 0 => I 1
  | S n' => ket 0 ⊗ initial_state n'
  end.

Definition q_bool (b:bool) := if b then ket 1 else ket 0.

Notation target_state_qubit_i := q_bool.

Fixpoint target_state n (data: bit_string) : Vector (2^n) :=
  match data with
  | [] => I 1
  | d::data' => target_state_qubit_i d ⊗ target_state (n-1) data'
  end.


Definition output_state_qubit_i (d ab bb : bool) :=
  if (eqb ab bb) then
    q_bool d
  else
    hadamard × q_bool d.

Fixpoint output_state n (l: combined_bit_string) : Vector (2 ^ n) :=
  match l with
  | [] => I 1
  | (d, ab, bb)::l' => output_state_qubit_i d ab bb ⊗ output_state (n-1) l'
  end.

Theorem output_target_equal_base_equal: forall n data base, length data = n -> length base = n -> target_state n data = output_state n (zip (zip data base) base).
Proof.
  intro n.
  induction n; intros.
  - destruct data, base; try discriminate.
    simpl.
    reflexivity.
  - destruct data, base; try discriminate.
    simpl.
    destruct b0; unfold output_state_qubit_i; simpl; rewrite <- minus_n_O; rewrite <- IHn; try (simpl in H; simpl in H0; apply eq_add_S in H; apply eq_add_S in H0; assumption); try (reflexivity).
Qed.

Lemma kron_dist_mult_id : forall n m (B C : Square m) , (I n) ⊗ (B × C) = ((I n) ⊗ B) × ((I n) ⊗ C).
  (* This lemma could potentially be extracted, since it seems quite useful *)
 intros.
 rewrite kron_mixed_product.
 rewrite Mmult_1_l.
 reflexivity.
 apply WF_I.
Qed.

Opaque circuit'_qubit_i_non_meas. (* For usage of lemmata *)

Lemma circuit'_helper_growth_i: forall n l i, (length l = S n) -> uc_eval(circuit'_helper l ((S i) + (S n)) (S i)) =  I (2^(S i)) ⊗ uc_eval (circuit'_helper l (S n) 0).
Proof.
  intro n.
  induction n; intros.
  - destruct l; try discriminate.
    destruct l; try discriminate.
    destruct i.
    * destruct p.
      destruct p.
      destruct b, b1, b0;
      simpl.
      rewrite 2 circuit'_individual_qubit_non_meas_same_base_true.
      restore_dims.
      rewrite unfold_pad.
      rewrite unfold_pad.
      simpl.
      rewrite denote_SKIP.
      rewrite denote_SKIP.
      simpl.
      solve_matrix.
      auto.
      auto.
      auto.
      auto.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_same_base_false.
        restore_dims.
        simpl.
        rewrite denote_SKIP.
        rewrite denote_SKIP.
        solve_matrix.
        auto.
        auto.
        auto.
        auto.
        auto.
        auto.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_diff_base_true.
        restore_dims.
        rewrite 2 denote_SKIP.
        rewrite 2 unfold_pad.
        simpl.
        solve_matrix.
        auto.
        auto.
        auto.
        auto.
        apply diff_false_true.
        auto.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_diff_base_false.
        restore_dims.
        rewrite 2 denote_SKIP.
        rewrite 2 unfold_pad.
        simpl.
        solve_matrix.
        auto.
        auto.
        apply diff_false_true.
        auto.
        apply diff_false_true.
        auto.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_diff_base_true.
        restore_dims.
        rewrite 2 denote_SKIP.
        rewrite 2 unfold_pad.
        simpl.
        solve_matrix.
        auto.
        auto.
        apply diff_true_false.
        auto.
        apply diff_true_false.
        auto.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_diff_base_false.
        restore_dims.
        rewrite 2 denote_SKIP.
        rewrite 2 unfold_pad.
        simpl.
        solve_matrix.
        auto.
        auto.
        apply diff_true_false.
        auto.
        apply diff_true_false.
        auto.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_same_base_true.
        restore_dims.
        rewrite 2 denote_SKIP.
        rewrite 2 unfold_pad.
        simpl.
        solve_matrix.
        auto.
        auto.
        auto.
        auto.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_same_base_false.
        rewrite 2 denote_SKIP.
        solve_matrix.
        auto.
        auto.
        auto.
        auto.
        auto.
        auto.
    * simpl.
      destruct p.
      destruct p.
      destruct b, b0, b1.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_same_base_true.
        rewrite unfold_pad.
        simpl.
        rewrite Nat.leb_refl.
        rewrite 2 denote_SKIP.
        rewrite unfold_pad.
        simpl.
        restore_dims.
        repeat rewrite kron_1_r.
        repeat rewrite kron_1_l.
        repeat rewrite Mmult_1_r.
        rewrite <- kron_1_r.
        restore_dims.
        rewrite Nat.sub_diag.
        rewrite Nat.pow_0_r.
        restore_dims.
        reflexivity.
        apply WF_σx.
        apply WF_kron; try reflexivity.
        apply WF_kron; try reflexivity.
        apply WF_I.
        apply WF_σx.
        apply WF_I.
        apply WF_σx.
        auto.
        apply gt_Sn_O.
        auto.
        apply gt_Sn_O.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_diff_base_true.
        rewrite unfold_pad.
        simpl.
        rewrite Nat.leb_refl.
        rewrite 2 denote_SKIP.
        rewrite unfold_pad.
        simpl.
        restore_dims.
        repeat rewrite kron_1_r.
        repeat rewrite kron_1_l.
        repeat rewrite Mmult_1_r.
        rewrite <- kron_1_r.
        restore_dims.
        rewrite Nat.sub_diag.
        rewrite Nat.pow_0_r.
        restore_dims.
        reflexivity.
        apply WF_mult.
        apply WF_hadamard.
        apply WF_σx.
        apply WF_kron; try reflexivity.
        apply WF_kron; try reflexivity.
        apply WF_I.
        apply WF_mult.
        apply WF_hadamard.
        apply WF_σx.
        apply WF_I.
        apply WF_mult.
        apply WF_hadamard.
        apply WF_σx.
        auto.
        apply gt_Sn_O.
        auto.
        apply gt_Sn_O.
        apply diff_false_true.
        apply gt_Sn_O.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_same_base_false.
        simpl.
        rewrite 2 denote_SKIP.
        simpl.
        restore_dims.
        repeat rewrite kron_1_r.
        repeat rewrite kron_1_l.
        repeat rewrite Mmult_1_r.
        rewrite id_kron.
        repeat rewrite Nat.add_0_r.
        repeat rewrite double_mult.
        rewrite mult_comm.
        rewrite <- pow_two_succ_r.
        reflexivity.
        apply WF_I.
        apply WF_I.
        auto.
        apply gt_Sn_O.
        auto.
        auto.
        apply gt_Sn_O.
        rewrite Nat.add_1_r.
        constructor.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_diff_base_false.
        rewrite unfold_pad.
        simpl.
        rewrite Nat.leb_refl.
        rewrite 2 denote_SKIP.
        rewrite unfold_pad.
        simpl.
        restore_dims.
        repeat rewrite kron_1_r.
        repeat rewrite kron_1_l.
        repeat rewrite Mmult_1_r.
        rewrite <- kron_1_r.
        restore_dims.
        rewrite Nat.sub_diag.
        rewrite Nat.pow_0_r.
        restore_dims.
        reflexivity.
        apply WF_hadamard.
        apply WF_kron; try reflexivity.
        apply WF_kron; try reflexivity.
        apply WF_I.
        apply WF_hadamard.
        apply WF_I.
        apply WF_hadamard.
        auto.
        apply gt_Sn_O.
        apply diff_false_true.
        auto.
        apply diff_false_true.
        apply gt_Sn_O.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_diff_base_true.
        rewrite unfold_pad.
        simpl.
        rewrite Nat.leb_refl.
        rewrite 2 denote_SKIP.
        rewrite unfold_pad.
        simpl.
        restore_dims.
        repeat rewrite kron_1_r.
        repeat rewrite kron_1_l.
        repeat rewrite Mmult_1_r.
        rewrite <- kron_1_r.
        restore_dims.
        rewrite Nat.sub_diag.
        rewrite Nat.pow_0_r.
        restore_dims.
        reflexivity.
        apply WF_mult.
        apply WF_hadamard.
        apply WF_σx.
        apply WF_kron; try reflexivity.
        apply WF_kron; try reflexivity.
        apply WF_I.
        apply WF_mult.
        apply WF_hadamard.
        apply WF_σx.
        apply WF_I.
        apply WF_mult.
        apply WF_hadamard.
        apply WF_σx.
        auto.
        apply gt_Sn_O.
        auto.
        apply diff_true_false.
        auto.
        apply diff_true_false.
        apply gt_Sn_O.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_same_base_true.
        rewrite unfold_pad.
        simpl.
        rewrite Nat.leb_refl.
        rewrite 2 denote_SKIP.
        rewrite unfold_pad.
        simpl.
        restore_dims.
        repeat rewrite kron_1_r.
        repeat rewrite kron_1_l.
        repeat rewrite Mmult_1_r.
        rewrite <- kron_1_r.
        restore_dims.
        rewrite Nat.sub_diag.
        rewrite Nat.pow_0_r.
        restore_dims.
        reflexivity.
        apply WF_σx.
        apply WF_kron; try reflexivity.
        apply WF_kron; try reflexivity.
        apply WF_I.
        apply WF_σx.
        apply WF_I.
        apply WF_σx.
        auto.
        apply gt_Sn_O.
        auto.
        apply gt_Sn_O.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_diff_base_false.
        rewrite unfold_pad.
        simpl.
        rewrite Nat.leb_refl.
        rewrite 2 denote_SKIP.
        rewrite unfold_pad.
        simpl.
        restore_dims.
        repeat rewrite kron_1_r.
        repeat rewrite kron_1_l.
        repeat rewrite Mmult_1_r.
        rewrite <- kron_1_r.
        restore_dims.
        rewrite Nat.sub_diag.
        rewrite Nat.pow_0_r.
        restore_dims.
        reflexivity.
        apply WF_hadamard.
        apply WF_kron; try reflexivity.
        apply WF_kron; try reflexivity.
        apply WF_I.
        apply WF_hadamard.
        apply WF_I.
        apply WF_hadamard.
        auto.
        apply gt_Sn_O.
        apply diff_true_false.
        auto.
        apply diff_true_false.
        apply gt_Sn_O.
      + simpl.
        rewrite 2 circuit'_individual_qubit_non_meas_same_base_false.
        simpl.
        rewrite 2 denote_SKIP.
        simpl.
        restore_dims.
        repeat rewrite kron_1_r.
        repeat rewrite kron_1_l.
        repeat rewrite Mmult_1_r.
        rewrite id_kron.
        repeat rewrite Nat.add_0_r.
        repeat rewrite double_mult.
        rewrite mult_comm.
        rewrite <- pow_two_succ_r.
        reflexivity.
        apply WF_I.
        apply WF_I.
        auto.
        apply gt_Sn_O.
        auto.
        auto.
        apply gt_Sn_O.
        rewrite Nat.add_1_r.
        constructor.
  - destruct l; try discriminate.
    simpl.
    destruct p.
    destruct p.
    simpl.
    destruct b, b0, b1.
    + rewrite 2 circuit'_individual_qubit_non_meas_same_base_true.
      rewrite 2 unfold_pad.
      simpl.
      rewrite i_1_i_S.
      replace (S (i + S (S n))) with (S (S i) + (S n))%nat.
      rewrite IHn.
      replace (S (S n)) with (1 + (S n))%nat. 
      rewrite IHn.
      rewrite kron_1_l.
      replace (2 ^ i + (2 ^ i + 0))%nat with (2 ^ (S i))%nat.
      replace ((i + (1 + S n) - (i + 1)))%nat with (S n).
      replace (2 ^ n + (2 ^n +0))%nat with (2 ^ (S n))%nat.
      restore_dims.
      rewrite kron_dist_mult_id.
      rewrite <- (kron_assoc (I (2^S i)) (I (2 ^1)) (uc_eval (circuit'_helper l (S n) 0))).
      rewrite id_kron.
      replace (2 ^ (S i) * 2 ^ 1)%nat with (2 ^ S (S i))%nat.
      rewrite <- kron_assoc.
      restore_dims.
      reflexivity.
      apply WF_I.
      apply WF_σx.
      apply WF_I.
      rewrite <- Nat.pow_add_r.
      replace (S i + 1)%nat with (S (S i)).
      reflexivity.
      rewrite Nat.add_1_r.
      reflexivity.
      apply WF_I.
      apply WF_I.
      apply WF_uc_eval.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      rewrite Nat.add_assoc.
      rewrite Nat.add_comm.
      rewrite Nat.add_sub.
      reflexivity.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      apply WF_σx.
      simpl in H.
      apply eq_add_S.
      assumption.
      auto.
      simpl in H.
      apply eq_add_S.
      assumption.
      rewrite Nat.add_succ_l.
      apply eq_S.
      replace (S i) with (i + 1)%nat.
      replace (S (S n)) with (1 + (S n))%nat.
      rewrite <- Nat.add_assoc.
      reflexivity.
      auto.
      apply Nat.add_1_r.
      apply gt_Sn_O.
      apply gt_Sn_O.
    + rewrite 2 circuit'_individual_qubit_non_meas_diff_base_true.
      remember (hadamard × σx) as hx.
      rewrite 2 unfold_pad.
      simpl.
      rewrite i_1_i_S.
      replace (S (i + S (S n))) with (S (S i) + (S n))%nat.
      rewrite IHn.
      replace (S (S n)) with (1 + (S n))%nat. 
      rewrite IHn.
      rewrite kron_1_l.
      replace (2 ^ i + (2 ^ i + 0))%nat with (2 ^ (S i))%nat.
      replace ((i + (1 + S n) - (i + 1)))%nat with (S n).
      replace (2 ^ n + (2 ^n +0))%nat with (2 ^ (S n))%nat.
      restore_dims.
      rewrite kron_dist_mult_id.
      rewrite <- (kron_assoc (I (2^S i)) (I (2 ^1)) (uc_eval (circuit'_helper l (S n) 0))).
      rewrite id_kron.
      replace (2 ^ (S i) * 2 ^ 1)%nat with (2 ^ S (S i))%nat.
      rewrite <- kron_assoc.
      restore_dims.
      reflexivity.
      apply WF_I.
      subst.
      apply WF_mult.
      apply WF_hadamard.
      apply WF_σx.
      apply WF_I.
      rewrite <- Nat.pow_add_r.
      replace (S i + 1)%nat with (S (S i)).
      reflexivity.
      rewrite Nat.add_1_r.
      reflexivity.
      apply WF_I.
      apply WF_I.
      apply WF_uc_eval.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      rewrite Nat.add_assoc.
      rewrite Nat.add_comm.
      rewrite Nat.add_sub.
      reflexivity.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      subst.
      apply WF_mult.
      apply WF_hadamard.
      apply WF_σx.
      simpl in H.
      apply eq_add_S.
      assumption.
      auto.
      simpl in H.
      apply eq_add_S.
      assumption.
      rewrite Nat.add_succ_l.
      apply eq_S.
      replace (S i) with (i + 1)%nat.
      replace (S (S n)) with (1 + (S n))%nat.
      rewrite <- Nat.add_assoc.
      reflexivity.
      auto.
      apply Nat.add_1_r.
      apply diff_false_true.
      apply gt_Sn_O.
      apply diff_false_true.
      apply gt_Sn_O.
    + rewrite 2 circuit'_individual_qubit_non_meas_same_base_false.
      simpl.
      repeat rewrite Mmult_1_l.
      repeat rewrite Mmult_1_r.
      replace (S (i + S (S n))) with (S (S i) + (S n))%nat.
      rewrite IHn.
      replace (S (S n)) with (1 + (S n))%nat. 
      rewrite IHn.
      replace (2 ^ i + (2 ^ i + 0))%nat with (2 ^ (S i))%nat.
      restore_dims.
      rewrite <- (kron_assoc (I (2^S i)) (I (2 ^1)) (uc_eval (circuit'_helper l (S n) 0))).
      rewrite id_kron.
      replace (2 ^ (S i) * 2 ^ 1)%nat with (2 ^ S (S i))%nat.
      restore_dims.
      reflexivity.
      rewrite mult_comm.
      rewrite Nat.pow_1_r.
      rewrite pow_two_succ_r.
      replace (S i + 1)%nat with (S (S i)).
      reflexivity.
      rewrite Nat.add_1_r.
      reflexivity.
      apply WF_I.
      apply WF_I.
      apply WF_uc_eval.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      simpl in H.
      apply eq_add_S.
      assumption.
      auto.
      simpl in H.
      apply eq_add_S.
      assumption.
      replace (S i) with (i + 1)%nat.
      replace (S (S n)) with (1 + (S n))%nat.
      rewrite plus_Sn_m.
      rewrite <- Nat.add_assoc.
      reflexivity.
      auto.
      apply Nat.add_1_r.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      apply WF_uc_eval.
      apply gt_Sn_O.
      apply lt_O_Sn.
      apply gt_Sn_O.
      constructor.
      replace (i + S (S n))%nat with (S (S (i +n)))%nat.
      apply le_n_S.
      apply le_n_S.
      apply le_plus_l.
      rewrite <- Nat.add_succ_comm.
      rewrite <- Nat.add_succ_comm.
      rewrite plus_Sn_m.
      rewrite plus_Sn_m.
      reflexivity.
    + rewrite 2 circuit'_individual_qubit_non_meas_diff_base_false.
      rewrite 2 unfold_pad.
      simpl.
      rewrite i_1_i_S.
      replace (S (i + S (S n))) with (S (S i) + (S n))%nat.
      rewrite IHn.
      replace (S (S n)) with (1 + (S n))%nat. 
      rewrite IHn.
      rewrite kron_1_l.
      replace (2 ^ i + (2 ^ i + 0))%nat with (2 ^ (S i))%nat.
      replace ((i + (1 + S n) - (i + 1)))%nat with (S n).
      replace (2 ^ n + (2 ^n +0))%nat with (2 ^ (S n))%nat.
      restore_dims.
      rewrite kron_dist_mult_id.
      rewrite <- (kron_assoc (I (2^S i)) (I (2 ^1)) (uc_eval (circuit'_helper l (S n) 0))).
      rewrite id_kron.
      replace (2 ^ (S i) * 2 ^ 1)%nat with (2 ^ S (S i))%nat.
      rewrite <- kron_assoc.
      restore_dims.
      reflexivity.
      apply WF_I.
      apply WF_hadamard.
      apply WF_I.
      rewrite <- Nat.pow_add_r.
      replace (S i + 1)%nat with (S (S i)).
      reflexivity.
      rewrite Nat.add_1_r.
      reflexivity.
      apply WF_I.
      apply WF_I.
      apply WF_uc_eval.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      rewrite Nat.add_assoc.
      rewrite Nat.add_comm.
      rewrite Nat.add_sub.
      reflexivity.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      apply WF_hadamard.
      simpl in H.
      apply eq_add_S.
      assumption.
      auto.
      simpl in H.
      apply eq_add_S.
      assumption.
      rewrite Nat.add_succ_l.
      apply eq_S.
      replace (S i) with (i + 1)%nat.
      replace (S (S n)) with (1 + (S n))%nat.
      rewrite <- Nat.add_assoc.
      reflexivity.
      auto.
      apply Nat.add_1_r.
      apply diff_false_true.
      apply gt_Sn_O.
      apply diff_false_true.
      apply gt_Sn_O.
    + rewrite 2 circuit'_individual_qubit_non_meas_diff_base_true.
      remember (hadamard × σx) as hx.
      rewrite 2 unfold_pad.
      simpl.
      rewrite i_1_i_S.
      replace (S (i + S (S n))) with (S (S i) + (S n))%nat.
      rewrite IHn.
      replace (S (S n)) with (1 + (S n))%nat. 
      rewrite IHn.
      rewrite kron_1_l.
      replace (2 ^ i + (2 ^ i + 0))%nat with (2 ^ (S i))%nat.
      replace ((i + (1 + S n) - (i + 1)))%nat with (S n).
      replace (2 ^ n + (2 ^n +0))%nat with (2 ^ (S n))%nat.
      restore_dims.
      rewrite kron_dist_mult_id.
      rewrite <- (kron_assoc (I (2^S i)) (I (2 ^1)) (uc_eval (circuit'_helper l (S n) 0))).
      rewrite id_kron.
      replace (2 ^ (S i) * 2 ^ 1)%nat with (2 ^ S (S i))%nat.
      rewrite <- kron_assoc.
      restore_dims.
      reflexivity.
      apply WF_I.
      subst.
      apply WF_mult.
      apply WF_hadamard.
      apply WF_σx.
      apply WF_I.
      rewrite <- Nat.pow_add_r.
      replace (S i + 1)%nat with (S (S i)).
      reflexivity.
      rewrite Nat.add_1_r.
      reflexivity.
      apply WF_I.
      apply WF_I.
      apply WF_uc_eval.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      rewrite Nat.add_assoc.
      rewrite Nat.add_comm.
      rewrite Nat.add_sub.
      reflexivity.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      subst.
      apply WF_mult.
      apply WF_hadamard.
      apply WF_σx.
      simpl in H.
      apply eq_add_S.
      assumption.
      auto.
      simpl in H.
      apply eq_add_S.
      assumption.
      rewrite Nat.add_succ_l.
      apply eq_S.
      replace (S i) with (i + 1)%nat.
      replace (S (S n)) with (1 + (S n))%nat.
      rewrite <- Nat.add_assoc.
      reflexivity.
      auto.
      apply Nat.add_1_r.
      apply diff_true_false.
      apply gt_Sn_O.
      apply diff_true_false.
      apply gt_Sn_O. 
    + rewrite 2 circuit'_individual_qubit_non_meas_same_base_true.
      rewrite 2 unfold_pad.
      simpl.
      rewrite i_1_i_S.
      replace (S (i + S (S n))) with (S (S i) + (S n))%nat.
      rewrite IHn.
      replace (S (S n)) with (1 + (S n))%nat. 
      rewrite IHn.
      rewrite kron_1_l.
      replace (2 ^ i + (2 ^ i + 0))%nat with (2 ^ (S i))%nat.
      replace ((i + (1 + S n) - (i + 1)))%nat with (S n).
      replace (2 ^ n + (2 ^n +0))%nat with (2 ^ (S n))%nat.
      restore_dims.
      rewrite kron_dist_mult_id.
      rewrite <- (kron_assoc (I (2^S i)) (I (2 ^1)) (uc_eval (circuit'_helper l (S n) 0))).
      rewrite id_kron.
      replace (2 ^ (S i) * 2 ^ 1)%nat with (2 ^ S (S i))%nat.
      rewrite <- kron_assoc.
      restore_dims.
      reflexivity.
      apply WF_I.
      apply WF_σx.
      apply WF_I.
      rewrite <- Nat.pow_add_r.
      replace (S i + 1)%nat with (S (S i)).
      reflexivity.
      rewrite Nat.add_1_r.
      reflexivity.
      apply WF_I.
      apply WF_I.
      apply WF_uc_eval.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      rewrite Nat.add_assoc.
      rewrite Nat.add_comm.
      rewrite Nat.add_sub.
      reflexivity.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      apply WF_σx.
      simpl in H.
      apply eq_add_S.
      assumption.
      auto.
      simpl in H.
      apply eq_add_S.
      assumption.
      rewrite Nat.add_succ_l.
      apply eq_S.
      replace (S i) with (i + 1)%nat.
      replace (S (S n)) with (1 + (S n))%nat.
      rewrite <- Nat.add_assoc.
      reflexivity.
      auto.
      apply Nat.add_1_r.
      apply gt_Sn_O.
      apply gt_Sn_O.
    + rewrite 2 circuit'_individual_qubit_non_meas_diff_base_false.
      rewrite 2 unfold_pad.
      simpl.
      rewrite i_1_i_S.
      replace (S (i + S (S n))) with (S (S i) + (S n))%nat.
      rewrite IHn.
      replace (S (S n)) with (1 + (S n))%nat. 
      rewrite IHn.
      rewrite kron_1_l.
      replace (2 ^ i + (2 ^ i + 0))%nat with (2 ^ (S i))%nat.
      replace ((i + (1 + S n) - (i + 1)))%nat with (S n).
      replace (2 ^ n + (2 ^n +0))%nat with (2 ^ (S n))%nat.
      restore_dims.
      rewrite kron_dist_mult_id.
      rewrite <- (kron_assoc (I (2^S i)) (I (2 ^1)) (uc_eval (circuit'_helper l (S n) 0))).
      rewrite id_kron.
      replace (2 ^ (S i) * 2 ^ 1)%nat with (2 ^ S (S i))%nat.
      rewrite <- kron_assoc.
      restore_dims.
      reflexivity.
      apply WF_I.
      apply WF_hadamard.
      apply WF_I.
      rewrite <- Nat.pow_add_r.
      replace (S i + 1)%nat with (S (S i)).
      reflexivity.
      rewrite Nat.add_1_r.
      reflexivity.
      apply WF_I.
      apply WF_I.
      apply WF_uc_eval.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      rewrite Nat.add_assoc.
      rewrite Nat.add_comm.
      rewrite Nat.add_sub.
      reflexivity.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      apply WF_hadamard.
      simpl in H.
      apply eq_add_S.
      assumption.
      auto.
      simpl in H.
      apply eq_add_S.
      assumption.
      rewrite Nat.add_succ_l.
      apply eq_S.
      replace (S i) with (i + 1)%nat.
      replace (S (S n)) with (1 + (S n))%nat.
      rewrite <- Nat.add_assoc.
      reflexivity.
      auto.
      apply Nat.add_1_r.
      apply diff_true_false.
      apply gt_Sn_O.
      apply diff_true_false.
      apply gt_Sn_O.
    + rewrite 2 circuit'_individual_qubit_non_meas_same_base_false.
      simpl.
      repeat rewrite Mmult_1_l.
      repeat rewrite Mmult_1_r.
      replace (S (i + S (S n))) with (S (S i) + (S n))%nat.
      rewrite IHn.
      replace (S (S n)) with (1 + (S n))%nat. 
      rewrite IHn.
      replace (2 ^ i + (2 ^ i + 0))%nat with (2 ^ (S i))%nat.
      restore_dims.
      rewrite <- (kron_assoc (I (2^S i)) (I (2 ^1)) (uc_eval (circuit'_helper l (S n) 0))).
      rewrite id_kron.
      replace (2 ^ (S i) * 2 ^ 1)%nat with (2 ^ S (S i))%nat.
      restore_dims.
      reflexivity.
      rewrite mult_comm.
      rewrite Nat.pow_1_r.
      rewrite pow_two_succ_r.
      replace (S i + 1)%nat with (S (S i)).
      reflexivity.
      rewrite Nat.add_1_r.
      reflexivity.
      apply WF_I.
      apply WF_I.
      apply WF_uc_eval.
      rewrite Nat.add_0_r.
      rewrite double_mult.
      rewrite Nat.pow_succ_r.
      reflexivity.
      apply Nat.le_0_l.
      simpl in H.
      apply eq_add_S.
      assumption.
      auto.
      simpl in H.
      apply eq_add_S.
      assumption.
      replace (S i) with (i + 1)%nat.
      replace (S (S n)) with (1 + (S n))%nat.
      rewrite plus_Sn_m.
      rewrite <- Nat.add_assoc.
      reflexivity.
      auto.
      apply Nat.add_1_r.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      apply WF_uc_eval.
      apply gt_Sn_O.
      apply lt_O_Sn.
      apply gt_Sn_O.
      constructor.
      replace (i + S (S n))%nat with (S (S (i +n)))%nat.
      apply le_n_S.
      apply le_n_S.
      apply le_plus_l.
      rewrite <- Nat.add_succ_comm.
      rewrite <- Nat.add_succ_comm.
      rewrite plus_Sn_m.
      rewrite plus_Sn_m.
      reflexivity.
Qed.

Theorem circuit'_helper_growth: forall n l, (length l = S n) ->  uc_eval(circuit'_helper l (S (S n)) 1) =  I 2 ⊗ uc_eval (circuit'_helper l (S n) 0).
  intros.
  replace (S (S n)) with (1+(S n))%nat.
  - rewrite (circuit'_helper_growth_i n l 0%nat).
    + reflexivity.
    + assumption.
  - auto.
Qed.

Theorem circuit'_output_correct: forall n data ab bb, (length data = S n) -> (length ab = S n) -> (length bb = S n) -> (uc_eval (circuit' data ab bb (S n))) × initial_state (S n) = output_state (S n) (zip (zip data ab) bb).
Proof.
  intros n.
  induction n; intros.
  - simpl.
    destruct data, ab, bb; try discriminate.
    destruct data, ab, bb; try discriminate.
    destruct b, b0, b1; simpl; try rewrite circuit'_individual_qubit_non_meas_same_base_true; try rewrite circuit'_individual_qubit_non_meas_same_base_false; try rewrite circuit'_individual_qubit_non_meas_diff_base_false; try rewrite circuit'_individual_qubit_non_meas_diff_base_true; try rewrite denote_SKIP; try rewrite denote_X; try rewrite denote_H; try auto; try apply diff_true_false; try apply diff_false_true.
     + simpl.
      rewrite Mmult_1_r.
      rewrite kron_1_r.
      restore_dims.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      rewrite kron_1_r.
      solve_matrix.
      apply WF_σx.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      rewrite kron_1_r.
      apply WF_σx.
      apply WF_σx.
    + simpl.
      rewrite Mmult_1_r.
      rewrite kron_1_r.
      restore_dims.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      rewrite kron_1_r.
      solve_matrix.
      unfold output_state_qubit_i.
      apply WF_mult.
      apply WF_hadamard.
      apply WF_σx.
      restore_dims.
      apply WF_pad.
      apply WF_mult.
      apply WF_hadamard.
      apply WF_σx.
    + simpl.
      rewrite Mmult_1_r.
      rewrite kron_1_r.
      restore_dims.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      rewrite kron_1_r.
      solve_matrix.
      unfold output_state_qubit_i.
      apply WF_mult.
      apply WF_hadamard.
      apply WF_σx.
      restore_dims.
      apply WF_pad.
      apply WF_mult.
      apply WF_hadamard.
      apply WF_σx.
    + simpl.
      rewrite Mmult_1_r.
      rewrite kron_1_r.
      restore_dims.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      rewrite kron_1_r.
      solve_matrix.
      apply WF_σx.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      rewrite kron_1_r.
      apply WF_σx.
      apply WF_σx.
    + rewrite Mmult_1_l.
      rewrite Mmult_1_l.
      reflexivity.
      rewrite kron_1_r.
      apply WF_ket.
      apply WF_I.
    + simpl.
      rewrite Mmult_1_r.
      rewrite kron_1_r.
      restore_dims.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      rewrite kron_1_r.
      solve_matrix.
      unfold output_state_qubit_i.
      apply WF_hadamard.
      restore_dims.
      apply WF_pad.
      apply WF_hadamard.
    + simpl.
      rewrite Mmult_1_r.
      rewrite kron_1_r.
      restore_dims.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      rewrite kron_1_r.
      solve_matrix.
      unfold output_state_qubit_i.
      apply WF_hadamard.
      restore_dims.
      apply WF_pad.
      apply WF_hadamard.
    + rewrite Mmult_1_l.
      rewrite Mmult_1_l.
      reflexivity.
      rewrite kron_1_r.
      apply WF_ket.
      apply WF_I.
  
  - simpl.
    destruct data, ab, bb; try discriminate.
    simpl.
    rewrite <- (IHn data ab bb).
    destruct b, b0, b1.
    + rewrite circuit'_individual_qubit_non_meas_same_base_true.
      rewrite circuit'_helper_growth.
      simpl.
      fold circuit'.
      replace (circuit'_helper (zip (zip data ab) bb) (S n)0) with (circuit' data ab bb (S n)).
      rewrite IHn.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      restore_dims.
      replace (σx ⊗ (I (2 ^n + (2 ^ n + 0))) × ((I 2) ⊗ (uc_eval (circuit' data ab bb (S n))))) with ((σx × I 2) ⊗ ( (I (2 ^n + (2 ^n + 0))) × uc_eval (circuit' data ab bb (S n)))).
      rewrite Mmult_1_l.
      rewrite Mmult_1_r.
      rewrite kron_mixed_product.
      replace (ket 0 ⊗ initial_state n) with (initial_state (S n)).
      rewrite IHn.
      replace (σx × ket 0) with (ket 1).
      reflexivity.
      solve_matrix.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      simpl.
      reflexivity.
      apply WF_σx.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      prep_matrix_equality.
      rewrite kron_mixed_product.
      simpl.
      reflexivity.
      apply WF_σx.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      unfold circuit'.
      reflexivity.
      simpl in H.
      simpl in H0.
      simpl in H1.
      apply eq_add_S in H.
      apply eq_add_S in H0.
      apply eq_add_S in H1.
      apply zip_same_length; try (apply zip_same_length; try assumption); try assumption.
      apply gt_Sn_O.
    + rewrite circuit'_individual_qubit_non_meas_diff_base_true.
      rewrite circuit'_helper_growth.
      simpl.
      fold circuit'.
      replace (circuit'_helper (zip (zip data ab) bb) (S n)0) with (circuit' data ab bb (S n)).
      rewrite IHn.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      restore_dims.
      replace (hadamard × σx ⊗ (I (2 ^n + (2 ^ n + 0))) × ((I 2) ⊗ (uc_eval (circuit' data ab bb (S n))))) with ((hadamard × σx × I 2) ⊗ ( (I (2 ^n + (2 ^n + 0))) × uc_eval (circuit' data ab bb (S n)))).
      rewrite Mmult_1_l.
      rewrite Mmult_1_r.
      rewrite kron_mixed_product.
      replace (ket 0 ⊗ initial_state n) with (initial_state (S n)).
      rewrite IHn.
      replace (hadamard × σx × ket 0) with (hadamard × ket 1).
      reflexivity.
      solve_matrix.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      simpl.
      reflexivity.
      apply WF_mult.
      apply WF_hadamard.
      apply WF_σx.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      prep_matrix_equality.
      rewrite kron_mixed_product.
      simpl.
      reflexivity.
      apply WF_mult.
      apply WF_hadamard.
      apply WF_σx.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      unfold circuit'.
      reflexivity.
      simpl in H.
      simpl in H0.
      simpl in H1.
      apply eq_add_S in H.
      apply eq_add_S in H0.
      apply eq_add_S in H1.
      apply zip_same_length; try (apply zip_same_length; try assumption); try assumption.
      apply diff_true_false.
      apply gt_Sn_O.
    + rewrite circuit'_individual_qubit_non_meas_diff_base_true.
      rewrite circuit'_helper_growth.
      simpl.
      fold circuit'.
      replace (circuit'_helper (zip (zip data ab) bb) (S n)0) with (circuit' data ab bb (S n)).
      rewrite IHn.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      restore_dims.
      replace (hadamard × σx ⊗ (I (2 ^n + (2 ^ n + 0))) × ((I 2) ⊗ (uc_eval (circuit' data ab bb (S n))))) with ((hadamard × σx × I 2) ⊗ ( (I (2 ^n + (2 ^n + 0))) × uc_eval (circuit' data ab bb (S n)))).
      rewrite Mmult_1_l.
      rewrite Mmult_1_r.
      rewrite kron_mixed_product.
      replace (ket 0 ⊗ initial_state n) with (initial_state (S n)).
      rewrite IHn.
      replace (hadamard × σx × ket 0) with (hadamard × ket 1).
      reflexivity.
      solve_matrix.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      simpl.
      reflexivity.
      apply WF_mult.
      apply WF_hadamard.
      apply WF_σx.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      prep_matrix_equality.
      rewrite kron_mixed_product.
      simpl.
      reflexivity.
      apply WF_mult.
      apply WF_hadamard.
      apply WF_σx.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      unfold circuit'.
      reflexivity.
      simpl in H.
      simpl in H0.
      simpl in H1.
      apply eq_add_S in H.
      apply eq_add_S in H0.
      apply eq_add_S in H1.
      apply zip_same_length; try (apply zip_same_length; try assumption); try assumption.
      apply diff_false_true.
      apply gt_Sn_O.
    + rewrite circuit'_individual_qubit_non_meas_same_base_true.
      rewrite circuit'_helper_growth.
      simpl.
      fold circuit'.
      replace (circuit'_helper (zip (zip data ab) bb) (S n)0) with (circuit' data ab bb (S n)).
      rewrite IHn.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      restore_dims.
      replace (σx ⊗ (I (2 ^n + (2 ^ n + 0))) × ((I 2) ⊗ (uc_eval (circuit' data ab bb (S n))))) with ((σx × I 2) ⊗ ( (I (2 ^n + (2 ^n + 0))) × uc_eval (circuit' data ab bb (S n)))).
      rewrite Mmult_1_l.
      rewrite Mmult_1_r.
      rewrite kron_mixed_product.
      replace (ket 0 ⊗ initial_state n) with (initial_state (S n)).
      rewrite IHn.
      replace (σx × ket 0) with (ket 1).
      reflexivity.
      solve_matrix.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      simpl.
      reflexivity.
      apply WF_σx.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      prep_matrix_equality.
      rewrite kron_mixed_product.
      simpl.
      reflexivity.
      apply WF_σx.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      unfold circuit'.
      reflexivity.
      simpl in H.
      simpl in H0.
      simpl in H1.
      apply eq_add_S in H.
      apply eq_add_S in H0.
      apply eq_add_S in H1.
      apply zip_same_length; try (apply zip_same_length; try assumption); try assumption.
      apply gt_Sn_O.
    + simpl.
      rewrite circuit'_helper_growth.
      simpl.
      fold circuit'.
      replace (circuit'_helper (zip (zip data ab) bb) (S n)0) with (circuit' data ab bb (S n)).
      rewrite IHn.
      rewrite circuit'_individual_qubit_non_meas_same_base_false.
      simpl.
      restore_dims.
      replace (σx ⊗ (I (2 ^n + (2 ^ n + 0))) × ((I 2) ⊗ (uc_eval (circuit' data ab bb (S n))))) with ((σx × I 2) ⊗ ( (I (2 ^n + (2 ^n + 0))) × uc_eval (circuit' data ab bb (S n)))).
      rewrite Mmult_1_l.
      rewrite kron_mixed_product.
      replace (ket 0 ⊗ initial_state n) with (initial_state (S n)).
      rewrite IHn.
      replace (σx × ket 0) with (ket 1).
      rewrite Mmult_1_l.
      reflexivity.
      apply WF_ket.
      solve_matrix.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      simpl.
      reflexivity.
      simpl in H.
      apply eq_add_S in H.
      apply WF_kron.
      reflexivity.
      reflexivity.
      apply WF_I.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      prep_matrix_equality.
      rewrite kron_mixed_product.
      simpl.
      reflexivity.
      apply gt_Sn_O.
      apply lt_O_Sn.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      unfold circuit'.
      reflexivity.
      simpl in H.
      simpl in H0.
      simpl in H1.
      apply eq_add_S in H.
      apply eq_add_S in H0.
      apply eq_add_S in H1.
      apply zip_same_length; try (apply zip_same_length; try assumption); try assumption.
    + rewrite circuit'_individual_qubit_non_meas_diff_base_false.
      rewrite circuit'_helper_growth.
      simpl.
      fold circuit'.
      replace (circuit'_helper (zip (zip data ab) bb) (S n)0) with (circuit' data ab bb (S n)).
      rewrite IHn.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      restore_dims.
      replace (hadamard ⊗ (I (2 ^n + (2 ^ n + 0))) × ((I 2) ⊗ (uc_eval (circuit' data ab bb (S n))))) with ((hadamard × I 2) ⊗ ( (I (2 ^n + (2 ^n + 0))) × uc_eval (circuit' data ab bb (S n)))).
      rewrite Mmult_1_l.
      rewrite Mmult_1_r.
      rewrite kron_mixed_product.
      replace (ket 0 ⊗ initial_state n) with (initial_state (S n)).
      rewrite IHn.
      replace (hadamard × ket 0) with (hadamard × ket 0).
      reflexivity.
      solve_matrix.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      simpl.
      reflexivity.
      apply WF_hadamard.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      prep_matrix_equality.
      rewrite kron_mixed_product.
      simpl.
      reflexivity.
      apply WF_hadamard.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      unfold circuit'.
      reflexivity.
      simpl in H.
      simpl in H0.
      simpl in H1.
      apply eq_add_S in H.
      apply eq_add_S in H0.
      apply eq_add_S in H1.
      apply zip_same_length; try (apply zip_same_length; try assumption); try assumption.
      apply diff_true_false.
      apply gt_Sn_O.
    + rewrite circuit'_individual_qubit_non_meas_diff_base_false.
      rewrite circuit'_helper_growth.
      simpl.
      fold circuit'.
      replace (circuit'_helper (zip (zip data ab) bb) (S n)0) with (circuit' data ab bb (S n)).
      rewrite IHn.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      restore_dims.
      replace (hadamard ⊗ (I (2 ^n + (2 ^ n + 0))) × ((I 2) ⊗ (uc_eval (circuit' data ab bb (S n))))) with ((hadamard × I 2) ⊗ ( (I (2 ^n + (2 ^n + 0))) × uc_eval (circuit' data ab bb (S n)))).
      rewrite Mmult_1_l.
      rewrite Mmult_1_r.
      rewrite kron_mixed_product.
      replace (ket 0 ⊗ initial_state n) with (initial_state (S n)).
      rewrite IHn.
      replace (hadamard × ket 0) with (hadamard × ket 0).
      reflexivity.
      solve_matrix.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      simpl.
      reflexivity.
      apply WF_hadamard.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      prep_matrix_equality.
      rewrite kron_mixed_product.
      simpl.
      reflexivity.
      apply WF_hadamard.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      unfold circuit'.
      reflexivity.
      simpl in H.
      simpl in H0.
      simpl in H1.
      apply eq_add_S in H.
      apply eq_add_S in H0.
      apply eq_add_S in H1.
      apply zip_same_length; try (apply zip_same_length; try assumption); try assumption.
      apply diff_false_true.
      apply gt_Sn_O.
    + simpl.
      rewrite circuit'_helper_growth.
      rewrite circuit'_individual_qubit_non_meas_same_base_false.      
      simpl.
      fold circuit'.
      replace (circuit'_helper (zip (zip data ab) bb) (S n)0) with (circuit' data ab bb (S n)).
      rewrite IHn.
      simpl.
      restore_dims.
      replace (σx ⊗ (I (2 ^n + (2 ^ n + 0))) × ((I 2) ⊗ (uc_eval (circuit' data ab bb (S n))))) with ((σx × I 2) ⊗ ( (I (2 ^n + (2 ^n + 0))) × uc_eval (circuit' data ab bb (S n)))).
      rewrite Mmult_1_l.
      rewrite kron_mixed_product.
      replace (ket 0 ⊗ initial_state n) with (initial_state (S n)).
      rewrite IHn.
      replace (σx × ket 0) with (ket 1).
      restore_dims.
      rewrite Mmult_1_l.
      reflexivity.
      apply WF_ket.
      solve_matrix.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      simpl.
      reflexivity.
      apply WF_kron.
      reflexivity.
      reflexivity.
      apply WF_I.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      prep_matrix_equality.
      rewrite kron_mixed_product.
      simpl.
      reflexivity.
      simpl in H.
      apply eq_add_S in H.
      assumption.
      simpl in H0.
      apply eq_add_S in H0.
      assumption.
      simpl in H1.
      apply eq_add_S in H1.
      assumption.
      unfold circuit'.
      reflexivity.
      apply gt_Sn_O.
      apply lt_O_Sn.
      simpl in H.
      simpl in H0.
      simpl in H1.
      apply eq_add_S in H.
      apply eq_add_S in H0.
      apply eq_add_S in H1.
      apply zip_same_length; try (apply zip_same_length; try assumption); try assumption.
   + simpl in H.
     apply eq_add_S in H.
     assumption.
   + simpl in H0.
     apply eq_add_S in H0.
     assumption.
   + simpl in H1.
     apply eq_add_S in H1.
     assumption.
Qed.


Theorem circuit'_same_base_correct: forall n data base, (length data = S n) -> (length base = S n) -> (uc_eval (circuit' data base base (S n))) × initial_state (S n) = target_state (S n) data.
Proof.
  intros.
  rewrite (output_target_equal_base_equal (S n) data base); try assumption.
  apply circuit'_output_correct; assumption.
Qed.

Lemma norm_kron: forall (A : Vector 1) (B : Vector 1), @norm (1) (A ⊗ B) = (@norm 1 A * @norm 1 B)%R.
  unfold norm.
  unfold kron.
  intros.
  simpl.
  remember (fst (A 0%nat 0%nat)) as a10.
  remember (snd (A 0%nat 0%nat)) as a20.
  remember (fst (B 0%nat 0%nat)) as b10.
  remember (snd (B 0%nat 0%nat)) as b20.
  replace (a10 * a10)%R with (a10 ^ 2)%R by lra.
  replace (- a20 * a20)%R with (-(a20 ^ 2))%R by lra.
  replace (b10 * b10)%R with (b10 ^ 2)%R by lra.
  replace (- b20 * b20)%R with (-(b20 ^ 2))%R by lra.
  rewrite <- sqrt_mult.
  rewrite 3 Rplus_0_l.
  repeat (
  repeat rewrite Rmult_minus_distr_l;
  repeat rewrite Rmult_minus_distr_r;
  repeat rewrite Rmult_plus_distr_l;
  repeat rewrite Rmult_plus_distr_r
    ).
  repeat rewrite Rminus_unfold.
  repeat rewrite Ropp_involutive.
  rewrite <- (Rplus_comm (- (a20 * b20 * (a10 * b10))) (a10 * b10 * (a10 * b10))).
  repeat rewrite Ropp_mult_distr_l.
  repeat rewrite Ropp_involutive.
  repeat rewrite Ropp_mult_distr_r.
  repeat rewrite <- Rmult_plus_distr_r.
  repeat rewrite Ropp_mult_distr_r.
  repeat rewrite Ropp_involutive.
  rewrite Ropp_plus_distr.
  rewrite Ropp_mult_distr_l.
  rewrite Ropp_mult_distr_r.
  repeat rewrite Ropp_involutive.
  replace ((- a20 * b20 + a10 * b10) * (a10 * b10))%R with ((-a20 * b20 * a10 + a10 ^2 * b10) * b10)%R by lra.
  replace ( (a10 * b10 + - a20 * b20) * (a20 * - b20) )%R with ((-a10 *b10 *a20 + a20 ^ 2 * b20) * b20)%R by lra.
  replace (((a10 * b20 + a20 * b10) * (a10 * b20)))%R with ((a10 ^2 *b20 + a20 * b10 * a10) * b20)%R by lra.
  rewrite Rmult_opp_opp.
  replace ((a10 * b20 + a20 * b10) * (a20 * b10))%R with ((a10 *b20 *a20 + a20 ^2 * b10) * b10)%R by lra.
  rewrite <- Rplus_assoc.
  rewrite Rplus_comm.
  rewrite Rplus_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- Rplus_assoc.
  rewrite <- Rplus_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- Rplus_assoc.
  replace ((a10 * b20 * a20 + a20 ^ 2 * b10 + - a20 * b20 * a10 + a10 ^ 2 * b10))%R with ((a10 ^2 + a20 ^2) * b10 )%R by lra.
  replace ( (- a10 * b10 * a20 + a20 ^ 2 * b20 + a10 ^ 2 * b20 + a20 * b10 * a10))%R with ((a10 ^2  + a20^2)*b20)%R by lra.
  rewrite Rmult_assoc.
  rewrite Rmult_assoc.
  replace (b10 * b10)%R with (b10 * b10 ^ 1)%R by lra.
  replace (b20 * b20)%R with (b20 * b20 ^ 1)%R by lra.
  rewrite (tech_pow_Rmult b10 1).
  rewrite (tech_pow_Rmult b20 1).
  reflexivity.
  apply Rplus_le_le_0_compat.
  apply Rle_refl.
  replace ( a10 ^ 2 - - a20 ^ 2)%R with (a10 ^2 + a20 ^2)%R by lra.
  apply Rplus_le_le_0_compat; apply pow2_ge_0.
  apply Rplus_le_le_0_compat.
  apply Rle_refl.
  replace ( b10 ^ 2 - - b20 ^ 2)%R with (b10 ^2 + b20 ^2)%R by lra.
  apply Rplus_le_le_0_compat; apply pow2_ge_0.
Qed.

Lemma target_state_norm: forall n data, (length data = S n) -> norm ((target_state (S n) data)† × (target_state (S n) data)) = 1.
Proof.
  intro n.
  induction n; intros.
  - destruct data; try discriminate.
    destruct data; try discriminate.
    destruct b;
    simpl;
    rewrite kron_1_r;
    rewrite ket2bra;
    try rewrite bra1ket1; try rewrite bra0ket0;
    unfold norm;
    simpl;
    replace (0 + (1 * 1 - - 0 * 0))%R with 1%R by lra;
    apply sqrt_1.
  - destruct data; try discriminate.
    destruct b;
    simpl;
    restore_dims;
    rewrite kron_adjoint;
    rewrite kron_mixed_product;
    rewrite norm_kron;
    rewrite IHn; try (simpl in H; apply eq_add_S in H; assumption);
    simpl;
    rewrite ket2bra;
    try rewrite bra1ket1; try rewrite bra0ket0;
    unfold norm;
    simpl;
    replace (0 + (1 * 1 - - 0 * 0))%R with 1%R by lra;
    rewrite sqrt_1;
    lra.
Qed.

Require Import Utilities.

Theorem probibility_correct: forall n data base, (length data = S n) -> (length base = S n) -> probability_of_outcome (uc_eval (circuit' data base base (S n)) × initial_state (S n)) (target_state (S n) data) = 1%R.
  intros.
  rewrite circuit'_same_base_correct; try assumption.
  rewrite probability_of_outcome_is_norm.
  rewrite target_state_norm; try assumption.
  lra.
Qed.

Theorem probability_correct_single_qubit: forall data base, probability_of_outcome (output_state_qubit_i data base base) (target_state_qubit_i data) = 1.
Proof.
  intros.
  destruct data, base;
  unfold output_state_qubit_i;
  simpl;
  unfold probability_of_outcome;
  unfold Cmod;
  simpl;
  C_field_simplify;
  R_field_simplify;
  repeat (
  repeat rewrite Rmult_0_l;
  repeat rewrite Rmult_0_r;
  repeat rewrite Rplus_0_l;
  repeat rewrite Rplus_0_r;
  repeat rewrite Rminus_0_l;
  repeat rewrite Rminus_0_r;
  repeat rewrite Ropp_0;
  repeat rewrite Rmult_1_l;
  repeat rewrite rmult_1_r
  );
  rewrite sqrt_1;
  R_field.
Qed.

Theorem probability_incorrect_single_qubit: forall data ab bb, (ab <> bb) -> probability_of_outcome (output_state_qubit_i data ab bb) (target_state_qubit_i data) = (1/2)%R.
Proof.
  intros.
  destruct data, ab, bb; try contradiction; simpl; unfold output_state_qubit_i; simpl.
  - unfold probability_of_outcome.
    replace (((hadamard × ket 1)† × ket 1) 0%nat 0%nat) with (-/ √ 2).
    replace (Cmod (-/ √ 2)) with (/ √ 2)%R.
    simpl.
    R_field_simplify.
    reflexivity.
    apply sqrt_neq_0_compat.
    apply Rlt_0_2.
    unfold Cmod.
    replace (fst (-/ √ 2)) with (-/ √ 2)%R.
    replace (snd (-/ √ 2)) with (0%R).
    rewrite <- sqrt2_inv.
    simpl.
    rewrite Rmult_1_r.
    rewrite Rmult_opp_opp.
    rewrite sqrt_def.
    rewrite Rmult_0_l.
    rewrite Rplus_0_r.
    reflexivity.
    lra.
    unfold snd.
    simpl.
    R_field_simplify.
    reflexivity.
    apply sqrt2_neq_0.
    unfold fst.
    simpl.
    R_field_simplify.
    reflexivity.
    apply sqrt2_neq_0.
    replace ((hadamard × ket 1)† × ket 1) with (list2D_to_matrix [[- / √ 2]]).
    reflexivity.
    restore_dims.
    solve_matrix.
  - unfold probability_of_outcome.
    replace (((hadamard × ket 1)† × ket 1) 0%nat 0%nat) with (-/ √ 2).
    replace (Cmod (-/ √ 2)) with (/ √ 2)%R.
    simpl.
    R_field_simplify.
    reflexivity.
    apply sqrt_neq_0_compat.
    apply Rlt_0_2.
    unfold Cmod.
    replace (fst (-/ √ 2)) with (-/ √ 2)%R.
    replace (snd (-/ √ 2)) with (0%R).
    rewrite <- sqrt2_inv.
    simpl.
    rewrite Rmult_1_r.
    rewrite Rmult_opp_opp.
    rewrite sqrt_def.
    rewrite Rmult_0_l.
    rewrite Rplus_0_r.
    reflexivity.
    lra.
    unfold snd.
    simpl.
    R_field_simplify.
    reflexivity.
    apply sqrt2_neq_0.
    unfold fst.
    simpl.
    R_field_simplify.
    reflexivity.
    apply sqrt2_neq_0.
    replace ((hadamard × ket 1)† × ket 1) with (list2D_to_matrix [[- / √ 2]]).
    reflexivity.
    restore_dims.
    solve_matrix.
  - unfold probability_of_outcome.
    replace (((hadamard × ket 0)† × ket 0) 0%nat 0%nat) with (/ √ 2).
    replace (Cmod (/ √ 2)) with (/ √ 2)%R.
    simpl.
    R_field_simplify.
    reflexivity.
    apply sqrt_neq_0_compat.
    apply Rlt_0_2.
    unfold Cmod.
    replace (fst (/ √ 2)) with (/ √ 2)%R.
    replace (snd (/ √ 2)) with (0%R).
    rewrite <- sqrt2_inv.
    simpl.
    rewrite Rmult_1_r.
    rewrite sqrt_def.
    rewrite Rmult_0_l.
    rewrite Rplus_0_r.
    reflexivity.
    lra.
    unfold snd.
    simpl.
    R_field_simplify.
    reflexivity.
    apply sqrt2_neq_0.
    unfold fst.
    simpl.
    R_field_simplify.
    reflexivity.
    apply sqrt2_neq_0.
    replace ((hadamard × ket 0)† × ket 0) with (list2D_to_matrix [[/ √ 2]]).
    reflexivity.
    restore_dims.
    solve_matrix.
  - unfold probability_of_outcome.
    replace (((hadamard × ket 0)† × ket 0) 0%nat 0%nat) with (/ √ 2).
    replace (Cmod (/ √ 2)) with (/ √ 2)%R.
    simpl.
    R_field_simplify.
    reflexivity.
    apply sqrt_neq_0_compat.
    apply Rlt_0_2.
    unfold Cmod.
    replace (fst (/ √ 2)) with (/ √ 2)%R.
    replace (snd (/ √ 2)) with (0%R).
    rewrite <- sqrt2_inv.
    simpl.
    rewrite Rmult_1_r.
    rewrite sqrt_def.
    rewrite Rmult_0_l.
    rewrite Rplus_0_r.
    reflexivity.
    lra.
    unfold snd.
    simpl.
    R_field_simplify.
    reflexivity.
    apply sqrt2_neq_0.
    unfold fst.
    simpl.
    R_field_simplify.
    reflexivity.
    apply sqrt2_neq_0.
    replace ((hadamard × ket 0)† × ket 0) with (list2D_to_matrix [[/ √ 2]]).
    reflexivity.
    restore_dims.
    solve_matrix.
Qed.

Fixpoint count_diff l1 l2 :=
  match l1, l2 with
  | [], _ => 0%nat
  | _, [] => 0%nat
  | h1::t1, h2::t2 => if eqb h1 h2 then count_diff t1 t2 else (1 + count_diff t1 t2)%nat
  end.

Theorem probibility_incorrect: forall n n_diff data ab bb, (length data = S n) -> (length ab = S n) -> (length bb = S n) -> count_diff ab bb = n_diff -> probability_of_outcome (uc_eval (circuit' data ab bb (S n)) × initial_state (S n)) (target_state (S n) data) = ((1/2)%R^n_diff)%R.
Proof.
  intro n.
  induction n; intros; (rewrite circuit'_output_correct; try assumption); (destruct data, ab, bb; try discriminate).
  Opaque output_state_qubit_i.
  Opaque target_state_qubit_i.
  - destruct data, ab, bb; try discriminate.
    destruct b, b0, b1; simpl; try (
      rewrite 2 kron_1_r;
      try rewrite probability_correct_single_qubit;
      try rewrite probability_incorrect_single_qubit;
      simpl in H2;
      subst;
      R_field
      ).
  - destruct b, b0, b1; simpl;
      try ( (* Case no diff *)
      rewrite probability_of_outcome_is_norm;
      restore_dims;
      rewrite kron_adjoint;
      rewrite kron_mixed_product;
      restore_dims;
      rewrite norm_kron;
      rewrite Rpow_mult_distr;
      rewrite <- probability_of_outcome_is_norm;
      rewrite probability_correct_single_qubit;
      rewrite <- circuit'_output_correct; try (simpl in H; simpl in H0; simpl in H1; apply eq_add_S in H; apply eq_add_S in H0; apply eq_add_S in H1; assumption);
      rewrite <- probability_of_outcome_is_norm;
      simpl in H2;
      rewrite (IHn n_diff); try (simpl in H; simpl in H0; simpl in H1; apply eq_add_S in H; apply eq_add_S in H0; apply eq_add_S in H1; assumption); try (subst; trivial);
      rewrite Rmult_1_l;
      reflexivity);
      try ( (* Case diff *)
      rewrite probability_of_outcome_is_norm;
      restore_dims;
      rewrite kron_adjoint;
      rewrite kron_mixed_product;
      restore_dims;
      rewrite norm_kron;
      rewrite Rpow_mult_distr;
      rewrite <- probability_of_outcome_is_norm;
      rewrite probability_incorrect_single_qubit; try apply diff_false_true; try apply diff_true_false;
      rewrite <- circuit'_output_correct; try (simpl in H; simpl in H0; simpl in H1; apply eq_add_S in H; apply eq_add_S in H0; apply eq_add_S in H1; assumption);
      rewrite <- probability_of_outcome_is_norm;
      simpl in H2;
      rewrite (IHn (n_diff - 1)%nat); try (simpl in H; simpl in H0; simpl in H1; apply eq_add_S in H; apply eq_add_S in H0; apply eq_add_S in H1; assumption); try (subst; trivial); try lia;
      replace (S (count_diff ab bb) - 1)%nat with (count_diff ab bb) by lia;
      rewrite tech_pow_Rmult;
      reflexivity).
Qed.
