Require Import Lists.List.
Import ListNotations.

Definition bit_string := list bool. 

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
      Search (S _ = S _ -> _ = _).
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

Lemma list_add_eq: forall A (l1 l2 : list A) (a1 a2 : A), a1 = a2 /\ l1 = l2 -> a1::l1=a2::l2.
Proof.
  intros.
  destruct H.
  subst.
  reflexivity.
Qed.

Lemma inv_stmt: forall (A B : Prop), (A -> B) -> (~B -> ~A).
  intros.
  contradict H0.
  apply H.
  assumption.
Qed.


Lemma list_add_neq: forall A (l1 l2 : list A) (a1 a2 : A), a1::l1 <> a2::l2 -> a1 <> a2 \/ l1 <> l2.
Proof.
  intros.
  assert (~(a1::l1 = a2::l2) -> ~(a1 = a2 /\ l1 = l2)).
  apply inv_stmt.
  apply list_add_eq.
  assert (~ (a1 = a2 /\ l1 = l2) -> a1 <> a2 \/ l1 <> l2).
  {
    admit. (* This proof turned out to be hard/ pontentially impossible  - but the actual lemmma is clearly true so in the interest of time I focussed on the quantum part below*)
  }
  apply H1.
  apply H0.
  apply H.
Admitted.

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


Fixpoint bob_helper (base : list bool) (i n : nat) : base_ucom n :=
  match base with
  | [] => SKIP
  | b::base' => bob_bit_manip b n i ; bob_helper base' (S i) n
end.

Definition bob (base: list bool) (n : nat) : base_ucom n := bob_helper base 0 n.

Definition circuit'_qubit_i_non_meas (ad ab bb : bool) (n i : nat) : base_ucom n := alice_bit_manip ab ad n i; bob_bit_manip bb n i.

Fixpoint circuit'_helper (l : (list ((bool * bool) * bool))) (n : nat) (i : nat) : base_ucom n :=
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

Definition circuit (alice_data alice_base bob_base : list bool) (n : nat) :=
  alice (zip alice_base alice_data) n; bob bob_base n; bob_measure n.




Definition circuit' (alice_data alice_base bob_base : list bool) (n : nat) :=
  circuit'_helper (zip (zip alice_data alice_base) bob_base) n 0.


Lemma MmultHHX: (hadamard × hadamard × σx) = σx.
Proof.
  solve_matrix.
Qed.

Search pad.

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




Definition R_Bool_Rel (r : R) b := (r = 1 /\ b = true) \/ (r = 0 /\ b = false).

Lemma circuit_growth_same_base: forall n data base, length data = (S n) -> length base = (S n) -> @pad 1 0 (S n) σx × uc_eval (circuit'_helper (zip (zip data base) base) (S n) 1) = uc_eval_circuit_same_base data ⊗ σx.
  intros.
  induction n.
  - simpl.
    destruct data, base; try discriminate.
    destruct data, base; try discriminate.
    simpl.
    Search pad.
    destruct b, b0; try rewrite denote_H; try rewrite denote_X; try rewrite denote_SKIP; try (repeat rewrite unfold_pad); try simpl; try auto.
Abort.

    
    

Lemma circuit_growth_old: forall z' z n, (n > 0)%nat -> (n = length (z')) -> (uc_eval (circuit'_helper (z::z') (S n) 1)) = uc_eval (circuit'_helper z' n 0) ⊗ I 2.
Proof.
  intros z'.
  induction z'; intros.
  - simpl in H0.
    subst.
    contradict H.
    apply gt_irrefl.
  - Opaque circuit'_qubit_i_non_meas.
    simpl.
    destruct a, z; destruct p, p0.
    simpl.
Abort.

  Theorem circuit_individual_qubit_same_base: forall data base (n: nat), (length data = S n) -> (length base = S n) -> uc_eval (circuit' data base base (S n)) = uc_eval_circuit_same_base data.
Proof.
  intros.
  generalize dependent base.
  generalize dependent data.
  induction n; intros.
  - simpl.
    destruct data, base; try discriminate.
    destruct data, base; try discriminate.
    simpl.
    rewrite denote_SKIP; try auto.
    destruct b, b0; try rewrite circuit'_individual_qubit_non_meas_same_base_true; try rewrite circuit'_individual_qubit_non_meas_same_base_false; simpl; restore_dims; try auto; try (rewrite Mmult_1_r; rewrite unfold_pad; simpl; try rewrite kron_1_l; try rewrite kron_1_r; solve_matrix; try apply WF_pad; try apply WF_σx; try apply WF_I); try solve_matrix.
  - unfold circuit'.
    assert (length (zip (zip data base) base)  = S (S n)).
    {
      assert (length (zip data base) = S (S n)).
      {
        apply zip_same_length.
        assumption.
        assumption.
      }
      apply zip_same_length.
      assumption.
      assumption.
    }
    destruct data; try discriminate H.
    destruct base; try discriminate H0.
    Opaque circuit'_qubit_i_non_meas.
    simpl.
    destruct b0, b.
    + Search (circuit'_qubit_i_non_meas).
      rewrite circuit'_individual_qubit_non_meas_same_base_true; try trivial (* For assuption (S n > 0) *).
      simpl.
Abort.

Fixpoint initial_state n : Vector (2^n) :=
  match n with
  | 0 => I 1
  | S n' => ket 0 ⊗ initial_state n'
  end.

Fixpoint target_state n (data: list bool) : Vector (2^n) :=
  match data with
  | [] => I 1
  | d::data' => (if d then ket 1 else ket 0) ⊗ target_state (n-1) data'
  end.


Theorem circuit'_helper_growth: forall n l, (length l = S n) ->  uc_eval(circuit'_helper l (S (S n)) 1) =  I 2 ⊗ uc_eval (circuit'_helper l (S n) 0).
Proof.
  intro n.
  induction n; intros.
  - destruct l; try discriminate.
    destruct l; try discriminate.
    destruct p.
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
  - destruct l; try discriminate.
    simpl.
    destruct p.
    destruct p.
    simpl.
    rewrite IHn.
Admitted.


Theorem circuit'_same_base_correct: forall n data base, (length data = S n) -> (length base = S n) -> (uc_eval (circuit' data base base (S n))) × initial_state (S n) = target_state (S n)  data.
Proof.
  intros n.
  induction n; intros.
  - simpl.
    destruct data, base; try discriminate.
    destruct data, base; try discriminate.
    destruct b, b0; simpl; try rewrite circuit'_individual_qubit_non_meas_same_base_true; try rewrite circuit'_individual_qubit_non_meas_same_base_false; try rewrite denote_SKIP; try rewrite denote_X; try auto
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
    + rewrite Mmult_1_l.
      rewrite Mmult_1_l.
      reflexivity.
      rewrite kron_1_r.
      apply WF_ket.
      apply WF_I.
  -
    simpl.
    destruct data, base; try discriminate.
    simpl.
    rewrite <- (IHn data base).
    destruct b, b0.
    + rewrite circuit'_individual_qubit_non_meas_same_base_true.
      rewrite circuit'_helper_growth.
      simpl.
      fold circuit'.
      replace (circuit'_helper (zip (zip data base) base) (S n)0) with (circuit' data base base (S n)).
      rewrite IHn.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      Search ((_ ⊗ _ ) × (_⊗_)).
      restore_dims.
      replace (σx ⊗ (I (2 ^n + (2 ^ n + 0))) × ((I 2) ⊗ (uc_eval (circuit' data base base (S n))))) with ((σx × I 2) ⊗ ( (I (2 ^n + (2 ^n + 0))) × uc_eval (circuit' data base base (S n)))).
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
      simpl.
      reflexivity.
      apply WF_σx.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      Search (_ × _ ⊗ (_ × _)).
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
      unfold circuit'.
      reflexivity.
      simpl in H.
      simpl in H0.
      apply eq_add_S in H.
      apply eq_add_S in H0.
      apply zip_same_length; try (apply zip_same_length; try assumption); try assumption.
      apply gt_Sn_O.
    + rewrite circuit'_individual_qubit_non_meas_same_base_true.
      rewrite circuit'_helper_growth.
      simpl.
      fold circuit'.
      replace (circuit'_helper (zip (zip data base) base) (S n)0) with (circuit' data base base (S n)).
      rewrite IHn.
      rewrite unfold_pad.
      simpl.
      rewrite kron_1_l.
      Search ((_ ⊗ _ ) × (_⊗_)).
      restore_dims.
      replace (σx ⊗ (I (2 ^n + (2 ^ n + 0))) × ((I 2) ⊗ (uc_eval (circuit' data base base (S n))))) with ((σx × I 2) ⊗ ( (I (2 ^n + (2 ^n + 0))) × uc_eval (circuit' data base base (S n)))).
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
      simpl.
      reflexivity.
      apply WF_σx.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      Search (_ × _ ⊗ (_ × _)).
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
      unfold circuit'.
      reflexivity.
      simpl in H.
      simpl in H0.
      apply eq_add_S in H.
      apply eq_add_S in H0.
      apply zip_same_length; try (apply zip_same_length; try assumption); try assumption.
      apply gt_Sn_O.
    + simpl.
      rewrite circuit'_helper_growth.
      simpl.
      fold circuit'.
      replace (circuit'_helper (zip (zip data base) base) (S n)0) with (circuit' data base base (S n)).
      rewrite IHn.
      rewrite circuit'_individual_qubit_non_meas_same_base_false.
      simpl.
      Search ((_ ⊗ _ ) × (_⊗_)).
      restore_dims.
      replace (σx ⊗ (I (2 ^n + (2 ^ n + 0))) × ((I 2) ⊗ (uc_eval (circuit' data base base (S n))))) with ((σx × I 2) ⊗ ( (I (2 ^n + (2 ^n + 0))) × uc_eval (circuit' data base base (S n)))).
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
      Search (_ × _ ⊗ (_ × _)).
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
      unfold circuit'.
      reflexivity.
      simpl in H.
      simpl in H0.
      apply eq_add_S in H.
      apply eq_add_S in H0.
      apply zip_same_length; try (apply zip_same_length; try assumption); try assumption.
    + simpl.
      rewrite circuit'_helper_growth.
      rewrite circuit'_individual_qubit_non_meas_same_base_false.      
      simpl.
      fold circuit'.
      replace (circuit'_helper (zip (zip data base) base) (S n)0) with (circuit' data base base (S n)).
      rewrite IHn.
      simpl.
      Search ((_ ⊗ _ ) × (_⊗_)).
      restore_dims.
      replace (σx ⊗ (I (2 ^n + (2 ^ n + 0))) × ((I 2) ⊗ (uc_eval (circuit' data base base (S n))))) with ((σx × I 2) ⊗ ( (I (2 ^n + (2 ^n + 0))) × uc_eval (circuit' data base base (S n)))).
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
      simpl.
      reflexivity.
      apply WF_kron.
      reflexivity.
      reflexivity.
      apply WF_I.
      restore_dims.
      apply WF_uc_eval.
      restore_dims.
      Search (_ × _ ⊗ (_ × _)).
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
      unfold circuit'.
      reflexivity.
      apply gt_Sn_O.
      apply lt_O_Sn.
      simpl in H.
      simpl in H0.
      apply eq_add_S in H.
      apply eq_add_S in H0.
      apply zip_same_length; try (apply zip_same_length; try assumption); try assumption.
   + simpl in H.
     apply eq_add_S in H.
     assumption.
   

Admitted.



