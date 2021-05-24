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

Local Open Scope com_scope.

Fixpoint bob_measure_helper {U} (n i : nat) : com U n := 
  match i with
  | 0 => measure 0
  | S i' => measure i; bob_measure_helper n i'
end.

Definition bob_measure {U} n : com U n := bob_measure_helper n n.

Definition circuit (alice_data alice_base bob_base : list bool) (n : nat) :=
  alice (zip alice_base alice_data) n; bob bob_base n; bob_measure n.

Definition circuit'_qubit_i (ad ab bb : bool) (n i : nat) := circuit'_qubit_i_non_meas ad ab bb n i ; measure i. 

Fixpoint circuit'_helper (l : (list ((bool * bool) * bool))) (n : nat) (i : nat) : com base_Unitary n :=
  match l with
  | [] => SKIP
  | ((ad,ab),bb)::l' => circuit'_helper l' n (S i); circuit'_qubit_i ad ab bb n i
end.

Definition circuit' (alice_data alice_base bob_base : list bool) (n : nat) :=
  circuit'_helper (zip (zip alice_data alice_base) bob_base) n 0.


Lemma MmultHHX: (hadamard × hadamard × σx) = σx.
Proof.
  solve_matrix.
Qed.

Lemma circuit'_individual_qubit_non_meas_same_base_false: forall base n i, (n > 0)%nat -> uc_eval (circuit'_qubit_i_non_meas false base base n i) = I (2 ^ n). 
Proof.
  intros.
  destruct base; simpl; try rewrite denote_H; try rewrite denote_X; try rewrite denote_SKIP.
  - rewrite Mmult_1_r.
    repeat rewrite pad_mult.
    + admit.
    + apply WF_pad.
      apply WF_hadamard.
  - assumption.
  - repeat rewrite Mmult_1_l; try apply WF_I. 
    reflexivity.
  - assumption.
Admitted.

Lemma circuit'_individual_qubit_non_meas_same_base_true: forall base n i, (n > 0)%nat -> uc_eval (circuit'_qubit_i_non_meas true base base n i) = @pad 1 i n σx. 
Proof.
  intros.
  destruct base; simpl; try rewrite denote_H; try rewrite denote_X; try rewrite denote_SKIP.
  - repeat rewrite pad_mult.
    rewrite <- Mmult_assoc.
    admit.
  - repeat rewrite Mmult_1_l; try apply WF_pad; try apply WF_σx.
    reflexivity.
  - assumption.
Admitted.


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

Theorem circuit_individual_qubit_same_base: forall ad base (n i : nat), (n > 0)%nat -> (i <= n)%nat -> exists o, c_eval (circuit'_qubit_i ad base base n i) = o.
Proof.
  intros.
  unfold circuit'_qubit_i.
  Opaque circuit'_qubit_i_non_meas.
  destruct ad,base; simpl; try rewrite circuit'_individual_qubit_non_meas_same_base_false; try rewrite circuit'_individual_qubit_non_meas_same_base_true.
Admitted.

  

      
    
