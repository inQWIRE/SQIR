Require Export IBMGateSet.
Require Import List.
Import IBMList.
Require Import MappingConstraints.
Open Scope ucom.

Local Open Scope ucom_scope.

(** Combine multiple U gates on a qubit to one U gate. **)

Fixpoint cx_cancellation' {dim} (l : IBM_ucom_l dim) (n: nat) acc : IBM_ucom_l dim :=
  match n with
  | O => rev_append acc l
  | S n' => 
    match l with
    | [] => rev_append acc []
    | (App2 _ q1 q2) as g :: t => 
      match next_two_qubit_gate t q1 with
      | Some (l1, _, q1', q2', l2) => 
        if (q1 =? q1') && (q2 =? q2') && (does_not_reference l1 q2)
        then cx_cancellation' (l1 ++ l2) n' acc
        else cx_cancellation' t n' (g :: acc)
      | None => cx_cancellation' t n' (g :: acc)
      end
    | g :: t => cx_cancellation' t n' (g :: acc)
    end
  end.

Definition cx_cancellation {dim} (l : IBM_ucom_l dim) := 
  cx_cancellation' l (length l) [].

(** semantics preservation **)

Lemma cx_cancellation'_sound : forall {dim} (l : IBM_ucom_l dim) n acc,
  uc_well_typed_l l ->
  cx_cancellation' l n acc =l= rev_append acc l.
Proof.
  intros dim l n acc WT.
  rewrite rev_append_rev.
  generalize dependent acc.
  generalize dependent l.
  induction n; intros l WT acc.
  simpl. rewrite rev_append_rev. reflexivity.
  destruct l.
  simpl. rewrite rev_append_rev. reflexivity.
  destruct g as [u | u | u]; simpl.
  - inversion WT; subst.
    rewrite IHn; auto. simpl. rewrite <- app_assoc. reflexivity.
  - inversion WT; subst.
    destruct (next_two_qubit_gate l n0) eqn:ntqg.
    2: { rewrite IHn; auto. simpl. rewrite <- app_assoc. reflexivity. }
    repeat destruct p. 
    bdestruct (n0 =? n3); bdestruct (n1 =? n2); 
      destruct (does_not_reference g0 n1) eqn:dnr; simpl.
    all: rewrite IHn; auto.
    all: try (simpl; rewrite <- app_assoc; reflexivity).
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ _ ntqg) as dnr'.
    apply ntqg_preserves_structure in ntqg.
    subst.
    rewrite (cons_to_app _ (_ ++ _)).
    apply_app_congruence.
    rewrite <- (does_not_reference_commutes_app2 g0) by assumption.
    rewrite <- (app_nil_l g0) at 1.
    apply_app_congruence.
    dependent destruction i.
    dependent destruction u.
    unfold uc_equiv_l; simpl.
    symmetry.
    rewrite SKIP_id_r.
    apply CNOT_CNOT_id; assumption.
    apply ntqg_WT in ntqg; auto.
    apply uc_well_typed_l_app.
    assumption.
  - inversion u.
Qed.

Lemma cx_cancellation_sound : forall {dim} (l : IBM_ucom_l dim),
  uc_well_typed_l l ->
  cx_cancellation l =l= l.
Proof.
  intros.
  apply cx_cancellation'_sound.
  assumption.
Qed.

(** mapping preservation **)

Lemma cx_cancellation'_respects_constraints: forall {dim} (l acc : IBM_ucom_l dim) (is_in_graph : nat -> nat -> bool) n,
  respects_constraints_directed is_in_graph UIBM_CNOT l -> 
  respects_constraints_directed is_in_graph UIBM_CNOT acc ->
  respects_constraints_directed is_in_graph UIBM_CNOT (cx_cancellation' l n acc ).
Proof.
  intros.
  generalize dependent acc.
  generalize dependent l. 
  induction n.
  - intros. simpl.
    apply rev_append_respects_constraints; assumption. 
  - intros.
    remember (cx_cancellation' l (S n) acc) as l' eqn: H1.
    simpl in H1.
    symmetry in H1.
    destruct_matches. 
    + apply rev_append_respects_constraints; assumption.
    + destruct g.
      * apply IHn.
        constructor.
        constructor.
        assumption .
      * simpl.
        apply IHn.
        constructor.
        dependent destruction i.
        constructor.
        inversion H; subst. 
        assumption.
        assumption.
      * inversion H.
    + dependent destruction g.
      * inversion H; subst.
        apply IHn.
        assumption.
        constructor.
        assumption.
      * remember (next_two_qubit_gate (g0 :: H2) n0) as H1.
        destruct H1.
        inversion H; subst.
        repeat (destruct p).
        dependent destruction i. 
        assert_and_prove_next_gate.        
        destruct H1 as [rcdg1 [rcdg iign3n2]].
        bdestruct_all; simpl.
        destruct (does_not_reference g1 n1) eqn:dnr; simpl.
        all: apply IHn; try constructor; try assumption. 
        apply respects_constraints_directed_app; assumption.
        inversion H; subst; assumption. 
        inversion H; subst; constructor; assumption.
      * inversion H. 
Qed. 

Lemma cx_cancellation_respects_constraints: forall {dim} (l : IBM_ucom_l dim) (is_in_graph : nat -> nat -> bool),
  respects_constraints_directed is_in_graph UIBM_CNOT l -> 
  respects_constraints_directed is_in_graph UIBM_CNOT (cx_cancellation l).
Proof. 
  intros. 
  unfold cx_cancellation. 
  apply cx_cancellation'_respects_constraints.
  assumption.
  constructor. 
Qed.
