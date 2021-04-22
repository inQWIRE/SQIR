Require Import UnitarySem.
Require Export RzQGateSet.
Require Import Optimize1qGates.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

Require Import SimpleMapping.
Require Import UnitaryListRepresentationRespectsConstraints.

Require Import IBMGateSet.


Lemma optimize_1q_gates'_respects_constraints: forall {dim} (l l' acc : IBM_ucom_l dim) (is_in_graph : nat -> nat -> bool) n,
respects_constraints_directed is_in_graph UIBM_CNOT l -> 
respects_constraints_directed is_in_graph UIBM_CNOT acc ->
respects_constraints_directed is_in_graph UIBM_CNOT (optimize_1q_gates' l n acc).
Proof.
  intros.
  generalize dependent acc.
  generalize dependent l. 
  induction n.
  - 
    intros.
    simpl.
    apply rev_append_respects_constraints; try assumption. 

  - intros.
    simpl.
    repeat destruct_matches_goal; try inversion H; try subst. 

    apply rev_append_respects_constraints; try assumption. 
    +

      apply IHn with (l := []) (acc := (App1 i n0 :: acc)); try assumption; try constructor. 
      assumption.

    +   apply IHn with (l := []) (acc := (App2 UIBM_CNOT n0 n1 :: acc));
          try assumption; try constructor.
        assumption. 
        assumption. 

        
    +
      inversion H; subst. 
      assert_and_prove_next_gate. 
      destruct H2 as [rcdg1 rcdg].
      apply IHn.
      apply respects_constraints_directed_app; assumption.

      dependent destruction i;
        dependent destruction i0;
        constructor; assumption.

    + apply IHn.
      inversion H; subst.
      assumption.
      dependent destruction i; constructor; assumption.  

    +
      apply IHn.
      assumption.
      inversion H; subst. 
      constructor; assumption.
    
Qed. 


Lemma simplify_1q_gates_respects_constraints: forall {dim} (l l' acc : IBM_ucom_l dim) (is_in_graph : nat -> nat -> bool) ,
respects_constraints_directed is_in_graph UIBM_CNOT l -> 
respects_constraints_directed is_in_graph UIBM_CNOT acc ->
respects_constraints_directed is_in_graph UIBM_CNOT (simplify_1q_gates l acc).
Proof.
  intros.

  generalize dependent acc.
  induction l.
  - intros.
    apply rev_append_respects_constraints; assumption. 

  - intros.
    simpl.
    inversion H; subst. 
    repeat destruct_matches_goal; apply IHl; try assumption; try constructor; try assumption.

    apply IHl.
    assumption.
    constructor.
    assumption.
    assumption. 
Qed. 
