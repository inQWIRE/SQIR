Require Import UnitarySem.
Require Export RzQGateSet.
Require Import CXCancellation.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

Require Import SimpleMapping.
Require Import UnitaryListRepresentationRespectsConstraints.

Require Import StandardGateSet.
Import StdList.


Lemma cx_cancellation'_respects_constraints: forall {dim} (l acc : IBM_ucom_l dim) (is_in_graph : nat -> nat -> bool) n,
respects_constraints_directed is_in_graph UIBM_CNOT l -> 
    respects_constraints_directed is_in_graph UIBM_CNOT acc ->
respects_constraints_directed is_in_graph UIBM_CNOT (cx_cancellation' l n acc ).
Proof.
  intros.
  generalize dependent acc.
  generalize dependent l. 
  induction n.
  - 
    intros. simpl.
    apply rev_append_respects_constraints; assumption. 
  - intros.
    remember (cx_cancellation' l (S n) acc) as l' eqn: H1.
    simpl in H1.
    symmetry in H1.
    destruct_matches. 

    
    + apply rev_append_respects_constraints; assumption.
    + destruct g.
      *  apply IHn.
         constructor.
         constructor.
         assumption .

      *
        simpl.
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
        repeat destruct_matches_goal.
        dependent destruction i. 
        assert_and_prove_next_gate.        
        destruct H1 as [rcdg1 [rcdg iign3n2]].
        apply IHn; try assumption. 
        apply respects_constraints_directed_app;
          assumption.

        apply IHn; try constructor; try assumption. 


        apply IHn; try constructor; try assumption. 
        inversion H; subst; assumption. 

        inversion H; subst. apply res_dir_app2; assumption.
      * inversion H. 
Qed. 
