Require Import UnitarySem.
Require Export RzQGateSet.
Require Import HadamardReduction.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

Require Import SimpleMapping.
Require Import UnitaryListRepresentationRespectsConstraints.

Require Import StandardGateSet.
Import StdList.

Lemma apply_H_equivalence1_respects_constraints: forall {dim} q (l l': RzQ_ucom_l dim)
                                                        (is_in_graph : nat->nat->bool),
    respects_constraints_directed is_in_graph URzQ_CNOT l ->
    apply_H_equivalence1 q l = Some l' ->
    respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros.
  unfold apply_H_equivalence1 in H0.
  eapply replace_pattern_respects_constraints. 
  apply H.
  remember (RzQGateSet.H q:: RzQGateSet.P q:: RzQGateSet.H q::[]) as pre. 
  assert (respects_constraints_directed is_in_graph URzQ_CNOT pre).
  subst; repeat constructor.
  
  subst. 
  apply H1.
  remember (RzQGateSet.PDAG q:: RzQGateSet.H q:: RzQGateSet.PDAG q::[]) as pat. 
  assert (respects_constraints_directed is_in_graph URzQ_CNOT pat).
  subst; repeat constructor.
  subst.
  apply H1.
  apply H0.
Qed. 

Lemma apply_H_equivalence2_respects_constraints: forall {dim} q (l l': RzQ_ucom_l dim)
                                                        (is_in_graph : nat->nat->bool),
    respects_constraints_directed is_in_graph URzQ_CNOT l ->
    apply_H_equivalence2 q l = Some l' ->
    respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros.
  unfold apply_H_equivalence2 in H0.
  eapply replace_pattern_respects_constraints. 
  apply H.
  remember (RzQGateSet.H q:: RzQGateSet.PDAG q:: RzQGateSet.H q::[]) as pre. 
  assert (respects_constraints_directed is_in_graph URzQ_CNOT pre).
  subst; repeat constructor.
  
  subst. 
  apply H1.
  remember (RzQGateSet.P q:: RzQGateSet.H q:: RzQGateSet.P q::[]) as pat. 
  assert (respects_constraints_directed is_in_graph URzQ_CNOT pat).
  subst; repeat constructor.
  subst.
  apply H1.
  apply H0.
Qed.

Lemma apply_H_equivalence4_respects_constraints: forall {dim} q (l l': RzQ_ucom_l dim)
                                                        (is_in_graph : nat->nat->bool),
    respects_constraints_directed is_in_graph URzQ_CNOT l ->
    apply_H_equivalence4 q l = Some l' ->
    respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros.
  unfold apply_H_equivalence4 in H0.
  repeat destruct_matches.
  inversion H0; subst; clear H0.

  remember (RzQGateSet.H q :: RzQGateSet.P q:: []) as pre.
  assert (respects_constraints_directed is_in_graph URzQ_CNOT pre).
  subst; repeat constructor.  subst. 
  assert (respects_constraints_directed is_in_graph URzQ_CNOT g).
  eapply remove_prefix_respects_constraints.
  apply H.
  apply H0.
  symmetry in HeqH1.
  apply HeqH1. 
  
  assert_and_prove_next_gate. 
  destruct H2 as [rcdg1 [rcdg0 iign0n]].

  apply respects_constraints_directed_app.
  assumption. repeat (try constructor; try assumption).

  eapply remove_prefix_respects_constraints.
  apply rcdg0.
   remember (RzQGateSet.PDAG q :: RzQGateSet.H q:: []) as pre.
  assert (respects_constraints_directed is_in_graph URzQ_CNOT pre).
  subst. repeat constructor. subst. 
  apply H2. 
  symmetry in HeqH3.
  apply HeqH3. 
Qed. 

(* Same as 4 *) 
Lemma apply_H_equivalence5_respects_constraints: forall {dim} q (l l': RzQ_ucom_l dim)
                                                        (is_in_graph : nat->nat->bool),
    respects_constraints_directed is_in_graph URzQ_CNOT l ->
    apply_H_equivalence5 q l = Some l' ->
    respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros.
  unfold apply_H_equivalence5 in H0.
  repeat destruct_matches.
  inversion H0; subst; clear H0.

  remember (RzQGateSet.H q :: RzQGateSet.PDAG q:: []) as pre.
  assert (respects_constraints_directed is_in_graph URzQ_CNOT pre).
  subst; repeat constructor.  subst. 
  assert (respects_constraints_directed is_in_graph URzQ_CNOT g).
  eapply remove_prefix_respects_constraints.
  apply H.
  apply H0.
  symmetry in HeqH1.
  apply HeqH1. 
  
  assert_and_prove_next_gate.

  destruct H2 as [rcdg1 [rcdg0 iign0n]].

  apply respects_constraints_directed_app.
  assumption. repeat (try constructor; try assumption).

  eapply remove_prefix_respects_constraints.
  apply rcdg0.
   remember (RzQGateSet.P q :: RzQGateSet.H q:: []) as pre.
  assert (respects_constraints_directed is_in_graph URzQ_CNOT pre).
  subst. repeat constructor. subst. 
  apply H2. 
  symmetry in HeqH3.
  apply HeqH3.
Qed. 

Definition apply_respectful_H_equivalence {dim} (l : RzQ_ucom_l dim) (q : nat) : option (RzQ_ucom_l dim) :=
  try_rewrites l (apply_H_equivalence1 q :: apply_H_equivalence2 q::
                                       apply_H_equivalence4 q :: apply_H_equivalence5 q :: []).

Lemma apply_respectful_H_equivalence_respects_constraints: forall {dim} q (l l': RzQ_ucom_l dim)
                                                        (is_in_graph : nat->nat->bool),
    respects_constraints_directed is_in_graph URzQ_CNOT l ->
    apply_respectful_H_equivalence  l q = Some l' ->
    respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros.
  unfold apply_respectful_H_equivalence in H0.
  eapply try_rewrites_respects_constraints.
  apply H.
  intros.
  2: { apply H0. } 
  destruct_In;

  subst.
  - eapply apply_H_equivalence1_respects_constraints.
    apply H2. apply H3.
  - eapply apply_H_equivalence2_respects_constraints.
    apply H2. apply H3.

  - eapply apply_H_equivalence4_respects_constraints.
    apply H2. apply H3.
  - eapply apply_H_equivalence5_respects_constraints.
    apply H2. apply H3.
Qed.     

Fixpoint apply_respectful_H_equivalences' {dim} (l  : RzQ_ucom_l dim) (n: nat) (acc : RzQ_ucom_l dim) 
  : RzQ_ucom_l dim :=
  match n with
  | 0%nat => rev_append acc l
  | S n' => 
      match l with
      | [] => rev_append acc []
      | (App1 URzQ_H q) :: t => 
          match apply_respectful_H_equivalence l q with
          | None => apply_respectful_H_equivalences' t n' (RzQGateSet.H q  :: acc)
          | Some l' => apply_respectful_H_equivalences' l' n' acc
          end
      | g :: t => apply_respectful_H_equivalences' t n' (g :: acc)
      end
  end.

Lemma apply_respectful_H_equivalences'_respects_constraints: forall {dim} n (l acc l': RzQ_ucom_l dim)
                                                        (is_in_graph : nat->nat->bool),
    respects_constraints_directed is_in_graph URzQ_CNOT l ->
        respects_constraints_directed is_in_graph URzQ_CNOT acc ->
    apply_respectful_H_equivalences'  l n acc =  l' ->
    respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros.
  generalize dependent l.
  generalize dependent acc. 
  induction n.
  - intros.
    simpl in H1.
    subst.
    apply rev_append_respects_constraints; try assumption.
    
  - intros.

    induction l. 

    + subst. apply rev_append_respects_constraints; try assumption. 

    +
      simpl in H1;
      destruct a; dependent destruction r. 
      * remember (apply_respectful_H_equivalence (App1 URzQ_H n0 :: l) n0) as respect eqn:rsp.
        destruct respect.
        eapply IHn.
        apply H0.
        eapply apply_respectful_H_equivalence_respects_constraints. 
        apply H. symmetry in rsp. apply rsp. apply H1.

        assert (respects_constraints_directed is_in_graph URzQ_CNOT (App1 URzQ_H n0 :: acc)).
        constructor; assumption. 
        eapply IHn.
        apply H2.
        inversion H; subst. 
        apply H6.
        apply H1.
      *
        
        assert (respects_constraints_directed is_in_graph URzQ_CNOT (App1 URzQ_X n0 :: acc)).
        constructor; assumption. 
        eapply IHn.
        apply H2.
        inversion H; subst. 
        apply H6.
        apply H1.
      *
        assert (respects_constraints_directed is_in_graph URzQ_CNOT (App1 (URzQ_Rz a) n0 :: acc)).
        constructor; assumption. 
        eapply IHn.
        apply H2.
        inversion H; subst. 
        apply H6.
        apply H1.
      *
        assert (respects_constraints_directed is_in_graph URzQ_CNOT (App2 URzQ_CNOT n0 n1 :: acc)).
        constructor. inversion H; subst; assumption. assumption.
        eapply IHn.
        apply H2.
        inversion H; subst. 
        apply H9.
        apply H1.
Qed. 

Definition respectful_hadamard_reduction {dim} (l : RzQ_ucom_l dim) := 
  apply_respectful_H_equivalences' l (2 * (length l)) [].

Lemma respectful_hadamard_reduction_respects_constraints:
  forall {dim}  (l l': RzQ_ucom_l dim) (is_in_graph : nat->nat->bool),
    respects_constraints_directed is_in_graph URzQ_CNOT l ->
    respectful_hadamard_reduction l =  l' ->
    respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros. 
  unfold respectful_hadamard_reduction in H0.
  eapply apply_respectful_H_equivalences'_respects_constraints. 
  apply H.
  apply res_dir_nil.
  apply H0.
Qed. 
