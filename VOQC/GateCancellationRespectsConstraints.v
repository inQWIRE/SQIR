Require Import UnitarySem.
Require Export RzQGateSet.
Require Import GateCancellation.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

Require Import SimpleMapping.
Require Import UnitaryListRepresentationRespectsConstraints.

Require Import StandardGateSet.
Import StdList.

Lemma Rz_commute_rule1_respects_constraints: forall {dim} q  (in_l out_l1 out_l2 : RzQ_ucom_l dim)
      (is_in_graph : nat->nat->bool) , 
    respects_constraints_directed is_in_graph URzQ_CNOT in_l
    -> (@Rz_commute_rule1 dim q in_l) = (Some (out_l1, out_l2)) ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l1
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
   
  unfold Rz_commute_rule1 in H0.
  destruct_matches. 
  repeat destruct_matches.

  assert_and_prove_next_gate.  
  destruct H1 as [respects_g0 respects_g].


  assert_and_prove_next_gate.
  destruct H1 as [respects_g2 [respects_g1 iiggn0n]].
  assert_and_prove_next_gate.
  destruct H1 as [respects_g4 respects_g3].    

  split.
  - inversion H0; subst.
    repeat (try apply respects_constraints_directed_app; auto; try constructor).  

    
    symmetry in HeqH2.
    rewrite Nat.eqb_eq in HeqH2.
    subst.
    assumption.
    
  - inversion H0; subst.
    assumption. 
Qed.


Lemma Rz_commute_rule2_respects_constraints: forall {dim} q (in_l out_l1 out_l2 : RzQ_ucom_l dim)
      (is_in_graph : nat->nat->bool), 
    respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
    (@Rz_commute_rule2 dim q in_l) = (Some (out_l1, out_l2)) ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l1
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof. 
  intros.
  unfold Rz_commute_rule2 in H0.
  repeat destruct_matches. 

  assert_and_prove_next_gate.
  destruct H1 as  [respects_g0 [respects_g iiggn0n]].

  assert_and_prove_next_gate.
  destruct H1 as [respects_g2 respects_g1].

  assert_and_prove_next_gate. 
  destruct H1 as  [respects_g4 [respects_g3 iiggn2n1]].

  
  symmetry in HeqH0.
  rewrite Nat.eqb_eq in HeqH0.
  subst.
  split; inversion H0; subst;
  repeat (try apply respects_constraints_directed_app; try assumption; try constructor).

Qed.   


Lemma Rz_commute_rule3_respects_constraints: forall {dim} q  (in_l out_l1 out_l2 : RzQ_ucom_l dim)
      (is_in_graph : nat->nat->bool), 
    respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
    (@Rz_commute_rule3 dim q in_l) = (Some (out_l1, out_l2)) ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l1 /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold Rz_commute_rule3 in H0.
  repeat destruct_matches. 

  assert_and_prove_next_gate. 
  destruct H1 as  [respects_g4 [respects_g3 iiggn2n1]].

  split;
  inversion H0; subst; 
  repeat (try apply respects_constraints_directed_app; try assumption; try constructor).

Qed.

Lemma X_commute_rule_respects_constraints: forall {dim} q (in_l out_l1 out_l2 : RzQ_ucom_l dim)
      (is_in_graph : nat->nat->bool), 
    respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
    (@X_commute_rule dim q in_l) = (Some (out_l1, out_l2)) ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l1 /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold X_commute_rule in H0.
  repeat destruct_matches. 

  
  assert_and_prove_next_gate.

  destruct H1 as  [respects_g4 [respects_g3 iiggn2n1]].

   split; inversion H0; subst;
  repeat (try apply respects_constraints_directed_app; try assumption; try constructor).
Qed.

Lemma CNOT_commute_rule1_respects_constraints: forall {dim} q (in_l out_l1 out_l2 : RzQ_ucom_l dim)
      (is_in_graph : nat->nat->bool), 
    respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
    (@CNOT_commute_rule1 dim q in_l) = (Some (out_l1, out_l2)) ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l1 /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold CNOT_commute_rule1 in H0.
  repeat destruct_matches. 

  assert_and_prove_next_gate.
  destruct H1. 

  split;
    inversion H0; subst; 
      repeat (try apply respects_constraints_directed_app; try assumption; try constructor).

Qed.

Lemma CNOT_commute_rule2_respects_constraints: forall {dim} q1 q2 (in_l out_l1 out_l2 : RzQ_ucom_l dim)
      (is_in_graph : nat->nat->bool), 
    respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
    (@CNOT_commute_rule2 dim q1 q2 in_l) = (Some (out_l1, out_l2)) ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l1 /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold CNOT_commute_rule2 in H0.
  repeat destruct_matches.
  assert_and_prove_next_gate. 

  destruct H1 as [respects_g0 [ respects_g is_in_graphn0n]].
  split;
    inversion H0; subst; 
      repeat (try apply respects_constraints_directed_app; try assumption; try constructor).
    
  symmetry in HeqH0.
  rewrite Nat.eqb_eq in HeqH0.
  subst. 
  assumption.
    
Qed.


Lemma CNOT_commute_rule3_respects_constraints: forall {dim} q1 q2 (in_l out_l1 out_l2 : RzQ_ucom_l dim)
      (is_in_graph : nat->nat->bool), 
    respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
    (@CNOT_commute_rule3 dim q1 q2 in_l) = (Some (out_l1, out_l2)) ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l1 /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold CNOT_commute_rule3 in H0.
  repeat destruct_matches.
  assert_and_prove_next_gate. 
  destruct H1 as [respects_g0 [ respects_g is_in_graphn0n]].

  split;
    inversion H0; subst; 
      repeat (try apply respects_constraints_directed_app; try assumption; try constructor).
    
  symmetry in HeqH0.
  rewrite Nat.eqb_eq in HeqH0.
  subst. 
  assumption.
Qed.


Lemma CNOT_commute_rule4_respects_constraints: forall {dim} q1 q2  (in_l out_l1 out_l2 : RzQ_ucom_l dim)
      (is_in_graph : nat->nat->bool), 
    respects_constraints_directed is_in_graph URzQ_CNOT in_l
    -> (@CNOT_commute_rule4 dim q1 q2 in_l) = (Some (out_l1, out_l2)) ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l1
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold CNOT_commute_rule4 in H0.
  repeat destruct_matches.

  assert_and_prove_next_gate. 
  destruct H1 as [respects_g0 respects_g].

  assert_and_prove_next_gate. 
  destruct H1 as [respects_g2  [respects_g1 is_in_n0_n]].

  assert_and_prove_next_gate. 
  destruct H1 as [respects_g4  respects_g3].

  
  split;
    inversion H0; subst; 
      repeat (try apply respects_constraints_directed_app; try assumption; try constructor).
  symmetry in HeqH2.
  rewrite <- andb_assoc in HeqH2. 
  apply andb_true_iff in HeqH2.
  destruct HeqH2 as [q2n0 q1ndnrf].
  apply andb_true_iff in q1ndnrf.
  destruct q1ndnrf as [q1n dnr].
  
  rewrite Nat.eqb_eq in q2n0.
  subst.
  assumption. 

Qed.


Lemma CNOT_commute_rule5_respects_constraints: forall {dim} q1 q2  (in_l out_l1 out_l2 : RzQ_ucom_l dim)
      (is_in_graph : nat->nat->bool), 
    respects_constraints_directed is_in_graph URzQ_CNOT in_l
    -> (@CNOT_commute_rule5 dim q1 q2 in_l) = (Some (out_l1, out_l2)) ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l1
    /\ respects_constraints_directed is_in_graph URzQ_CNOT out_l2.
Proof.
  intros.
  unfold CNOT_commute_rule5 in H0.
  repeat destruct_matches.

  assert_and_prove_next_gate. 
  destruct H1 as [respects_g0  respects_g].
  
  assert_and_prove_next_gate.
  destruct H1 as [respects_g2  [respects_g1 is_in_n0_n]].

  assert_and_prove_next_gate. 
  destruct H1 as [respects_g4  respects_g3].

  split;
    inversion H0; subst; 
      repeat (try apply respects_constraints_directed_app; try assumption; try constructor).

Qed.

Lemma combines_rotations_respects_constraints:
  forall {dim} a a' q (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph URzQ_CNOT (@combine_rotations dim a a' q).
Proof.
  intros.
  unfold combine_rotations.
  destruct (Qeq_bool (RzQGateSet.bound (a + a')) zero_Q).
  constructor.
  constructor.
  constructor.
Qed. 

Lemma try_rewrites_respects_constraints: forall { dim} (l l' : RzQ_ucom_l dim)
                                           rules  (is_in_graph : nat -> nat -> bool),
    respects_constraints_directed is_in_graph URzQ_CNOT l ->
    (forall r, List.In r rules -> forall l l',
          respects_constraints_directed is_in_graph URzQ_CNOT l ->
          r l = Some l'
          -> respects_constraints_directed is_in_graph URzQ_CNOT l') ->
    try_rewrites l rules = Some l' -> 
    respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros.
  induction rules.
  inversion H1.
  simpl in H1.
  destruct (a l) eqn:al.
  inversion H1; subst.
  eapply H0.
  left. reflexivity. apply H. apply al.
  apply IHrules.
  intros. 
  eapply H0.  right.  
  apply H2.
  apply H3.
  apply H4. 
  apply H1. 
Qed.

Lemma try_rewrites2_respects_constraints: forall {dim} (l l1 l2 : RzQ_ucom_l dim)
                                                 rules  (is_in_graph : nat -> nat -> bool),
    respects_constraints_directed is_in_graph URzQ_CNOT l ->
    (forall r, List.In r rules -> forall l l1 l2,
          respects_constraints_directed is_in_graph URzQ_CNOT l ->
          r l = Some (l1, l2) 
          -> respects_constraints_directed is_in_graph URzQ_CNOT l1
             /\ respects_constraints_directed is_in_graph URzQ_CNOT l2) ->
    try_rewrites2 l rules = Some (l1, l2) -> 
    respects_constraints_directed is_in_graph URzQ_CNOT l1
    /\ respects_constraints_directed is_in_graph URzQ_CNOT l2.
Proof.
  intros.
  induction rules.
  inversion H1.
  simpl in H1.
  destruct (a l) eqn:al.
  inversion H1; subst.
  eapply H0.
  left. reflexivity. apply H. apply al.
  apply IHrules.
  intros. 
  eapply H0.  right.  
  apply H2.
  apply H3.
  apply H4.
  
  apply H1. 

Qed.

Definition cancel_rules_respect_constraints {dim }  rules is_in_graph :=
  forall r, 
    List.In r rules ->
    forall (l l' : RzQ_ucom_l dim),
      (respects_constraints_directed is_in_graph URzQ_CNOT l -> r l = Some l'
       -> respects_constraints_directed is_in_graph URzQ_CNOT l').


Definition commute_rules_respect_constraints  {dim } rules is_in_graph :=
  forall r, 
    List.In r rules ->
    forall (l l1 l2: RzQ_ucom_l dim),
      (respects_constraints_directed is_in_graph URzQ_CNOT l -> r l = Some (l1, l2)
       -> respects_constraints_directed is_in_graph URzQ_CNOT l1
          /\ respects_constraints_directed is_in_graph URzQ_CNOT  l2).

Lemma propagate'_respects_constraints : 
  forall { dim} (l : RzQ_ucom_l dim) 
    commute_rules cancel_rules n acc l'  is_in_graph,
    respects_constraints_directed is_in_graph URzQ_CNOT l ->
      respects_constraints_directed is_in_graph URzQ_CNOT acc -> 

  cancel_rules_respect_constraints cancel_rules is_in_graph ->
  commute_rules_respect_constraints commute_rules is_in_graph ->
  propagate' l commute_rules cancel_rules n acc = Some l' ->
  respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.

  intros.
  generalize dependent acc.
  generalize dependent l'.
  generalize dependent l.
  induction n; intros l respects_l l' acc respects_acc res; try discriminate.
  simpl in res.
  destruct (try_rewrites l cancel_rules) eqn:rewr1.
  inversion res; subst.
  rewrite rev_append_rev.
  apply respects_constraints_directed_app.
  apply rev_respects_constraints.
  assumption.
  apply try_rewrites_respects_constraints with (l':= g) (l0:= l) (rules := cancel_rules).
  assumption.
  intros r Hr l0 l' Hrcdl H0.
  apply H1 with (r := r) (l := l0); try assumption.
  assumption.

  
  destruct (try_rewrites2 l commute_rules) eqn:rewr2; try discriminate.
  destruct p.
  assert (respects_constraints_directed is_in_graph URzQ_CNOT g
          /\ respects_constraints_directed is_in_graph URzQ_CNOT g0). 
  apply try_rewrites2_respects_constraints with (l0 := l) (l1:= g) (l2:= g0)
                                                (rules := commute_rules).
  assumption.
  intros r Hr l0 l1 l2 Hrcdl0 rls. 
  eapply H2. apply Hr. apply Hrcdl0. apply rls. apply rewr2. 
  apply IHn with (l := g0) (acc := (rev_append g acc)).
  apply H.
  rewrite rev_append_rev.
  apply respects_constraints_directed_app.
  apply rev_respects_constraints.
  apply H.
  assumption.
  apply res.
Qed. 
  
Lemma propagate_respects_constraints :  forall {dim} (l l' : RzQ_ucom_l dim)
                                           n  commute_rules cancel_rules 
                                          (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph URzQ_CNOT l ->
      cancel_rules_respect_constraints  cancel_rules is_in_graph ->
      commute_rules_respect_constraints commute_rules is_in_graph  ->
    propagate l commute_rules cancel_rules n = Some l' ->
    respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros.
  apply (propagate'_respects_constraints l commute_rules cancel_rules n [] l' is_in_graph) ; try assumption; try constructor.
Qed. 


Lemma Rz_cancel_rule_respects_constraints: 
     forall { dim}  (is_in_graph : nat->nat->bool) a q, 
    @cancel_rules_respect_constraints dim [Rz_cancel_rule q a] is_in_graph.
Proof.
  intros.
  unfold cancel_rules_respect_constraints.
  intros. 
  unfold Rz_cancel_rule in H.
  destruct_In.
  rewrite <- H2 in H1.
  repeat destruct_matches.
  assert_and_prove_next_gate. 
  destruct H as [respects_g0  respects_g].
  inversion H1.
  apply respects_constraints_directed_app.
  apply combines_rotations_respects_constraints.
  apply respects_constraints_directed_app.
  assumption.
  assumption. 
Qed.

Lemma H_cancel_rule_respects_constraints: 
     forall { dim}  (is_in_graph : nat->nat->bool)  q, 
    @cancel_rules_respect_constraints dim [H_cancel_rule q] is_in_graph.
Proof.
  intros.
  unfold cancel_rules_respect_constraints.
  intros. 
  unfold H_cancel_rule in H.
  destruct_In.
  rewrite <- H2 in H1.
  repeat destruct_matches. 

  assert_and_prove_next_gate.
  destruct H as [respects_g0  respects_g].
  inversion H1.
  apply respects_constraints_directed_app.
 
  assumption.
  assumption. 
Qed.


Lemma X_cancel_rule_respects_constraints: 
     forall { dim}  (is_in_graph : nat->nat->bool)  q, 
    @cancel_rules_respect_constraints dim  [X_cancel_rule q] is_in_graph.
Proof.
  intros.
  unfold cancel_rules_respect_constraints.
  intros. 
  unfold X_cancel_rule in H.
  destruct_In.
  rewrite <- H2 in H1.
  repeat destruct_matches. 
  assert_and_prove_next_gate.
  destruct H as [respects_g0  respects_g].

  inversion H1.
  apply respects_constraints_directed_app.
 
  assumption.
  assumption. 
Qed.

Lemma CNOT_cancel_rule_respects_constraints: 
     forall { dim}  (is_in_graph : nat->nat->bool) q1 q2, 
    @cancel_rules_respect_constraints dim [CNOT_cancel_rule q1 q2] is_in_graph.
Proof.
  intros.
  unfold cancel_rules_respect_constraints.
  intros. 
  unfold CNOT_cancel_rule in H.
  destruct_In.
  rewrite <- H2 in H1.
  repeat destruct_matches.
  assert_and_prove_next_gate. 
  destruct H as [respects_g0 [ respects_g is_inn0n]].
  inversion H1.
  apply respects_constraints_directed_app. 
  
  assumption.
  assumption. 
Qed.


Lemma Rz_commute_rules_respect_constraints: 
     forall { dim} n (is_in_graph : nat->nat->bool), 
    @commute_rules_respect_constraints dim (Rz_commute_rules n) is_in_graph.
Proof.
  intros.
  unfold commute_rules_respect_constraints.
  intros. 
  unfold Rz_commute_rules in H.
  destruct_In.
  
  -
    rewrite <- H2 in H1.
    eapply Rz_commute_rule1_respects_constraints.
    apply H0.
    apply H1.
  -
    rewrite <- H in H1. 
    eapply Rz_commute_rule2_respects_constraints.
    apply H0.
    apply H1. 
  -
    rewrite <-  H2 in H1. 
    eapply Rz_commute_rule3_respects_constraints.
    apply H0.
    apply H1. 

Qed.


Lemma CNOT_commute_rules_respect_constraints: 
     forall { dim} n1 n2 (is_in_graph : nat->nat->bool), 
    @commute_rules_respect_constraints dim  (CNOT_commute_rules n1 n2) is_in_graph.
Proof.
  intros.
  unfold commute_rules_respect_constraints.
  intros. 
  unfold CNOT_commute_rules in H.
  destruct_In.
  
  -
    rewrite <- H2 in H1.
    eapply CNOT_commute_rule1_respects_constraints.
    apply H0.
    apply H1.
  -
    rewrite <- H in H1. 
    eapply CNOT_commute_rule2_respects_constraints.
    apply H0.
    apply H1. 
  -
    rewrite <-  H2 in H1. 
    eapply CNOT_commute_rule3_respects_constraints.
    apply H0.
    apply H1. 
  -
    rewrite <-  H in H1. 
    eapply CNOT_commute_rule4_respects_constraints.
    apply H0.
    apply H1. 
  -
    rewrite <-  H2 in H1. 
    eapply CNOT_commute_rule5_respects_constraints.
    apply H0.
    apply H1. 
  
Qed.
Lemma propagate_Rz_respects_constraints : forall {dim} a (l : RzQ_ucom_l dim)
                                                 (is_in_graph : nat -> nat -> bool) (q : nat) l',

     respects_constraints_directed is_in_graph URzQ_CNOT l ->
     propagate_Rz a l q = Some l' ->
     respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros. 
  unfold propagate_Rz in H0.
  eapply propagate_respects_constraints.
  apply H.
  apply Rz_cancel_rule_respects_constraints.
  apply Rz_commute_rules_respect_constraints.
  apply H0. 
Qed.


Lemma propagate_H_respects_constraints : forall {dim}  (l : RzQ_ucom_l dim)
                                                 (is_in_graph : nat -> nat -> bool) (q : nat) l',

     respects_constraints_directed is_in_graph URzQ_CNOT l ->
     propagate_H  l q = Some l' ->
     respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros. 
  unfold propagate_H in H0.
  eapply propagate_respects_constraints.
  apply H.
  apply H_cancel_rule_respects_constraints.
  assert (@commute_rules_respect_constraints  dim  [] is_in_graph).
  unfold commute_rules_respect_constraints.
  intros.
  destruct_In.
  apply H1. 
  apply H0. 
Qed.   

Lemma propagate_X_respects_constraints : forall {dim} (l : RzQ_ucom_l dim)
                                                 (is_in_graph : nat -> nat -> bool) (q : nat) l',

     respects_constraints_directed is_in_graph URzQ_CNOT l ->
     propagate_X  l q = Some l' ->
     respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros. 
  unfold propagate_X in H0.
  eapply propagate_respects_constraints.
  apply H.
  apply X_cancel_rule_respects_constraints.
  assert (@commute_rules_respect_constraints  dim [X_commute_rule q] is_in_graph).
  unfold commute_rules_respect_constraints.
  intros.
  destruct_In.
  rewrite <- H4 in H3. 
  eapply X_commute_rule_respects_constraints.
  apply H2.
  apply H3.
  apply H1.
  apply H0. 
Qed.


Lemma propagate_CNOT_respects_constraints : forall {dim}  (l : RzQ_ucom_l dim)
                                                 (is_in_graph : nat -> nat -> bool) (q1 q2 : nat) l',

     respects_constraints_directed is_in_graph URzQ_CNOT l ->
     propagate_CNOT  l q1 q2 = Some l' ->
     respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros. 
  unfold propagate_Rz in H0.
  eapply propagate_respects_constraints.
  apply H.
  apply CNOT_cancel_rule_respects_constraints.
  apply CNOT_commute_rules_respect_constraints.
  apply H0. 
Qed.


Lemma cancel_single_qubit_gates'_respects_constraints : forall {dim}  (l l' acc: RzQ_ucom_l dim)
                                                 (is_in_graph : nat -> nat -> bool) (n : nat) ,

    respects_constraints_directed is_in_graph URzQ_CNOT l ->
    respects_constraints_directed is_in_graph URzQ_CNOT acc ->
     cancel_single_qubit_gates'  l n acc =  l' ->
     respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  
  intros.

  generalize dependent acc.
  generalize dependent l.
  induction n. 
  
  - intros. inversion H1. 
    subst. unfold cancel_single_qubit_gates'. rewrite rev_append_rev.
    apply respects_constraints_directed_app.
    apply rev_respects_constraints.
    assumption.
    assumption.
  - intros.
    induction l.
    +
      intros. 
      unfold cancel_single_qubit_gates' in H1.
      subst.
      apply rev_append_respects_constraints; assumption. 

    +
      intros. 
      unfold cancel_single_qubit_gates' in H1.
      destruct a.      
      dependent destruction r.
      *  remember (propagate_H l n0) as pH.
         
        destruct pH.
        
        {
          fold (@cancel_single_qubit_gates' dim l0 n acc) in H1.   
          assert (respects_constraints_directed is_in_graph URzQ_CNOT l0).
          eapply propagate_H_respects_constraints.
          inversion H.
          apply H5.  
          symmetry in HeqpH. 
          apply HeqpH.

          eapply IHn.
          apply H2.
          apply H0.
          apply H1. 
        }

        {
          fold (@cancel_single_qubit_gates' dim l n (RzQGateSet.H n0 :: acc)) in H1.
          inversion H; subst. 
          
          apply IHn with (l0:= l) (acc0:= (RzQGateSet.H n0 :: acc)).
          
          apply H5.
          constructor. 
          apply H0. 
          reflexivity. 
        }
      *  remember (propagate_X l n0) as pX.
         
        destruct pX.
        
        {
          fold (@cancel_single_qubit_gates' dim l0 n acc) in H1.   
          assert (respects_constraints_directed is_in_graph URzQ_CNOT l0).
          eapply propagate_X_respects_constraints.
          inversion H.
          apply H5. 
          symmetry in HeqpX. 
          apply HeqpX.

          eapply IHn.
          apply H2.
          apply H0.
          apply H1. 
        }

        {
          fold (@cancel_single_qubit_gates' dim l n (RzQGateSet.X n0 :: acc)) in H1.
          inversion H; subst. 
          
          apply IHn with (l0:= l) (acc0:= (RzQGateSet.X n0 :: acc)).
          
          apply H5.
          constructor. 
          apply H0. 
          reflexivity. 
        }

      * remember (propagate_Rz a l n0) as pRz.
         
        destruct pRz.
        
        {
          fold (@cancel_single_qubit_gates' dim l0 n acc) in H1.   
          assert (respects_constraints_directed is_in_graph URzQ_CNOT l0).
          eapply propagate_Rz_respects_constraints.
          inversion H.
          apply H5. 
          symmetry in HeqpRz. 
          apply HeqpRz.

          eapply IHn.
          apply H2.
          apply H0.
          apply H1. 
        }

        {
          fold (@cancel_single_qubit_gates' dim l n (Rzq a n0 :: acc)) in H1.
          inversion H; subst. 
          
          apply IHn with (l0:= l) (acc0:= (Rzq a n0 :: acc)).
          
          apply H5.
          constructor. 
          apply H0. 
          reflexivity. 
        }

      * fold (@cancel_single_qubit_gates' dim l n (App2 r n0 n1 :: acc)) in H1. 
       
        inversion H; subst.
        apply IHn with (l0 :=l) (acc0 := App2 URzQ_CNOT n0 n1 :: acc).
        apply H9.
        constructor.
        assumption.
        assumption.
        reflexivity.
      * inversion H. 
Qed. 

Lemma cancel_single_qubit_gates_respects_constraints : forall {dim}  (l l': RzQ_ucom_l dim)
                                                 (is_in_graph : nat -> nat -> bool) ,

    respects_constraints_directed is_in_graph URzQ_CNOT l ->
     cancel_single_qubit_gates  l =  l' ->
     respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros.
  apply cancel_single_qubit_gates'_respects_constraints with (l0 := l) (acc := []) (n := (length l)) . 
  assumption.
  constructor.
  unfold cancel_single_qubit_gates in H0.
  assumption.
  Qed. 

Lemma cancel_two_qubit_gates'_respects_constraints : forall {dim}  (l l' acc: RzQ_ucom_l dim)
                                                 (is_in_graph : nat -> nat -> bool) (n : nat) ,

    respects_constraints_directed is_in_graph URzQ_CNOT l ->
    respects_constraints_directed is_in_graph URzQ_CNOT acc ->
     cancel_two_qubit_gates'  l n acc =  l' ->
     respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  
  intros.

  generalize dependent acc.
  generalize dependent l.
  induction n. 
  
  - intros. inversion H1. 
    subst. unfold cancel_two_qubit_gates'.
    apply rev_append_respects_constraints; assumption. 
  - intros.

    

    
    induction l.
    +
      intros. 
      unfold cancel_two_qubit_gates' in H1.
      subst. 
      apply rev_append_respects_constraints; assumption. 
    +
      intros. 
      unfold cancel_two_qubit_gates' in H1.  
      destruct a.      
      dependent destruction r.
      (* These should be able to be ltac'd *)
      *  fold (@cancel_two_qubit_gates' dim l n (App1 URzQ_H n0 :: acc)) in H1.
         
        inversion H; subst.
        apply IHn  with (l0 :=l) (acc0 := (App1 URzQ_H n0 :: acc)).
        apply H5.
        constructor.
        assumption.
        reflexivity.
      * fold (@cancel_two_qubit_gates' dim l n (App1 URzQ_X n0 :: acc)) in H1.
         
        inversion H; subst.
        apply IHn  with (l0 :=l) (acc0 := (App1 URzQ_X n0 :: acc)).
        apply H5.
        constructor.
        assumption.
        reflexivity.
      * fold (@cancel_two_qubit_gates' dim l n (App1 (URzQ_Rz a) n0 :: acc)) in H1.
         
        inversion H; subst.
        apply IHn  with (l0 :=l) (acc0 := (App1 (URzQ_Rz a) n0 :: acc)).
        apply H5.
        constructor.
        assumption.
        reflexivity.
      * remember (propagate_CNOT l n0 n1) as pCNOT.
         
        destruct pCNOT;
        dependent destruction r. 
        {
          fold (@cancel_two_qubit_gates' dim l0 n acc) in H1.   
          assert (respects_constraints_directed is_in_graph URzQ_CNOT l0).
          eapply propagate_CNOT_respects_constraints.
          inversion H.
          apply H8. 
          symmetry in HeqpCNOT. 
          apply HeqpCNOT.

          eapply IHn.
          apply H2.
          apply H0.
          apply H1. 
        }

        {
          fold (@cancel_two_qubit_gates' dim l n (RzQGateSet.CNOT n0 n1 :: acc)) in H1.
          inversion H; subst. 
          
          apply IHn with (l0:= l) (acc0:= (RzQGateSet.CNOT n0 n1 :: acc)).
          
          apply H8.
          constructor. 
          apply H6.
          assumption. 
          reflexivity. 
        }
      *
        inversion H. 
Qed.         

Lemma cancel_two_qubit_gates_respects_constraints : forall {dim}  (l l': RzQ_ucom_l dim)
                                                 (is_in_graph : nat -> nat -> bool) ,

    respects_constraints_directed is_in_graph URzQ_CNOT l ->
     cancel_two_qubit_gates  l =  l' ->
     respects_constraints_directed is_in_graph URzQ_CNOT l'.
Proof.
  intros.
  apply cancel_two_qubit_gates'_respects_constraints with (l0 := l) (acc := []) (n := (length l)) . 
  assumption.
  constructor.
  unfold cancel_two_qubit_gates in H0.
  assumption.
  Qed. 
