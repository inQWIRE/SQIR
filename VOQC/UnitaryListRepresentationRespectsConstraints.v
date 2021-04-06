Require Import UnitarySem.
Require Export RzQGateSet.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

Require Import SimpleMapping.

Require Import UnitaryListRepresentation.
Require Import StandardGateSet.
Import StdList.

Lemma next_single_qubit_gate_respects_constraints:
    forall {U dim} (l l1 l2: gate_list U dim) g (q : nat) (is_in_graph : nat->nat-> bool) cnot,
    respects_constraints_directed is_in_graph cnot l ->
    Some (l1, g, l2) = (next_single_qubit_gate l q) ->
    respects_constraints_directed is_in_graph cnot l1
    /\ respects_constraints_directed is_in_graph  cnot l2.
Proof.
  intros.
  symmetry in H0.
  apply nsqg_preserves_structure in H0. 
  split;
  inversion H0; subst; 
  eapply respects_constraints_directed_app_split in H; 
  destruct H as [rcdapp rcdl1].
  apply rcdl1.

  eapply respects_constraints_directed_app_split in rcdapp.
  destruct rcdapp as [rcdl2 rcda1].
  assumption. 
  Qed. 


Lemma next_two_qubit_gate_respects_constraints:
  forall {U dim} (l l1 l2: gate_list U dim) g (q q1 q2 : nat)
         (is_in_graph : nat->nat-> bool) cons,
    respects_constraints_directed is_in_graph cons l ->
    Some (l1, g, q1, q2, l2) = (next_two_qubit_gate l q) ->
    respects_constraints_directed is_in_graph cons l1
    /\ respects_constraints_directed is_in_graph cons l2 /\ is_in_graph q1 q2 = true.
Proof.
  intros.
  symmetry in H0.
  apply ntqg_preserves_structure in H0. 
  rewrite H0 in H. 
  eapply respects_constraints_directed_app_split in H.
  destruct H as [rcdapp rcdl1].
  eapply respects_constraints_directed_app_split in rcdapp.
  destruct rcdapp as [rcdl2 rcdapp2].
  split.
  assumption. 
  split.
  assumption. 
  inversion rcdapp2; subst.
  assumption. 
  
   
Qed.       



Lemma try_rewrites_respects_constraints:
  forall {U dim} (l l' : gate_list U dim) rules  (is_in_graph : nat -> nat -> bool) cons,
    respects_constraints_directed is_in_graph cons l ->
    (forall r, List.In r rules ->
               forall l l', respects_constraints_directed is_in_graph cons l ->
                            r l = Some l' ->
                            respects_constraints_directed is_in_graph cons l') ->
    try_rewrites l rules = Some l' -> 
    respects_constraints_directed is_in_graph cons l'.
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

Lemma try_rewrites2_respects_constraints:
  forall {U dim} (l l1 l2 : gate_list U dim) rules (is_in_graph : nat -> nat -> bool) cons,
    respects_constraints_directed is_in_graph cons l ->
    (forall r, List.In r rules ->
               forall l l1 l2, respects_constraints_directed is_in_graph cons l ->
                               r l = Some (l1, l2) ->
                               respects_constraints_directed is_in_graph cons l1
    /\ respects_constraints_directed is_in_graph cons l2) ->
    try_rewrites2 l rules = Some (l1, l2) -> 
    respects_constraints_directed is_in_graph cons l1
    /\ respects_constraints_directed is_in_graph cons l2.
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

Lemma combines_rotations_respects_constraints:
  forall {dim} a a' q (is_in_graph : nat-> nat-> bool) cons,
    respects_constraints_directed is_in_graph cons (@combine_rotations dim a a' q).
Proof.
  intros.
  unfold combine_rotations.
  destruct (Qeq_bool (RzQGateSet.bound (a + a')) zero_Q).
  constructor.
  constructor.
  constructor.
Qed. 


Definition cancel_rules_respect_constraints {dim U}  rules is_in_graph cons :=
  forall r, 
  List.In r rules ->
  forall (l l' : gate_list U dim), (respects_constraints_directed is_in_graph cons l ->
                                    r l = Some l' ->
                                    respects_constraints_directed is_in_graph cons l').


Definition commute_rules_respect_constraints  {dim U} rules is_in_graph cons :=
  forall r, 
  List.In r rules ->
  forall (l l1 l2: gate_list U dim), (respects_constraints_directed is_in_graph cons l ->
                                      r l = Some (l1, l2) ->
                                      respects_constraints_directed is_in_graph cons l1
                                      /\ respects_constraints_directed is_in_graph cons l2).

Lemma propagate'_respects_constraints : 
  forall {U dim} (l : gate_list U dim) 
    commute_rules cancel_rules n acc l'  is_in_graph cons,
    respects_constraints_directed is_in_graph cons l ->
      respects_constraints_directed is_in_graph cons acc -> 

  cancel_rules_respect_constraints cancel_rules is_in_graph cons ->
  commute_rules_respect_constraints commute_rules is_in_graph cons ->
  propagate' l commute_rules cancel_rules n acc = Some l' ->
  respects_constraints_directed is_in_graph cons l'.
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
  assert (respects_constraints_directed is_in_graph cons g
          /\ respects_constraints_directed is_in_graph cons g0). 
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
                                          (is_in_graph : nat-> nat-> bool) cons,
    respects_constraints_directed is_in_graph cons l ->
      cancel_rules_respect_constraints  cancel_rules is_in_graph cons ->
      commute_rules_respect_constraints commute_rules is_in_graph cons ->
    propagate l commute_rules cancel_rules n = Some l' ->
    respects_constraints_directed is_in_graph cons l'.
Proof.
  intros.
  apply (propagate'_respects_constraints l commute_rules cancel_rules n [] l' is_in_graph);
    try assumption; try constructor.
Qed. 




(* Some maybe helpful Ltacs for proofs *)
Ltac destruct_matches :=
  
  match goal with
  | H :   match ?Y with _ => _  end = _ |- _ =>
    let h:= fresh in remember Y as h;
                     try destruct h;
                     try dependent destruction h;
                     try discriminate; destruct_pairs; subst
  end.

Ltac assert_next_single_qubit_gate  :=
  
  match reverse goal with
  |[ H :   Some (?l11, ?gat, ?l22) = next_single_qubit_gate ?in_l ?qub 
    |- respects_constraints_directed ?iig ?c _ /\
       respects_constraints_directed ?iig ?c _] =>
    assert (respects_constraints_directed iig c l11
            /\ respects_constraints_directed iig c l22)
  | H :   Some (?l11, ?gat, ?l22) = next_single_qubit_gate ?in_l ?qub 
     |- respects_constraints_directed ?iig ?c _  =>
   assert (respects_constraints_directed iig c l11
           /\ respects_constraints_directed iig c l22)
           
  end.
Open Scope ucom.
Require Export RzQGateSet.
Ltac assert_next_two_qubit_gate :=
  match reverse goal with
  |[ H :   Some (?l11, URzQ_CNOT, ?n0, ?n, ?l22) = next_two_qubit_gate ?in_l ?qub 
    |- respects_constraints_directed ?iig ?c _ /\
       respects_constraints_directed ?iig ?c _] =>
    assert (respects_constraints_directed iig c l11
            /\ respects_constraints_directed iig c l22
            /\ iig n0 n = true)
  |[ H :   Some (?l11, URzQ_CNOT, ?n0, ?n, ?l22) = next_two_qubit_gate ?in_l ?qub 
     |- respects_constraints_directed ?iig ?c _] =>
   assert (respects_constraints_directed iig c l11
           /\ respects_constraints_directed iig c l22
           /\ iig n0 n = true)
  end.

Ltac prove_next_gates_assertion  :=
  
  match reverse goal with
  | H :   Some (?l11, ?gat, ?l22) = next_single_qubit_gate ?in_l ?qub 
    |- respects_constraints_directed ?iig ?c ?ll1 /\
       respects_constraints_directed ?iig ?c ?ll2 =>
    
    try (eapply next_single_qubit_gate_respects_constraints
           with (l := in_l) (l1 := l11) (l2 := l22) (g5 := gat) (q0 := qub));
    try (eapply next_single_qubit_gate_respects_constraints
           with (l := in_l) (l1 := l11) (l2 := l22) (g1 := gat) (q0 := qub));
    try assumption
        
  | H :   Some  (?l11, URzQ_CNOT, ?n0, ?n, ?l22) = next_two_qubit_gate ?in_l ?qub 
    |- respects_constraints_directed ?iig ?c ?ll1 /\
       respects_constraints_directed ?iig ?c ?ll2 /\ ?iig ?n0 ?n = true=>
    
    try (eapply next_two_qubit_gate_respects_constraints
           with (l := in_l) (l1 := l11) (l2 := l22) (g5 := URzQ_CNOT) (q0 := qub));
        try (eapply next_two_qubit_gate_respects_constraints
      with (l := in_l) (l1 := l11) (l2 := l22) (g1 := URzQ_CNOT) (q0 := qub));
    try assumption
  end.

Ltac clear_next_gates  :=
  
  match reverse goal with
  | H :   Some (_) = _
    |- _ =>
    clear H

  end.
