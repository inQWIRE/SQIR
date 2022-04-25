Require Import UnitaryListRepresentation.

(* This file defines 'respects_constraints' predicates for describing when a 
   program is properly mapped (i.e. respects architecture connectivity 
   constraints) and utilities for proving 'respects_constraints' properties. *)


(** Predicates describing a correctly mapped program (gate set independent). **)
Inductive respects_constraints_undirected {U dim} : (nat -> nat -> bool) -> gate_list U dim -> Prop :=
  | res_und_nil : forall is_in_graph,
      respects_constraints_undirected is_in_graph []
  | res_und_app1 : forall u n t is_in_graph, 
      respects_constraints_undirected is_in_graph t ->
      respects_constraints_undirected is_in_graph (App1 u n :: t)
  | res_und_app2 : forall u n1 n2 t is_in_graph, 
      is_in_graph n1 n2 = true \/ is_in_graph n2 n1 = true -> (* undirected *)
      respects_constraints_undirected is_in_graph t ->
      respects_constraints_undirected is_in_graph (App2 u n1 n2 :: t).

Inductive respects_constraints_directed {U : nat -> Set} {dim} : (nat -> nat -> bool) -> U 2%nat -> gate_list U dim -> Prop :=
  | res_dir_nil : forall is_in_graph cnot,
      respects_constraints_directed is_in_graph cnot []
  | res_dir_app1 : forall u n t is_in_graph cnot, 
      respects_constraints_directed is_in_graph cnot t ->
      respects_constraints_directed is_in_graph cnot (App1 u n :: t)
  | res_dir_app2 : forall n1 n2 t is_in_graph cnot, 
      is_in_graph n1 n2 = true -> (* directed *) 
      respects_constraints_directed is_in_graph cnot t ->
      respects_constraints_directed is_in_graph cnot (App2 cnot n1 n2 :: t).

Lemma respects_constraints_undirected_app : forall {U dim} (l1 l2 : gate_list U dim) is_in_graph,
  respects_constraints_undirected is_in_graph l1 ->
  respects_constraints_undirected is_in_graph l2 ->
  respects_constraints_undirected is_in_graph (l1 ++ l2).
Proof.
  intros U dim l1 l2 is_in_graph Hl1 Hl2.
  induction Hl1.
  simpl; assumption.
  rewrite <- app_comm_cons.
  constructor; auto.
  constructor; auto.
Qed.

Lemma respects_constraints_undirected_app_split : forall {U dim} (l1 l2 : gate_list U dim) is_in_graph,
  respects_constraints_undirected is_in_graph (l1 ++ l2) ->
  respects_constraints_undirected is_in_graph l2 /\
  respects_constraints_undirected is_in_graph l1.
Proof.
  intros U dim l1 l2 is_in_graph H.
  split.
  - induction l1.
    simpl in H.
    assumption.
    rewrite <- app_comm_cons in H.
    destruct a; remember (l1 ++ l2) as l; inversion H; subst;
      try (apply IHl1 in H2); auto.
  - induction l1.
    constructor.
    rewrite <- app_comm_cons in H;   
      destruct a; remember (l1 ++ l2) as l; inversion H; subst.
    constructor; auto.
    constructor; auto.
Qed.

Lemma rev_respects_constraints_undirected:
  forall {U dim} (l : gate_list U dim) (is_in_graph : nat -> nat -> bool),
    respects_constraints_undirected is_in_graph l ->
    respects_constraints_undirected is_in_graph (rev l).
Proof.
  intros.
  induction l; simpl; auto.
  destruct a; inversion H; subst.
  apply respects_constraints_undirected_app; auto.
  constructor. constructor.
  apply respects_constraints_undirected_app; auto.
  constructor. auto. constructor.
Qed. 

Lemma rev_append_respects_constraints_undirected:
  forall {U dim} (l1 l2 : gate_list U dim) (is_in_graph : nat -> nat -> bool),
    respects_constraints_undirected is_in_graph l1 ->
    respects_constraints_undirected is_in_graph l2 ->
    respects_constraints_undirected is_in_graph (rev_append l1 l2).
Proof.
  intros.
  rewrite rev_append_rev.
  apply respects_constraints_undirected_app.
  apply rev_respects_constraints_undirected.
  assumption.
  assumption.
Qed.

Lemma next_two_qubit_gate_respects_constraints_undirected:
  forall {U dim} (l l1 l2: gate_list U dim) g (q q1 q2 : nat) (is_in_graph : nat -> nat -> bool),
  respects_constraints_undirected is_in_graph l ->
  next_two_qubit_gate l q = Some (l1, g, q1, q2, l2) ->
  respects_constraints_undirected is_in_graph l1
    /\ respects_constraints_undirected is_in_graph l2 /\ 
      (is_in_graph q1 q2 = true \/ is_in_graph q2 q1 = true).
Proof.
  intros.
  apply ntqg_preserves_structure in H0. 
  rewrite H0 in H. 
  eapply respects_constraints_undirected_app_split in H.
  destruct H as [rcdapp rcdl1].
  eapply respects_constraints_undirected_app_split in rcdapp.
  destruct rcdapp as [rcdl2 rcdapp2].
  repeat split; auto.
  inversion rcdapp2; subst.
  assumption.
Qed.

Lemma respects_constraints_directed_app : forall {U dim} (l1 l2 : gate_list U dim) is_in_graph cnot,
  respects_constraints_directed is_in_graph cnot l1 ->
  respects_constraints_directed is_in_graph cnot l2 ->
  respects_constraints_directed is_in_graph cnot (l1 ++ l2).
Proof.
  intros U dim l1 l2 is_in_graph cnot Hl1 Hl2.
  induction Hl1.
  simpl; assumption.
  rewrite <- app_comm_cons.
  constructor; auto.
  constructor; auto.
Qed.

Lemma respects_constraints_directed_app_split : forall {U dim} (l1 l2 : gate_list U dim) is_in_graph cnot,
  respects_constraints_directed is_in_graph cnot (l1 ++ l2) ->
  respects_constraints_directed is_in_graph cnot l2 /\
  respects_constraints_directed is_in_graph cnot l1.
Proof.
  intros U dim l1 l2 is_in_graph cnot H.
  split.
  - induction l1.
    simpl in H.
    assumption.
    rewrite <- app_comm_cons in H.
    destruct a; remember (l1 ++ l2) as l; inversion H; subst;
    try (apply IHl1 in H2); try assumption.
    + apply IHl1 in H3. assumption.
    + apply IHl1 in H7.  assumption. 
  -induction l1.
   + apply res_dir_nil.
   + rewrite <- app_comm_cons in H;   
   destruct a; remember (l1 ++ l2) as l; inversion H; subst.
   * apply IHl1 in H3.
     apply res_dir_app1 with (u0 := u) (n0 := n).
     assumption.
   * apply IHl1 in H7.
     apply res_dir_app2 with (n1 := n) (n2 := n0) in H7.
     assumption.
     assumption.
Qed.

Lemma rev_respects_constraints:
  forall {U dim} (l : gate_list U dim) (is_in_graph : nat -> nat -> bool) cnot,
    respects_constraints_directed is_in_graph cnot l ->
    respects_constraints_directed is_in_graph cnot (rev l).
Proof.
  intros.
  induction l.
  - simpl. assumption.
  - simpl.
    apply respects_constraints_directed_app.
    apply IHl.
    inversion H; subst.
    assumption. 
    assumption.
    destruct a; try constructor; try constructor.
    inversion H; subst.
    constructor; try assumption.
    constructor.
    inversion H; subst.
Qed. 

Lemma rev_append_respects_constraints:
  forall {U dim} (l1 l2 : gate_list U dim) (is_in_graph : nat -> nat -> bool) cnot,
    respects_constraints_directed is_in_graph cnot l1 ->
    respects_constraints_directed is_in_graph cnot l2 ->
    respects_constraints_directed is_in_graph cnot (rev_append l1 l2).
Proof.
  intros.
  rewrite rev_append_rev.
  apply respects_constraints_directed_app.
  apply rev_respects_constraints.
  assumption.
  assumption.
Qed.

(** X_respects_constraints facts about the defns in UnitaryListRepresentation. **)

Lemma next_single_qubit_gate_respects_constraints:
  forall {U dim} (l l1 l2: gate_list U dim) g (q : nat) (is_in_graph : nat -> nat -> bool) cnot,
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
  forall {U dim} (l l1 l2: gate_list U dim) g (q q1 q2 : nat) (is_in_graph : nat -> nat -> bool) cnot,
  respects_constraints_directed is_in_graph cnot l ->
  Some (l1, g, q1, q2, l2) = (next_two_qubit_gate l q) ->
  respects_constraints_directed is_in_graph cnot l1
    /\ respects_constraints_directed is_in_graph cnot l2 /\ is_in_graph q1 q2 = true.
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

Ltac assert_next_single_qubit_gate  :=
  match reverse goal with
  |[ H :   Some (?l11, ?gat, ?l22) = next_single_qubit_gate ?in_l ?qub 
    |- respects_constraints_directed ?iig _ /\
       respects_constraints_directed ?iig _] =>
    assert (respects_constraints_directed iig l11
            /\ respects_constraints_directed iig l22)
  | H :   Some (?l11, ?gat, ?l22) = next_single_qubit_gate ?in_l ?qub 
     |- respects_constraints_directed ?iig _  =>
   assert (respects_constraints_directed iig l11
           /\ respects_constraints_directed iig l22)
end.

Ltac assert_next_two_qubit_gate :=
  match reverse goal with
  |[ H :   Some (?l11, _, ?n0, ?n, ?l22) = next_two_qubit_gate ?in_l ?qub 
    |- respects_constraints_directed ?iig _ /\
       respects_constraints_directed ?iig _] =>
    assert (respects_constraints_directed iig l11
            /\ respects_constraints_directed iig l22
            /\ iig n0 n = true)
  |[ H :   Some (?l11, _, ?n0, ?n, ?l22) = next_two_qubit_gate ?in_l ?qub 
     |- respects_constraints_directed ?iig _] =>
   assert (respects_constraints_directed iig l11
           /\ respects_constraints_directed iig l22
           /\ iig n0 n = true)
  end. 

Ltac prove_next_gates_assertion  :=
  match reverse goal with
  | H :   Some (?l11, ?gat, ?l22) = next_single_qubit_gate ?in_l ?qub 
    |- respects_constraints_directed ?iig ?ll1 /\
       respects_constraints_directed ?iig ?ll2 =>
    
    try (eapply next_single_qubit_gate_respects_constraints
           with (l := in_l) (l1 := l11) (l2 := l22) (g5 := gat) (q0 := qub));
    try (eapply next_single_qubit_gate_respects_constraints
           with (l := in_l) (l1 := l11) (l2 := l22) (g1 := gat) (q0 := qub));
    try assumption
        
  | H :   Some  (?l11, _, ?n0, ?n, ?l22) = next_two_qubit_gate ?in_l ?qub 
    |- respects_constraints_directed ?iig ?ll1 /\
       respects_constraints_directed ?iig ?ll2 /\ ?iig ?n0 ?n = true=>
    
    try (eapply next_two_qubit_gate_respects_constraints
           with (l := in_l) (l1 := l11) (l2 := l22) (q0 := qub));
        try (eapply next_two_qubit_gate_respects_constraints
      with (l := in_l) (l1 := l11) (l2 := l22) (q0 := qub));
    try assumption
  end.

Ltac clear_next_gates  :=
  match reverse goal with
  | H : Some (_) = _  |- _ => clear H
  end.

Lemma try_rewrites_respects_constraints:
  forall {U dim} (l l' : gate_list U dim) rules  (is_in_graph : nat -> nat -> bool) cnot,
    respects_constraints_directed is_in_graph cnot l ->
    (forall r, List.In r rules ->
               forall l l', respects_constraints_directed is_in_graph cnot l ->
                            r l = Some l' ->
                            respects_constraints_directed is_in_graph cnot l') ->
    try_rewrites l rules = Some l' -> 
    respects_constraints_directed is_in_graph cnot l'.
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
  forall {U dim} (l l1 l2 : gate_list U dim) rules (is_in_graph : nat -> nat -> bool) cnot,
    respects_constraints_directed is_in_graph cnot l ->
    (forall r, List.In r rules ->
               forall l l1 l2, respects_constraints_directed is_in_graph cnot l ->
                               r l = Some (l1, l2) ->
                               respects_constraints_directed is_in_graph cnot l1
    /\ respects_constraints_directed is_in_graph cnot l2) ->
    try_rewrites2 l rules = Some (l1, l2) -> 
    respects_constraints_directed is_in_graph cnot l1
    /\ respects_constraints_directed is_in_graph cnot l2.
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

Definition cancel_rules_respect_constraints {dim U} rules is_in_graph cnot :=
  forall r, 
  List.In r rules ->
  forall (l l' : gate_list U dim), (respects_constraints_directed is_in_graph cnot l ->
                                    r l = Some l' ->
                                    respects_constraints_directed is_in_graph cnot l').

Definition commute_rules_respect_constraints  {dim U} rules is_in_graph cnot :=
  forall r, 
  List.In r rules ->
  forall (l l1 l2: gate_list U dim), (respects_constraints_directed is_in_graph cnot l ->
                                      r l = Some (l1, l2) ->
                                      respects_constraints_directed is_in_graph cnot l1
                                      /\ respects_constraints_directed is_in_graph cnot l2).

Lemma propagate'_respects_constraints : 
  forall {U dim} (l : gate_list U dim) 
    commute_rules cancel_rules n acc l'  is_in_graph cnot,
  respects_constraints_directed is_in_graph cnot l ->
  respects_constraints_directed is_in_graph cnot acc -> 
  cancel_rules_respect_constraints cancel_rules is_in_graph cnot ->
  commute_rules_respect_constraints commute_rules is_in_graph cnot ->
  propagate' l commute_rules cancel_rules n acc = Some l' ->
  respects_constraints_directed is_in_graph cnot l'.
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
  assert (respects_constraints_directed is_in_graph cnot g
          /\ respects_constraints_directed is_in_graph cnot g0). 
  apply try_rewrites2_respects_constraints with (l0 := l) (l1:= g) (l2:= g0)
                                                (rules := commute_rules).
  assumption.
  intros r Hr l0 l1 l2 Hrcdl0 rls. 
  eapply H2. apply Hr. apply Hrcdl0. apply rls. apply rewr2. 
  apply IHn with (l := g0) (acc := (rev_append g acc)).
  apply H.
  apply rev_append_respects_constraints; try assumption.  
  apply H.
  assumption.
Qed. 

Lemma propagate_respects_constraints :  forall {U dim} (l l' : gate_list U dim)
                                           n  commute_rules cancel_rules 
                                          (is_in_graph : nat -> nat -> bool) cnot,
    respects_constraints_directed is_in_graph cnot l ->
    cancel_rules_respect_constraints  cancel_rules is_in_graph cnot ->
    commute_rules_respect_constraints commute_rules is_in_graph cnot ->
    propagate l commute_rules cancel_rules n = Some l' ->
    respects_constraints_directed is_in_graph cnot l'.
Proof.
  intros.
  apply (propagate'_respects_constraints l commute_rules cancel_rules n [] l' is_in_graph);
    try assumption; try constructor.
Qed.

Ltac destruct_matches :=
  match goal with
  | H :   match ?Y with _ => _  end = _ |- _ =>
    let h:= fresh in remember Y as h;
                     try destruct h;
                     try dependent destruction h;
                     try discriminate; destruct_pairs; subst
  end.

Lemma next_gate'_respects_constraints:
  forall {U dim} (l l1 l2 acc: gate_list U dim) g (f : nat -> bool) is_in_graph cnot,
  respects_constraints_directed is_in_graph cnot l -> 
  respects_constraints_directed is_in_graph cnot acc ->
  next_gate' l f acc  = Some (l1, g,  l2) ->
  respects_constraints_directed is_in_graph cnot l1
    /\ respects_constraints_directed is_in_graph cnot l2
    /\ respects_constraints_directed is_in_graph cnot [g].
Proof.
  intros.
  generalize dependent acc. 
  induction l; intros. 
  - simpl in H1.
    inversion H1.
  - inversion H1; subst.
    repeat destruct_matches; 
      try (
          inversion H3; subst;
          try split; 
          try apply rev_append_respects_constraints; try assumption;  try constructor;
          try split ; 
          try inversion H; try subst;  try assumption ;
          try constructor; try constructor).
    all: try (
             assert(respects_constraints_directed is_in_graph cnot (App1 u n :: acc));
             try constructor; try assumption; try apply H2; try assumption).
    all: try (eapply IHl;  try assumption;  try apply H2;  try assumption ).
    assumption. 
    
    all: try (
             assert(respects_constraints_directed is_in_graph u (App2 u n n0 :: acc));
             try apply res_dir_app2; try apply H8; try assumption; try apply H0). 
Qed. 

Lemma next_gate_respects_constraints:
  forall {U dim} (l l1 l2: gate_list U dim) g (f : nat -> bool) is_in_graph cnot ,
    respects_constraints_directed is_in_graph cnot l ->
    Some (l1, g,  l2) = next_gate l f  ->
    respects_constraints_directed is_in_graph cnot l1
    /\ respects_constraints_directed is_in_graph cnot l2
    /\ respects_constraints_directed is_in_graph cnot [g].
Proof.
  intros.
  eapply next_gate'_respects_constraints.
  apply H.
  apply res_dir_nil.
  unfold next_gate in H0.
  symmetry in H0.
  apply H0. 
Qed.

(* This is nested matches so it finds the first hypothesis and doesn't try to find first match expression*)
Ltac assert_and_prove_next_gate :=
  
  match reverse goal with
  |[ H1 : respects_constraints_directed ?iig ?cnot _ |- _] =>
   match reverse goal with
   |[ H :   Some ?tuple = ?n_g ?in_l ?qub 
      |-  _ ] =>
    match n_g with
    | next_single_qubit_gate =>
      match tuple with
      |(?l11, ?gat,  ?l22) =>
       assert (respects_constraints_directed iig cnot l11
               /\ respects_constraints_directed iig cnot l22);
       [try eapply (next_single_qubit_gate_respects_constraints in_l l11 l22 gat qub);
        try assumption|]; clear H end
    | next_two_qubit_gate =>
      match tuple with
      |(?l11, ?cnot, ?n0, ?n, ?l22) =>
       assert (respects_constraints_directed iig cnot l11
               /\ respects_constraints_directed iig cnot l22
               /\ iig n0 n = true);
       [try eapply (next_two_qubit_gate_respects_constraints in_l l11 l22 cnot qub);
        try assumption|]; clear H end
    | next_gate =>
      match tuple with
        (?l11, ?gat, ?l22) => 
        assert (respects_constraints_directed iig cnot l11
                /\ respects_constraints_directed iig cnot l22
                /\ respects_constraints_directed iig cnot [gat]);
               [try eapply (next_gate_respects_constraints in_l l11 l22 gat qub);
        try assumption|]; clear H end
    end 
   end
  end.
      
 Lemma remove_prefix_respects_constraints:
   forall {U dim} (l l' pfx: gate_list U dim)
          (match_gate : (forall {n}, U n -> U n -> bool))
         is_in_graph cons,
    respects_constraints_directed is_in_graph cons l -> 
    respects_constraints_directed is_in_graph cons pfx ->
    remove_prefix l pfx (fun n => @match_gate n)  = Some l' ->
    respects_constraints_directed is_in_graph cons l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction pfx.
  - intros.
    induction l.
    + inversion H1.
      constructor.
    + simpl in H1. 
      destruct a; inversion H1;
        inversion H;  try constructor; try assumption. 
  - intros.
    induction l. 
    + simpl in H1. destruct a; inversion H1.
    + simpl in H1. 
      repeat destruct_matches.
      * eapply IHpfx.
        inversion H0; subst; assumption. 
        assert_and_prove_next_gate. 
        destruct H2 as [rcdg0 rcdg].
        assert (respects_constraints_directed is_in_graph cons (g0 ++ g)).
        apply respects_constraints_directed_app.
        apply rcdg0. apply rcdg. 
        apply H2.
        assumption. 
      * eapply IHpfx.
        inversion H0; subst; assumption.
        assert_and_prove_next_gate.
        destruct H2 as [iigg0 [iigg iigA2]].
        assert (respects_constraints_directed is_in_graph cons (g0++g)). 
        apply respects_constraints_directed_app; assumption.
        apply H2.
        apply H1. 
Qed.

Lemma remove_suffix_respects_constraints:
  forall {U dim} (l l' sfx: gate_list U dim) (match_gate : (forall {n}, U n -> U n -> bool))
         is_in_graph cnot,
    respects_constraints_directed is_in_graph cnot l -> 
    respects_constraints_directed is_in_graph cnot  sfx ->
    remove_suffix l sfx (fun n => @match_gate n)  = Some l' ->
    respects_constraints_directed is_in_graph cnot l'.
Proof.
  intros.
  unfold remove_suffix in H1. 
  destruct_matches.
  inversion H1; subst.
  assert (respects_constraints_directed is_in_graph cnot g). 
  eapply remove_prefix_respects_constraints.
  apply rev_append_respects_constraints. 
  apply H. apply res_dir_nil. 
  apply rev_append_respects_constraints. 
  apply H0. apply res_dir_nil. 
  symmetry in HeqH2.
  apply HeqH2.
  apply rev_append_respects_constraints; try assumption; try constructor. 
Qed. 
  
Ltac assert_get_matching_prefix' :=
      match reverse goal with
    |[ H :  get_matching_prefix' ?l1 ?l2 ?pacc ?lacc _ _ _ = _ 
       |- respects_constraints_directed ?iig ?c _ /\
           _] =>
     assert (respects_constraints_directed iig c l1
             /\ respects_constraints_directed iig c l2
             /\ respects_constraints_directed iig c pacc
             /\ respects_constraints_directed iig c lacc
            )
    end.

 Lemma get_matching_prefix'_respects_constraints:
   forall {U dim} n (l1 l2 pacc lacc l2a l2b u2: gate_list U  dim) blst
          (match_gate : (forall {n}, U n -> U n -> bool))
         is_in_graph cnot ,
    respects_constraints_directed is_in_graph cnot l1 -> 
    respects_constraints_directed is_in_graph cnot l2 ->
    respects_constraints_directed is_in_graph cnot  lacc ->
    respects_constraints_directed is_in_graph cnot pacc ->
    get_matching_prefix' l1 l2 pacc lacc blst n (fun n => @match_gate n)  = (l2a, u2, l2b) ->
    respects_constraints_directed is_in_graph cnot l2a
    /\ respects_constraints_directed is_in_graph cnot l2b
    /\ respects_constraints_directed is_in_graph cnot u2.
Proof.
  intros.
  generalize dependent l1.
  generalize dependent l2.
  generalize dependent pacc.
  generalize dependent lacc.
  generalize dependent blst.  
  induction n.
  - intros.
    simpl in H3. 
    inversion H3; subst; clear H3. 
    split.
    + apply rev_append_respects_constraints; try assumption;  constructor. 
    + split.
      assumption.
      apply rev_append_respects_constraints; try assumption; try constructor.
  - intros. 
    simpl in H3. 
    repeat destruct_matches;

      (* Each case has one or two next gate type calls*)
      try (assert_and_prove_next_gate; destruct H4 as [rcdg0 [rcdg rcdaun0]]) ;
      try (assert_and_prove_next_gate; destruct H4 as [rcdg2 rcdg1]) ;
      try destruct rcdg1 as [rcdg11 rcdg12];
  
      (* Last two cases *)
      try (inversion H3; subst; clear H3; split;
           [apply rev_append_respects_constraints; try assumption; try constructor|
            split;
            [assumption|apply rev_append_respects_constraints; try assumption; try constructor]] 
          ).
    +
      assert_get_matching_prefix'. 
       split; try assumption; split; try assumption. 
       apply respects_constraints_directed_app;
         assumption. 
       split.
       constructor.
       assumption.
       apply rev_append_respects_constraints; try assumption; try constructor.
       destruct H4 as [s1 [s2 [s3 s4]]]; eapply IHn. 
       apply s4. apply s3. apply s2. apply s1. 
       apply H3.
    + assert_get_matching_prefix'.
      split; try assumption; split; try  assumption; split; try assumption. 
      constructor. 
      apply rev_append_respects_constraints; try assumption; try constructor.
      destruct H4 as [s1 [s2 [s3 s4]]]; eapply IHn. 
      apply s4. apply s3. apply s2. apply s1. 
      apply H3.
    + assert_get_matching_prefix'.             
      split; try assumption; split; try  assumption; split; try assumption. 
      constructor. 
      apply rev_append_respects_constraints; try assumption; try constructor. 
      destruct H4 as [s1 [s2 [s3 s4]]]; eapply IHn. 
      apply s4. apply s3. apply s2. apply s1. 
      apply H3.
    + assert_get_matching_prefix'.
      split; try assumption; split; try assumption; split; try assumption; try constructor.  
      inversion rcdaun0; subst. 
      constructor.
      assumption. 
      apply rev_append_respects_constraints; try assumption; try constructor.
      destruct H4 as [s1 [s2 [s3 s4]]]; eapply IHn. 
      apply s4. apply s3. apply s2. apply s1. 
      apply H3.
    + assert_get_matching_prefix'.
      split; try assumption; split.
      apply respects_constraints_directed_app; try assumption. 
      split.
      inversion rcdaun0; subst; try constructor; try assumption.
      apply rev_append_respects_constraints; try assumption. 
      destruct H4 as [s1 [s2 [s3 s4]]]; eapply IHn. 
      apply s4. apply s3. apply s2. apply s1. 
      apply H3.
    + assert_get_matching_prefix'.
      split; try assumption; split; try assumption; split; try assumption. 
      inversion rcdaun0; subst; try constructor; try assumption.
      apply rev_append_respects_constraints; try assumption. 
      destruct H4 as [s1 [s2 [s3 s4]]]; eapply IHn. 
      apply s4. apply s3. apply s2. apply s1. 
      apply H3.      
    + assert_get_matching_prefix'.
      split; try assumption; split; try assumption; split; try assumption. 
      inversion rcdaun0; subst; try constructor; try assumption.
      apply rev_append_respects_constraints; try assumption. 
      destruct H4 as [s1 [s2 [s3 s4]]]; eapply IHn. 
      apply s4. apply s3. apply s2. apply s1. 
      apply H3.
    + assert_get_matching_prefix'.
      split; try assumption; split; try assumption; split; try assumption. 
      inversion rcdaun0; subst; try constructor; try assumption.
      apply rev_append_respects_constraints; try assumption. 
      destruct H4 as [s1 [s2 [s3 s4]]]; eapply IHn. 
      apply s4. apply s3. apply s2. apply s1. 
      apply H3.
Qed.

Lemma get_matching_prefix_respects_constraints:
  forall {U dim}  (l1 l2 pacc lacc l2a l2b u2: gate_list U dim)
         (match_gate : (forall {n}, U n -> U n -> bool))
         is_in_graph cnot ,
    respects_constraints_directed is_in_graph cnot l1 -> 
    respects_constraints_directed is_in_graph cnot l2 ->
    get_matching_prefix l1 l2 (fun n => @match_gate n) = (l2a, u2, l2b) ->
    respects_constraints_directed is_in_graph cnot l2a
    /\ respects_constraints_directed is_in_graph cnot l2b
    /\ respects_constraints_directed is_in_graph cnot u2.
Proof.
  intros.
  unfold get_matching_prefix in H1.
  eapply get_matching_prefix'_respects_constraints.
  apply H. apply H0. apply res_dir_nil. apply res_dir_nil. apply H1. 
Qed.

Lemma LCR_respects_constraints: 
  forall {U dim} (b l2a l2b u2: gate_list U dim) opt
         (match_gate : (forall {n}, U n -> U n -> bool))
         is_in_graph cnot,
    (forall p, respects_constraints_directed is_in_graph cnot p -> 
        respects_constraints_directed is_in_graph cnot (opt p)) -> 
    respects_constraints_directed is_in_graph cnot b -> 
    LCR b opt (fun n => @match_gate n) = Some (l2a, u2, l2b) ->
    respects_constraints_directed is_in_graph cnot l2a
    /\ respects_constraints_directed is_in_graph cnot l2b
    /\ respects_constraints_directed is_in_graph cnot u2.
Proof.
  intros.
  unfold LCR in H1.
  repeat destruct_matches.
  assert (respects_constraints_directed is_in_graph cnot (opt b)).
  apply H. assumption.
  assert (respects_constraints_directed is_in_graph cnot (opt b ++ opt b)).
  apply respects_constraints_directed_app; assumption. 
  assert (respects_constraints_directed is_in_graph cnot (opt b ++ opt b ++ opt b)). 
  apply respects_constraints_directed_app. assumption.
  apply respects_constraints_directed_app; assumption. 
  assert (respects_constraints_directed is_in_graph cnot (opt (opt b ++ opt b))).
  apply H; assumption. 
  assert (respects_constraints_directed is_in_graph cnot (opt (opt b ++ opt b ++ opt b))).
  apply H; assumption. 
  assert (respects_constraints_directed is_in_graph cnot l
    /\ respects_constraints_directed is_in_graph cnot g
    /\ respects_constraints_directed is_in_graph cnot l0). 
  eapply get_matching_prefix_respects_constraints; try assumption.
  apply H2. apply H5. symmetry in HeqH2. apply HeqH2.  
  inversion H1; subst.
  split. apply H7. split. apply H7.
  destruct H7 as [rcdl2a [rcdl2b rcdl0]].
  assert (respects_constraints_directed is_in_graph cnot g0). 
  eapply remove_prefix_respects_constraints.
  apply H6. apply rcdl2a. symmetry in HeqH0. apply HeqH0. 
  eapply remove_suffix_respects_constraints.
  apply H7. apply rcdl2b. symmetry. apply HeqH1. 
Qed.

Lemma replace_pattern_respects_constraints:
  forall {U dim} (l l' pat rep: gate_list U dim) match_gate is_in_graph cnot,
    respects_constraints_directed is_in_graph cnot l -> 
    respects_constraints_directed is_in_graph cnot pat ->
    respects_constraints_directed is_in_graph cnot rep ->
    replace_pattern l pat rep match_gate = Some l' -> 
    respects_constraints_directed is_in_graph cnot l'.
Proof. 
  intros.
  unfold replace_pattern in H2.
  destruct_matches.
  inversion H2; subst.
  assert (respects_constraints_directed is_in_graph cnot g).
  eapply remove_prefix_respects_constraints. 
  apply H. apply H0. symmetry in HeqH3.  apply HeqH3.
  apply respects_constraints_directed_app; assumption.
Qed.
