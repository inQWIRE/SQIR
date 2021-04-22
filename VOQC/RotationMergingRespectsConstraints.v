
Require Import RotationMerging.


Require Import SimpleMapping.
Require Import GateCancellationRespectsConstraints.

Lemma merge_at_beginning_respects_constraints:
  forall {dim} (in_l out_l: RzQ_ucom_l dim) a q (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
    @merge_at_beginning dim in_l a q = Some (out_l) ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l.
Proof.
  intros.
  unfold merge_at_beginning in H0.
  repeat destruct_matches.
  
  symmetry in HeqH1. 
  apply find_merge_preserves_structure in HeqH1. 
  inversion H0; subst.
  apply respects_constraints_directed_app.
  apply combines_rotations_respects_constraints.
  apply respects_constraints_directed_app;
  apply respects_constraints_directed_app_split in H;
  destruct H; 
  apply respects_constraints_directed_app_split in H;
  destruct H; assumption. 

Qed. 

Lemma merge_at_end_respects_constraints:
  forall {dim} (in_l out_l: RzQ_ucom_l dim) a q (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
    @merge_at_end dim in_l a q = Some (out_l) ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l.
Proof.
  intros.
  unfold merge_at_end in H0.
  repeat destruct_matches.
  symmetry in HeqH1. 

  apply find_merge_preserves_structure in HeqH1. 
  inversion H0; subst.
  apply respects_constraints_directed_app;

  apply respects_constraints_directed_app_split in H;
  destruct H; 
  apply respects_constraints_directed_app_split in H;
  destruct H. 
  assumption.
  apply respects_constraints_directed_app.
  apply combines_rotations_respects_constraints.

  assumption.
Qed. 

Lemma merge_rotations_at_beginning_respects_constraints:
  forall {dim}  (in_l out_l acc: RzQ_ucom_l dim) n (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
    respects_constraints_directed is_in_graph URzQ_CNOT acc -> 
    @merge_rotations_at_beginning dim in_l n acc = out_l ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l.
Proof.
  intros.
  generalize dependent acc.
  generalize dependent in_l. 
  induction n; intros.
   
  -  unfold merge_rotations_at_beginning in H1.
     inversion H1; subst.
     apply rev_append_respects_constraints; assumption. 
  - generalize dependent n.
    induction in_l.
    + intros.
      inversion H1; subst.
      unfold merge_rotations_at_beginning.
      apply rev_append_respects_constraints; assumption. 
       
    + intros. 
      destruct a eqn: A;
      dependent destruction r;
      simpl in H1.
      * inversion H; subst.
        apply IHn with (in_l0 := in_l) (acc0 := (App1 URzQ_H n0 :: acc));
          try constructor; try assumption.  

      *
        inversion H; subst. 
        apply IHn with (in_l0 := in_l) (acc0 := (App1 URzQ_X n0 :: acc));
          try constructor; try assumption. 

      * destruct (merge_at_beginning in_l a0 n0) eqn: MaB.
        assert (respects_constraints_directed is_in_graph URzQ_CNOT l).
        apply merge_at_beginning_respects_constraints
          with (in_l0 := in_l) (out_l0 := l) (a1 := a0) (q := n0);
          try constructor; try assumption. 
        inversion H; subst; assumption. 
        apply IHn with (in_l := l) (acc := acc); assumption. 
        
        apply IHn with (in_l := in_l) (acc := (Rzq a0 n0 :: acc)).
        inversion H; subst; assumption. 
        constructor.
        assumption.
        assumption.

      * 
        apply IHn with (in_l := in_l) (acc := (App2 URzQ_CNOT n0 n1 :: acc));
          try constructor; try assumption .
        inversion H; subst; assumption.
        inversion H; subst. 
        assumption.

Qed. 
        
(* So this is literally the same proof with changed titles *)

Lemma merge_rotations_at_end_respects_constraints:
  forall {dim}  (in_l out_l acc: RzQ_ucom_l dim) n (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
    respects_constraints_directed is_in_graph URzQ_CNOT acc -> 
    @merge_rotations_at_end dim in_l n acc = out_l ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l.
Proof.
  intros.
  generalize dependent acc.
  generalize dependent in_l. 
  induction n; intros.
   
  -  unfold merge_rotations_at_end in H1.
     inversion H1; subst.
    apply rev_append_respects_constraints; assumption. 
  - generalize dependent n.
    induction in_l.
    + intros.
      inversion H1; subst.
      unfold merge_rotations_at_end.
      apply rev_append_respects_constraints; assumption. 
      
    + intros. 
      destruct a eqn: A;
      dependent destruction r;
      simpl in H1.
      *
        inversion H; subst.  
        apply IHn with (in_l0 := in_l) (acc0 := (App1 URzQ_H n0 :: acc));
          try constructor; try assumption.
         
      *
        inversion H; subst. 
        apply IHn with (in_l0 := in_l) (acc0 := (App1 URzQ_X n0 :: acc));
          try assumption; try constructor. 
        assumption. 

      * destruct (merge_at_end in_l a0 n0) eqn: MaB.
        assert (respects_constraints_directed is_in_graph URzQ_CNOT l).
        apply merge_at_end_respects_constraints
              with (in_l0 := in_l) (out_l0 := l) (a1 := a0) (q := n0).
        inversion H; subst; assumption. 
        assumption.
        apply IHn with (in_l := l) (acc := acc); try assumption. 


        apply IHn with (in_l := in_l) (acc := (Rzq a0 n0 :: acc));
          try assumption.
        inversion H; subst; assumption.
        constructor.
        assumption.

      * 
        apply IHn with (in_l := in_l) (acc := (App2 URzQ_CNOT n0 n1 :: acc)).
        inversion H; subst; assumption.
        constructor.
        inversion H; subst. 
        assumption.
        assumption.
        assumption.
Qed.

Lemma rev_append_w_map_invert_gate_respects_constraints: 
  forall {dim}  (in_l1 in_l2 out_l: RzQ_ucom_l dim)(is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph URzQ_CNOT in_l1 ->
     respects_constraints_directed is_in_graph URzQ_CNOT in_l2 ->
    RotationMerging.rev_append_w_map  invert_gate in_l1 in_l2 = out_l ->
    respects_constraints_directed  is_in_graph URzQ_CNOT out_l.
Proof.
  intros.
  generalize dependent out_l.
  generalize dependent in_l2. 
  induction in_l1.
  - intros. simpl in H1; subst. assumption. 
  - intros.
    simpl in H1. 
    apply IHin_l1 with (in_l2 := (invert_gate a) :: in_l2).
    inversion H; subst; assumption.
    destruct a.
    dependent destruction r; try constructor; try assumption.
    + dependent destruction r. constructor. inversion H; subst; assumption.
      assumption.
    +inversion H.
     
    + destruct a;
      dependent destruction r; try constructor; try assumption. 
Qed. 
  
     
Lemma invert_respects_constraints:
  forall {dim} in_l out_l (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
    @RotationMerging.invert dim in_l = out_l ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l.
Proof.
  intros.
  induction in_l.
  
  - unfold RotationMerging.invert in H0;
  unfold rev_append_w_map in H0.
  subst; constructor. 

  -
    unfold RotationMerging.invert in H0.
    eapply rev_append_w_map_invert_gate_respects_constraints with (is_in_graph0 := is_in_graph).
    apply H.
    constructor. 
    assumption.  
Qed.     


    
Lemma merge_rotations_respects_constraints:
  forall {dim}  (in_l out_l: RzQ_ucom_l dim) (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph URzQ_CNOT in_l ->
    @merge_rotations dim in_l = out_l ->
    respects_constraints_directed is_in_graph URzQ_CNOT out_l.
Proof.
  intros.
  unfold merge_rotations in H0.
  apply invert_respects_constraints
  with (in_l0 :=  (merge_rotations_at_end
            (RotationMerging.invert (merge_rotations_at_beginning in_l (length in_l) []))
            (length (merge_rotations_at_beginning in_l (length in_l) [])) []));
    try auto. 
  - apply merge_rotations_at_end_respects_constraints
      with (in_l0 :=(RotationMerging.invert (merge_rotations_at_beginning in_l (length in_l) [])))
           (n := (length (merge_rotations_at_beginning in_l (length in_l) [])))
           (acc := []); try constructor; try auto. 
    + apply invert_respects_constraints
        with (in_l0 := (merge_rotations_at_beginning in_l (length in_l) [])); try auto.
      * apply merge_rotations_at_beginning_respects_constraints
              with (in_l0 := in_l) (n := (length in_l)) (acc := []); try constructor; try auto. 
Qed. 
