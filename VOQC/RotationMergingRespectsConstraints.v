
Require Import RotationMerging.


Require Import SimpleMapping.
Require Import GateCancellationRespectsConstraints.

Lemma merge_at_beginning_respects_constraints:
  forall {dim} (in_l out_l: RzQ_ucom_l dim) a q (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph in_l ->
    @merge_at_beginning dim in_l a q = Some (out_l) ->
    respects_constraints_directed is_in_graph out_l.
Proof.
  intros.
  unfold merge_at_beginning in H0.
  destruct (find_merge in_l q) eqn: found.
  destruct p.
  destruct p.
  destruct p.
  apply find_merge_preserves_structure in found. 
  inversion H0; subst.
  apply respects_constraints_directed_app.
  apply combines_rotations_respects_constraints.
  apply respects_constraints_directed_app;
  apply respects_constraints_directed_app_split in H;
  destruct H; 
  apply respects_constraints_directed_app_split in H;
  destruct H. 
  assumption.
  assumption.
  inversion H0.
Qed. 

Lemma merge_at_end_respects_constraints:
  forall {dim} (in_l out_l: RzQ_ucom_l dim) a q (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph in_l ->
    @merge_at_end dim in_l a q = Some (out_l) ->
    respects_constraints_directed is_in_graph out_l.
Proof.
  intros.
  unfold merge_at_end in H0.
  destruct (find_merge in_l q) eqn: found.
  destruct p.
  destruct p.
  destruct p.
  apply find_merge_preserves_structure in found. 
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
  inversion H0.
Qed. 

Lemma merge_rotations_at_beginning_respects_constraints:
  forall {dim}  (in_l out_l acc: RzQ_ucom_l dim) n (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph in_l ->
    respects_constraints_directed is_in_graph acc -> 
    @merge_rotations_at_beginning dim in_l n acc = out_l ->
    respects_constraints_directed is_in_graph out_l.
Proof.
  intros.
  generalize dependent acc.
  generalize dependent in_l. 
  induction n; intros.
   
  -  unfold merge_rotations_at_beginning in H1.
     inversion H1; subst.
    rewrite rev_append_rev. 
    apply respects_constraints_directed_app.
    apply rev_respects_constraints. 
    assumption.
    assumption. 
  - generalize dependent n.
    induction in_l.
    + intros.
      inversion H1; subst.
      unfold merge_rotations_at_beginning.
      rewrite rev_append_rev. 
      apply respects_constraints_directed_app.
      apply rev_respects_constraints. 
      assumption.
      constructor.
      
    + intros. 
      destruct a eqn: A;
      dependent destruction r;
      simpl in H1.
      * apply IHn with (in_l := in_l) (acc := (App1 URzQ_H n0 :: acc)). 
        inversion H; subst.  
        assumption. 
        constructor.
        assumption.
        assumption. 
      *  
         apply IHn with (in_l := in_l) (acc := (App1 URzQ_X n0 :: acc)). 
        inversion H; subst. 
        assumption. 
        constructor.
        assumption.
        assumption.
      * destruct (merge_at_beginning in_l a0 n0) eqn: MaB.
        assert (respects_constraints_directed is_in_graph l).
        apply merge_at_beginning_respects_constraints
              with (in_l0 := in_l) (out_l0 := l) (a1 := a0) (q := n0).
        inversion H; subst; assumption. 
        assumption.
        apply IHn with (in_l := l) (acc := acc).
        assumption.
        assumption.
        assumption.

        apply IHn with (in_l := in_l) (acc := (Rz a0 n0 :: acc)).
        inversion H; subst; assumption.
        constructor.
        assumption.
        assumption.

      * 
        apply IHn with (in_l := in_l) (acc := (App2 URzQ_CNOT n0 n1 :: acc)).
        inversion H; subst; assumption.
        constructor.
        inversion H; subst. 
        assumption.
        assumption.
        assumption .
Qed. 
        
(* So this is literally the same proof with changed titles *)
Lemma merge_rotations_at_end_respects_constraints:
  forall {dim}  (in_l out_l acc: RzQ_ucom_l dim) n (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph in_l ->
    respects_constraints_directed is_in_graph acc -> 
    @merge_rotations_at_end dim in_l n acc = out_l ->
    respects_constraints_directed is_in_graph out_l.
Proof.
  intros.
  generalize dependent acc.
  generalize dependent in_l. 
  induction n; intros.
   
  -  unfold merge_rotations_at_end in H1.
     inversion H1; subst.
    rewrite rev_append_rev. 
    apply respects_constraints_directed_app.
    apply rev_respects_constraints. 
    assumption.
    assumption. 
  - generalize dependent n.
    induction in_l.
    + intros.
      inversion H1; subst.
      unfold merge_rotations_at_end.
      rewrite rev_append_rev. 
      apply respects_constraints_directed_app.
      apply rev_respects_constraints. 
      assumption.
      constructor.
      
    + intros. 
      destruct a eqn: A;
      dependent destruction r;
      simpl in H1.
      * apply IHn with (in_l := in_l) (acc := (App1 URzQ_H n0 :: acc)). 
        inversion H; subst.  
        assumption. 
        constructor.
        assumption.
        assumption. 
      *  
         apply IHn with (in_l := in_l) (acc := (App1 URzQ_X n0 :: acc)). 
        inversion H; subst. 
        assumption. 
        constructor.
        assumption.
        assumption.
      * destruct (merge_at_end in_l a0 n0) eqn: MaB.
        assert (respects_constraints_directed is_in_graph l).
        apply merge_at_end_respects_constraints
              with (in_l0 := in_l) (out_l0 := l) (a1 := a0) (q := n0).
        inversion H; subst; assumption. 
        assumption.
        apply IHn with (in_l := l) (acc := acc).
        assumption.
        assumption.
        assumption.

        apply IHn with (in_l := in_l) (acc := (Rz a0 n0 :: acc)).
        inversion H; subst; assumption.
        constructor.
        assumption.
        assumption.

      * 
        apply IHn with (in_l := in_l) (acc := (App2 URzQ_CNOT n0 n1 :: acc)).
        inversion H; subst; assumption.
        constructor.
        inversion H; subst. 
        assumption.
        assumption.
        assumption .
Qed.
Locate rev_append_w_map.

Lemma rev_append_w_map_invert_gate_respects_constraints: 
  forall {dim}  (in_l1 in_l2 out_l: RzQ_ucom_l dim)(is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph in_l1 ->
     respects_constraints_directed is_in_graph in_l2 ->
    RotationMerging.rev_append_w_map  invert_gate in_l1 in_l2 = out_l ->
    respects_constraints_directed  is_in_graph out_l.
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
    + constructor. inversion H; subst; assumption.
      assumption.
    +inversion H.
     
    + destruct a;
      dependent destruction r; try constructor; try assumption. 
Qed. 
  
     
Lemma invert_respects_constraints:
  forall {dim} in_l out_l (is_in_graph : nat-> nat-> bool),
    respects_constraints_directed is_in_graph in_l ->
    @RotationMerging.invert dim in_l = out_l ->
    respects_constraints_directed is_in_graph out_l.
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
    respects_constraints_directed is_in_graph in_l ->
    @merge_rotations dim in_l = out_l ->
    respects_constraints_directed is_in_graph out_l.
Proof.
  intros.
  unfold merge_rotations in H0.
  apply invert_respects_constraints
  with (in_l0 :=  (merge_rotations_at_end
            (RotationMerging.invert (merge_rotations_at_beginning in_l (length in_l) []))
            (length (merge_rotations_at_beginning in_l (length in_l) [])) [])).
  - apply merge_rotations_at_end_respects_constraints
      with (in_l0 :=(RotationMerging.invert (merge_rotations_at_beginning in_l (length in_l) [])))
           (n := (length (merge_rotations_at_beginning in_l (length in_l) [])))
           (acc := []).
    + apply invert_respects_constraints
        with (in_l0 := (merge_rotations_at_beginning in_l (length in_l) [])).
      * apply merge_rotations_at_beginning_respects_constraints
              with (in_l0 := in_l) (n := (length in_l)) (acc := []).
        assumption.
        constructor.
        reflexivity.
      *reflexivity.
    + constructor.
    + reflexivity.
  - assumption.
Qed. 
