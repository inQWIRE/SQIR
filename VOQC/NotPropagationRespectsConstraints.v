
Require Import NotPropagation.
Require Import SimpleMapping.

Lemma finalize_respects_constraints: forall {dim} qs (is_in_graph : nat -> nat -> bool),
   
    respects_constraints_directed is_in_graph (@finalize dim qs).
Proof.
  intros.
  unfold finalize.
  apply FSetProps.fold_rec.
  -intros.
   constructor.
  -  intros.
     constructor; assumption.
Qed.


Lemma not_propagation'_respects_constraints : forall {dim} (l acc : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool) qs,
respects_constraints_directed is_in_graph l -> 
    respects_constraints_directed is_in_graph acc ->
respects_constraints_directed is_in_graph (not_propagation' l acc qs).
Proof.
  intros dim l acc is_in_graph qs H H1.
  generalize dependent acc. generalize dependent qs.
  induction l.
  intros qs acc H1.
  simpl.
  rewrite rev_append_rev.
  apply respects_constraints_directed_app.
  -
    apply rev_respects_constraints. assumption.
  -
    apply finalize_respects_constraints.
  - intros qs acc H1.
    simpl.
    destruct a. dependent destruction r; destruct (NotPropagation.FSet.mem n qs) eqn:H2; apply IHl; inversion H; subst; try (apply H4); try repeat (constructor); try assumption.
      
    + dependent destruction r.
      apply IHl.
      inversion H; subst.
      apply H7.
      constructor.
      inversion H; subst.
      apply H4.
      apply H1.
   + assumption.
Qed.

Lemma not_propagation_respects_constraints_directed :
  forall {dim} (l : RzQ_ucom_l dim) (is_in_graph : nat -> nat -> bool),
    respects_constraints_directed is_in_graph l ->
    respects_constraints_directed is_in_graph (not_propagation l).
Proof.
  intros dim l is_in_graph  H.

  unfold not_propagation.
  apply not_propagation'_respects_constraints; (try assumption); (try constructor).
  Qed. 
