Require Import UnitarySem.
Require Import Equivalences.
Require Import Coq.Reals.ROrderedType.
Open Scope ucom.

(***********************************)
(** Optimization: remove ID gates **)
(***********************************)

Definition is_id (u : base_Unitary 1) := 
  match u with
  | U_R θ ϕ λ => Reqb θ 0 && Reqb ϕ 0 && Reqb λ 0
  end.

Fixpoint rm_ids {dim} (c : base_ucom dim) : base_ucom dim :=
  match c with
  | c1 ; c2 => match rm_ids c1, rm_ids c2 with
              | uapp1 u n, uapp1 u' n' => 
                  if is_id u then uapp1 u' n' 
                  else if is_id u' then uapp1 u n 
                       else uapp1 u n ; uapp1 u' n'
              | uapp1 u n, c2' => if is_id u then c2' else uapp1 u n ; c2'
              | c1', uapp1 u n => if is_id u then c1' else c1' ; uapp1 u n 
              | c1', c2'   => c1'; c2'
              end
  | c'      => c'
  end.

Lemma WT_rm_ids : forall {dim} (c : base_ucom dim), 
  uc_well_typed c -> uc_well_typed (rm_ids c).
Proof.
  intros dim c H.
  induction H.
  - simpl.
    destruct (rm_ids c1), (rm_ids c2); 
    try destruct (is_id b); 
    try destruct (is_id b0);
    try assumption; 
    try constructor; 
    assumption.
  - simpl. constructor; assumption.
  - simpl. constructor; assumption.
  - inversion u.
Qed.      

(* rm_uskips is semantics-preserving. *)
Lemma rm_ids_sound : forall {dim} (c : base_ucom dim),
  uc_well_typed c -> rm_ids c ≡ c.
Proof.
  intros dim c H.
  induction c; try reflexivity.
  simpl.
  inversion H; subst.
  specialize (IHc1 H2).
  specialize (IHc2 H3).
  apply WT_rm_ids in H2.
  apply WT_rm_ids in H3.
  assert (id_l : forall dim u n (c : base_ucom dim), (n < dim)%nat -> is_id u = true -> uapp1 u n ; c ≡ c).
  { clear.
    intros dim u n c Hn H.
    dependent destruction u.
    unfold is_id in H.
    repeat match goal with 
    | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
    | H : Reqb _ _ = true |- _ => apply Reqb_eq in H; subst
    end.
    unfold uc_equiv; simpl.
    rewrite I_rotation.
    autorewrite with eval_db.
    bdestructΩ (n + 1 <=? dim).
    repeat rewrite id_kron.
    Msimpl_light; reflexivity.
  }
  assert (id_r : forall dim u n (c : base_ucom dim), (n < dim)%nat -> is_id u = true -> c ; uapp1 u n ≡ c).
  { clear.
    intros dim u n c Hn H.
    dependent destruction u.
    unfold is_id in H.
    repeat match goal with 
    | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
    | H : Reqb _ _ = true |- _ => apply Reqb_eq in H; subst
    end.
    unfold uc_equiv; simpl.
    rewrite I_rotation.
    autorewrite with eval_db.
    bdestructΩ (n + 1 <=? dim).
    repeat rewrite id_kron.
    Msimpl_light; reflexivity.
  }
  destruct (rm_ids c1); destruct (rm_ids c2);
  try (rewrite <- IHc1, <- IHc2; reflexivity).
  5: inversion b0. (* uapp3 is invalid in base_ucom *)  
  6: inversion b.
  all: match goal with
       | |- context [is_id ?b] => destruct (is_id b) eqn:E; 
                                rewrite <- IHc1, <- IHc2; 
                                try reflexivity
       end.
  all: try (inversion H3; subst;
            rewrite (id_r _ _ _ _ H1 E);
            reflexivity).
  all: try (inversion H2; subst;
            rewrite (id_l _ _ _ _ H1 E);
            reflexivity).
  inversion H2; inversion H3; subst. 
  destruct (is_id b0) eqn:E'.
  rewrite (id_r _ _ _ _ H6 E'); reflexivity.
  reflexivity.
Qed.

(* The output of rm_ids is either a single skip intruction, or a program
   that contains no id operations. *)
Inductive id_free {dim} : base_ucom dim -> Prop :=
  | IDF_seq : forall c1 c2, id_free c1 -> id_free c2 -> id_free (c1; c2)
  | IDF_app_R : forall n θ ϕ λ, not (θ = 0 /\ ϕ = 0 /\ λ = 0) -> id_free (uapp1 (U_R θ ϕ λ) n)
  | IDF_app_CNOT : forall m n, id_free (uapp2 U_CNOT m n).

Lemma rm_ids_correct : forall {dim} (c : base_ucom dim),
  (exists n, (rm_ids c) = uapp1 (U_R 0 0 0) n) \/ id_free (rm_ids c).
Proof.
  assert (H_id: is_id (U_R 0 0 0) = true).
  { unfold is_id. assert (Reqb 0 0 = true) by (apply Reqb_eq; reflexivity). 
    rewrite H; reflexivity. }
  induction c.
  - destruct IHc1; destruct IHc2.
    + destruct H; destruct H0. 
      left. exists x0. simpl. rewrite H, H0. 
      rewrite H_id; simpl.
      reflexivity.
    + destruct H. right. simpl. rewrite H. 
      destruct (rm_ids c2); rewrite H_id; simpl;
      assumption.
    + destruct H0. right. simpl; rewrite H0. 
      destruct (rm_ids c1); try inversion b; 
      try (rewrite H_id; assumption).
      inversion H; subst.
      destruct (is_id (U_R θ ϕ λ)) eqn:E.
      * contradict E. apply not_true_iff_false.
        unfold is_id.
        repeat match goal with 
        | H: not (_ /\ _) |- _ => apply Classical_Prop.not_and_or in H as [? | ?]
        | H: _ <> 0 |- _ => rewrite <- Reqb_eq in H; apply not_true_iff_false in H
        end. 
        apply andb_false_intro1; apply andb_false_intro1; assumption.
        apply andb_false_intro1; apply andb_false_intro2; assumption.
        apply andb_false_intro2; assumption.
      * rewrite H_id; assumption.
    + right. simpl. 
      destruct (rm_ids c1); destruct (rm_ids c2); 
      try apply IDF_seq; try assumption. 
      all: try destruct (is_id b); try destruct (is_id b0); try assumption.
      all: try apply IDF_seq; assumption.       
  - destruct (is_id u) eqn:E. 
    + left. exists n. dependent destruction u. unfold is_id in E. 
      repeat match goal with 
      | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
      | H : Reqb _ _ = true |- _ => apply Reqb_eq in H; subst
      end.
      reflexivity.
    + right. dependent destruction u. unfold is_id in E.
      constructor.
      repeat match goal with 
      | H : _ && _ = false |- _ => apply andb_false_elim in H as [? | ?]
      | H : Reqb _ _ = false |- _ => apply not_true_iff_false in H; rewrite Reqb_eq in H
      end.
      * apply Classical_Prop.or_not_and. 
        left; assumption.
      * apply Classical_Prop.or_not_and. 
        right. apply Classical_Prop.or_not_and.
        left; assumption.
      * apply Classical_Prop.or_not_and.
        right. apply Classical_Prop.or_not_and.
        right; assumption.
  - right; simpl. dependent destruction u. apply IDF_app_CNOT.
  - inversion u.
Qed.

(* The output of rm_uskips has no more operations than the input program. *)
Local Close Scope C_scope.
Local Close Scope R_scope.

Fixpoint count_ops {dim} (c : base_ucom dim) : nat :=
  match c with
  | c1; c2 => (count_ops c1) + (count_ops c2)
  | _ => 1
  end.

Lemma rm_uskips_reduces_count : forall {dim} (c : base_ucom dim),
  count_ops (rm_ids c) <= count_ops c.
Proof.
  induction c; try (simpl; lia).
  simpl. 
  destruct (rm_ids c1); destruct (rm_ids c2);
  try destruct (is_id b); try destruct (is_id b0);
  simpl in *; lia.
Qed.
