Require Import UnitarySem.
Require Import Equivalences.
Open Scope ucom.

(********************************)
(** Optimization: remove skips **)
(********************************)

Fixpoint rm_uskips {dim} (c : ucom dim) : ucom dim :=
  match c with
  | c1 ; c2 => match rm_uskips c1, rm_uskips c2 with
              | uskip, c2' => c2'
              | c1', uskip => c1'
              | c1', c2'   => c1'; c2'
              end
  | c'      => c'
  end.

(* The output of rm_uskips is well-typed.
   (Note that well-typedness is not necessary in the soundness proof.) *)
Hint Constructors uc_well_typed : type_db.
Lemma WT_rm_uskips : forall {dim} (c : ucom dim), uc_well_typed c <-> uc_well_typed (rm_uskips c).
Proof.
  intros dim c.
  split; intros H.
  - induction H.
    + constructor.
    + simpl.
      destruct (rm_uskips c1), (rm_uskips c2); auto with type_db.
    + simpl. auto with type_db.
    + simpl. auto with type_db.
  - induction c.
    + constructor.
    + destruct (rm_uskips (c1; c2)) eqn:E.
      * simpl in E.
        destruct (rm_uskips c1), (rm_uskips c2); auto with type_db; discriminate.
      * simpl in E.
        destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; auto with type_db;
        rewrite <- E in H; inversion H; auto with type_db.
      * simpl in E.
        destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; auto with type_db;
        rewrite <- E in H; inversion H; auto with type_db.
      * simpl in E.
        destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; auto with type_db;
        rewrite <- E in H; inversion H; auto with type_db.
    + simpl in H; easy.
    + simpl in H; easy.
Qed.      

(* rm_uskips is semantics-preserving. *)
Lemma rm_uskips_sound : forall {dim} (c : ucom dim),
  c ≡ (rm_uskips c).
Proof.
  induction c; try reflexivity.
  unfold uc_equiv; simpl.
  destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; trivial;
    rewrite IHc1, IHc2; simpl; Msimpl; easy.
Qed.

(* Alternate proof using congruence instead of Msimpl. *)
Lemma rm_uskips_sound' : forall {dim} (c : ucom dim),
  c ≡ (rm_uskips c).
Proof.
  induction c; try reflexivity.
  simpl.
  destruct (rm_uskips c1); destruct (rm_uskips c2);
    rewrite IHc1, IHc2;
    try apply uskip_id_l; try apply uskip_id_r;
    reflexivity.
Qed.

(* The output of rm_uskips is either a single skip intruction, or a program
   that contains no skip instructions. *)
Inductive skip_free {dim} : ucom dim -> Prop :=
  | SF_seq : forall c1 c2, skip_free c1 -> skip_free c2 -> skip_free (c1; c2)
  | SF_app1 : forall n (u : Unitary 1), skip_free (uapp1 u n)
  | SF_app2 : forall m n (u : Unitary 2), skip_free (uapp2 u m n).

Lemma rm_uskips_correct : forall {dim} (c : ucom dim),
  (rm_uskips c) = uskip \/ skip_free (rm_uskips c).
Proof.
  induction c.
  - left; easy.
  - destruct IHc1; destruct IHc2.
    + left. simpl. rewrite H. rewrite H0. reflexivity.
    + right. simpl. rewrite H. assumption.
    + right. simpl. rewrite H0. 
      destruct (rm_uskips c1); try easy.
    + right. simpl. 
      destruct (rm_uskips c1); try assumption;
      destruct (rm_uskips c2); try (apply SF_seq); easy. 
  - right; simpl. apply SF_app1.
  - right; simpl. apply SF_app2.
Qed.

(* The output of rm_uskips has no more operations than the input program. *)
Local Close Scope C_scope.
Local Close Scope R_scope.

Fixpoint count_ops {dim} (c : ucom dim) : nat :=
  match c with
  | c1; c2 => (count_ops c1) + (count_ops c2)
  | _ => 1
  end.

Lemma rm_uskips_reduces_count : forall {dim} (c : ucom dim),
  count_ops (rm_uskips c) <= count_ops c.
Proof.
  induction c; try (simpl; lia).
  simpl. destruct (rm_uskips c1); try lia; 
  destruct (rm_uskips c2); 
  simpl in *;
  lia.
Qed.
