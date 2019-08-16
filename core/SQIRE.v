Require Import Reals.
Require Export List.
Export ListNotations.
Require Import Psatz.

(**********************)
(** Unitary Programs **)
(**********************)

(* Note: we only support application of one-qubit rotations and CNOTs.
   We could instead allow something more general (e.g. application of
   an arbitrary unitary to a list of arguments), but this would make
   proofs longer for little added benefit. New operations can be defined
   as combinations of the following base set. *)
Inductive ucom (dim : nat): Set :=
| uskip : ucom dim
| useq :  ucom dim -> ucom dim -> ucom dim
(* application of a single-qubit rotation *)
| uapp_R : R -> R -> R -> nat -> ucom dim
(* application of a controlled-not *)
| uapp_CNOT : nat -> nat -> ucom dim.

(* Set the dimension argument to be implicit. *)
Arguments uskip {dim}.
Arguments useq {dim}.
Arguments uapp_R {dim}.
Arguments uapp_CNOT {dim}.

Delimit Scope ucom_scope with ucom.
Notation "p1 ; p2" := (useq p1 p2) (at level 50) : ucom_scope.

Local Open Scope ucom_scope.

(* Inverse for unitary circuits. *)
Fixpoint invert_ucom {dim} (c : ucom dim) : ucom dim :=
  match c with
  | uskip => uskip
  | c1 ; c2 => invert_ucom c2 ; invert_ucom c1
  | uapp_R θ ϕ λ n => uapp_R (- θ) (- λ) (- ϕ) n
  | uapp_CNOT m n => uapp_CNOT m n
  end.

(* Some shorthand definitions. See UnitarySem.v for their semantics. *)
Definition H {dim} n : ucom dim := uapp_R (PI/2) 0 PI n.  
Definition X {dim} n : ucom dim := uapp_R PI 0 PI n.  
Definition Y {dim} n : ucom dim := uapp_R PI (PI/2) (PI/2) n.  
Definition Z {dim} n : ucom dim := uapp_R 0 0 PI n.  
Definition Rz {dim} λ n : ucom dim := uapp_R 0 0 λ n.
Definition T {dim} n : ucom dim := Rz (PI / 4) n.
Definition TDAG {dim} n : ucom dim := Rz (- (PI / 4)) n.
Definition P {dim} n : ucom dim := Rz (PI / 2) n. 
Definition PDAG {dim} n : ucom dim := Rz (- (PI / 2)) n.
Definition CNOT {dim} m n : ucom dim := uapp_CNOT m n.  
Definition CZ {dim} m n : ucom dim :=
  H n ; CNOT m n ; H n.
Definition SWAP {dim} m n : ucom dim :=
  CNOT m n; CNOT n m; CNOT m n.

(*************************)
(** Well Typed Circuits **)
(*************************)

Inductive uc_well_typed {dim} : ucom dim -> Prop :=
| WT_uskip : uc_well_typed uskip
| WT_seq : forall c1 c2, uc_well_typed c1 -> uc_well_typed c2 -> uc_well_typed (c1; c2)
| WT_app_R : forall θ ϕ λ n, n < dim -> uc_well_typed (uapp_R θ ϕ λ n)
| WT_app_CNOT : forall m n, m < dim -> n < dim -> m <> n -> uc_well_typed (uapp_CNOT m n).

(* Equivalent boolean version *)
Fixpoint uc_well_typed_b {dim} (c : ucom dim) : bool :=
  match c with
  | uskip => true
  | c1 ; c2 => uc_well_typed_b c1 && uc_well_typed_b c2 
  | uapp_R _ _ _ n => n <? dim
  | uapp_CNOT m n => (m <? dim) && (n <? dim) && (negb (m =? n))
  end.

Lemma uc_well_typed_b_equiv : forall {dim} (c : ucom dim), 
  uc_well_typed_b c = true <-> uc_well_typed c.
Proof.
  intros. split.
  - intros.
    induction c.
    + constructor.
    + simpl in H0; apply Bool.andb_true_iff in H0 as [H1 H2]. 
      constructor. 
      apply IHc1; assumption.
      apply IHc2; assumption.
    + simpl in H0. apply Nat.ltb_lt in H0.
      constructor; assumption.
    + simpl in H0. apply Bool.andb_true_iff in H0 as [H H3]. 
      apply Bool.andb_true_iff in H as [H1 H2].
      apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
      apply Bool.negb_true_iff in H3. apply Nat.eqb_neq in H3.
      constructor; assumption.
  - intros.
    induction H0; subst; simpl.
    + reflexivity.
    + apply Bool.andb_true_iff. split; assumption.
    + apply Nat.ltb_lt; assumption.
    + apply Bool.andb_true_iff.
      split.
      * apply Bool.andb_true_iff. split; apply Nat.ltb_lt; assumption. 
      * apply Bool.negb_true_iff. apply Nat.eqb_neq; assumption.
Qed.

Local Close Scope ucom.

Lemma uc_well_typed_H : forall dim n, n < dim <-> @uc_well_typed dim (H n).
Proof. 
  intros. split; intros.
  constructor; assumption. 
  inversion H0; subst; assumption. 
Qed.

Lemma uc_well_typed_X : forall dim n, n < dim <-> @uc_well_typed dim (X n).
Proof. 
  intros. split; intros.
  constructor; assumption. 
  inversion H0; subst; assumption. 
Qed.

Lemma uc_well_typed_Y : forall dim n, n < dim <-> @uc_well_typed dim (Y n).
Proof. 
  intros. split; intros.
  constructor; assumption. 
  inversion H0; subst; assumption. 
Qed.

Lemma uc_well_typed_Z : forall dim n, n < dim <-> @uc_well_typed dim (Z n).
Proof. 
  intros. split; intros.
  constructor; assumption. 
  inversion H0; subst; assumption. 
Qed.

Lemma uc_well_typed_Rz : forall dim λ n, n < dim <-> @uc_well_typed dim (Rz λ n).
Proof. 
  intros. split; intros.
  constructor; assumption. 
  inversion H0; subst; assumption. 
Qed.

Lemma uc_well_typed_CNOT : forall dim m n, 
  (m < dim /\ n < dim /\ m <> n) <-> @uc_well_typed dim (CNOT m n).
Proof. 
  intros. split; intros.
  destruct H0 as [H1 [H2 H3]]. constructor; assumption. 
  split; try split; inversion H0; subst; assumption. 
Qed.

Global Opaque H X Y Z Rz CNOT.

(**********************)
(** General Programs **)
(**********************)

Delimit Scope com_scope with com.
Local Open Scope com_scope.

Inductive com (dim : nat) : Set :=
| skip : com dim
| seq : com dim -> com dim -> com dim
| app_R : R -> R -> R -> nat -> com dim
| app_CNOT : nat -> nat -> com dim
| meas : nat -> com dim -> com dim -> com dim.

Arguments skip {dim}.
Arguments seq {dim}.
Arguments app_R {dim}.
Arguments app_CNOT {dim}.
Arguments meas {dim}.

Fixpoint from_ucom {dim} (c : ucom dim) : com dim :=
  match c with
  | uskip => skip
  | useq c1 c2 => seq (from_ucom c1) (from_ucom c2)
  | uapp_R θ ϕ λ a => app_R θ ϕ λ a
  | uapp_CNOT a b => app_CNOT a b
  end.

Coercion from_ucom : ucom >-> com.

Notation "p1 ; p2" := (seq p1 p2) (at level 50) : com_scope.
Notation "'mif' n 'then' p1 'else' p2" := (meas n p1 p2) (at level 40) : com_scope.
Notation "'measure' n" := (meas n skip skip) (at level 40) : com_scope.
Notation "'reset' n" := (meas n (X n) skip) (at level 40) : com_scope.
Notation "n <- 0" := (reset n) (at level 20) : com_scope.
Notation "n <- 1" := (meas n skip (X n)) (at level 20) : com_scope.

(*****************************)
(** Higher-level Constructs **)
(*****************************)

Fixpoint crepeat {dim} (k : nat) (p : com dim) : com dim :=
  match k with
  | 0    => skip
  | S k' => p ; crepeat k' p
  end.

Fixpoint while {dim} (max_iters : nat) (n : nat) (p : com dim) : com dim :=
  match max_iters with
  | 0        => skip
  | S iters' => mif n then p ; while iters' n p else skip
  end.
