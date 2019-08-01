Require Import Reals.
Require Export List.
Export ListNotations.
Require Import Psatz.

(* This gate set allows arbitrary single-qubit unitaries (parameterized by 
   rotation angles around the x, y, and z axes) and the two-qubit CNOT unitary.
   It is the base gate set used by Open QASM. *)
Inductive Unitary : nat -> Set := 
  | U_R         : R -> R -> R -> Unitary 1 
  | U_CNOT      : Unitary 2.

Definition invert_u {n : nat} (u : Unitary n) : Unitary n := 
  match u with
  | U_R θ ϕ λ => U_R (- θ) (- λ) (- ϕ)
  | U_CNOT => U_CNOT
  end.

(**********************)
(** Unitary Programs **)
(**********************)

(* Note: we're using tuple arguments here to simplify proofs.
   It can be a little tedious to handle cases of unitaries being applied
   to the incorrect number of arguments. *)
Inductive ucom (dim : nat): Set :=
| uskip : ucom dim
| useq :  ucom dim -> ucom dim -> ucom dim
| uapp1 : Unitary 1 -> nat -> ucom dim
| uapp2 : Unitary 2 -> nat -> nat -> ucom dim.

(* Set the dimension argument to be implicit. *)
Arguments uskip {dim}.
Arguments useq {dim}.
Arguments uapp1 {dim}.
Arguments uapp2 {dim}.

Delimit Scope ucom_scope with ucom.
Notation "p1 ; p2" := (useq p1 p2) (at level 50) : ucom_scope.

Local Open Scope ucom_scope.

(* Inverse for unitary circuits. *)
Fixpoint invert_ucom {dim} (c : ucom dim) : ucom dim :=
  match c with
  | uskip => uskip
  | c1 ; c2 => invert_ucom c2 ; invert_ucom c1
  | uapp1 u n => uapp1 (invert_u u) n
  | uapp2 u m n => uapp2 (invert_u u) m n
  end.

(*************************)
(** Well Typed Circuits **)
(*************************)

Inductive uc_well_typed {dim} : ucom dim -> Prop :=
| WT_uskip : uc_well_typed uskip
| WT_seq : forall c1 c2, uc_well_typed c1 -> uc_well_typed c2 -> uc_well_typed (c1; c2)
| WT_app1 : forall u n, n < dim -> uc_well_typed (uapp1 u n)
| WT_app2 : forall u m n, m < dim -> n < dim -> m <> n -> uc_well_typed (uapp2 u m n).

(* Equivalent boolean version *)
Fixpoint uc_well_typed_b {dim} (c : ucom dim) : bool :=
  match c with
  | uskip => true
  | c1 ; c2 => uc_well_typed_b c1 && uc_well_typed_b c2 
  | uapp1 u n => n <? dim
  | uapp2 u m n => (m <? dim) && (n <? dim) && (negb (m =? n))
  end.

Lemma uc_well_typed_b_equiv : forall {dim} (c : ucom dim), 
  uc_well_typed_b c = true <-> uc_well_typed c.
Proof.
  intros. split.
  - intros.
    induction c.
    + constructor.
    + simpl in H; apply Bool.andb_true_iff in H as [H1 H2]. 
      constructor. 
      apply IHc1; assumption.
      apply IHc2; assumption.
    + simpl in H. apply Nat.ltb_lt in H.
      constructor; assumption.
    + simpl in H. apply Bool.andb_true_iff in H as [H H3]. 
      apply Bool.andb_true_iff in H as [H1 H2].
      apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
      apply Bool.negb_true_iff in H3. apply Nat.eqb_neq in H3.
      constructor; assumption.
  - intros.
    induction H; subst; simpl.
    + reflexivity.
    + apply Bool.andb_true_iff. split; assumption.
    + apply Nat.ltb_lt; assumption.
    + apply Bool.andb_true_iff.
      split.
      * apply Bool.andb_true_iff. split; apply Nat.ltb_lt; assumption. 
      * apply Bool.negb_true_iff. apply Nat.eqb_neq; assumption.
Qed.

Local Close Scope ucom.

(**********************)
(** General Programs **)
(**********************)

Delimit Scope com_scope with com.
Local Open Scope com_scope.

Inductive com (dim : nat) : Set :=
| skip : com dim
| seq : com dim -> com dim -> com dim
| app1 : Unitary 1 -> nat -> com dim
| app2 : Unitary 2 -> nat -> nat -> com dim
| meas : nat -> com dim -> com dim -> com dim.

Arguments skip {dim}.
Arguments seq {dim}.
Arguments app1 {dim}.
Arguments app2 {dim}.
Arguments meas {dim}.

Fixpoint from_ucom {dim} (c : ucom dim) : com dim :=
  match c with
  | uskip => skip
  | useq c1 c2 => seq (from_ucom c1) (from_ucom c2)
  | uapp1 u a => app1 u a
  | uapp2 u a b => app2 u a b
  end.

Coercion from_ucom : ucom >-> com.

Notation "p1 ; p2" := (seq p1 p2) (at level 50) : com_scope.
Notation "'mif' n 'then' p1 'else' p2" := (meas n p1 p2) (at level 40) : com_scope.
Notation "'measure' n" := (meas n skip skip) (at level 40) : com_scope.

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
