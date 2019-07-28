Require Import Reals.
Require Export List.
Export ListNotations.
Require Import Psatz.

Inductive Unitary : nat -> Set := 
  | U_H         : Unitary 1 
  | U_X         : Unitary 1
  | U_Y         : Unitary 1
  | U_Z         : Unitary 1
  | U_R         : R -> Unitary 1 
  | U_CNOT      : Unitary 2.

(* One possible alternative, inspired by Open QASM:

Inductive Unitary : nat -> Set := 
  | U_R         : R -> R -> R -> Unitary 1 
  | U_CNOT      : Unitary 2.

This gate set allows arbitrary single-qubit unitaries (parameterized by 
rotation angles around the x, y, and z axes) and the two-qubit CNOT unitary.
This is the base gate set used by Open QASM. It's attractive because of its
simplicity and generality, but it might introduce some challenges with writing
functions over programs (how can you easily pattern match on a X gate with 
this definition?). Working with the semantics (which involves Cexp and sin/cos)
might also be tricky.

The denotation of U_R is described as follows.

Definition rotation (θ ϕ λ : R) : Matrix 2 2 :=
  fun x y => match x, y with
             | 0, 0 => (Cexp (-(ϕ + λ)/2)) * (cos (θ/2))
             | 0, 1 => - (Cexp (-(ϕ - λ)/2)) * (sin (θ/2))
             | 1, 0 => (Cexp ((ϕ - λ)/2)) * (sin (θ/2))
             | 1, 1 => (Cexp ((ϕ + λ)/2)) * (cos (θ/2))
             | _, _ => C0
             end.

The standard gates can be defined in terms of U_R as follows.

Definition R λ a := uapp (U_R 0 0 λ) [a].
Definition H a := uapp (U_R (PI/2) 0 PI) [a].  
Definition X a := uapp (U_R PI 0 PI) [a].  
Definition Y a := uapp (U_R PI (PI/2) (PI/2)) [a].
Definition Z a := uapp (U_R 0 0 PI) [a]. 

See the Open QASM tech report for more example gates in terms of U_R.

*)

Fixpoint invert_gate {n : nat} (u : Unitary n) : Unitary n := 
  match u with
  | U_H => U_H
  | U_X => U_X
  | U_Y => U_Y
  | U_Z => U_Z
  | U_R ϕ => U_R (-ϕ)
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

(* Gate application definitions and notations *)

(* Set the dimension argument to be implicit. *)
Arguments uskip {dim}.
Arguments useq {dim}.
Arguments uapp1 {dim}.
Arguments uapp2 {dim}.

Delimit Scope ucom_scope with ucom.
Notation "p1 ; p2" := (useq p1 p2) (at level 50) : ucom_scope.

Local Open Scope ucom_scope.

(*
Notation "'H' n" := (uapp1 _ U_H n) (at level 0). 
Notation "'X' n" := (uapp1 _ U_X n) (at level 0). 
Notation "'Y' n" := (uapp1 _ U_Y n) (at level 0). 
Notation "'Z' n" := (uapp1 _ U_Z n) (at level 0). 
Notation "'R_' θ . n" := (uapp1 (U_R θ) n) (at level 0). (* not working *)
Notation "'CNOT' m ',' n" := (uapp2 U_CNOT m n) (at level 0). 
*)

Definition H {dim} n : ucom dim := uapp1 U_H n.  
Definition X {dim} n : ucom dim := uapp1 U_X n.  
Definition Y {dim} n : ucom dim := uapp1 U_Y n.  
Definition Z {dim} n : ucom dim := uapp1 U_Z n.  
Definition CNOT {dim} m n : ucom dim := uapp2 U_CNOT m n.  
Definition T {dim} n : ucom dim := uapp1 (U_R (PI / 4)) n.
Definition P {dim} n : ucom dim := uapp1 (U_R (PI / 2)) n. 
Definition PDAG {dim} n : ucom dim := uapp1 (U_R (- (PI / 2))) n.
Definition Rz {dim} θ n : ucom dim := uapp1 (U_R θ) n.  

Definition CZ {dim} m n : ucom dim :=
  H n ; CNOT m n ; H n.

Definition SWAP {dim} m n : ucom dim :=
  CNOT m n; CNOT n m; CNOT m n.

(* Inverse for unitary circuits. *)
Fixpoint invert_u {dim} (c : ucom dim) : ucom dim :=
  match c with
  | uskip => uskip
  | c1 ; c2 => invert_u c2 ; invert_u c1
  | uapp1 u n => uapp1 (invert_gate u) n
  | uapp2 u m n => uapp2 (invert_gate u) m n
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
Notation "'reset' n" := (meas n (X n) skip) (at level 40) : com_scope.
Notation "n <- 0" := (reset n) (at level 20) : com_scope.
(* Notation "n <- 1" := (reset n ; X n) (at level 20) : com_scope. *)
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
