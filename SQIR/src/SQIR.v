Require Import Reals.
Require Import Psatz.

(**********************)
(** Unitary Programs **)
(**********************)

(* Note: We only support application of 1-, 2-, and 3-qubit unitaries.
   We could instead allow something more general (e.g. application of
   an arbitrary unitary to a list of arguments), but this would make
   proofs longer for little added benefit. *)
Inductive ucom (U: nat -> Set) (dim : nat) : Set :=
| useq :  ucom U dim -> ucom U dim -> ucom U dim
| uapp1 : U 1 -> nat -> ucom U dim
| uapp2 : U 2 -> nat -> nat -> ucom U dim
| uapp3 : U 3 -> nat -> nat -> nat -> ucom U dim.

(* Set the dimension argument to be implicit. *)
Arguments useq {U dim}.
Arguments uapp1 {U dim}.
Arguments uapp2 {U dim}.
Arguments uapp3 {U dim}.

Declare Scope ucom_scope.
Delimit Scope ucom_scope with ucom.
Local Open Scope ucom.
Notation "p1 ; p2" := (useq p1 p2) (at level 50) : ucom_scope.

(** Example Gate Set **) 

(* The gate set below is used for computing the semantics of programs. The
   R rotation unitary allows for easy description of any single-qubit gate 
   and CNOT is the standard two-qubit gate. *)
Inductive base_Unitary : nat -> Set := 
  | U_R                  : R -> R -> R -> base_Unitary 1 
  | U_CNOT               : base_Unitary 2.

Definition base_ucom := ucom base_Unitary.

(* Some useful shorthands. *)
Definition U_H := U_R (PI/2) 0 PI.
Definition U_X := U_R PI 0 PI.
Definition U_Y := U_R PI (PI/2) (PI/2).
Definition U_Z := U_R 0 0 PI.
Definition H {dim} n : base_ucom dim := uapp1 U_H n.  
Definition X {dim} n : base_ucom dim := uapp1 U_X n.  
Definition Y {dim} n : base_ucom dim := uapp1 U_Y  n.  
Definition Z {dim} n : base_ucom dim := uapp1 U_Z n. 
Definition ID {dim} n : base_ucom dim := uapp1 (U_R 0 0 0) n. 
Definition SKIP {dim} : base_ucom dim := ID 0.
Definition Rz {dim} λ n : base_ucom dim := uapp1 (U_R 0 0 λ) n.
Definition T {dim} n : base_ucom dim := Rz (PI / 4) n.
Definition TDAG {dim} n : base_ucom dim := Rz (- (PI / 4)) n.
Definition P {dim} n : base_ucom dim := Rz (PI / 2) n.
Definition PDAG {dim} n : base_ucom dim := Rz (- (PI / 2)) n.
Definition CNOT {dim} m n : base_ucom dim := uapp2 U_CNOT m n.  
Definition CZ {dim} m n : base_ucom dim :=
  H n ; CNOT m n ; H n.
Definition SWAP {dim} m n : base_ucom dim :=
  CNOT m n; CNOT n m; CNOT m n.

(*************************)
(** Well Typed Circuits **)
(*************************)

Inductive uc_well_typed {U dim} : ucom U dim -> Prop :=
| WT_seq : forall c1 c2, uc_well_typed c1 -> uc_well_typed c2 -> uc_well_typed (c1; c2)
| WT_app1 : forall u n, n < dim -> uc_well_typed (uapp1 u n)
| WT_app2 : forall u m n, m < dim -> n < dim -> m <> n -> uc_well_typed (uapp2 u m n)
| WT_app3 : forall u m n p, m < dim -> n < dim -> p < dim -> 
    m <> n -> n <> p -> m <> p -> uc_well_typed (uapp3 u m n p).

(* No ucom is well-typed for dim = 0. *)
Lemma uc_well_typed_implies_dim_nonzero : forall {U dim} (c : ucom U dim),
  uc_well_typed c -> dim > 0.
Proof.
  intros U dim c WT.
  induction WT; try apply (Nat.lt_lt_0 n); assumption.
Qed.

(* Equivalent boolean version *)
Fixpoint uc_well_typed_b {U dim} (c : ucom U dim) : bool :=
  match c with
  | c1 ; c2 => uc_well_typed_b c1 && uc_well_typed_b c2 
  | uapp1 _ n => n <? dim
  | uapp2 _ m n => (m <? dim) && (n <? dim) && (negb (m =? n))
  | uapp3 _ m n p => (m <? dim) && (n <? dim) && (p <? dim) && 
      (negb (m =? n)) && (negb (n =? p)) && (negb (m =? p))
  end.

Lemma uc_well_typed_b_equiv : forall {U dim} (c : ucom U dim), 
  uc_well_typed_b c = true <-> uc_well_typed c.
Proof.
  intros U dim c. split; intros H.
  - induction c;
    constructor;
    simpl in H;
    repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H as [? ?]
    | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
    | H : negb (_ =? _) = true |- _ => apply Bool.negb_true_iff in H; 
                                     apply Nat.eqb_neq in H
    end;
    try apply IHc1;
    try apply IHc2;
    assumption.
  - induction H; subst; simpl;
    repeat match goal with
    | |- (_ && _)%bool = true => apply Bool.andb_true_iff; split
    | |- (_ <? _) = true => apply Nat.ltb_lt
    | |- negb (_ =? _) = true => apply Bool.negb_true_iff; apply Nat.eqb_neq
    end;
    try apply IHuc_well_typed1;
    try apply IHuc_well_typed2;
    assumption.
Qed.

Local Close Scope ucom.

(**********************)
(** General Programs **)
(**********************)

Declare Scope com_scope.
Delimit Scope com_scope with com.
Local Open Scope com_scope.

Inductive com (U: nat -> Set) (dim : nat) : Set :=
| skip : com U dim
| seq : com U dim -> com U dim -> com U dim
| uc : ucom U dim -> com U dim
| meas : nat -> com U dim -> com U dim -> com U dim.

Arguments skip {U dim}.
Arguments seq {U dim}.
Arguments uc {U dim}.
Arguments meas {U dim}.

Definition from_ucom {U dim} (c : ucom U dim) : com U dim := uc c.
Coercion from_ucom : ucom >-> com.

Notation "p1 ; p2" := (seq p1 p2) (at level 50) : com_scope.
Notation "'mif' n 'then' p1 'else' p2" := (meas n p1 p2) (at level 40) : com_scope.
Notation "'measure' n" := (meas n skip skip) (at level 40) : com_scope.
Notation "'reset' n" := (meas n (X n) skip) (at level 40) : com_scope.
Notation "n <- 1" := (meas n skip (X n)) (at level 20) : com_scope.
Notation "n <- 0" := (reset n) (at level 20) : com_scope.

Definition base_com := com base_Unitary.

(* Well-typedness for non-unitary programs. *)
Inductive c_well_typed {U dim} : com U dim -> Prop :=
| WT_skip : c_well_typed skip
| WT_cseq : forall c1 c2, c_well_typed c1 -> c_well_typed c2 -> c_well_typed (c1; c2)
| WT_uc : forall u, uc_well_typed u -> c_well_typed (uc u)
| WT_meas : forall n c1 c2, n < dim -> c_well_typed c1 -> c_well_typed c2 -> c_well_typed (meas n c1 c2).

(*****************************)
(** Higher-level Constructs **)
(*****************************)

Fixpoint crepeat {U dim} (k : nat) (p : com U dim) : com U dim :=
  match k with
  | 0    => skip
  | S k' => p ; crepeat k' p
  end.

Fixpoint while {U dim} (max_iters : nat) (n : nat) (p : com U dim) : com U dim :=
  match max_iters with
  | 0        => skip
  | S iters' => mif n then p ; while iters' n p else skip
  end.
