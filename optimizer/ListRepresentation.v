Require Import Setoid.
Require Import Coq.Reals.ROrderedType.

Require Import QWIRE.Proportional.
Require Import optimizer.Equivalences.

Require Export List.

Local Open Scope ucom_scope.
Local Close Scope R_scope.

(* This file contains utilities for manipulating (unitary) SQIRE programs 
   to make implementing transformations easier. The primary contribution is 
   a 'list of gates' representation.

   TODO: We've been thinking for a while about adding a DAG representation of 
   circuits. This would be useful for implementing optimizations because the
   dependence between gates would be obvious (and existing optimizers like Qiskit
   and the Nam et al. optimizer use a DAG representation). However, we have put
   this off for several reasons:
      - Reasoning about the semantics of graphs will be complicated by the need
        to topologically sort the graph to find the order of instructions.
      - A Coq-based representation of graphs (as sets of nodes and edges) will
        probably not be nice to export to OCaml.
   If we decide to return to this in the future, we should look to existing
   verified compilers (e.g. CompCert) to see how they use graphs.
*)

(* Represent a unitary circuit as a list of gate applications. *)

Inductive gate_app (U: nat -> Set) (dim : nat): Set :=
| App1 : U 1 -> nat -> gate_app U dim
| App2 : U 2 -> nat -> nat -> gate_app U dim
| App3 : U 3 -> nat -> nat -> nat -> gate_app U dim.

Arguments App1 {U} {dim}.
Arguments App2 {U} {dim}.
Arguments App3 {U} {dim}.

Definition gate_list U dim := list (gate_app U dim).

(* Well-typedness for lists *)

Inductive uc_well_typed_l {U dim} : gate_list U dim -> Prop :=
| WT_nil : dim > 0 -> uc_well_typed_l []
| WT_app1 : forall u n t, n < dim -> uc_well_typed_l t 
            -> uc_well_typed_l ((App1 u n) :: t)
| WT_app2 : forall u m n t, m < dim -> n < dim -> m <> n -> uc_well_typed_l t 
            ->  uc_well_typed_l ((App2 u m n) :: t)
| WT_app3 : forall u m n p t, m < dim -> n < dim -> p < dim 
            -> m <> n -> n <> p -> m <> p -> uc_well_typed_l t 
            ->  uc_well_typed_l ((App3 u m n p) :: t).

Lemma uc_well_typed_l_implies_dim_nonzero : forall {U dim} (l : gate_list U dim),
  uc_well_typed_l l -> dim > 0.
Proof. intros. induction H; assumption. Qed.

Lemma uc_well_typed_l_app : forall {U dim} (l1 l2 : gate_list U dim),
  uc_well_typed_l l1 /\ uc_well_typed_l l2 <-> uc_well_typed_l (l1 ++ l2).
Proof.
  intros. split.  
  - intros [Hl1 Hl2]. 
    induction Hl1; simpl; try constructor; assumption.
  - intros H.
    induction l1. 
    + split; simpl in H; try constructor; try assumption.
      apply (uc_well_typed_l_implies_dim_nonzero _ H).
    + inversion H; subst;
      match goal with
      | H : uc_well_typed_l (?l1 ++ ?l2) |- _ => apply IHl1 in H as [? ?]
      end; 
      split; try constructor; assumption.
Qed.

Lemma uc_well_typed_l_rev : forall {U dim} (l : gate_list U dim),
  uc_well_typed_l l <-> uc_well_typed_l (rev l).
Proof.
  intros.
  induction l; split; intros; simpl; try constructor; 
  try apply (uc_well_typed_l_implies_dim_nonzero _ H).
  - apply uc_well_typed_l_app.
    split; inversion H; subst; try apply IHl; repeat constructor; try assumption.
    apply (uc_well_typed_l_implies_dim_nonzero _ H3).
    apply (uc_well_typed_l_implies_dim_nonzero _ H5).
    apply (uc_well_typed_l_implies_dim_nonzero _ H8).
  - simpl in H. apply uc_well_typed_l_app in H as [H1 H2].
    inversion H2; subst; try constructor; try apply IHl; assumption. 
Qed.

(* Equivalent boolean version *)
Fixpoint uc_well_typed_l_b {U} dim (l : gate_list U dim) : bool :=
  match l with
  | [] => 0 <? dim
  | App1 _ n :: t => (n <? dim) && (uc_well_typed_l_b dim t)
  | App2 _ m n :: t => (m <? dim) && (n <? dim) && (negb (m =? n)) && 
      (uc_well_typed_l_b dim t)
  | App3 _ m n p :: t => (m <? dim) && (n <? dim) && (p <? dim) && 
      (negb (m =? n)) && (negb (n =? p)) && (negb (m =? p)) &&
      (uc_well_typed_l_b dim t)
  end.

Lemma uc_well_typed_l_b_equiv : forall {U dim} (l : gate_list U dim), 
  uc_well_typed_l_b dim l = true <-> uc_well_typed_l l.
Proof.
  intros U dim l. split; intros H.
  - induction l; 
    try destruct a;
    constructor;
    simpl in H;
    repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H as [? ?]
    | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
    | H : negb (_ =? _) = true |- _ => apply Bool.negb_true_iff in H; 
                                     apply Nat.eqb_neq in H
    end;
    try apply IHl;
    assumption.
  - induction H; subst; simpl;
    repeat match goal with
    | |- (_ && _)%bool = true => apply Bool.andb_true_iff; split
    | |- (_ <? _) = true => apply Nat.ltb_lt
    | |- negb (_ =? _) = true => apply Bool.negb_true_iff; apply Nat.eqb_neq
    end;
    assumption.
Qed.

(** Conversion between gate_list and ucom in the base gate set. **)

Definition base_list dim := gate_list base_Unitary dim.

Fixpoint ucom_to_list {dim} (c: base_ucom dim) : base_list dim :=
  match c with
  | c1; c2 => (ucom_to_list c1) ++ (ucom_to_list c2)
  | uapp1 u n => [App1 u n]
  | uapp2 u m n => [App2 u m n]
  | uapp3 u m n p => [App3 u m n p]
  end.

Fixpoint list_to_ucom {dim} (l : base_list dim) : base_ucom dim :=
  match l with
  | []               => SKIP
  | (App1 u n)::t     => uapp1 u n ; list_to_ucom t
  | (App2 u m n)::t   => uapp2 u m n ; list_to_ucom t
  | (App3 u m n p)::t => uapp3 u m n p ; list_to_ucom t
  end.

Lemma list_to_ucom_append : forall {dim} (l1 l2 : base_list dim),
  list_to_ucom (l1 ++ l2) ≡ list_to_ucom l1 ; list_to_ucom l2.
Proof.
  intros dim l1 l2.
  unfold uc_equiv.
  induction l1; simpl.
  - destruct dim eqn:H. 
    + (* dim = 0 *)
      assert (H1: uc_eval (list_to_ucom l2) = Zero).
      { apply Classical_Prop.NNPP.
        rewrite uc_eval_nonzero_iff.
        intro contra.
        apply uc_well_typed_implies_dim_nonzero in contra.
        contradict contra.
        lia. }
      rewrite H1.
      Msimpl_light.
      reflexivity.
    + (* dim > 0 *)
      rewrite denote_SKIP; try lia. 
      Msimpl_light.
      reflexivity.
  - destruct a; simpl;
    rewrite IHl1; simpl;
    rewrite Mmult_assoc;
    reflexivity.
Qed.

Lemma ucom_list_equiv : forall {dim} (c : base_ucom dim),
  list_to_ucom (ucom_to_list c) ≡ c.
Proof.
  intros.
  unfold uc_equiv.
  induction c; simpl; try dependent destruction u.
  - rewrite list_to_ucom_append; simpl.
    rewrite IHc1, IHc2; reflexivity.
  - simpl; unfold pad. 
    destruct dim; gridify.
    rewrite denote_SKIP; try lia.
    Msimpl_light; reflexivity.
  - simpl; unfold ueval_cnot, pad. 
    destruct dim; gridify;
    rewrite denote_SKIP; try lia;
    Msimpl_light; reflexivity.
Qed.

Lemma list_to_ucom_WT : forall {dim} (l : base_list dim), 
  uc_well_typed_l l <-> uc_well_typed (list_to_ucom l).
Proof.
  intros. 
  split; intros. 
  - induction H; try dependent destruction u.
    + simpl. unfold SKIP. apply uc_well_typed_ID; lia.
    + constructor. 
      constructor; assumption.
      apply IHuc_well_typed_l.
    + constructor.
      constructor; assumption.
      apply IHuc_well_typed_l.
  - induction l.
    + simpl in H. constructor.
      apply (uc_well_typed_implies_dim_nonzero _ H).
    + destruct a; dependent destruction b;
      inversion H; subst;
      inversion H2; subst;
      constructor;
      try apply IHl;
      assumption.
Qed.

(** Useful operations on the list representation. **)

(* Get the next single-qubit gate applied to qubit q.
   
   Returns None if there is no next gate on qubit q or the next gate is
   not a single-qubit gate. Otherwise, it returns Some (l1, g, l2) where g is 
   the next gate, l1 is the portion of the program before the gate, and l2 is
   the portion of the program after the gate.
*)
Fixpoint next_single_qubit_gate {U dim} (l : gate_list U dim) (q : nat) 
             : option (gate_list U dim * U 1 * gate_list U dim) :=
  match l with
  | [] => None
  | (App1 u n) :: t => if n =? q
                     then Some ([], u, t) 
                     else match (next_single_qubit_gate t q) with
                          | None => None
                          | Some (l1, u', l2) => Some ((App1 u n) :: l1, u', l2)
                          end
  | (App2 u m n) :: t => if (m =? q) || (n =? q)
                       then None 
                       else match (next_single_qubit_gate t q) with
                            | None => None
                            | Some (l1, u', l2) => Some ((App2 u m n) :: l1, u', l2)
                            end
  | (App3 u m n p) :: t => if (m =? q) || (n =? q) || (p =? q)
                         then None 
                         else match (next_single_qubit_gate t q) with
                              | None => None
                              | Some (l1, u', l2) => Some ((App3 u m n p) :: l1, u', l2)
                              end
  end.    

Lemma nsqg_preserves_structure : forall {U dim} (l : gate_list U dim) q u l1 l2,
  next_single_qubit_gate l q = Some (l1, u, l2) -> 
  l = l1 ++ [App1 u q] ++ l2.
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a.
  - bdestruct (n =? q).
    + inversion H; subst. reflexivity.
    + destruct (next_single_qubit_gate l q); try easy; destruct p; destruct p.
      inversion H; subst.
      rewrite IHl with (l1:=g0); reflexivity.
  - bdestruct (n =? q); bdestruct (n0 =? q); simpl in H; try discriminate.
    destruct (next_single_qubit_gate l q); try easy; destruct p; destruct p.
    inversion H; subst.
    rewrite IHl with (l1:=g0); reflexivity.  
  - bdestruct (n =? q); bdestruct (n0 =? q); bdestruct (n1 =? q);
    simpl in H; try discriminate.
    destruct (next_single_qubit_gate l q); try discriminate; destruct p; destruct p.
    inversion H; subst.
    rewrite IHl with (l1:=g0); reflexivity. 
Qed.

Lemma nsqg_WT : forall {U dim} (l : gate_list U dim) q u l1 l2,
  next_single_qubit_gate l q = Some (l1, u, l2) -> 
  uc_well_typed_l l -> 
  uc_well_typed_l l1 /\ uc_well_typed_l l2.
Proof.
  intros U dim l q u l1 l2 H WT.
  apply nsqg_preserves_structure in H.
  subst l.
  apply uc_well_typed_l_app in WT as [WT1 WT2].
  apply uc_well_typed_l_app in WT2 as [_ WT2].
  split; assumption.
Qed.

(* Get the last single-qubit gate applied to qubit q. *)
Definition last_single_qubit_gate {U dim} (l : gate_list U dim) (q : nat) 
             : option (gate_list U dim * U 1 * gate_list U dim) :=
  match next_single_qubit_gate (rev l) q  with
  | Some (l1, u, l2) => Some (rev l2, u, rev l1)
  | None => None
  end.

Lemma lsqg_preserves_structure : forall {U dim} (l : gate_list U dim) q u l1 l2,
  last_single_qubit_gate l q = Some (l1, u, l2) -> 
  l = l1 ++ [App1 u q] ++ l2.
Proof.
  intros.
  unfold last_single_qubit_gate in H. 
  destruct (next_single_qubit_gate (rev l) q) eqn:nsqg; try easy.
  destruct p; destruct p.
  inversion H; subst.
  specialize (nsqg_preserves_structure _ _ _ _ _ nsqg) as H1.
  replace ([@App1 U dim u q]) with (rev [@App1 U dim u q]) by easy.
  rewrite <- 2 rev_app_distr.
  rewrite <- app_assoc.
  rewrite <- H1.
  rewrite rev_involutive.
  reflexivity.
Qed.

Lemma lsqg_WT : forall {U dim} (l : gate_list U dim) q u l1 l2,
  last_single_qubit_gate l q = Some (l1, u, l2) -> 
  uc_well_typed_l l -> 
  uc_well_typed_l l1 /\ uc_well_typed_l l2.
Proof.
  intros.
  unfold last_single_qubit_gate in H. 
  destruct (next_single_qubit_gate (rev l) q) eqn:nsqg; try easy.
  destruct p; destruct p.
  inversion H; subst.
  specialize (nsqg_WT _ _ _ _ _ nsqg) as H1.
  apply uc_well_typed_l_rev in H0.
  apply H1 in H0 as [H2 H3].
  split; rewrite <- uc_well_typed_l_rev; assumption.
Qed.

(* Get the next two-qubit gate (CNOT) applied to qubit q.
   
   Returns None if there is no next gate on qubit q or the next gate is
   not a two-qubit gate. Otherwise, it returns Some (l1, q1, q2, l2) where 
   q1 and q2 are the arguments to the CNOT, l1 is the portion of the program 
   before the CNOT, and l2 is the portion of the program after the CNOT.
*)
Fixpoint next_two_qubit_gate {U dim} (l : gate_list U dim) (q : nat) 
             : option (gate_list U dim * U 2 * nat * nat * gate_list U dim) :=
  match l with
  | [] => None
  | (App1 u n) :: t => if n =? q
                     then None
                     else match (next_two_qubit_gate t q) with
                          | None => None
                          | Some (l1, u', m', n', l2) => 
                              Some ((App1 u n) :: l1, u', m', n', l2)
                          end
  | (App2 u m n) :: t => if (m =? q) || (n =? q)
                       then Some ([], u, m, n, t) 
                       else match (next_two_qubit_gate t q) with
                            | None => None
                            | Some (l1, u', m', n', l2) => 
                                Some ((App2 u m n) :: l1, u', m', n', l2)
                            end
  | (App3 u m n p) :: t => if (m =? q) || (n =? q) || (p =? q)
                         then None
                         else match (next_two_qubit_gate t q) with
                              | None => None
                              | Some (l1, u', m', n', l2) => 
                                  Some ((App3 u m n p) :: l1, u', m', n', l2)
                              end
  end.

Lemma ntqg_returns_two_qubit_gate : forall {U dim} (l : gate_list U dim) q l1 u m n l2,
  next_two_qubit_gate l q = Some (l1, u, m, n, l2) -> 
  (q = m \/ q = n).
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a.
  - bdestruct (n0 =? q); try easy.
    destruct (next_two_qubit_gate l q); try easy; do 4 destruct p. 
    inversion H; subst.
    eapply IHl; reflexivity.
  - bdestruct (n0 =? q).
    + simpl in H; inversion H; subst.
      left; reflexivity.
    + bdestruct (n1 =? q); simpl in H.
      * inversion H; subst.
        right; reflexivity.
      * destruct (next_two_qubit_gate l q); try easy; do 4 destruct p.
        inversion H; subst.
        apply IHl with (l1:=g0); reflexivity.
  - bdestruct (n0 =? q); bdestruct (n1 =? q); bdestruct (n2 =? q); try easy.
    destruct (next_two_qubit_gate l q); try easy; do 4 destruct p.
    inversion H; subst.
    apply IHl with (l1:=g0); reflexivity.
Qed.

Lemma ntqg_preserves_structure : forall {U dim} (l : gate_list U dim) q l1 u m n l2,
  next_two_qubit_gate l q = Some (l1, u, m, n, l2) -> 
  l = l1 ++ [App2 u m n] ++ l2.
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a.
  - destruct (n0 =? q); try easy.
    destruct (next_two_qubit_gate l q); try easy.
    do 4 destruct p; inversion H; subst.
    rewrite IHl with (l1:=g0); reflexivity.
  - destruct ((n0 =? q) || (n1 =? q)).
    + inversion H; subst. reflexivity.
    + destruct (next_two_qubit_gate l q); try easy.
      do 4 destruct p; inversion H; subst.
      rewrite IHl with (l1:=g0); reflexivity.
  - destruct ((n0 =? q) || (n1 =? q) || (n2 =? q)); try easy.
    destruct (next_two_qubit_gate l q); try easy.
    do 4 destruct p; inversion H; subst.
    rewrite IHl with (l1:=g0); reflexivity.
Qed.

Lemma ntqg_WT : forall {U dim} (l : gate_list U dim) q l1 u m n l2,
  next_two_qubit_gate l q = Some (l1, u, m, n, l2) -> 
  uc_well_typed_l l -> 
  uc_well_typed_l l1 /\ uc_well_typed_l l2.
Proof.
  intros U dim l q l1 u m n l2 H WT.
  apply ntqg_preserves_structure in H.
  subst l.
  apply uc_well_typed_l_app in WT as [WT1 WT2].
  apply uc_well_typed_l_app in WT2 as [_ WT2].
  split; assumption.
Qed.

(* Get the next gate acting on any qubit in qs. *)

Fixpoint next_gate {U dim} (l : gate_list U dim) (qs : list nat)
             : option (gate_list U dim * gate_app U dim * gate_list U dim) :=
  match l with 
  | [] => None
  | App1 u q :: t => 
      if inb q qs 
      then Some ([], App1 u q, t)
      else match next_gate t qs with
           | Some (l1, g, l2) => Some (App1 u q :: l1, g, l2)
           | _ => None
           end
  | App2 u q1 q2 :: t => 
      if (inb q1 qs) || (inb q2 qs) 
      then Some ([], App2 u q1 q2, t)
      else match next_gate t qs with
           | Some (l1, g, l2) => Some (App2 u q1 q2 :: l1, g, l2)
           | _ => None
           end
  | App3 u q1 q2 q3 :: t => 
      if (inb q1 qs) || (inb q2 qs) || (inb q3 qs)
      then Some ([], App3 u q1 q2 q3, t)
      else match next_gate t qs with
           | Some (l1, g, l2) => Some (App3 u q1 q2 q3 :: l1, g, l2)
           | _ => None
           end
  end.

Lemma next_gate_preserves_structure : forall {U dim} (l : gate_list U dim) qs l1 g l2,
  next_gate l qs = Some (l1, g, l2) ->
  l = l1 ++ [g] ++ l2.
Proof.
  intros.
  generalize dependent l1.
  induction l; try discriminate.
  intros l1 H.
  simpl in H.
  destruct a;
  [ destruct (inb n qs)
  | destruct (inb n qs || inb n0 qs) 
  | destruct (inb n qs || inb n0 qs || inb n1 qs) ].
  all: try (inversion H; subst; reflexivity).
  all: destruct (next_gate l qs); try discriminate; repeat destruct p;
       inversion H; subst;
       rewrite IHl with (l1:=g1); reflexivity.
Qed.

Lemma inb_true : forall l x,
  inb x l = true -> List.In x l.
Proof.
  intros.
  induction l. 
  - inversion H.
  - simpl in *.
    apply orb_true_elim in H as [H | H].
    + apply Nat.eqb_eq in H. left. assumption.
    + right. apply IHl. assumption.
Qed.

Lemma next_gate_app1_returns_q : forall {U dim} (l : gate_list U dim) qs l1 u q l2,
  next_gate l qs = Some (l1, App1 u q, l2) -> List.In q qs.
Proof.
  intros.
  generalize dependent l1.
  induction l; intros l1 H; simpl in H; try discriminate.
  destruct a;
  [ destruct (inb n qs) eqn:Hinb
  | destruct (inb n qs || inb n0 qs)
  | destruct (inb n qs || inb n0 qs || inb n1 qs) ];
  try destruct (next_gate l qs) eqn:ng; 
  try discriminate;
  repeat destruct p.
  all: inversion H; subst. 
  all: try (apply inb_true; assumption).
  all: eapply IHl; reflexivity.
Qed.

Lemma next_gate_app2_returns_q : forall {U dim} (l : gate_list U dim) qs l1 u q1 q2 l2,
  next_gate l qs = Some (l1, App2 u q1 q2, l2) -> (List.In q1 qs \/ List.In q2 qs).
Proof.
  intros.
  generalize dependent l1.
  induction l; intros l1 H; simpl in H; try discriminate.
  destruct a;
  [ destruct (inb n qs)
  | destruct (inb n qs || inb n0 qs) eqn:Hinb
  | destruct (inb n qs || inb n0 qs || inb n1 qs) ];
  try destruct (next_gate l qs) eqn:ng; 
  try discriminate;
  repeat destruct p.
  all: inversion H; subst. 
  all: try (eapply IHl; reflexivity).
  all: apply orb_true_elim in Hinb; destruct Hinb.
  all: try (left; apply inb_true; assumption).
  all: try (right; apply inb_true; assumption).
Qed.

(* does_not_reference *)

Definition does_not_reference_appl {U dim} q (g : gate_app U dim) :=
  match g with
  | App1 u n => negb (n =? q)
  | App2 u m n => negb ((m =? q) || (n =? q))
  | App3 u m n p => negb ((m =? q) || (n =? q) || (p =? q))
  end.

Definition does_not_reference {U dim} (l : gate_list U dim) (q : nat) :=
  forallb (does_not_reference_appl q) l.

Lemma does_not_reference_app : forall {U dim} (l1 l2 : gate_list U dim) q,
  does_not_reference l1 q && does_not_reference l2 q = true <-> 
  does_not_reference (l1 ++ l2) q = true.
Proof.
  intros.
  unfold does_not_reference.
  rewrite forallb_app.
  reflexivity.
Qed.

Lemma does_not_reference_rev : forall {U dim} (l : gate_list U dim) q,
  does_not_reference l q = true <-> does_not_reference (rev l) q = true.
Proof.
  intros.
  induction l; split; intros; simpl in *; trivial. 
  - apply does_not_reference_app.
    apply andb_true_iff.
    apply andb_true_iff in H as [H1 H2].
    split. apply IHl; assumption.
    simpl; apply andb_true_iff. split; trivial.
  - apply does_not_reference_app in H. 
    apply andb_true_iff in H as [H1 H2].
    simpl in H2; apply andb_true_iff in H2 as [H2 _].
    apply andb_true_iff.
    split; try apply IHl; assumption.
Qed.

Lemma nsqg_l1_does_not_reference : forall {U dim} (l : gate_list U dim) q l1 u l2,
  next_single_qubit_gate l q = Some (l1, u, l2) ->
  does_not_reference l1 q = true.
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a;
  [  destruct (n =? q) eqn:E 
   | destruct ((n =? q) || (n0 =? q)) eqn:E 
   | destruct ((n =? q) || (n0 =? q) || (n1 =? q)) eqn:E ];
  try (inversion H; subst; constructor);
  destruct (next_single_qubit_gate l q); try discriminate;
  do 2 destruct p; inversion H; subst;
  simpl;
  apply andb_true_intro;
  split;
  try (apply negb_true_iff; assumption);
  apply IHl; try reflexivity.
Qed.

Lemma lsqg_l2_does_not_reference : forall {U dim} (l : gate_list U dim) q l1 u l2,
  last_single_qubit_gate l q = Some (l1, u, l2) ->
  does_not_reference l2 q = true.
Proof.
  intros.
  unfold last_single_qubit_gate in H.
  destruct (next_single_qubit_gate (rev l) q) eqn:nsqg; try easy.
  destruct p; destruct p; inversion H; subst.
  apply nsqg_l1_does_not_reference in nsqg.
  rewrite <- does_not_reference_rev.
  assumption.
Qed.

Lemma ntqg_l1_does_not_reference : forall {U dim} (l : gate_list U dim) q l1 u m n l2,
  next_two_qubit_gate l q = Some (l1, u, m, n, l2) ->
  does_not_reference l1 q = true.
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a;
  [  destruct (n0 =? q) eqn:E 
   | destruct ((n0 =? q) || (n1 =? q)) eqn:E 
   | destruct ((n0 =? q) || (n1 =? q) || (n2 =? q)) eqn:E ];
  try (inversion H; subst; constructor);
  destruct (next_two_qubit_gate l q); try discriminate;
  do 4 destruct p; inversion H; subst;
  simpl;
  apply andb_true_intro;
  split;
  try (apply negb_true_iff; assumption);
  apply IHl; try reflexivity.
Qed.

Lemma inb_false : forall l x,
  inb x l = false -> forall y, List.In y l -> x <> y.
Proof.
  intros.
  induction l. 
  - inversion H0.
  - simpl in *.
    apply orb_false_elim in H as [H1 H2].
    destruct H0.
    + subst. apply Nat.eqb_neq in H1. lia.
    + apply IHl; assumption.
Qed.

Lemma next_gate_l1_does_not_reference : forall {U dim} (l : gate_list U dim) qs l1 g l2,
  next_gate l qs = Some (l1, g, l2) ->
  forall q, List.In q qs -> does_not_reference l1 q = true.
Proof.
  intros.
  generalize dependent l1.
  induction l; try discriminate.
  intros l1 H.
  simpl in H.
  destruct a;
  [ destruct (inb n qs) eqn:E
  | destruct (inb n qs || inb n0 qs) eqn:E
  | destruct (inb n qs || inb n0 qs || inb n1 qs) eqn:E ].
  all: try (inversion H; subst; constructor).
  all: destruct (next_gate l qs); try discriminate; repeat destruct p;
       inversion H; subst.
  all: simpl; repeat apply andb_true_intro; split.
  all: try (apply IHl; reflexivity).
  2: apply orb_false_elim in E as [E1 E2].
  3: apply orb_false_elim in E as [E12 E3];
     apply orb_false_elim in E12 as [E1 E2].
  all: apply negb_true_iff; repeat apply orb_false_intro; apply eqb_neq.
  all: apply (inb_false qs); assumption.
Qed.

