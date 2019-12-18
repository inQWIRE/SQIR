Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.
Require Export core.UnitarySem. 
Require Export core.DensitySem. 

Local Open Scope ucom_scope.
Local Close Scope R_scope.
Local Open Scope signature_scope.

(* This file contains utilities for manipulating SQIR programs to make implementing 
   transformations easier. The primary contribution is a 'list of gates' 
   representation for unitary programs and a 'list of lists' representation for
   non-unitary programs.

   This file also cintains utilities for writing optimizations, including:
   - given a set of rewrite rules, try to apply each until one succeeds
   - propagate a gate right and cancel when possible 
   - replace a (one-qubit) subcircuit with an equivalent subcircuit

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

(** Represent a unitary circuit as a list of gate applications. **)

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

Definition base_ucom_l dim := gate_list base_Unitary dim.

Fixpoint ucom_to_list {dim} (c: base_ucom dim) : base_ucom_l dim :=
  match c with
  | c1; c2 => (ucom_to_list c1) ++ (ucom_to_list c2)
  | uapp1 u n => [App1 u n]
  | uapp2 u m n => [App2 u m n]
  | uapp3 u m n p => [App3 u m n p]
  end.

Fixpoint list_to_ucom {dim} (l : base_ucom_l dim) : base_ucom dim :=
  match l with
  | []               => SKIP
  | (App1 u n)::t     => uapp1 u n ; list_to_ucom t
  | (App2 u m n)::t   => uapp2 u m n ; list_to_ucom t
  | (App3 u m n p)::t => uapp3 u m n p ; list_to_ucom t
  end.

Lemma list_to_ucom_append : forall {dim} (l1 l2 : base_ucom_l dim),
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

Lemma list_to_ucom_WT : forall {dim} (l : base_ucom_l dim), 
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

(** Useful operations on the ucom list representation. **)

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

Lemma inb_reflect : forall x l, reflect (List.In x l) (inb x l).
Proof.
  intros x l.
  apply iff_reflect.  
  split; intro H.
  - induction l; inversion H; simpl.
    subst. apply orb_true_iff. left. apply beq_nat_true_iff. reflexivity.
    apply orb_true_iff. right. apply IHl. assumption.
  - induction l; simpl in H. discriminate.
    apply orb_true_iff in H. destruct H. 
    apply beq_nat_true_iff in H. subst. left. reflexivity.
    right. apply IHl. assumption.
Qed.
Hint Resolve inb_reflect : bdestruct.

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

Lemma next_gate_app1_returns_q : forall {U dim} (l : gate_list U dim) qs l1 u q l2,
  next_gate l qs = Some (l1, App1 u q, l2) -> List.In q qs.
Proof.
  intros.
  generalize dependent l1.
  induction l; intros l1 H; simpl in H; try discriminate.
  destruct a; 
  [ bdestruct (inb n qs)
  | destruct (inb n qs || inb n0 qs)
  | destruct (inb n qs || inb n0 qs || inb n1 qs) ];
  try destruct (next_gate l qs) eqn:ng; 
  try discriminate;
  repeat destruct p.
  all: inversion H; subst. 
  all: try assumption.
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
  | bdestruct (inb n qs); bdestruct (inb n0 qs)
  | destruct (inb n qs || inb n0 qs || inb n1 qs) ];
  try destruct (next_gate l qs) eqn:ng; 
  try discriminate;
  repeat destruct p.
  all: inversion H; subst. 
  all: try (left; assumption).
  all: try (right; assumption).
  all: eapply IHl; reflexivity.
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
  [ bdestruct (inb n qs)
  | bdestruct (inb n qs); bdestruct (inb n0 qs)
  | bdestruct (inb n qs); bdestruct (inb n0 qs); bdestruct (inb n1 qs) ].
  all: try (inversion H; subst; constructor).
  all: destruct (next_gate l qs); try discriminate; repeat destruct p;
       inversion H; subst.
  all: simpl; repeat apply andb_true_intro; split.
  all: try (apply IHl; reflexivity).
  all: apply negb_true_iff; repeat apply orb_false_intro; apply eqb_neq.
  all: intro; subst; contradiction.
Qed.

(* Given a list of rewrite rules, try to apply each rule until one succeeds. 
   Return None if no rewrite succeeds. In the proof we keep 'P' abstract for 
   maximum generality. *)
Fixpoint try_rewrites {U dim} l (rules : list (gate_list U dim -> option (gate_list U dim))) :=
  match rules with
  | [] => None
  | h :: t => match (h l) with
            | Some l' => Some l'
            | None => try_rewrites l t
            end
  end.

Lemma try_rewrites_preserves_property : 
  forall {U dim} (l l' : gate_list U dim) 
            (P : gate_list U dim -> gate_list U dim -> Prop) 
            rules,
    (forall r, List.In r rules -> forall l l', r l = Some l' -> P l l') ->
    try_rewrites l rules = Some l' ->
    P l l'.
Proof.
  intros U dim l l' P rules Hrules res.
  induction rules. 
  inversion res.
  simpl in res.
  destruct (a l) eqn:al. 
  inversion res; subst.
  eapply Hrules. left. reflexivity. assumption.
  apply IHrules. 
  intros.
  eapply Hrules. right. apply H.
  assumption. assumption.
Qed.

(* 'try_rewrites' with rules that return a pair of lists. *)
Fixpoint try_rewrites2 {U dim} l (rules : list (gate_list U dim -> option (gate_list U dim * gate_list U dim))) :=
  match rules with
  | [] => None
  | h :: t => match (h l) with
            | Some l' => Some l'
            | None => try_rewrites2 l t
            end
  end.

Lemma try_rewrites2_preserves_property :
  forall {U dim} (l l1 l2 : gate_list U dim) 
            (P : gate_list U dim -> (gate_list U dim * gate_list U dim) -> Prop) 
            rules,
    (forall r, List.In r rules -> forall l l1 l2, r l = Some (l1,l2) -> P l (l1,l2)) ->
    try_rewrites2 l rules = Some (l1,l2) ->
    P l (l1,l2).
Proof.
  intros U dim l l1 l2 P rules Hrules res.
  induction rules. 
  inversion res.
  simpl in res.
  destruct (a l) eqn:al. 
  inversion res; subst.
  eapply Hrules. left. reflexivity. assumption.
  apply IHrules. 
  intros.
  eapply Hrules. right. apply H.
  assumption. assumption.
Qed.

(* Try to cancel a gate using a set of cancellation rules, allowing for
   commuting subcircuits described by a set of commutation rules. If
   no cancellation is found, return None. Otherwise return Some l'
   where l' is the modified list.
   

   l             : input list
   commute_rules : rules for commuting the gate right
   cancel_rules  : rules for canceling the gate
   n             : max number of iterations (we usually want n = length l)

   In the soundness proof below we take 'eq' as a parameter to allow for 
   equivalence over different gate sets.
*)
Fixpoint propagate {U dim} (l : gate_list U dim) commute_rules cancel_rules n :=
  match n with
  | O => None
  | S n' => 
      match try_rewrites l cancel_rules with
      | Some l' => Some l'
      | None => match try_rewrites2 l commute_rules with
               | Some (l1, l2) => 
                    match propagate l2 commute_rules cancel_rules n' with
                    | Some l2' => Some (l1 ++ l2')
                    | None => None
                    end
                | None => None
                end
      end
  end.

Definition cancel_rules_correct {U dim} (g : gate_app U dim) rules
    (eq : gate_list U dim -> gate_list U dim -> Prop) :=
  forall r, 
  List.In r rules ->
  forall l l', (r l = Some l' -> eq (g :: l) l').

Definition commute_rules_correct {U dim} (g : gate_app U dim) rules
    (eq : gate_list U dim -> gate_list U dim -> Prop)  :=
  forall r, 
  List.In r rules ->
  forall l l1 l2, (r l = Some (l1, l2) -> eq (g :: l) (l1 ++ [g] ++ l2)).

(* Useful for handling *_rules_correct preconditions. *)
Ltac destruct_In :=
  repeat match goal with
  | H : List.In _ _ |- _ => inversion H; clear H
  end.

Lemma propagate_preserves_semantics : 
  forall {U dim} (l : gate_list U dim) 
    commute_rules cancel_rules n l' g eq 
   `{Equivalence (gate_list U dim) eq} 
   `{Proper _ (eq ==> eq ==> eq) (@app (gate_app U dim))},
  cancel_rules_correct g cancel_rules eq ->
  commute_rules_correct g commute_rules eq ->
  propagate l commute_rules cancel_rules n = Some l' ->
  eq (g :: l) l'.
Proof.
  intros U dim l com can n l' g eq equiv_pf mor_pf Hcan Hcom res.
  generalize dependent l'.
  generalize dependent l.
  induction n; intros l l' res; try discriminate.
  simpl in res.
  destruct (try_rewrites l can) eqn:rewr1.
  inversion res; subst.
  remember (fun l l' => eq (g :: l) l') as P.
  replace (eq (g :: l) l') with (P l l') by (subst; reflexivity).
  apply try_rewrites_preserves_property with (rules:=can).
  2: assumption.
  intros.
  specialize (Hcan r H _ _ H0). subst. assumption.
  destruct (try_rewrites2 l com) eqn:rewr2; try discriminate.
  destruct p.
  destruct (propagate g1 com can n) eqn:prop; try discriminate.
  inversion res; subst.
  apply IHn in prop.
  rewrite <- prop.
  remember (fun l (p : gate_list U dim * gate_list U dim) => 
              let (l1,l2) := p in
              eq (g :: l) (l1 ++ [g] ++ l2)) as P.
  replace (eq (g :: l) (g0 ++ g :: g1)) with (P l (g0,g1)) by (subst; reflexivity).
  apply try_rewrites2_preserves_property with (rules:=com).
  2: assumption.
  intros.    
  specialize (Hcom r H _ _ _ H0). subst. assumption.
Qed.  

(* Rewrite with a single-qubit circuit equivalence.

   We restrict to single-qubit circuit equivalences for now because dealing
   with multi-qubit patterns is tedious with the list representation. For
   example, say that we are looking for the sub-circuit:
       C = [ H 0; H 2; CNOT 1 2; X 0 ]
   When searching for this sub-circuit, we need to keep in mind that these
   gates may be interspersed among other gates in the circuit in any order
   that respects dependence relationships. For example, the following program
   contains C, although it may not be obvious from casual inspection.
       [X 3; H 2; H 0; X 0; CNOT 0 3; CNOT 1 2]
*)

Definition single_qubit_pattern (U : nat -> Set) := list (U 1).

Fixpoint single_qubit_pattern_to_program {U} dim (pat : single_qubit_pattern U) q 
    : gate_list U dim :=
  match pat with
  | [] => []
  | u :: t => App1 u q :: (single_qubit_pattern_to_program dim t q)
  end. 

(* If the next sequence of gates applied to qubit q matches 'pat', then remove
   'pat' from the program. *)
Fixpoint remove_single_qubit_pattern {U dim} (l : gate_list U dim) (q : nat) (pat : single_qubit_pattern U) (match_gate : U 1 -> U 1 -> bool) : option (gate_list U dim) :=
  match pat with
  | [] => Some l
  | u :: t =>
      match next_single_qubit_gate l q with
      | Some (l1, u', l2) =>
          if match_gate u u'
          then remove_single_qubit_pattern (l1 ++ l2) q t match_gate
          else None
      | _ => None
      end
  end.

(* If the next sequence of gates applied to qubit q matches 'pat', then replace
   'pat' with 'rep'. *)
Definition replace_single_qubit_pattern {U dim} (l : gate_list U dim) (q : nat) (pat rep : single_qubit_pattern U) match_gate : option (gate_list U dim) :=
  match (remove_single_qubit_pattern l q pat match_gate) with
  | Some l' => Some ((single_qubit_pattern_to_program dim rep q) ++ l')
  | None => None
  end.

(** List-of-lists representation for non-unitary programs. **)

Local Open Scope com_scope.

Inductive instr (U: nat -> Set) (dim : nat): Set :=
| UC : gate_list U dim -> instr U dim
| Meas : nat -> list (instr U dim) -> list (instr U dim) -> instr U dim.

Definition com_list U dim := list (instr U dim).

Arguments UC {U} {dim}.
Arguments Meas {U} {dim}.

(* Induction principle for com_list *)
Section com_list_ind.
  Variable U : nat -> Set.
  Variable dim : nat.
  Variable P : com_list U dim -> Prop.

  Hypothesis Nil_case : P ([] : com_list U dim).
  Hypothesis UC_case : forall (u : gate_list U dim) t,
    P t -> P ((UC u) :: t).
  Hypothesis Meas_case : forall n (l1 l2 : com_list U dim) t,
    P l1 -> P l2 -> P t -> P ((Meas n l1 l2) :: t).

  Fixpoint instr_ind_aux (i : instr U dim) :=
    match i with
    | UC u => (fun t Pft => UC_case u t Pft)
    | Meas n l1 l2 => 
        let fix f (l : com_list U dim) :=
           match l with
           | [] => Nil_case
           | h :: t => instr_ind_aux h t (f t)
           end in
        (fun t Pft => Meas_case n l1 l2 t (f l1) (f l2) Pft)
    end.

  Fixpoint com_list_ind (l : com_list U dim) : P l :=
    match l with
    | [] => Nil_case
    | h :: t => instr_ind_aux h t (com_list_ind t)
    end.

End com_list_ind.

(* Well-typedness *)
Inductive c_well_typed_l {U dim} : com_list U dim -> Prop :=
| WT_nilc : c_well_typed_l []
| WT_UC : forall u t, uc_well_typed_l u -> c_well_typed_l t -> c_well_typed_l ((UC u) :: t)
| WT_Meas : forall n l1 l2 t, (n < dim)%nat -> c_well_typed_l l1 -> c_well_typed_l l2 
            -> c_well_typed_l t -> c_well_typed_l ((Meas n l1 l2) :: t).

(** Conversion between gate_list and ucom in the base gate set. **)

Definition base_com_l dim := com_list base_Unitary dim.

Fixpoint com_to_list {dim} (c: base_com dim) : base_com_l dim :=
  match c with
  | skip         => []
  | c1; c2       => (com_to_list c1) ++ (com_to_list c2)
  | uc u         => [UC (ucom_to_list u)]
  | meas n c1 c2 => [Meas n (com_to_list c1) (com_to_list c2)]
  end.

(* Written awkwardly to convince Coq of termination. *)
Fixpoint instr_to_com {dim} (i : instr base_Unitary dim) : base_com dim :=
  match i with 
  | UC u => uc (list_to_ucom u)
  | Meas n l1 l2 => 
      let fix f l := match l with
                     | [] => skip
                     | h :: t => instr_to_com h ; f t
                     end in
      meas n (f l1) (f l2)
  end.
Fixpoint list_to_com {dim} (l : base_com_l dim) : base_com dim :=
  match l with
  | [] => skip
  | h :: t => instr_to_com h ; list_to_com t
  end.

Lemma instr_to_com_UC : forall dim (u : base_ucom_l dim),
  instr_to_com (UC u) = uc (list_to_ucom u).
Proof. intros. reflexivity. Qed.

Lemma instr_to_com_Meas : forall dim n (l1 : base_com_l dim) l2,
  instr_to_com (Meas n l1 l2) = meas n (list_to_com l1) (list_to_com l2).
Proof.
  intros.
  simpl.
  apply f_equal2.
  - induction l1; try rewrite IHl1; reflexivity.
  - induction l2; try rewrite IHl2; reflexivity.
Qed.
Global Opaque instr_to_com.
Hint Rewrite instr_to_com_UC instr_to_com_Meas.

Lemma list_to_com_append : forall {dim} (l1 l2 : base_com_l dim),
  list_to_com (l1 ++ l2) ≡ list_to_com l1 ; list_to_com l2.
Proof.
  intros dim l1 l2.
  unfold c_equiv.
  induction l1; simpl; try reflexivity.
  destruct a; simpl; intros;
  unfold compose_super; rewrite IHl1; 
  auto with wf_db.
Qed.

Lemma com_list_equiv : forall {dim} (c : base_com dim),
  list_to_com (com_to_list c) ≡ c.
Proof.
  intros.
  unfold c_equiv.
  induction c; simpl; try reflexivity; intros.
  - rewrite list_to_com_append; simpl; try assumption.
    unfold compose_super.
    rewrite IHc1, IHc2; auto with wf_db.
  - rewrite instr_to_com_UC; simpl.
    rewrite ucom_list_equiv; reflexivity.
  - rewrite instr_to_com_Meas; simpl.
    unfold compose_super, Splus.
    rewrite IHc1, IHc2; auto with wf_db.
Qed.

Lemma list_to_com_WT : forall {dim} (l : base_com_l dim), 
  c_well_typed_l l <-> c_well_typed (list_to_com l).
Proof.
  intros; split; intros H.
  - induction H; constructor; 
    try rewrite instr_to_com_UC; try rewrite instr_to_com_Meas; try constructor; 
    auto.
    apply list_to_ucom_WT. assumption.
  - induction l using com_list_ind; inversion H; subst; 
    try rewrite instr_to_com_UC in H2; try rewrite instr_to_com_Meas in H2; try inversion H2; subst;
    constructor; auto.
    apply list_to_ucom_WT. assumption.
Qed.

(** Useful operations on the com list representation. **)

Fixpoint does_not_reference_instr {U dim} q (i : instr U dim) :=
  match i with 
  | UC u => does_not_reference u q
  | Meas n l1 l2 => 
      negb (q =? n) && 
      forallb (does_not_reference_instr q) l1 && 
      forallb (does_not_reference_instr q) l2
  end.
Definition does_not_reference_c {U dim} (l : com_list U dim) (q : nat) :=
  forallb (does_not_reference_instr q) l.

Lemma does_not_reference_instr_UC : forall U dim q (u : gate_list U dim),
  does_not_reference_instr q (UC u) = does_not_reference u q.
Proof. intros. reflexivity. Qed.

Lemma does_not_reference_instr_Meas : forall U dim q n (l1 : com_list U dim) l2,
  does_not_reference_instr q (Meas n l1 l2) = negb (q =? n) && does_not_reference_c l1 q && does_not_reference_c l2 q.
Proof.
  intros.
  simpl.
  apply f_equal2; [apply f_equal2 |].
  - reflexivity.
  - induction l1; simpl; try rewrite IHl1; reflexivity.
  - induction l2; simpl; try rewrite IHl2; reflexivity.
Qed.
Global Opaque does_not_reference_instr.

(* Get the next measurement operation on qubit q. *)
Fixpoint next_measurement {U dim} (l : com_list U dim) q :=
  match l with
  | [] => None
  | UC u :: t => 
      if does_not_reference u q 
      then match next_measurement t q with
           | None => None
           | Some (l1, l1', l2', l2) => 
               Some (UC u :: l1, l1', l2', l2)
           end
      else None
  | Meas n l1 l2 :: t => 
      if q =? n
      then Some ([], l1, l2, t)
      else if does_not_reference_c l1 q && does_not_reference_c l2 q
           then match next_measurement t q with
                | None => None
                | Some (l1', l1'', l2'', l2') => 
                    Some (Meas n l1 l2 :: l1', l1'', l2'', l2')
                end
           else None
  end.

Lemma next_measurement_preserves_structure : forall U dim (l : com_list U dim) q l1 l1' l2' l2,
  next_measurement l q = Some (l1, l1', l2', l2) ->
  l = l1 ++ [Meas q l1' l2'] ++ l2.
Proof.
  intros.
  generalize dependent l1.
  induction l; intros.
  - inversion H.
  - simpl in H.
    destruct a.
    + destruct (does_not_reference g q); try discriminate.
      destruct (next_measurement l q); try discriminate.
      do 3 destruct p.
      inversion H; subst.
      rewrite IHl with (l1:=l4); reflexivity.
    + bdestruct (q =? n).
      inversion H; subst. reflexivity.
      destruct (does_not_reference_c l0 q && does_not_reference_c l3 q); try discriminate.
      destruct (next_measurement l q); try discriminate.
      do 3 destruct p.
      inversion H; subst.
      rewrite IHl with (l1:=l6); reflexivity.
Qed.  

Lemma next_measurement_l1_does_not_reference : forall {U dim} (l : com_list U dim) q l1 l1' l2' l2,
  next_measurement l q = Some (l1, l1', l2', l2) ->
  does_not_reference_c l1 q = true.
Proof.
  intros.
  generalize dependent l1.
  induction l; intros.
  - inversion H.
  - simpl in H.
    destruct a.
    + destruct (does_not_reference g q) eqn:dnr; try discriminate.
      destruct (next_measurement l q) eqn:nm; try discriminate.
      do 3 destruct p.
      inversion H; subst.
      simpl.
      apply andb_true_intro; split.
      assumption.
      rewrite IHl with (l1:=l4); reflexivity.
    + bdestruct (q =? n).
      inversion H; subst. reflexivity.
      destruct (does_not_reference_c l0 q) eqn:dnrl0. 
      destruct (does_not_reference_c l3 q) eqn:dnrl3.
      all: simpl in H; try discriminate.
      destruct (next_measurement l q) eqn:Hnm; try discriminate.
      do 3 destruct p.
      inversion H; subst.
      simpl.
      rewrite does_not_reference_instr_Meas.
      repeat (try apply andb_true_intro; split).
      apply negb_true_iff; apply eqb_neq; assumption.
      all: try assumption.
      rewrite IHl with (l1:=l6); reflexivity.
Qed.

(* Count the number of UC/Meas operations in a non-unitary program. This is useful
   when we're too lazy to write functions in a nested recursive style & use the
   special induction principle 'com_list_ind'. Instead, we can use the result of
   this function as initial fuel to a function and recurse on the size of the fuel.
   (This only works if the function in question performs N operations where N
   can be over-approximated by an expression involving count_ops.) *)
Fixpoint count_ops_instr {U dim} (i : instr U dim) :=
  match i with
  | UC u => 1%nat
  | Meas n l1 l2 =>
      let fix f l := match l with
                     | [] => O
                     | h :: t => (count_ops_instr h + f t)%nat
                     end in
      (1 + f l1 + f l2)%nat
  end.
Fixpoint count_ops {U dim} (l : com_list U dim) :=
  match l with
  | [] => O
  | h :: t => (count_ops_instr h + count_ops t)%nat
  end.

(* 'canonicalize' a non-unitary program by combining adjacent UC terms and
   removing empty UC terms. This will allow for more effective application 
   of unitary optimizations (and nicer printing). *)
Fixpoint canonicalize_com_l' {U dim} (l : com_list U dim) n : com_list U dim :=
  match n with
  | O => l
  | S n' => match l with
           | [] => []
           | Meas n l1 l2 :: t => 
               let l1' := canonicalize_com_l' l1 n' in
               let l2' := canonicalize_com_l' l2 n' in
               Meas n l1' l2' :: (canonicalize_com_l' t n')
           | UC [] :: t => canonicalize_com_l' t n'
           | UC u1 :: UC u2 :: t => canonicalize_com_l' ((UC (u1 ++ u2)) :: t) n'
           
           | h :: t => h :: (canonicalize_com_l' t n')
           end
  end.
Definition canonicalize_com_l {U dim} (l : com_list U dim) :=
  canonicalize_com_l' l (count_ops l).

