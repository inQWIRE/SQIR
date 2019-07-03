Require Import Setoid.
Require Import Equivalences.

Local Open Scope ucom_scope.


(* This file contains utilities for manipulating (unitary) SQIRE programs 
   to make implementing transformations easier. The primary contribution is 
   two different program representations:
      1. a 'list of gates' representation
      2. a 'list of layers' (grid) representation
   The first representation is useful for optimizations and the second
   representation is useful for circuit mapping.

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


(**************************)
(** List representation  **)
(**************************)
(* Represent a unitary circuit as a list of gate applications. *)

Inductive gate_app (dim : nat): Set :=
| App1 : Unitary 1 -> nat -> gate_app dim
| App2 : Unitary 2 -> nat -> nat -> gate_app dim.

Arguments App1 {dim}.
Arguments App2 {dim}.

Definition gate_list dim := list (gate_app dim).

Fixpoint ucom_to_list {dim} (c: ucom dim) : gate_list dim :=
  match c with
  | c1; c2 => (ucom_to_list c1) ++ (ucom_to_list c2)
  | uapp1 u n => [App1 u n]
  | uapp2 u m n => [App2 u m n]
  | uskip => []
  end.

Fixpoint list_to_ucom {dim} (l : gate_list dim) : ucom dim :=
  match l with
  | [] => uskip
  | (App1 u n)::t => (uapp1 u n) ; (list_to_ucom t)
  | (App2 u m n)::t => (uapp2 u m n) ; (list_to_ucom t)
  end.

Lemma list_to_ucom_append : forall {dim} (l1 l2 : gate_list dim),
  list_to_ucom (l1 ++ l2) ≡ list_to_ucom l1 ; list_to_ucom l2.
Proof.
  intros dim l1 l2.
  unfold uc_equiv.
  induction l1; simpl.
  - Msimpl. reflexivity.
  - destruct a; simpl;
    rewrite IHl1; simpl;
    rewrite Mmult_assoc;
    reflexivity.
Qed.

Lemma ucom_list_equiv : forall {dim} (c : ucom dim),
  c ≡ list_to_ucom (ucom_to_list c).
Proof.
  intros dim c.
  unfold uc_equiv.
  induction c; simpl.
  - reflexivity.
  - repeat rewrite list_to_ucom_append; simpl.
    rewrite IHc1, IHc2.
    reflexivity.
  - Msimpl. reflexivity.
  - Msimpl. reflexivity.
Qed.

Lemma ucom_to_list_WT : forall {dim} (c : ucom dim),
  uc_well_typed c -> uc_well_typed (list_to_ucom (ucom_to_list c)).
Proof.
  intros.
  apply uc_eval_nonzero_iff.
  apply uc_eval_nonzero_iff in H.
  rewrite <- ucom_list_equiv; assumption.
Qed. 

(** Equivalences that allow us to do rewriting. **)

Definition uc_equiv_l {dim} (l1 l2 : gate_list dim) := 
  (list_to_ucom l1) ≡ (list_to_ucom l2).
Infix "=l=" := uc_equiv_l (at level 70).

Lemma uc_equiv_l_refl : forall {dim} (l1 : gate_list dim), l1 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_sym : forall {dim} (l1 l2 : gate_list dim), l1 =l= l2 -> l2 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_trans : forall {dim} (l1 l2 l3 : gate_list dim), 
  l1 =l= l2 -> l2 =l= l3 -> l1 =l= l3.
Proof. intros dim l1 l2 l3 H12 H23. unfold uc_equiv_l in *. rewrite H12. easy. Qed.

Lemma uc_eval_l_cons_app1 : forall {dim} (U : Unitary 1) (n : nat) (t : gate_list dim),
  uc_eval (list_to_ucom ((App1 U n)::t)) = uc_eval (list_to_ucom t) × ueval1 dim n U.
Proof. easy. Qed.

Lemma uc_eval_l_cons_app2 : forall {dim} (U : Unitary 2) (m n : nat) (t : gate_list dim),
  uc_eval (list_to_ucom ((App2 U m n)::t)) = uc_eval (list_to_ucom t) × ueval_cnot dim m n.
Proof. easy. Qed.

Lemma uc_eval_l_app : forall {dim} (l1 l2 : gate_list dim),
  uc_eval (list_to_ucom (l1 ++ l2)) = uc_eval (list_to_ucom l2) × uc_eval (list_to_ucom l1).
Proof.
  intros.
  induction l1.
  - simpl. Msimpl. reflexivity.
  - simpl. 
    destruct a; simpl; rewrite IHl1; rewrite Mmult_assoc; reflexivity.
Qed.

Lemma cons_congruence : forall {dim} (g : gate_app dim)  (l l' : gate_list dim),
  l =l= l' ->
  g :: l =l= g :: l'.
Proof.
  intros dim g l l' Hl.
  unfold uc_equiv_l, uc_equiv.
  destruct g.
  - repeat rewrite uc_eval_l_cons_app1.
    rewrite Hl.
    reflexivity.
  - repeat rewrite uc_eval_l_cons_app2.
    rewrite Hl.
    reflexivity.
Qed.

Lemma app_congruence : forall {dim} (l1 l1' l2 l2' : gate_list dim),
  l1 =l= l1' ->
  l2 =l= l2' ->
  l1 ++ l2 =l= l1' ++ l2'.
Proof.
  intros dim l1 l1' l2 l2' Hl1 Hl2.
  unfold uc_equiv_l, uc_equiv.
  repeat rewrite uc_eval_l_app.
  rewrite Hl1, Hl2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (gate_list dim) (@uc_equiv_l dim)
  reflexivity proved by uc_equiv_l_refl
  symmetry proved by uc_equiv_l_sym
  transitivity proved by uc_equiv_l_trans
  as uc_equiv_l_rel.

Add Parametric Morphism (dim : nat) : (@cons (gate_app dim))
  with signature eq ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as cons_mor.
Proof. intros y x0 y0 H0. apply cons_congruence; easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app dim))
  with signature (@uc_equiv_l dim) ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as app_mor.
Proof. intros x y H x0 y0 H0. apply app_congruence; easy. Qed.

(** Useful operations on the list representation. **)

(* Get the next single-qubit gate applied to qubit q.
   
   Returns None if there is no next gate on qubit q or the next gate is
   not a single-qubit gate. Otherwise, it returns Some (g, l') where g is 
   the application of the gate and l' is the program with that application
   removed.
*)
Fixpoint next_single_qubit_gate {dim} (l : gate_list dim) (q : nat) 
             : option (gate_app dim * gate_list dim) :=
  match l with
  | [] => None
  | (App1 u n) :: t => if n =? q
                     then Some (App1 u n, t) 
                     else match (next_single_qubit_gate t q) with
                          | None => None
                          | Some (g, l') => Some (g, (App1 u n) :: l')
                          end
  | (App2 u m n) :: t => if (m =? q) || (n =? q)
                       then None 
                       else match (next_single_qubit_gate t q) with
                            | None => None
                            | Some (g, l') => Some (g, (App2 u m n) :: l')
                            end
  end.

(* Commutativity lemmas for list representation. *)
Lemma U_V_comm_l : forall {dim} (u1 : Unitary 1) (u2 : Unitary 1) q1 q2 (l : gate_list dim),
  q1 <> q2 ->
  (App1 u1 q1)::(App1 u2 q2)::l =l= (App1 u2 q2)::(App1 u1 q1)::l.
Proof.
  intros.
  unfold uc_equiv_l.
  simpl list_to_ucom.
  rewrite <- useq_assoc. 
  rewrite (U_V_comm _ _ _ _ H).
  rewrite <- useq_assoc. 
  reflexivity.
Qed.

Lemma U_CNOT_comm_l : forall {dim} (u1 : Unitary 1) (u2 : Unitary 2) q1 q2 q3 (l : gate_list dim),
  q1 <> q2 -> q1 <> q3 ->
  (App1 u1 q1)::(App2 u2 q2 q3)::l =l= (App2 u2 q2 q3)::(App1 u1 q1)::l.
Proof.
  intros.
  unfold uc_equiv_l.
  simpl list_to_ucom.
  dependent destruction u2.
  rewrite <- useq_assoc.
  specialize (@U_CNOT_comm dim q1 q2 q3 u1 H H0) as Hcomm.
  rewrite Hcomm.
  rewrite <- useq_assoc. 
  reflexivity.
Qed.        

Lemma nsqg_returns_single_qubit_gate : forall {dim} (l : gate_list dim) q g l',
  next_single_qubit_gate l q = Some (g, l') -> exists u, g = App1 u q.
Proof.
  intros.
  generalize dependent l'.
  induction l; try easy.
  intros l' H.
  simpl in H.
  destruct a.
  - bdestruct (n =? q).
    + inversion H; subst. exists u. reflexivity.
    + destruct (next_single_qubit_gate l q); try easy; destruct p.
      inversion H; subst.
      apply IHl with (l':=g1).
      reflexivity.
  - destruct ((n =? q) || (n0 =? q)); try easy.
    destruct (next_single_qubit_gate l q); try easy; destruct p.
    inversion H; subst.
    apply IHl with (l':=g1).
    reflexivity.
Qed.

Lemma nsqg_preserves_semantics : forall {dim} (l : gate_list dim) q g l',
  next_single_qubit_gate l q = Some (g, l') -> l =l= g :: l'.
Proof.
  intros.
  generalize dependent l'.
  induction l; try easy.
  intros l' H.
  simpl in H.
  destruct a.
  - bdestruct (n =? q).
    + inversion H; subst. reflexivity.
    + remember (next_single_qubit_gate l q) as next_gate.     
      destruct next_gate; try easy; destruct p.
      inversion H; subst.
      rewrite IHl with (l':=g1); try reflexivity.
      symmetry in Heqnext_gate.
      specialize (nsqg_returns_single_qubit_gate l q g g1 Heqnext_gate) as H1.
      destruct H1; rewrite H1.
      apply U_V_comm_l; assumption.      
  - bdestruct (n =? q); bdestruct (n0 =? q); simpl in H; try easy.
    remember (next_single_qubit_gate l q) as next_gate.     
    destruct next_gate; try easy; destruct p.
    inversion H; subst.
    rewrite IHl with (l':=g1); try reflexivity.
    symmetry in Heqnext_gate.
    specialize (nsqg_returns_single_qubit_gate l q g g1 Heqnext_gate) as H2.
    destruct H2; rewrite H2.
    rewrite U_CNOT_comm_l; try lia. 
    reflexivity.  
Qed.

(* Get the next two-qubit gate applied to qubit q.
   
   Returns None if there is no next gate on qubit q or the next gate is
   not a two-qubit gate. Otherwise, it returns Some (l1, g, l2) where g is 
   the application of the gate, l1 is the portion of the program before g, 
   and l2 is the portion of the program after g.
*)
Fixpoint next_two_qubit_gate {dim} (l : gate_list dim) (q : nat) 
             : option (gate_list dim * gate_app dim * gate_list dim) :=
  match l with
  | [] => None
  | (App1 u n) :: t => if n =? q
                     then None
                     else match (next_two_qubit_gate t q) with
                          | None => None
                          | Some (l1, g, l2) => Some ((App1 u n) :: l1, g, l2)
                          end
  | (App2 u m n) :: t => if (m =? q) || (n =? q)
                       then Some ([], App2 u m n, t) 
                       else match (next_two_qubit_gate t q) with
                            | None => None
                            | Some (l1, g, l2) => Some ((App2 u m n) :: l1, g, l2)
                            end
  end.

Lemma ntqg_returns_two_qubit_gate : forall {dim} (l : gate_list dim) q l1 g l2,
  next_two_qubit_gate l q = Some (l1, g, l2) -> 
  exists u m n, (g = App2 u m n /\ (q = m \/ q = n)).
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a.
  - bdestruct (n =? q); try easy.
    destruct (next_two_qubit_gate l q); try easy; destruct p; destruct p.
    inversion H; subst.
    apply IHl with (l1:=g1); reflexivity.
  - bdestruct (n =? q).
    + simpl in H; inversion H; subst.
      exists u, q, n0.
      split; try left; reflexivity.
    + bdestruct (n0 =? q); simpl in H.
      * exists u, n, q.
        inversion H; subst.
        split; try right; reflexivity.
      * destruct (next_two_qubit_gate l q); try easy; destruct p; destruct p.
        inversion H; subst.
        apply IHl with (l1:=g1); reflexivity.
Qed.

Lemma ntqg_preserves_semantics : forall {dim} (l : gate_list dim) q l1 g l2,
  next_two_qubit_gate l q = Some (l1, g, l2) -> l =l= l1 ++ [g] ++ l2.
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a.
  - destruct (n =? q); try easy.
    destruct (next_two_qubit_gate l q); try easy.
    destruct p; destruct p; inversion H; subst.
    rewrite IHl with (l1:=g1); reflexivity.
  - destruct ((n =? q) || (n0 =? q)).
    + inversion H; subst. reflexivity.
    + destruct (next_two_qubit_gate l q); try easy.
      destruct p; destruct p; inversion H; subst.
      rewrite IHl with (l1:=g1); reflexivity.
Qed.

Fixpoint does_not_reference {dim} (l : gate_list dim) (q : nat) :=
  match l with
  | [] => true
  | (App1 u n) :: t => (negb (n =? q)) && (does_not_reference t q)
  | (App2 u m n) :: t => negb ((m =? q) || (n =? q)) && (does_not_reference t q)
  end.


(**************************)
(** Grid representation  **)
(**************************)

(* Represent a unitary circuit as a list of time slices of operations
   that can be performed in parallel. This representation is a little
   closer to the circuit presentation of quantum programs.
 
   This representation is useful for circuit mapping, which typically 
   performs routing between circuit time slices. *)
Definition grid dim := list (gate_list dim). 

(* The goal is to break the program into lists of operations that can be
   performed in parallel. The dumb way to do this would be to put each
   operation in its own time slice. We have tried to be a little smarter 
   by putting as many operations as possible in the same slice.

   It would be interesting to prove that the length of the resulting grid 
   is actually equal to the depth of the circuit. (Although defining the 
   depth of a circuit may require a DAG representation.) *)
Fixpoint build_slice' {dim} (l acc : gate_list dim) (n : nat) :
    (gate_list dim * gate_list dim) :=
  match n with
  | O => (acc, l)
  | S n' => match (next_single_qubit_gate l n') with
           | Some (g, l') => build_slice' l' (g :: acc) n'
           | None => match (next_two_qubit_gate l n') with
                    | Some (l1, App2 u m n, l2) =>
                        if m =? n'
                        then (* CNOT n' n *)
                          if (n' <? n) && (does_not_reference l1 n)
                          then build_slice' (l1 ++ l2) (App2 u n' n :: acc) n'
                          else build_slice' l acc n'
                        else (* CNOT m n' *)
                          if (m <? n') && (does_not_reference l1 m)
                          then build_slice' (l1 ++ l2) (App2 u m n' :: acc) n'
                          else build_slice' l acc n'
                    | _ => build_slice' l acc n'
                    end
           end
  end.

Definition build_slice {dim} (l : gate_list dim) : (gate_list dim * gate_list dim) := 
  build_slice' l [] dim.

(* The n argument is used to prove termination. we begin with n = (length l)
   because this is the maximum number of time slices in the program. *)
Fixpoint list_to_grid' {dim} (l : gate_list dim) (n : nat) : grid dim :=
  match n with
  | O => []
  | S n' => match l with 
           | [] => []
           | _ => match build_slice l with
                | (s, l') => s :: (list_to_grid' l' n')
                end
           end
  end.

Definition list_to_grid {dim} (l : gate_list dim) := list_to_grid' l (List.length l).

Fixpoint grid_to_list {dim} (g : grid dim) :=
  match g with
  | [] => []
  | s :: g' => s ++ (grid_to_list g')
  end.

Lemma list_grid_equiv : forall {dim} (l : gate_list dim),
  l =l= grid_to_list (list_to_grid l).
Proof.
  (* We'll need to prove some more lemmas before we can do this. *)
Admitted.

(* Simple tests. -- Why aren't list notations working? *)
Local Close Scope ucom.
Require Import List.
Import ListNotations.

Definition test1 : gate_list 3 := (App1 U_H 0) :: (App2 U_CNOT 1 2) :: (App2 U_CNOT 0 1) :: (App1 U_X 1) :: [].
Compute (list_to_grid test1).
Compute (grid_to_list (list_to_grid test1)).

Definition test2 : gate_list 3 := (App1 U_H 0) :: (App1 U_H 0) :: (App1 U_H 0) :: (App1 U_H 0) :: [].
Compute (list_to_grid test2).
Compute (grid_to_list (list_to_grid test2)).

Definition test3 : gate_list 3 := (App1 U_H 0) :: (App1 U_H 0) :: (App1 U_H 0) :: (App2 U_CNOT 1 2) :: (App2 U_CNOT 0 1) :: (App1 U_X 1) :: (App1 U_X 2) :: (App1 U_X 2) :: [].
Compute (list_to_grid test3).
Compute (grid_to_list (list_to_grid test3)).