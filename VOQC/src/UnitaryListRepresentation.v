Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.
Require Export Setoid.
Require Export GateSet.
Require Export Equivalences.

(* Used in get_matching_prefix. *)
Require Import FSets.FSetAVL.
Require Import FSets.FSetFacts.
Module FSet := FSetAVL.Make(Coq.Structures.OrderedTypeEx.Nat_as_OT).
Module FSetFacts := FSetFacts.Facts FSet.

Local Open Scope ucom_scope.
Local Close Scope R_scope.
Local Open Scope signature_scope.

(* This file presents a 'list of gates' representation for unitary SQIR 
   programs as well as utilities for writing optimizations, including:
   - given a set of rewrite rules, try to apply each until one succeeds
   - propagate a gate right and cancel when possible 
   - replace a subcircuit with an equivalent subcircuit

   First we present gate set independent definitions. Proofs of lemmas, 
   parameterized by gate set, are given in the UListRepresentationProps module.

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

(* Get the next single-qubit gate applied to qubit q.
   
   Returns None if there is no next gate on qubit q or the next gate is
   not a single-qubit gate. Otherwise, it returns Some (l1, g, l2) where g is 
   the next gate, l1 is the portion of the program before the gate, and l2 is
   the portion of the program after the gate.
*)
Fixpoint next_single_qubit_gate' {U dim} (l : gate_list U dim) (q : nat) acc
             : option (gate_list U dim * U 1 * gate_list U dim) :=
  match l with
  | [] => None
  | (App1 u n) :: t => if n =? q
                     then Some (rev_append acc [], u, t) 
                     else next_single_qubit_gate' t q (App1 u n :: acc)
  | (App2 u m n) :: t => if (m =? q) || (n =? q)
                       then None 
                       else next_single_qubit_gate' t q (App2 u m n :: acc)
  | (App3 u m n p) :: t => if (m =? q) || (n =? q) || (p =? q)
                         then None 
                         else next_single_qubit_gate' t q (App3 u m n p :: acc)
  end.
Definition next_single_qubit_gate {U dim} (l : gate_list U dim) q :=
  next_single_qubit_gate' l q [].

(* Get the last single-qubit gate applied to qubit q. *)
Definition last_single_qubit_gate {U dim} (l : gate_list U dim) (q : nat) 
             : option (gate_list U dim * U 1 * gate_list U dim) :=
  match next_single_qubit_gate (rev_append l []) q  with
  | Some (l1, u, l2) => Some (rev_append l2 [], u, rev_append l1 [])
  | None => None
  end.

(* Get the next two-qubit gate (CNOT) applied to qubit q.
   
   Returns None if there is no next gate on qubit q or the next gate is
   not a two-qubit gate. Otherwise, it returns Some (l1, q1, q2, l2) where 
   q1 and q2 are the arguments to the CNOT, l1 is the portion of the program 
   before the CNOT, and l2 is the portion of the program after the CNOT.
*)
Fixpoint next_two_qubit_gate' {U dim} (l : gate_list U dim) (q : nat) acc
             : option (gate_list U dim * U 2 * nat * nat * gate_list U dim) :=
  match l with
  | [] => None
  | (App1 u n) :: t => if n =? q
                     then None
                     else next_two_qubit_gate' t q (App1 u n :: acc)
  | (App2 u m n) :: t => if (m =? q) || (n =? q)
                       then Some (rev_append acc [], u, m, n, t) 
                       else next_two_qubit_gate' t q (App2 u m n :: acc)
  | (App3 u m n p) :: t => if (m =? q) || (n =? q) || (p =? q)
                         then None 
                         else next_two_qubit_gate' t q (App3 u m n p :: acc)
  end.
Definition next_two_qubit_gate {U dim} (l : gate_list U dim) q :=
  next_two_qubit_gate' l q [].

(* Get the next gate acting on a qubit that satisfies f. *)

Fixpoint next_gate' {U dim} (l : gate_list U dim) (f : nat -> bool) acc
             : option (gate_list U dim * gate_app U dim * gate_list U dim) :=
  match l with 
  | [] => None
  | App1 u q :: t => 
      if f q 
      then Some (rev_append acc [], App1 u q, t)
      else next_gate' t f (App1 u q :: acc)
  | App2 u q1 q2 :: t => 
      if (f q1) || (f q2) 
      then Some (rev_append acc [], App2 u q1 q2, t)
      else next_gate' t f (App2 u q1 q2 :: acc)
  | App3 u q1 q2 q3 :: t => 
      if (f q1) || (f q2) || (f q3)
      then Some (rev_append acc [], App3 u q1 q2 q3, t)
      else next_gate' t f (App3 u q1 q2 q3 :: acc)
  end.
Definition next_gate {U dim} (l : gate_list U dim) f := next_gate' l f [].

(* Definition of "referencing" a qubit - important for commutativity *)

Definition does_not_reference_appl {U dim} q (g : gate_app U dim) :=
  match g with
  | App1 u n => negb (n =? q)
  | App2 u m n => negb ((m =? q) || (n =? q))
  | App3 u m n p => negb ((m =? q) || (n =? q) || (p =? q))
  end.

Definition does_not_reference {U dim} (l : gate_list U dim) (q : nat) :=
  forallb (does_not_reference_appl q) l.

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

(* 'try_rewrites' with rules that return a pair of lists. *)
Fixpoint try_rewrites2 {U dim} l (rules : list (gate_list U dim -> option (gate_list U dim * gate_list U dim))) :=
  match rules with
  | [] => None
  | h :: t => match (h l) with
            | Some l' => Some l'
            | None => try_rewrites2 l t
            end
  end.

(* Try to cancel a gate using a set of cancellation rules, allowing for
   commuting subcircuits described by a set of commutation rules. If
   no cancellation is found, return None. Otherwise return Some l'
   where l' is the modified list.
   

   l             : input list
   commute_rules : rules for commuting the gate right
   cancel_rules  : rules for canceling the gate
   n             : max number of iterations (we usually want n = length l)
   
   In the soundness proof below we take 'eq' as a parameter to allow for 
   different definitions of equivalence.
*)
Fixpoint propagate' {U dim} (l : gate_list U dim) commute_rules cancel_rules n acc :=
  match n with
  | O => None
  | S n' => 
      match try_rewrites l cancel_rules with
      | Some l' => Some (rev_append acc l')
      | None => match try_rewrites2 l commute_rules with
               | Some (l1, l2) => 
                   propagate' l2 commute_rules cancel_rules n' (rev_append l1 acc)
               | None => None
               end
      end
  end.
Definition propagate {U dim} (l : gate_list U dim) commute_rules cancel_rules n :=
  propagate' l commute_rules cancel_rules n [].

(* Remove a sub-circuit from the beginning (or end) of a program. This is
   useful when we want to replace a sub-circuit with an optimized version. *)
Definition remove_prefix {U dim} (l pfx : gate_list U dim) (match_gate : forall {n}, U n -> U n -> bool) : option (gate_list U dim) :=
  let fix f l pfx :=
      match pfx with
      | [] => Some l
      | App1 u q :: t =>
          match next_single_qubit_gate l q with
          | Some (l1, u', l2) =>
              if match_gate u u'
              then f (l1 ++ l2) t
              else None
          | _ => None
          end
      | App2 u q1 q2 :: t =>
          match next_gate l (fun q => (q =? q1) || (q =? q2)) with
          | Some (l1, App2 u' q1' q2', l2) =>
              if (q1 =? q1') && (q2 =? q2') && match_gate u u'
              then f (l1 ++ l2) t
              else None
          | _ => None
            end
      (* ignoring 3-qubit gates *)
      | _ => None
      end in
  f l pfx.

Definition remove_suffix {U dim} (l sfx : gate_list U dim) match_gate :=
  match remove_prefix (rev_append l []) (rev_append sfx []) match_gate with
  | Some l => Some (rev_append l [])
  | _ => None
  end.

(* remove_prefix can also be used to check syntactic equality of programs
   (equality up to unimportant reordering of gates). *)
Definition equalb {U dim} (l1 l2 : gate_list U dim) match_gate :=
  match remove_prefix l1 l2 match_gate with
  | Some [] => true
  | _ => false
  end.

(* If the next sequence of gates applied matches 'pat', then replace 'pat' 
   with 'rep'. *)
Definition replace_pattern {U dim} (l pat rep : gate_list U dim) match_gate : option (gate_list U dim) :=
  match remove_prefix l pat match_gate with
  | Some l' => Some (rep ++ l')
  | None => None
  end.

(* Find the matching prefix of two programs.

   In the program below, pacc and lacc are accumulators for pfx and l1.
   blst tracks "blacklisted" qubits that cannot be in the matching prefix.
   Qubits are added to the blacklist when they occur in a gate application
   in l1 that has no matching gate in l2. n is a fuel argument to convince
   Coq of termination. *)
Definition get_matching_prefix' {U dim} (l1 l2 pacc lacc : gate_list U dim) blst n (match_gate : forall {n}, U n -> U n -> bool) :=
  let fix f l1 l2 pacc lacc blst n :=
      match n with
      | O => (rev_append pacc [], rev_append lacc l1, l2)
      | S n' =>
          match next_gate l1 (fun q => negb (FSet.mem q blst)) with
          | Some (l1a, App1 u1 q, l1b) =>
              let lacc := rev_append l1a lacc in
              let pacc' := App1 u1 q :: pacc in   (* u1 is in the prefix *)
              let lacc' := App1 u1 q :: lacc in   (* u1 is not in the prefix *)
              let blst' := FSet.add q blst in
              match next_single_qubit_gate l2 q with
              | Some (l2a, u2, l2b) => 
                  if match_gate u1 u2 
                  then f l1b (l2a ++ l2b) pacc' lacc blst n'
                  else f l1b l2 pacc lacc' blst' n'
              | _ => f l1b l2 pacc lacc' blst' n'
              end
          | Some (l1a, App2 u1 q1 q2, l1b) => 
              let lacc := rev_append l1a lacc in
              let pacc' := App2 u1 q1 q2 :: pacc in 
              let lacc' := App2 u1 q1 q2 :: lacc in
              let blst' := FSet.add q1 (FSet.add q2 blst) in
              match next_gate l2 (fun q => (q =? q1) || (q =? q2)) with
              | Some (l2a, App2 u2 q1' q2', l2b) => 
                  if match_gate u1 u2 && (q1 =? q1') && (q2 =? q2') && 
                     negb (FSet.mem q1 blst) && negb (FSet.mem q2 blst)
                  then f l1b (l2a ++ l2b) pacc' lacc blst n'
                  else f l1b l2 pacc lacc' blst' n'
              | _ => f l1b l2 pacc lacc' blst' n'
              end
          (* ignoring 3-qubit gates *)
          | _ => (rev_append pacc [], rev_append lacc l1, l2)
          end
      end in
  f l1 l2 pacc lacc blst n.

Definition get_matching_prefix {U dim} (l1 l2 : gate_list U dim) match_gate :=
  get_matching_prefix' l1 l2 [] [] FSet.empty (length l1) match_gate.

(* Apply optimization function opt to loop body b.

   Algorithm:
   1. Optimize the loop body b to produce O.
   2. Optimize O^2 to get LR where L is the maximal prefix of O in the 
      optimization of O^2.
   3. Optimize O^3 to get LCR where R is the maximal suffix of O in the 
      optimization of O^3.
   
   Now b^n is equivalent to LC^{n-2}R. *)
Definition LCR {U dim} (b : gate_list U dim) (opt : gate_list U dim -> gate_list U dim) (match_gate : forall {n}, U n -> U n -> bool) :=
  let o := opt b in
  let o2 := opt (o ++ o) in
  let (tmp, r) := get_matching_prefix o o2 (fun n => @match_gate n) in
  let (l, _) := tmp in
  let o3 := opt (o ++ o ++ o) in
  match remove_prefix o3 l (fun n => @match_gate n) with
  | Some cr => match remove_suffix cr r (fun n => @match_gate n) with
              | Some c => Some (l, c, r)
              | _ => None
              end
  | _ => None
  end.

Lemma cons_to_app : forall {A} (h : A) (t : list A), h :: t = [h] ++ t.
Proof. reflexivity. Qed.

Module UListRepresentationProps (G : GateSet).

(** Well-typedness for unitary lists. **)

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

Local Open Scope ucom_scope.
Fixpoint list_to_ucom {dim} (l : gate_list G.U dim) : base_ucom dim :=
  match l with
  | []               => SKIP
  | (App1 u n)::t     => uapp1 (G.to_base u) n ; list_to_ucom t
  | (App2 u m n)::t   => uapp2 (G.to_base u) m n ; list_to_ucom t
  | (App3 u m n p)::t => uapp3 (G.to_base u) m n p ; list_to_ucom t
  end.

Lemma list_to_ucom_append : forall {dim} (l1 l2 : gate_list G.U dim),
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

Lemma list_to_ucom_WT : forall {dim} (l : gate_list G.U dim), 
  uc_well_typed_l l <-> uc_well_typed (list_to_ucom l).
Proof.
  intros. 
  split; intros. 
  - induction H; try dependent destruction u.
    simpl. unfold SKIP. apply uc_well_typed_ID; lia.
    all: constructor. 
    all: try (constructor; assumption).
    all: apply IHuc_well_typed_l.
  - induction l.
    + simpl in H. constructor.
      apply (uc_well_typed_implies_dim_nonzero _ H).
    + destruct a;
      inversion H; subst;
      inversion H2; subst;
      constructor; auto.
Qed.

Definition eval {dim} (l : gate_list G.U dim) := uc_eval (list_to_ucom l).

(** Equivalences over unitary lists. **)

Definition uc_equiv_l {dim} (l1 l2 : gate_list G.U dim) := 
  list_to_ucom l1 ≡ list_to_ucom l2.
Infix "=l=" := uc_equiv_l (at level 70) : ucom_scope.

Lemma uc_equiv_l_refl : forall {dim} (l1 : gate_list G.U dim), l1 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_sym : forall {dim} (l1 l2 : gate_list G.U dim), l1 =l= l2 -> l2 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_trans : forall {dim} (l1 l2 l3 : gate_list G.U dim), 
  l1 =l= l2 -> l2 =l= l3 -> l1 =l= l3.
Proof. intros dim l1 l2 l3 H12 H23. unfold uc_equiv_l in *. rewrite H12. easy. Qed.

Lemma uc_cons_congruence : forall {dim} (g : gate_app G.U dim)  (l l' : gate_list G.U dim),
  l =l= l' ->
  g :: l =l= g :: l'.
Proof.
  intros dim g l l' Hl.
  unfold uc_equiv_l, uc_equiv.
  simpl.
  destruct g; simpl; try rewrite Hl; reflexivity.
Qed.

Lemma uc_app_congruence : forall {dim} (l1 l1' l2 l2' : gate_list G.U dim),
  l1 =l= l1' ->
  l2 =l= l2' ->
  l1 ++ l2 =l= l1' ++ l2'.
Proof.
  intros dim l1 l1' l2 l2' Hl1 Hl2.
  unfold uc_equiv_l, uc_equiv.
  simpl.
  repeat rewrite list_to_ucom_append; simpl.
  rewrite Hl1, Hl2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (gate_list G.U dim) (@uc_equiv_l dim)
  reflexivity proved by uc_equiv_l_refl
  symmetry proved by uc_equiv_l_sym
  transitivity proved by uc_equiv_l_trans
  as uc_equiv_l_rel.

Add Parametric Morphism (dim : nat) : (@List.cons (gate_app G.U dim))
  with signature eq ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as uc_cons_mor.
Proof. intros y x0 y0 H0. apply uc_cons_congruence; easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app G.U dim))
  with signature (@uc_equiv_l dim) ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as uc_app_mor.
Proof. intros x y H x0 y0 H0. apply uc_app_congruence; easy. Qed.

(* We'll often have goals of the form a ++ X ++ b =l= a ++ Y ++ b,
   which can be simpified to X =l= Y. That's what this tactic is for. *)
Ltac apply_app_congruence :=
  repeat rewrite app_assoc;
  repeat (apply uc_app_congruence; [| reflexivity]);
  repeat rewrite <- app_assoc;
  repeat (apply uc_app_congruence; [reflexivity |]).

Lemma uc_equiv_l_implies_WT : forall {dim} (l l' : gate_list G.U dim),
  l =l= l' ->
  uc_well_typed_l l ->
  uc_well_typed_l l'.
Proof.
  intros dim l l' H WT.
  apply list_to_ucom_WT. 
  apply uc_eval_nonzero_iff.
  apply list_to_ucom_WT in WT.
  apply uc_eval_nonzero_iff in WT.
  rewrite <- H; assumption.
Qed.

(* Equivalence up to a phase. *)

Definition uc_cong_l {dim} (l1 l2 : gate_list G.U dim) := 
  list_to_ucom l1 ≅ list_to_ucom l2.
Infix "≅l≅" := uc_cong_l (at level 20) : ucom_scope.

Lemma uc_cong_l_refl : forall {dim : nat} (l1 : gate_list G.U dim), l1 ≅l≅ l1.
Proof. intros. exists 0%R. rewrite Cexp_0. rewrite Mscale_1_l. reflexivity. Qed.

Lemma uc_cong_l_sym : forall {dim : nat} (l1 l2 : gate_list G.U dim), l1 ≅l≅ l2 -> l2 ≅l≅ l1.
Proof. intros dim l1 l2 H. unfold uc_cong_l in *. rewrite H. reflexivity. Qed.

Lemma uc_cong_l_trans : forall {dim : nat} (l1 l2 l3 : gate_list G.U dim), l1 ≅l≅ l2 -> l2 ≅l≅ l3 -> l1 ≅l≅ l3.
Proof.
  intros dim l1 l2 l3 H1 H2.
  unfold uc_cong_l in *.
  eapply uc_cong_trans. apply H1. apply H2.
Qed.  

Lemma uc_cong_l_cons_congruence : forall {dim : nat} (g : gate_app G.U dim) (l l' : gate_list G.U dim),
  l ≅l≅ l' -> (g :: l) ≅l≅ (g :: l').
Proof.
  intros dim g l l' H. unfold uc_cong_l in *.
  simpl.
  inversion H.
  destruct g as [u | u | u];
  exists x; simpl; rewrite <- Mscale_mult_dist_l; rewrite H0; reflexivity.
Qed.

Lemma uc_cong_l_app_congruence : forall {dim : nat} (l l' m m': gate_list G.U dim),
  l ≅l≅ l' -> m ≅l≅ m' -> (m ++ l) ≅l≅ (m' ++ l').
Proof.
  intros dim l l' m m' H1 H2.
  unfold uc_cong_l in *.
  inversion H1. inversion H2.
  exists (x + x0)%R.
  repeat rewrite list_to_ucom_append; simpl.
  rewrite H, H0. 
  rewrite Mscale_mult_dist_r.
  rewrite Mscale_mult_dist_l.
  rewrite Mscale_assoc.
  rewrite <- Cexp_add.
  rewrite Rplus_comm.
  reflexivity.
Qed.
    
Add Parametric Relation (dim : nat) : (gate_list G.U dim) (@uc_cong_l dim)
  reflexivity proved by uc_cong_l_refl
  symmetry proved by uc_cong_l_sym
  transitivity proved by uc_cong_l_trans
  as uc_cong_l_rel.

Add Parametric Morphism (dim : nat) : (@List.cons (gate_app G.U dim))
  with signature eq ==> (@uc_cong_l dim) ==> (@uc_cong_l dim) as uc_cons_mor_cong.
Proof. intros. apply uc_cong_l_cons_congruence. easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app G.U dim))
  with signature (@uc_cong_l dim) ==> (@uc_cong_l dim) ==> (@uc_cong_l dim) as uc_app_mor_cong.
Proof. intros x y H x0 y0 H0. apply uc_cong_l_app_congruence; easy. Qed.

Ltac apply_app_congruence_cong :=
  repeat rewrite app_assoc;
  repeat (apply uc_cong_l_app_congruence; [reflexivity |]);
  repeat rewrite <- app_assoc;
  repeat (apply uc_cong_l_app_congruence; [| reflexivity]).

Lemma uc_equiv_cong_l : forall {dim : nat} (c c' : gate_list G.U dim), c =l= c' -> c ≅l≅ c'.
Proof.
  intros dim c c' H.
  exists 0%R. rewrite Cexp_0, Mscale_1_l. 
  apply H.
Qed.

Lemma uc_cong_l_implies_WT : forall {dim} (l l' : gate_list G.U dim),
  l ≅l≅ l' ->
  uc_well_typed_l l ->
  uc_well_typed_l l'.
Proof.
  intros dim l l' H WT.
  apply list_to_ucom_WT. 
  apply uc_eval_nonzero_iff.
  apply list_to_ucom_WT in WT.
  apply uc_eval_nonzero_iff in WT.
  destruct H.
  rewrite H in WT. 
  intros contra.
  rewrite contra in WT.
  contradict WT.
  Msimpl.
  reflexivity.
Qed.

(** Basic commutativity lemmas. **)

Lemma does_not_reference_app : forall {U dim} (l1 l2 : gate_list U dim) q,
  does_not_reference l1 q && does_not_reference l2 q = true <-> 
  does_not_reference (l1 ++ l2) q = true.
Proof.
  intros.
  unfold does_not_reference.
  rewrite forallb_app.
  reflexivity.
Qed.

(* Automation for simplifying does_not_reference terms *)
Ltac simpl_dnr :=
  repeat match goal with 
  | H : does_not_reference (_ ++ _) _ = true |- _ =>
      apply does_not_reference_app in H
  | H : does_not_reference [_] _ = _ |- _ =>
      simpl in H
  | H : does_not_reference_appl _ _ = _ |- _ =>
      simpl in H
  | H : negb _ = true |- _ => 
      apply negb_true_iff in H
  | H : _ || _ = false |- _ => 
      apply orb_false_elim in H as [? ?]
  | H : _ && _ = true |- _ =>
      apply andb_true_iff in H as [? ?]
  | H : (_ =? _)%nat = false |- _ => 
      apply beq_nat_false in H
  end.

Lemma does_not_reference_commutes_app1 : forall {dim} (l : gate_list G.U dim) u q,
  does_not_reference l q = true ->
  [App1 u q] ++ l =l= l ++ [App1 u q]. 
Proof.
  intros dim l u q H.
  induction l.
  - reflexivity.
  - simpl in *.
    destruct a as [u' | u' | u'];
    simpl_dnr;
    rewrite <- IHl; auto;
    unfold uc_equiv_l; simpl;
    repeat rewrite <- useq_assoc.
    rewrite U_V_comm; auto; reflexivity.
    remember (G.to_base u') as base; dependent destruction base.
    rewrite (U_CNOT_comm _ n n0); auto; reflexivity.
    remember (G.to_base u') as base; dependent destruction base.
Qed.

Lemma does_not_reference_commutes_app2 : forall {dim} (l : gate_list G.U dim) u m n,
  does_not_reference l m = true ->
  does_not_reference l n = true ->
  [App2 u m n] ++ l =l= l ++ [App2 u m n]. 
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl in *.
    destruct a as [u' | u' | u'];
    simpl_dnr;
    rewrite <- IHl; auto;
    unfold uc_equiv_l; simpl;
    repeat rewrite <- useq_assoc.
    remember (G.to_base u) as base; dependent destruction base.
    rewrite (U_CNOT_comm n0 m n); auto; reflexivity.
    remember (G.to_base u) as base; dependent destruction base.
    remember (G.to_base u') as base'; dependent destruction base'.
    rewrite (CNOT_CNOT_comm m n n0 n1); auto; reflexivity.
    remember (G.to_base u') as base; dependent destruction base.
Qed.

(** Correctness lemmas for ops on unitary programs. **)

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

Lemma nsqg_preserves_structure : forall {U dim} (l : gate_list U dim) q u l1 l2,
  next_single_qubit_gate l q = Some (l1, u, l2) -> 
  l = l1 ++ [App1 u q] ++ l2.
Proof.
  assert (H : forall U dim (l : gate_list U dim) q u l1 l2 acc,
          next_single_qubit_gate' l q acc = Some (l1, u, l2) -> 
          (rev acc) ++ l = l1 ++ [App1 u q] ++ l2).
  { intros U dim l q u l1 l2 acc H.
    generalize dependent acc.
    generalize dependent l1.
    induction l; try easy.
    intros l1 acc H.
    simpl in H.
    destruct a.
    - bdestruct (n =? q).
      + inversion H; subst. rewrite rev_alt. reflexivity.
      + destruct (next_single_qubit_gate' l q (App1 u0 n :: acc)) eqn:res;
        try discriminate; destruct p; destruct p.
        inversion H; subst.
        apply IHl in res; simpl in *.
        rewrite <- res. 
        rewrite <- app_assoc; reflexivity.
    - bdestruct (n =? q); bdestruct (n0 =? q); simpl in H; try discriminate.
      destruct (next_single_qubit_gate' l q (App2 u0 n n0 :: acc)) eqn:res; 
      try discriminate; destruct p; destruct p.
      inversion H; subst.
      apply IHl in res; simpl in *.
      rewrite <- res. 
      rewrite <- app_assoc; reflexivity.
    - bdestruct (n =? q); bdestruct (n0 =? q); bdestruct (n1 =? q);
      simpl in H; try discriminate.
      destruct (next_single_qubit_gate' l q (App3 u0 n n0 n1 :: acc)) eqn:res; 
      try discriminate; destruct p; destruct p.
      inversion H; subst.
      apply IHl in res; simpl in *.
      rewrite <- res. 
      rewrite <- app_assoc; reflexivity. }
  intros ? ? ? ? ? ? ? H0.
  apply H in H0. rewrite <- H0. reflexivity.
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

Lemma nsqg_l1_does_not_reference : forall {U dim} (l : gate_list U dim) q l1 u l2,
  next_single_qubit_gate l q = Some (l1, u, l2) ->
  does_not_reference l1 q = true.
Proof.
  assert (H: forall {U dim} (l : gate_list U dim) q l1 u l2 acc,
          does_not_reference acc q = true ->
          next_single_qubit_gate' l q acc = Some (l1, u, l2) ->
          does_not_reference l1 q = true).
  { intros U dim l q l1 u l2 acc Hdnr H.
    generalize dependent acc.
    generalize dependent l1.
    induction l; try easy.
    intros l1 acc Hdnr H.
    simpl in H.
    destruct a;
    [  destruct (n =? q) eqn:E 
     | destruct ((n =? q) || (n0 =? q)) eqn:E 
     | destruct ((n =? q) || (n0 =? q) || (n1 =? q)) eqn:E ];
    try (inversion H; subst; constructor).
    rewrite <- rev_alt in H.
    inversion H; subst.
    rewrite <- does_not_reference_rev; auto.
    1: destruct (next_single_qubit_gate' l q (App1 u0 n :: acc)) eqn:res; try easy.
    2: destruct (next_single_qubit_gate' l q (App2 u0 n n0 :: acc)) eqn:res; try easy.
    3: destruct (next_single_qubit_gate' l q (App3 u0 n n0 n1 :: acc)) eqn:res; try easy.
    all: do 2 destruct p; inversion H; subst; eapply IHl; try apply res.
    all: simpl; apply andb_true_intro; split; try apply negb_true_iff; auto. }
  intros ? ? ? ? ? ? ? H0.
  eapply H; try apply H0.
  reflexivity.
Qed.

Lemma nsqg_commutes : forall {dim} (l : gate_list G.U dim) q u l1 l2,
  next_single_qubit_gate l q = Some (l1, u, l2) -> 
  l =l= [App1 u q] ++ l1 ++ l2.
Proof.
  intros dim l q u l1 l2 H.
  specialize (nsqg_preserves_structure _ _ _ _ _ H) as H1.
  subst.
  apply nsqg_l1_does_not_reference in H.
  apply (does_not_reference_commutes_app1 _ u _) in H.
  repeat rewrite app_assoc.  
  rewrite H.
  reflexivity.
Qed.

Lemma lsqg_preserves_structure : forall {U dim} (l : gate_list U dim) q u l1 l2,
  last_single_qubit_gate l q = Some (l1, u, l2) -> 
  l = l1 ++ [App1 u q] ++ l2.
Proof.
  intros.
  unfold last_single_qubit_gate in H. 
  rewrite <- rev_alt in H.
  destruct (next_single_qubit_gate (rev l) q) eqn:nsqg; try easy.
  destruct p; destruct p.
  repeat rewrite <- rev_alt in H.
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
  rewrite <- rev_alt in H.
  destruct (next_single_qubit_gate (rev l) q) eqn:nsqg; try easy.
  destruct p; destruct p.
  repeat rewrite <- rev_alt in H.
  inversion H; subst.
  specialize (nsqg_WT _ _ _ _ _ nsqg) as H1.
  apply uc_well_typed_l_rev in H0.
  apply H1 in H0 as [H2 H3].
  split; rewrite <- uc_well_typed_l_rev; assumption.
Qed.

Lemma lsqg_l2_does_not_reference : forall {U dim} (l : gate_list U dim) q l1 u l2,
  last_single_qubit_gate l q = Some (l1, u, l2) ->
  does_not_reference l2 q = true.
Proof.
  intros.
  unfold last_single_qubit_gate in H.
  rewrite <- rev_alt in H.
  destruct (next_single_qubit_gate (rev l) q) eqn:nsqg; try easy.
  destruct p; destruct p; inversion H; subst.
  rewrite <- rev_alt.
  apply nsqg_l1_does_not_reference in nsqg.
  rewrite <- does_not_reference_rev.
  assumption.
Qed.

Lemma lsqg_commutes : forall {dim} (l : gate_list G.U dim) q u l1 l2,
  last_single_qubit_gate l q = Some (l1, u, l2) -> 
  l =l= l1 ++ l2 ++ [App1 u q].
Proof.
  intros dim l q u l1 l2 H.
  specialize (lsqg_preserves_structure _ _ _ _ _ H) as H1.
  subst.
  apply lsqg_l2_does_not_reference in H.
  apply (does_not_reference_commutes_app1 _ u _) in H.
  rewrite H.
  reflexivity.
Qed.

Lemma ntqg_returns_two_qubit_gate : forall {U dim} (l : gate_list U dim) q l1 u m n l2,
  next_two_qubit_gate l q = Some (l1, u, m, n, l2) -> 
  (q = m \/ q = n).
Proof.
  assert (H : forall U dim (l : gate_list U dim) q l1 u m n l2 acc,
          next_two_qubit_gate' l q acc = Some (l1, u, m, n, l2) -> 
          (q = m \/ q = n)).
  { intros U dim l q l1 u m n l2 acc H.
    generalize dependent acc.
    generalize dependent l1.
    induction l; try easy.
    intros l1 acc H.
    simpl in H.
    destruct a.
    - bdestruct (n0 =? q); try easy.
      destruct (next_two_qubit_gate' l q (App1 u0 n0 :: acc)) eqn:res; 
      try easy; do 4 destruct p. 
      inversion H; subst.
      eapply IHl; apply res.
    - bdestruct (n0 =? q).
      + simpl in H; rewrite <- rev_alt in H. simpl in H.
        inversion H; subst.
        left; reflexivity.
      + bdestruct (n1 =? q); simpl in H.
        * inversion H; subst.
          right; reflexivity.
        * destruct (next_two_qubit_gate' l q (App2 u0 n0 n1 :: acc)) eqn:res; 
          try easy; do 4 destruct p.
          inversion H; subst.
          eapply IHl; apply res.
    - bdestruct (n0 =? q); bdestruct (n1 =? q); bdestruct (n2 =? q); try easy.
      destruct (next_two_qubit_gate' l q (App3 u0 n0 n1 n2 :: acc)) eqn:res; 
      try easy; do 4 destruct p.
      inversion H; subst.
      eapply IHl; apply res. }
  intros ? ? ? ? ? ? ? ? ? H0.
  eapply H. apply H0.
Qed.

Lemma ntqg_preserves_structure : forall {U dim} (l : gate_list U dim) q l1 u m n l2,
  next_two_qubit_gate l q = Some (l1, u, m, n, l2) -> 
  l = l1 ++ [App2 u m n] ++ l2.
Proof.
  assert (H : forall U dim (l : gate_list U dim) q l1 u m n l2 acc,
          next_two_qubit_gate' l q acc = Some (l1, u, m, n, l2) -> 
          (rev acc) ++ l = l1 ++ [App2 u m n] ++ l2).
  { intros U dim l q l1 u m n l2 acc H.
    generalize dependent acc.
    generalize dependent l1.
    induction l; try easy.
    intros l1 acc H.
    simpl in H.
    destruct a.
    - destruct (n0 =? q); try easy.
      destruct (next_two_qubit_gate' l q (App1 u0 n0 :: acc)) eqn:res; 
      try easy; do 4 destruct p.
      inversion H; subst.
      apply IHl in res; simpl in *.
      rewrite <- res. 
      rewrite <- app_assoc; reflexivity.
    - destruct ((n0 =? q) || (n1 =? q)).
      + rewrite <- rev_alt in H. inversion H; subst. reflexivity.
      + destruct (next_two_qubit_gate' l q (App2 u0 n0 n1 :: acc)) eqn:res; 
        try easy; do 4 destruct p. 
        inversion H; subst.
        apply IHl in res; simpl in *.
        rewrite <- res. 
        rewrite <- app_assoc; reflexivity.
    - destruct ((n0 =? q) || (n1 =? q) || (n2 =? q)); try easy.
      destruct (next_two_qubit_gate' l q (App3 u0 n0 n1 n2 :: acc)) eqn:res; 
      try easy; do 4 destruct p.
      inversion H; subst.
      apply IHl in res; simpl in *.
      rewrite <- res. 
      rewrite <- app_assoc; reflexivity. }
  intros ? ? ? ? ? ? ? ? ? H0.  
  apply H in H0. rewrite <- H0. reflexivity.
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

Lemma ntqg_l1_does_not_reference : forall {U dim} (l : gate_list U dim) q l1 u m n l2,
  next_two_qubit_gate l q = Some (l1, u, m, n, l2) ->
  does_not_reference l1 q = true.
Proof.
  assert (H: forall {U dim} (l : gate_list U dim) q l1 u m n l2 acc,
          does_not_reference acc q = true ->
          next_two_qubit_gate' l q acc = Some (l1, u, m, n, l2) ->
          does_not_reference l1 q = true).
  { intros U dim l q l1 u m n l2 acc Hdnr H.
    generalize dependent acc.
    generalize dependent l1.
    induction l; try easy.
    intros l1 acc Hdnr H.
    simpl in H.
    destruct a;
    [  destruct (n0 =? q) eqn:E 
     | destruct ((n0 =? q) || (n1 =? q)) eqn:E 
     | destruct ((n0 =? q) || (n1 =? q) || (n2 =? q)) eqn:E ];
    try (inversion H; subst; constructor).
    2: { inversion H; subst. rewrite <- rev_alt.
         rewrite <- does_not_reference_rev; auto. }
    1: destruct (next_two_qubit_gate' l q (App1 u0 n0 :: acc)) eqn:res; try easy.
    2: destruct (next_two_qubit_gate' l q (App2 u0 n0 n1 :: acc)) eqn:res; try easy.
    3: destruct (next_two_qubit_gate' l q (App3 u0 n0 n1 n2 :: acc)) eqn:res; try easy.
    all: do 2 destruct p; inversion H; subst; eapply IHl; try apply res.
    all: simpl; apply andb_true_intro; split; try apply negb_true_iff; auto. }
  intros ? ? ? ? ? ? ? ? ? H0.
  eapply H; try apply H0.
  reflexivity.
Qed.

Lemma next_gate_preserves_structure : forall {U dim} (l : gate_list U dim) f l1 g l2,
  next_gate l f = Some (l1, g, l2) ->
  l = l1 ++ [g] ++ l2.
Proof.
  assert (H : forall U dim (l : gate_list U dim) f l1 g l2 acc,
          next_gate' l f acc = Some (l1, g, l2) -> 
          (rev acc) ++ l = l1 ++ [g] ++ l2).
  { intros U dim l f l1 g l2 acc H.
    generalize dependent acc.
    generalize dependent l1.
    induction l; try discriminate.
    intros l1 acc H.
    simpl in H.
    destruct a;
    [ destruct (f n)
    | destruct (f n || f n0) 
    | destruct (f n || f n0 || f n1) ].
    all: try rewrite <- rev_alt in H. 
    all: try (inversion H; subst; reflexivity).
    1: destruct (next_gate' l f (App1 u n :: acc)) eqn:res; try discriminate.
    2: destruct (next_gate' l f (App2 u n n0 :: acc)) eqn:res; try discriminate.
    3: destruct (next_gate' l f (App3 u n n0 n1 :: acc)) eqn:res; try discriminate.
    all: repeat destruct p; inversion H; subst;
         erewrite <- IHl; try apply res. 
    all: simpl; rewrite <- app_assoc; reflexivity. }
  intros ? ? ? ? ? ? ? H0.  
  apply H in H0. rewrite <- H0. reflexivity.
Qed.

Lemma next_gate_app1_returns_q : forall {U dim} (l : gate_list U dim) f l1 u q l2,
  next_gate l f = Some (l1, App1 u q, l2) -> f q = true.
Proof.
  assert (H : forall U dim (l : gate_list U dim) f l1 u q l2 acc,
          next_gate' l f acc = Some (l1, App1 u q, l2) -> f q = true).
  { intros U dim l f l1 u q l2 acc H.
    generalize dependent acc.
    generalize dependent l1.
    induction l; intros l1 acc H; simpl in H; try discriminate.
    destruct a; 
    [ destruct (f n) eqn:?
    | destruct (f n || f n0)
    | destruct (f n || f n0 || f n1) ].
    all: try rewrite <- rev_alt in H.
    2: destruct (next_gate' l f (App1 u0 n :: acc)) eqn:res; try discriminate.
    4: destruct (next_gate' l f (App2 u0 n n0 :: acc)) eqn:res; try discriminate.
    6: destruct (next_gate' l f (App3 u0 n n0 n1 :: acc)) eqn:res; try discriminate.
    all: repeat destruct p.
    all: inversion H; subst; auto.
    all: eapply IHl; apply res. }
  intros ? ? ? ? ? ? ? ? H0.  
  eapply H. apply H0.
Qed.

Lemma next_gate_app2_returns_q : forall {U dim} (l : gate_list U dim) f l1 u q1 q2 l2,
  next_gate l f = Some (l1, App2 u q1 q2, l2) -> (f q1 = true \/ f q2 = true).
Proof.
  assert (H : forall U dim (l : gate_list U dim) f l1 u q1 q2 l2 acc,
          next_gate' l f acc = Some (l1, App2 u q1 q2, l2) ->
          (f q1 = true \/ f q2 = true)).
  { intros U dim l f l1 u q1 q2 l2 acc H.
    generalize dependent acc.
    generalize dependent l1.
    induction l; intros l1 acc H; simpl in H; try discriminate.
    destruct a; 
    [ destruct (f n)
    | destruct (f n) eqn:?; destruct (f n0) eqn:?
    | destruct (f n || f n0 || f n1) ].
    all: try rewrite <- rev_alt in H. 
    2: destruct (next_gate' l f (App1 u0 n :: acc)) eqn:res; try discriminate.
    6: destruct (next_gate' l f (App2 u0 n n0 :: acc)) eqn:res; try discriminate.
    8: destruct (next_gate' l f (App3 u0 n n0 n1 :: acc)) eqn:res; try discriminate.
    all: repeat destruct p.
    all: inversion H; subst; auto.
    all: eapply IHl; apply res. }
  intros ? ? ? ? ? ? ? ? ? H0.  
  eapply H. apply H0.
Qed.

Lemma next_gate_WT : forall {U dim} (l : gate_list U dim) q l1 g l2,
  next_gate l q = Some (l1, g, l2) -> 
  uc_well_typed_l l -> 
  uc_well_typed_l l1 /\ uc_well_typed_l l2.
Proof.
  intros U dim l q l1 g l2 H WT.
  apply next_gate_preserves_structure in H.
  subst l.
  apply uc_well_typed_l_app in WT as [WT1 WT2].
  apply uc_well_typed_l_app in WT2 as [_ WT2].
  split; assumption.
Qed.

Lemma next_gate_l1_does_not_reference : forall {U dim} (l : gate_list U dim) f l1 g l2,
  next_gate l f = Some (l1, g, l2) ->
  forall q, f q = true -> does_not_reference l1 q = true.
Proof.
  assert (H: forall {U dim} (l : gate_list U dim) f l1 g l2 acc,
          (forall q, f q = true -> does_not_reference acc q = true) ->
          next_gate' l f acc = Some (l1, g, l2) ->
          forall q, f q = true -> does_not_reference l1 q = true).
  { intros U dim l f l1 g l2 acc Hdnr H.
    generalize dependent acc.
    generalize dependent l1.
    induction l; try easy.
    intros l1 acc Hdnr H q Hq.
    simpl in H.
    destruct a;
    [ destruct (f n) eqn:?
    | destruct (f n) eqn:?; destruct (f n0) eqn:?
    | destruct (f n) eqn:?; destruct (f n0) eqn:?; destruct (f n1) eqn:? ].
    all: try rewrite <- rev_alt in H; simpl in H.
    2: destruct (next_gate' l f (App1 u n :: acc)) eqn:res; try easy.
    6: destruct (next_gate' l f (App2 u n n0 :: acc)) eqn:res; try easy.
    14: destruct (next_gate' l f (App3 u n n0 n1 :: acc)) eqn:res; try easy.
    all: repeat destruct p.
    all: inversion H; subst; try rewrite <- does_not_reference_rev; auto.
    all: eapply IHl; try apply res; auto.
    all: intros q0 Hq0.
    all: simpl; apply andb_true_intro; split.
    all: try apply Hdnr; auto.
    all: apply negb_true_iff; repeat apply orb_false_intro; apply eqb_neq.
    all: intro; subst. 
    all: try (rewrite Heqb in Hq0; inversion Hq0). 
    all: try (rewrite Heqb0 in Hq0; inversion Hq0). 
    rewrite Heqb1 in Hq0; inversion Hq0. }
  intros ? ? ? ? ? ? ? H0 q Hq.
  eapply H; try apply H0; auto.
Qed.

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

Lemma propagate'_preserves_semantics : 
  forall {U dim} (l : gate_list U dim) 
    commute_rules cancel_rules n acc l' g eq 
   `{Equivalence (gate_list U dim) eq} 
   `{Proper _ (eq ==> eq ==> eq) (@app (gate_app U dim))},
  cancel_rules_correct g cancel_rules eq ->
  commute_rules_correct g commute_rules eq ->
  propagate' l commute_rules cancel_rules n acc = Some l' ->
  eq (rev acc ++ g :: l) l'.
Proof.
  intros U dim l com can n acc l' g eq equiv_pf mor_pf Hcan Hcom res.
  generalize dependent acc.
  generalize dependent l'.
  generalize dependent l.
  induction n; intros l l' acc res; try discriminate.
  simpl in res.
  destruct (try_rewrites l can) eqn:rewr1.
  inversion res; subst.
  rewrite rev_append_rev.
  apply mor_pf; try reflexivity.
  remember (fun l l' => eq (g :: l) l') as P.
  replace (eq (g :: l) g0) with (P l g0) by (subst; reflexivity).
  apply try_rewrites_preserves_property with (rules:=can); auto.
  intros r Hr l0 l' H0.
  specialize (Hcan r Hr _ _ H0). subst. assumption.
  destruct (try_rewrites2 l com) eqn:rewr2; try discriminate.
  destruct p.
  destruct (propagate' g1 com can n (rev_append g0 acc)) eqn:prop; try discriminate.
  inversion res; subst.
  apply IHn in prop.
  rewrite <- prop.
  rewrite rev_append_rev, rev_app_distr, rev_involutive.
  rewrite <- app_assoc. 
  apply mor_pf; try reflexivity.
  remember (fun l (p : gate_list U dim * gate_list U dim) => 
              let (l1,l2) := p in
              eq (g :: l) (l1 ++ g :: l2)) as P.
  replace (eq (g :: l) (g0 ++ g :: g1)) with (P l (g0,g1)) by (subst; reflexivity).
  apply try_rewrites2_preserves_property with (rules:=com); auto.
  intros r Hr l0 l1 l2 H0.    
  specialize (Hcom r Hr _ _ _ H0). subst. assumption.
Qed. 

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
  intros ? ? ? ? ? ? ? ? ? equiv_pf ? Hcan ? H.
  eapply propagate'_preserves_semantics in H.
  2: apply equiv_pf.
  3: apply Hcan.
  simpl in H. 
  all: auto.
Qed.  

Lemma remove_prefix_correct : forall {dim} (l pfx l' : gate_list G.U dim),
  remove_prefix l pfx (fun n => @G.match_gate n) = Some l' ->
  l =l= pfx ++ l'.
Proof.
  intros dim l pfx.
  generalize dependent l.
  induction pfx; intros l l' H.
  - inversion H; subst. reflexivity.
  - simpl in H. 
    destruct a; try discriminate.
    destruct (next_single_qubit_gate l n) eqn:nsqg; try discriminate.
    repeat destruct p.
    destruct (G.match_gate u u0) eqn:mg; try discriminate.
    apply G.match_gate_implies_eq in mg; simpl.
    rewrite <- (IHpfx _ _ H). 
    rewrite (nsqg_commutes _ _ _ _ _ nsqg).
    rewrite app_comm_cons, (cons_to_app _ g0).
    rewrite <- app_assoc.
    apply_app_congruence.
    unfold uc_equiv_l; simpl; rewrite mg; reflexivity.
    destruct (next_gate l (fun q : nat => (q =? n) || (q =? n0))) eqn:ng; try discriminate.
    repeat destruct p.
    destruct g1; try discriminate.
    bdestruct (n =? n1); bdestruct (n0 =? n2); 
    destruct (G.match_gate u u0) eqn:mg; try discriminate.
    subst. simpl in *.
    apply G.match_gate_implies_eq in mg.
    rewrite <- (IHpfx _ _ H). 
    specialize (next_gate_l1_does_not_reference _ _ _ _ _ ng) as dnr.
    apply next_gate_preserves_structure in ng; subst.
    rewrite app_comm_cons, (cons_to_app _ g0).
    rewrite (does_not_reference_commutes_app2 g0); auto.
    rewrite <- app_assoc.
    apply uc_app_congruence; reflexivity.
    apply dnr. bdestructΩ (n1 =? n1); auto.
    apply dnr. bdestructΩ (n2 =? n2). apply orb_true_intro; auto.
Qed.

(* Note that in general (l =l= l') does not imply (rev l =l= rev l'). *)
Lemma remove_prefix_respects_rev : forall {dim} (l pfx l' : gate_list G.U dim),
  remove_prefix l pfx (fun n => @G.match_gate n) = Some l' ->
  rev l =l= rev (pfx ++ l').
Proof.
  intros dim l pfx.
  generalize dependent l.
  induction pfx; intros l l' H.
  - inversion H; subst. reflexivity.
  - simpl in H. 
    destruct a; try discriminate.
    destruct (next_single_qubit_gate l n) eqn:nsqg; try discriminate.
    repeat destruct p.
    destruct (G.match_gate u u0) eqn:mg; try discriminate.
    apply G.match_gate_implies_eq in mg.
    simpl.
    rewrite <- (IHpfx _ _ H). 
    specialize (nsqg_l1_does_not_reference _ _ _ _ _ nsqg) as dnr.
    apply nsqg_preserves_structure in nsqg.
    subst. repeat rewrite rev_app_distr; simpl.
    repeat rewrite <- app_assoc.
    rewrite (does_not_reference_commutes_app1 _ u0).
    apply_app_congruence.
    unfold uc_equiv_l; simpl; rewrite mg; reflexivity.
    rewrite <- does_not_reference_rev; auto.
    destruct (next_gate l (fun q : nat => (q =? n) || (q =? n0))) eqn:ng; try discriminate.
    repeat destruct p.
    destruct g1; try discriminate.
    bdestruct (n =? n1); bdestruct (n0 =? n2); 
    destruct (G.match_gate u u0) eqn:mg; try discriminate.
    subst. simpl in *.
    apply G.match_gate_implies_eq in mg.
    rewrite <- (IHpfx _ _ H). 
    specialize (next_gate_l1_does_not_reference _ _ _ _ _ ng) as dnr.
    apply next_gate_preserves_structure in ng; subst.
    repeat rewrite rev_app_distr; simpl.
    repeat rewrite <- app_assoc.
    rewrite (does_not_reference_commutes_app2 (rev g0)).
    apply_app_congruence. reflexivity.
    rewrite <- does_not_reference_rev.
    apply dnr. bdestructΩ (n1 =? n1); auto.
    rewrite <- does_not_reference_rev.
    apply dnr. bdestructΩ (n2 =? n2). apply orb_true_intro; auto.
Qed.

Lemma remove_suffix_correct : forall {dim} (l sfx l' : gate_list G.U dim),
  remove_suffix l sfx (fun n => @G.match_gate n) = Some l' ->
  l =l= l' ++ sfx.
Proof.
  intros dim l sfx l' H.
  unfold remove_suffix in H.
  destruct (remove_prefix (rev_append l []) (rev_append sfx [])) eqn:rp.
  2: discriminate.
  repeat rewrite <- rev_alt in *.
  inversion H; subst; clear H.
  apply remove_prefix_respects_rev in rp.
  rewrite rev_app_distr, 2 rev_involutive in rp. 
  apply rp.
Qed.

(* Equivalence up to a phase. Exact equivalence is also easy to prove, but not used 
   in our development. *)
Lemma replace_pattern_sound : forall {dim} (l l' pat rep : gate_list G.U dim),
  pat ≅l≅ rep -> 
  replace_pattern l pat rep (fun n => @G.match_gate n) = Some l' -> 
  l ≅l≅ l'.
Proof.
  intros dim l l' pat rep H1 H2.
  unfold replace_pattern in H2.
  destruct (remove_prefix l pat) eqn:rem; try discriminate.
  apply remove_prefix_correct in rem.
  apply uc_equiv_cong_l in rem.
  inversion H2; subst.
  rewrite rem, H1. 
  reflexivity.
Qed.

Lemma equalb_correct : forall {dim} (l1 l2 : gate_list G.U dim),
  equalb l1 l2 (fun n => @G.match_gate n) = true ->
  l1 =l= l2.
Proof.
  intros dim l1 l2 H.
  unfold equalb in H.
  destruct (remove_prefix l1 l2 (fun n : nat => G.match_gate)) eqn:rp; try discriminate.
  destruct g; try discriminate.
  apply remove_prefix_correct in rp.
  rewrite app_nil_r in rp.
  apply rp.
Qed.

Lemma get_matching_prefix_correct : forall {dim} (l1 l2 pfx l1' l2': gate_list G.U dim),
  get_matching_prefix l1 l2 (fun n => @G.match_gate n) = (pfx, l1', l2') ->
  l1 =l= pfx ++ l1' /\ l2 =l= pfx ++ l2'.
Proof.
  assert (H : forall {dim} (l1 l2 pfx l1acc : gate_list G.U dim) blst n pfx' l1' l2',
              get_matching_prefix' l1 l2 pfx l1acc blst n (fun n => @G.match_gate n) 
                = (pfx', l1', l2') ->
              (forall q, negb (FSet.mem q blst) = true -> does_not_reference l1acc q = true) ->
              rev pfx ++ rev l1acc ++ l1 =l= pfx' ++ l1' /\ 
                rev pfx ++ l2 =l= pfx' ++ l2').
  { intros dim l1 l2 pfx l1acc blst n.
    generalize dependent blst.
    generalize dependent l1acc.
    generalize dependent pfx.
    generalize dependent l2.
    generalize dependent l1.
    induction n; intros l1 l2 pfx l1acc blst pfx' l1' l2' H Hl1acc; simpl in H.
    inversion H; subst.
    repeat rewrite <- rev_alt.
    rewrite rev_append_rev.
    split; reflexivity.
    destruct (next_gate l1 (fun q : nat => negb (FSet.mem q blst))) eqn:ng.
    repeat destruct p.
    specialize (next_gate_l1_does_not_reference _ _ _ _ _ ng) as Hg0.
    specialize (next_gate_preserves_structure _ _ _ _ _ ng) as ?; subst.
    destruct g1.
    all: try (inversion H; subst;
              repeat rewrite <- rev_alt;
              rewrite rev_append_rev;
              split; reflexivity).
    - apply next_gate_app1_returns_q in ng. 
      destruct (next_single_qubit_gate l2 n0) eqn:nsqg.
      repeat destruct p.
      apply nsqg_commutes in nsqg; rewrite nsqg.
      destruct (G.match_gate u u0) eqn:mg.
      + apply IHn in H as [H1 H2]; simpl in *.
        rewrite rev_append_rev, rev_app_distr, rev_involutive in H1.
        rewrite <- H1, <- H2.
        rewrite (cons_to_app _ g), (cons_to_app _ (g2 ++ g1)).
        split.
        rewrite (app_assoc g0).
        rewrite <- does_not_reference_commutes_app1.
        rewrite 2 (app_assoc (rev l1acc)).
        rewrite <- does_not_reference_commutes_app1.
        repeat rewrite app_assoc; reflexivity.
        rewrite <- does_not_reference_rev.
        apply Hl1acc; auto.
        apply Hg0; auto.
        apply_app_congruence.
        unfold uc_equiv_l; simpl.
        apply G.match_gate_implies_eq in mg.
        rewrite mg; reflexivity.
        intros q Hq.
        rewrite rev_append_rev.
        apply does_not_reference_app.
        apply andb_true_intro; split.
        rewrite <- does_not_reference_rev.
        apply Hg0; auto.
        apply Hl1acc; auto.
      + apply IHn in H as [H1 H2]; simpl in *.
        rewrite rev_append_rev, rev_app_distr, rev_involutive in H1.
        rewrite <- H1, <- H2, nsqg.
        repeat rewrite <- app_assoc.
        split; reflexivity.
        intros q Hq.
        apply negb_true_iff in Hq.
        apply FSetFacts.not_mem_iff in Hq.
        rewrite FSetFacts.add_iff in Hq. 
        apply Decidable.not_or in Hq as [Hq1 Hq2].
        rewrite rev_append_rev; simpl.
        apply andb_true_intro; split.
        bdestructΩ (n0 =? q); auto.
        apply does_not_reference_app.
        apply andb_true_intro; split.
        rewrite <- does_not_reference_rev.
        apply Hg0. apply negb_true_iff. apply FSetFacts.not_mem_iff. auto.
        apply Hl1acc. apply negb_true_iff. apply FSetFacts.not_mem_iff. auto.
      + apply IHn in H as [H1 H2]; simpl in *.
        rewrite rev_append_rev, rev_app_distr, rev_involutive in H1.
        rewrite <- H1, <- H2.
        repeat rewrite <- app_assoc.
        split; reflexivity.
        intros q Hq.
        apply negb_true_iff in Hq.
        apply FSetFacts.not_mem_iff in Hq.
        rewrite FSetFacts.add_iff in Hq. 
        apply Decidable.not_or in Hq as [Hq1 Hq2].
        rewrite rev_append_rev; simpl.
        apply andb_true_intro; split.
        bdestructΩ (n0 =? q); auto.
        apply does_not_reference_app.
        apply andb_true_intro; split.
        rewrite <- does_not_reference_rev.
        apply Hg0. apply negb_true_iff. apply FSetFacts.not_mem_iff. auto.
        apply Hl1acc. apply negb_true_iff. apply FSetFacts.not_mem_iff. auto.
    - apply next_gate_app2_returns_q in ng. 
      destruct (next_gate l2 (fun q : nat => (q =? n0) || (q =? n1))) eqn:ng2.
      repeat destruct p.
      destruct g3.
      + apply IHn in H as [H1 H2]; simpl in *.
        rewrite rev_append_rev, rev_app_distr, rev_involutive in H1.
        rewrite <- H1, <- H2.
        repeat rewrite <- app_assoc.
        split; reflexivity.
        intros q Hq.
        apply negb_true_iff in Hq.
        apply FSetFacts.not_mem_iff in Hq.
        rewrite FSetFacts.add_iff in Hq. 
        apply Decidable.not_or in Hq as [Hn0 Hq].
        rewrite FSetFacts.add_iff in Hq. 
        apply Decidable.not_or in Hq as [Hn1 Hq].
        rewrite rev_append_rev; simpl.
        apply andb_true_intro; split.
        bdestructΩ (n0 =? q); bdestructΩ (n1 =? q); auto.
        apply does_not_reference_app.
        apply andb_true_intro; split.
        rewrite <- does_not_reference_rev.
        apply Hg0. apply negb_true_iff. apply FSetFacts.not_mem_iff. auto.
        apply Hl1acc. apply negb_true_iff. apply FSetFacts.not_mem_iff. auto.
      + specialize (next_gate_l1_does_not_reference _ _ _ _ _ ng2) as dnr.
        apply next_gate_preserves_structure in ng2; subst.
        destruct (G.match_gate u u0 && (n0 =? n2) && (n1 =? n3) && ¬ (FSet.mem n0 blst) && ¬ (FSet.mem n1 blst)) eqn:cond.
        apply IHn in H as [H1 H2]; simpl in *.
        rewrite rev_append_rev, rev_app_distr, rev_involutive in H1.
        rewrite <- H1, <- H2.
        apply andb_prop in cond as [cond ?].
        apply andb_prop in cond as [cond ?].
        apply andb_prop in cond as [cond eq1].
        apply andb_prop in cond as [? eq2].
        apply Nat.eqb_eq in eq1; apply Nat.eqb_eq in eq2; subst.
        rewrite (cons_to_app _ g), (cons_to_app _ g1).
        split.
        rewrite (app_assoc g0).
        rewrite <- does_not_reference_commutes_app2.
        rewrite 2 (app_assoc (rev l1acc)).
        rewrite <- does_not_reference_commutes_app2.
        repeat rewrite app_assoc; reflexivity.
        rewrite <- does_not_reference_rev.
        apply Hl1acc; auto. 
        rewrite <- does_not_reference_rev.
        apply Hl1acc; auto.
        apply Hg0; auto.
        apply Hg0; auto.
        rewrite (app_assoc _ _ g1).
        rewrite <- does_not_reference_commutes_app2; auto.
        apply_app_congruence. reflexivity.
        apply dnr. bdestructΩ (n2 =? n2); auto.
        apply dnr. bdestructΩ (n3 =? n3). apply orb_true_intro; auto.
        intros q Hq.
        rewrite rev_append_rev.
        apply does_not_reference_app.
        apply andb_true_intro; split.
        rewrite <- does_not_reference_rev.
        apply Hg0; auto.
        apply Hl1acc; auto.
        apply IHn in H as [H1 H2]; simpl in *.
        rewrite rev_append_rev, rev_app_distr, rev_involutive in H1.
        rewrite <- H1, <- H2.
        repeat rewrite <- app_assoc.
        split; reflexivity.
        intros q Hq.
        apply negb_true_iff in Hq.
        apply FSetFacts.not_mem_iff in Hq.
        rewrite FSetFacts.add_iff in Hq. 
        apply Decidable.not_or in Hq as [Hn0 Hq].
        rewrite FSetFacts.add_iff in Hq. 
        apply Decidable.not_or in Hq as [Hn1 Hq].
        rewrite rev_append_rev; simpl.
        apply andb_true_intro; split.
        bdestructΩ (n0 =? q); bdestructΩ (n1 =? q); auto.
        apply does_not_reference_app.
        apply andb_true_intro; split.
        rewrite <- does_not_reference_rev.
        apply Hg0. apply negb_true_iff. apply FSetFacts.not_mem_iff. auto.
        apply Hl1acc. apply negb_true_iff. apply FSetFacts.not_mem_iff. auto.
      + apply IHn in H as [H1 H2]; simpl in *.
        rewrite rev_append_rev, rev_app_distr, rev_involutive in H1.
        rewrite <- H1, <- H2.
        repeat rewrite <- app_assoc.
        split; reflexivity.
        intros q Hq.
        apply negb_true_iff in Hq.
        apply FSetFacts.not_mem_iff in Hq.
        rewrite FSetFacts.add_iff in Hq. 
        apply Decidable.not_or in Hq as [Hn0 Hq].
        rewrite FSetFacts.add_iff in Hq. 
        apply Decidable.not_or in Hq as [Hn1 Hq].
        rewrite rev_append_rev; simpl.
        apply andb_true_intro; split.
        bdestructΩ (n0 =? q); bdestructΩ (n1 =? q); auto.
        apply does_not_reference_app.
        apply andb_true_intro; split.
        rewrite <- does_not_reference_rev.
        apply Hg0. apply negb_true_iff. apply FSetFacts.not_mem_iff. auto.
        apply Hl1acc. apply negb_true_iff. apply FSetFacts.not_mem_iff. auto.
      + apply IHn in H as [H1 H2]; simpl in *.
        rewrite rev_append_rev, rev_app_distr, rev_involutive in H1.
        rewrite <- H1, <- H2.
        repeat rewrite <- app_assoc.
        split; reflexivity.
        intros q Hq.
        apply negb_true_iff in Hq.
        apply FSetFacts.not_mem_iff in Hq.
        rewrite FSetFacts.add_iff in Hq. 
        apply Decidable.not_or in Hq as [Hn0 Hq].
        rewrite FSetFacts.add_iff in Hq. 
        apply Decidable.not_or in Hq as [Hn1 Hq].
        rewrite rev_append_rev; simpl.
        apply andb_true_intro; split.
        bdestructΩ (n0 =? q); bdestructΩ (n1 =? q); auto.
        apply does_not_reference_app.
        apply andb_true_intro; split.
        rewrite <- does_not_reference_rev.
        apply Hg0. apply negb_true_iff. apply FSetFacts.not_mem_iff. auto.
        apply Hl1acc. apply negb_true_iff. apply FSetFacts.not_mem_iff. auto. }
  intros dim l1 l2 pfx l1' l2' H0.
  apply H in H0.
  simpl in H0. apply H0.
  intros; reflexivity.
Qed.

(* TODO: can we prove that get_matching_prefix returns the maximal prefix, per our 
   definition of remove_prefix?

Definition is_prefix {dim} (l1 l2 : RzQ_ucom_l dim) :=
  exists l', remove_prefix l2 l1 = Some l'. 
Lemma get_matching_prefix_returns_maximum_prefix 
    : forall {dim} (l1 l2 : RzQ_ucom_l dim) pfx l1' l2',
  get_matching_prefix l1 l2 = (pfx, l1', l2') ->
  forall pfx', is_prefix pfx' l1 -> is_prefix pfx' l2 -> is_prefix pfx' pfx. 
*)

Fixpoint niter {dim} (l : gate_list G.U dim) n :=
  match n with
  | O => []
  | S n' => l ++ niter l n'
  end.

Lemma LCR_correct : forall {dim} n (p l c r : gate_list G.U dim) (opt : gate_list G.U dim -> gate_list G.U dim),
  (n > 2)%nat -> uc_well_typed_l p ->
  (forall p, uc_well_typed_l p -> opt p ≅l≅ p) ->
  (forall p, uc_well_typed_l p -> uc_well_typed_l (opt p)) -> 
  LCR p opt (fun n => @G.match_gate n) = Some (l, c, r) ->
  niter p n ≅l≅ (l ++ (niter c (n - 2)) ++ r).
Proof.
  intros dim n p l c r opt Hn WT opt_sound opt_WT H.
  destruct n; try lia.
  destruct n; try lia.
  clear Hn.
  unfold LCR in H.
  destruct (get_matching_prefix (opt p) (opt (opt p ++ opt p)) (fun n : nat => G.match_gate)) eqn:gmp.
  destruct p0.
  apply get_matching_prefix_correct in gmp as [? H1].
  destruct (remove_prefix (opt (opt p ++ opt p ++ opt p)) l0 (fun n : nat => G.match_gate)) eqn:H2; try discriminate.
  apply remove_prefix_correct in H2.
  destruct (remove_suffix g0 g (fun n : nat => G.match_gate)) eqn:rs; try discriminate.
  apply remove_suffix_correct in rs.
  rewrite rs in H2; clear rs.
  inversion H; subst; clear H.
  apply uc_equiv_cong_l in H1.
  apply uc_equiv_cong_l in H2.
  do 2 rewrite opt_sound in *; auto. 
  all: repeat (apply uc_well_typed_l_app; split); auto.
  assert (WTr: uc_well_typed_l r).
  apply uc_cong_l_implies_WT in H1.
  apply uc_well_typed_l_app in H1 as [_ ?]; auto.
  apply uc_well_typed_l_app; auto.
  clear - H1 H2 WTr.
  induction n.
  - simpl; rewrite app_nil_r.
    apply H1.
  - simpl in *; rewrite Nat.sub_0_r in IHn.
    rewrite IHn; clear IHn.
    assert (Hpl : (p ++ l) ≅l≅ (l ++ c)).
    { rewrite H1 in H2.
      rewrite 2 app_assoc in H2.
      unfold uc_cong_l, uc_cong in *.
      repeat rewrite list_to_ucom_append in H2.
      destruct H2 as [x H2]; simpl in H2.
      rewrite <- Mscale_mult_dist_r in H2.
      apply list_to_ucom_WT in WTr.
      apply uc_eval_unitary_iff in WTr as [_ WTr].
      assert (H: (uc_eval (list_to_ucom r))† = (uc_eval (list_to_ucom r))†) by reflexivity.
      eapply (f_equal2 Mmult) in H2.
      2: apply H.
      rewrite <- 2 Mmult_assoc in H2.
      rewrite WTr in H2.
      rewrite 2 Mmult_1_l in H2; auto with wf_db.
      exists x; auto. }
    repeat rewrite app_assoc. 
    rewrite Hpl.   
    reflexivity.
Qed.

(* Automation *)

Ltac unfold_uc_equiv_l :=
  unfold uc_equiv_l; simpl;
  repeat rewrite SKIP_id_r;
  repeat rewrite <- useq_assoc.

Ltac destruct_list_ops :=
  repeat match goal with 
  (* a few common cases *)
  | H : context[?m =? ?n] |- _ => 
      bdestruct (m =? n); subst; try discriminate
  | H : Some _ = Some _ |- _ => 
      inversion H; subst; clear H
  (* next_single_qubit_gate *)
  | H : next_single_qubit_gate _ _ = Some _ |- _ => 
      specialize (nsqg_preserves_structure _ _ _ _ _ H) as ?; subst;
      apply nsqg_l1_does_not_reference in H
  | H : context[next_single_qubit_gate ?l ?q] |- _ => 
      destruct (next_single_qubit_gate l q) as [p |] eqn:?; try discriminate;
      destruct p as [p ?]; destruct p as [? r];
      dependent destruction r; try discriminate
  (* last_single_qubit_gate *)
  | H : last_single_qubit_gate _ _ = Some _ |- _ => 
      specialize (lsqg_preserves_structure _ _ _ _ _ H) as ?; subst;
      apply lsqg_l2_does_not_reference in H
  | H : context[last_single_qubit_gate ?l ?q] |- _ => 
      destruct (last_single_qubit_gate l q) as [p |] eqn:?; try discriminate;
      destruct p as [p ?]; destruct p as [? r];
      dependent destruction r; try discriminate
  (* next_two_qubit_gate *)
  | H : next_two_qubit_gate _ _ = Some _ |- _ => 
      specialize (ntqg_preserves_structure _ _ _ _ _ _ _ H) as ?; subst;
      specialize (ntqg_returns_two_qubit_gate _ _ _ _ _ _ _ H) as ?;
      apply ntqg_l1_does_not_reference in H
  | H : context[next_two_qubit_gate ?l ?q] |- _ => 
      destruct (next_two_qubit_gate l q) as [p |] eqn:?; try discriminate;
      do 3 destruct p as [p ?]; destruct p as [? r];
      dependent destruction r; try discriminate
  end.

End UListRepresentationProps.