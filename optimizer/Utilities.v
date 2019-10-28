Require Import UnitarySem.
Require Import PI4GateSet.
Require Import List.

Local Open Scope ucom_scope.
Local Close Scope R_scope.
Local Close Scope C_scope.

(* The goal of this file is to provide utilities for writing optimizations. 
   This removes some of the repetitive parts of soundness proofs and (hopefully)
   makes prototyping optimizations faster. We currently have utility functions
   based on the types of program tranformations we observed in Nam et al.:

   - replace a (one-qubit) subcircuit with an equivalent subcircuit
   - given a set of rewrite rules, try to apply each until one succeeds
   - propagate a gate right and cancel when possible  *)

(** Rewrite with a single-qubit circuit equivalence **)

(* We restrict to single-qubit circuit equivalences for now because dealing
   with multi-qubit patterns is tedious with the list representation. For
   example, say that we are looking for the sub-circuit:
       C = [ H 0; H 2; CNOT 1 2; X 0 ]
   When searching for this sub-circuit, we need to keep in mind that these
   gates may be interspersed among other gates in the circuit in any order
   that respects dependence relationships. For example, the following program
   contains C, although it may not be obvious from casual inspection.
       [X 3; H 2; H 0; X 0; CNOT 0 3; CNOT 1 2]
*)

Definition single_qubit_pattern := list (PI4_Unitary 1).

Fixpoint single_qubit_pattern_to_program dim (pat : single_qubit_pattern) q : PI4_ucom_l dim :=
  match pat with
  | [] => []
  | u :: t => App1 u q :: (single_qubit_pattern_to_program dim t q)
  end. 

(* If the next sequence of gates applied to qubit q matches 'pat', then remove
   'pat' from the program. *)
Fixpoint remove_single_qubit_pattern {dim} (l : PI4_ucom_l dim) (q : nat) (pat : single_qubit_pattern) : option (PI4_ucom_l dim) :=
  match pat with
  | [] => Some l
  | u :: t =>
      match next_single_qubit_gate l q with
      | Some (l1, u', l2) =>
          if match_gate u u'
          then remove_single_qubit_pattern (l1 ++ l2) q t
          else None
      | _ => None
      end
  end.

(* If the next sequence of gates applied to qubit q matches 'pat', then replace
   'pat' with 'rep'. *)
Definition replace_single_qubit_pattern {dim} (l : PI4_ucom_l dim) (q : nat) (pat rep : single_qubit_pattern) : option (PI4_ucom_l dim) :=
  match (remove_single_qubit_pattern l q pat) with
  | Some l' => Some ((single_qubit_pattern_to_program dim rep q) ++ l')
  | None => None
  end.
     
(* Simple tests *)
Definition test : PI4_ucom_l 4 := H 1 :: X 0 :: CNOT 2 3 :: Z 0 :: H 0 :: Z 1 :: Z 2 :: CNOT 0 2 :: [].
Compute (replace_single_qubit_pattern test 0 (UPI4_X :: UPI4_Z :: []) (UPI4_H :: UPI4_H :: [])).
Compute (replace_single_qubit_pattern test 0 (UPI4_X :: UPI4_H :: []) (UPI4_Z :: UPI4_Z :: [])).

(* Proofs *)

Lemma remove_single_qubit_pattern_correct : forall {dim} (l l' : PI4_ucom_l dim) (q : nat) (pat : single_qubit_pattern),
  remove_single_qubit_pattern l q pat = Some l' ->
  l =l= (single_qubit_pattern_to_program dim pat q) ++ l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction pat; intros.
  - inversion H; subst. reflexivity.
  - simpl in H. 
    destruct (next_single_qubit_gate l q) eqn:nsqg; try easy.
    repeat destruct p.
    destruct (match_gate a p) eqn:Hmatch; try easy.
    rewrite match_gate_refl in Hmatch; subst.
    simpl.
    rewrite <- (IHpat _ _ H). 
    apply (nsqg_commutes _ _ _ _ _ nsqg).
Qed.

Lemma replace_single_qubit_pattern_sound : forall {dim} (l l' : PI4_ucom_l dim) (q : nat) (pat rep : single_qubit_pattern),
  single_qubit_pattern_to_program dim pat q =l= single_qubit_pattern_to_program dim rep q ->
  replace_single_qubit_pattern l q pat rep = Some l' ->
  l =l= l'.
Proof.
  intros.
  unfold replace_single_qubit_pattern in H0.
  destruct (remove_single_qubit_pattern l q pat) eqn:rem; try easy.
  apply remove_single_qubit_pattern_correct in rem.
  inversion H0; subst.
  rewrite rem.
  rewrite H.
  reflexivity.
Qed.

(* Equivalence up to a phase. *)
Lemma replace_single_qubit_pattern_sound' : forall {dim} (l l' : PI4_ucom_l dim) (q : nat) (pat rep : single_qubit_pattern),
  single_qubit_pattern_to_program dim pat q ≅l≅ single_qubit_pattern_to_program dim rep q ->
  replace_single_qubit_pattern l q pat rep = Some l' ->
  l ≅l≅ l'.
Proof.
  intros.
  unfold replace_single_qubit_pattern in H0.
  destruct (remove_single_qubit_pattern l q pat) eqn:rem; try easy.
  apply remove_single_qubit_pattern_correct in rem.
  apply uc_equiv_cong_l in rem.
  inversion H0; subst.
  rewrite rem. 
  rewrite H. 
  reflexivity.
Qed.

(** Apply a set of rewrite rules **)

(* Given a list of rewrite rules, try to apply each rule until one succeeds. 
   Return None if no rewrite succeeds. *)
Fixpoint try_rewrites {dim} l (rules : list (PI4_ucom_l dim -> option (PI4_ucom_l dim))) :=
  match rules with
  | [] => None
  | h :: t => match (h l) with
            | Some l' => Some l'
            | None => try_rewrites l t
            end
  end.

Lemma try_rewrites_preserves_property : 
  forall {dim} (l l' : PI4_ucom_l dim) 
          (P : PI4_ucom_l dim -> PI4_ucom_l dim -> Prop) 
          rules,
    (forall r, In r rules -> forall l l', r l = Some l' -> P l l') ->
    try_rewrites l rules = Some l' ->
    P l l'.
Proof.
  intros dim l l' P rules Hrules res.
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
Fixpoint try_rewrites2 {dim} l (rules : list (PI4_ucom_l dim -> option (PI4_ucom_l dim * PI4_ucom_l dim))) :=
  match rules with
  | [] => None
  | h :: t => match (h l) with
            | Some l' => Some l'
            | None => try_rewrites2 l t
            end
  end.

Lemma try_rewrites2_preserves_property :
  forall {dim} (l l1 l2 : PI4_ucom_l dim) 
          (P : PI4_ucom_l dim -> (PI4_ucom_l dim * PI4_ucom_l dim) -> Prop) 
          rules,
    (forall r, In r rules -> forall l l1 l2, r l = Some (l1,l2) -> P l (l1,l2)) ->
    try_rewrites2 l rules = Some (l1,l2) ->
    P l (l1,l2).
Proof.
  intros dim l l1 l2 P rules Hrules res.
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

(** Propagate & Cancel **)

(* Try to cancel a gate using a set of cancellation rules, allowing for
   commuting subcircuits described by a set of commutation rules. If
   no cancellation is found, return None. Otherwise return Some l'
   where l' is the modified list.
   

   l             : input list
   commute_rules : rules for commuting the gate right
   cancel_rules  : rules for canceling the gate
   n             : max number of iterations (we usually want n = length l)
*)
Fixpoint propagate {dim} (l : PI4_ucom_l dim) commute_rules cancel_rules n :=
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

Definition cancel_rules_correct {dim} (g : gate_app PI4_Unitary dim) rules :=
  forall r, 
  List.In r rules ->
  forall l l', (r l = Some l' -> l' =l= g :: l).

Definition commute_rules_correct {dim} (g : gate_app PI4_Unitary dim) rules :=
  forall r, 
  List.In r rules ->
  forall l l1 l2, (r l = Some (l1, l2) -> l1 ++ [g] ++ l2 =l= g :: l).

(* Useful for handling preconditions of *_rules_correct. *)
Ltac destruct_In :=
  repeat match goal with
  | H : In _ _ |- _ => inversion H; clear H
  end.

Lemma propagate_preserves_semantics : forall {dim} (l : PI4_ucom_l dim) commute_rules cancel_rules n l' g,
  cancel_rules_correct g cancel_rules ->
  commute_rules_correct g commute_rules ->
  propagate l commute_rules cancel_rules n = Some l' ->
  l' =l= g :: l.
Proof.
  intros dim l com can n l' g Hcan Hcom res.
  generalize dependent l'.
  generalize dependent l.
  induction n; intros l l' res; try discriminate.
  simpl in res.
  destruct (try_rewrites l can) eqn:rewr1.
  inversion res; subst.
  remember (fun l l' => l' =l= g :: l) as P.
  replace (l' =l= g :: l) with (P l l') by (subst; reflexivity).
  apply try_rewrites_preserves_property with (rules:=can).
  2: assumption.
  intros.
  specialize (Hcan r H _ _ H0). subst. assumption.
  destruct (try_rewrites2 l com) eqn:rewr2; try discriminate.
  destruct p.
  destruct (propagate p0 com can n) eqn:prop; try discriminate.
  inversion res; subst.
  apply IHn in prop.
  rewrite prop.
  rewrite cons_to_app.
  remember (fun l (p : PI4_ucom_l dim * PI4_ucom_l dim) => let (l1,l2) := p in l1 ++ [g] ++ l2 =l= g :: l) as P.
  replace (p ++ [g] ++ p0 =l= g :: l) with (P l (p,p0)) by (subst; reflexivity).
  apply try_rewrites2_preserves_property with (rules:=com).
  2: assumption.
  intros.    
  specialize (Hcom r H _ _ _ H0). subst. assumption.
Qed.  
