Require Import Phase.
Require Import UnitarySem.
Require Import Representations.
Require Import Equivalences.
Require Import Proportional.
Require Import List.
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


(***********************************)
(** Optimization: not propagation **)
(***********************************)

(* Propagate an X gate on qubit q as far right as possible, cancelling
   the gate if possible.
   
   This will return None if no cancellation is possible or (Some l') 
   where l' is the result of removing the appropriate X gate from l. *)
Fixpoint propagate_not {dim} (l : gate_list dim) (q : nat) : option (gate_list dim) :=
  match l with
  | (App1 fU_X q') :: t => 
      if q =? q' then Some t 
      else match propagate_not t q with
           | None => None
           | Some l' => Some ((_X q') :: l')
           end
  | (App2 fU_CNOT q1 q2) :: t => 
      if q =? q1 then None 
      else match propagate_not t q with
           | None => None
           | Some l' => Some ((_CNOT q1 q2) :: l')
           end
  | (App1 u q') :: t => 
      if (q =? q')
      then None
      else match propagate_not t q with
           | None => None
           | Some l' => Some ((App1 u q') :: l')
           end
  | _ => None
  end.

(* Call propagate_not on all X gates in the circuit. 
   
   The extra n argument is to help Coq recognize termination.
   We start with n = (length l), which is the maximum
   number of times that propagate_nots will be called. *)
Fixpoint propagate_nots {dim} (l : gate_list dim) (n: nat) : gate_list dim :=
  match n with
  | 0 => l
  | S n' => match l with
           | (App1 fU_X q) :: t => 
               match propagate_not t q with
               | None => (App1 fU_X q) :: (propagate_nots t n')
               | Some l' => propagate_nots l' n'
               end
           | h :: t => h :: (propagate_nots t n')
           | _ => l
           end
  end.

Definition rm_nots {dim} (l : gate_list dim) : gate_list dim := 
  propagate_nots l (List.length l).

(* Small test cases. *)
Definition q0 : nat := 0.
Definition q1 : nat := 1.
Definition q2 : nat := 2.
Definition example1 : gate_list 3 := (_X q0) :: (_H q1) :: (_X q0) :: (_X q1) :: (_CNOT q2 q1) :: (_X q1) :: [].
Compute (rm_nots example1).
Definition example2 : gate_list 3 := (_X q0) :: (_X q1) :: (_X q2) :: [].
Compute (rm_nots example2).

(* propagate_not preserves well-typedness. *)
Lemma propagate_not_WT : forall {dim} (l l' : gate_list dim) q,
  uc_well_typed_l l ->
  propagate_not l q = Some l' ->
  uc_well_typed_l l'.
Proof.
  intros.
  generalize dependent l'.
  induction l; try easy.
  simpl; intros.
  destruct a. 
  dependent destruction f; 
  (* u = H, Z, T, TDAG, P, PDAG *)
  try (destruct (q =? n); try easy;
       destruct (propagate_not l q); try easy;
       inversion H; inversion H0; subst;
       constructor; try apply IHl; easy).
  - (* u = X *)
    destruct (q =? n).
    + inversion H; inversion H0; subst. assumption.
    + destruct (propagate_not l q); try easy.
      inversion H; inversion H0; subst.
      constructor; try apply IHl; easy.
  - (* u = CNOT *)
    dependent destruction f.
    destruct (q =? n); try easy.
    destruct (propagate_not l q); try easy.
    inversion H; inversion H0; subst.
    constructor; try apply IHl; easy.
Qed.

(* propagate_not is semantics-preserving. *)
Lemma propagate_not_sound : forall {dim} (l l' : gate_list dim) q,
  q < dim ->
  propagate_not l q = Some l' ->
  l' =l= (App1 fU_X q) :: l.
Proof.
  intros.
  generalize dependent l'.
  induction l; try easy.
  simpl; intros.   
  destruct a.
  dependent destruction f;
  (* u = H, Z, T, TDAG, P, PDAG *)
  try (bdestruct (q =? n); try easy;
       destruct (propagate_not l q); try easy;
       inversion H0; subst;
       rewrite IHl with (l':=g); trivial;
       apply U_V_comm_l; lia).
  - (* u = X *)
    bdestruct (q =? n).
    + inversion H0; subst.
      unfold uc_equiv_l; simpl.
      rewrite <- useq_assoc.
      rewrite (useq_congruence _ uskip _ (list_to_ucom l')); 
      try rewrite uskip_id_l; 
      try reflexivity.
      symmetry; apply XX_id. 
      constructor; assumption.
    + destruct (propagate_not l q); inversion H0; subst.
      rewrite IHl with (l':=g); trivial.
      apply U_V_comm_l; lia.
  - (* u = CNOT *)
    dependent destruction f.
    bdestruct (q =? n); try easy.
    destruct (propagate_not l q); inversion H0; subst.
    rewrite IHl with (l':=g); trivial.
    bdestruct (q =? n0).
    + subst. 
      unfold uc_equiv_l; simpl.
      repeat rewrite <- useq_assoc.
      rewrite (useq_congruence (uapp2 U_CNOT n n0; uapp1 U_X n0) (uapp1 U_X n0; uapp2 U_CNOT n n0) _ (list_to_ucom l)); try reflexivity.
      symmetry; apply X_CNOT_comm.
    + unfold uc_equiv_l; simpl.
      repeat rewrite <- useq_assoc.
      rewrite (useq_congruence (uapp2 U_CNOT n n0; uapp1 U_X q) (uapp1 U_X q; uapp2 U_CNOT n n0) _ (list_to_ucom l)); try reflexivity.
      symmetry; apply U_CNOT_comm; assumption.
Qed.   

(* propagate_nots is semantics-preserving. *)
Lemma propagate_nots_sound : forall {dim} (l : gate_list dim) n, 
  uc_well_typed_l l -> l =l= propagate_nots l n.
Proof.
  intros.
  generalize dependent l.
  induction n; try easy.
  intros l WT.
  destruct l; try easy.
  destruct g.
  inversion WT; subst.
  simpl.
  dependent destruction f;
  (* u = H, Z, T, TDAG, P, PDAG *)
  try (apply (cons_congruence _ l (propagate_nots l n));
       apply IHn; assumption).
  (* u = X *)
  - specialize (@propagate_not_sound dim) as H4.
    remember (propagate_not l n0) as x.
    destruct x.
    + symmetry in Heqx.
      specialize (H4 l g n0 H1 Heqx).
      rewrite <- H4.
      apply IHn.
      apply (propagate_not_WT l g n0); assumption.
    + apply (cons_congruence _ l (propagate_nots l n));
      apply IHn; assumption.
  (* u = CNOT *)
  - inversion WT; subst. 
    apply (cons_congruence _ l (propagate_nots l n)).
    apply IHn; assumption.
Qed.

(* rm_nots is semantics-preserving. 
   
   The well-typedness constraint is required because rm_nots can actually
   return a well-typed circuit given a circuit that is not well-typed.
     ==> Consider the program X 4; X 4 where dim = 3
   The output of the denotation function may change in this case. 
*)
Lemma rm_nots_sound : forall {dim} (l : gate_list dim), 
  uc_well_typed_l l -> l =l= rm_nots l.
Proof.
  intros dim l WT.
  unfold rm_nots.
  rewrite <- propagate_nots_sound.
  reflexivity.
  assumption.
Qed.


(*****************************************************************)
(** Optimization: rewrite w/ a single-qubit circuit equivalence **)
(*****************************************************************)

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

Definition single_qubit_pattern := list (fUnitary 1).

Fixpoint single_qubit_pattern_to_program {dim} (pat : single_qubit_pattern) q : gate_list dim :=
  match pat with
  | [] => []
  | u :: t => App1 u q :: (single_qubit_pattern_to_program t q)
  end. 

(* If the next sequence of gates applied to qubit q matches 'pat', then remove
   'pat' from the program. *)
Fixpoint remove_single_qubit_pattern {dim} (l : gate_list dim) (q : nat) (pat : single_qubit_pattern) : option (gate_list dim) :=
  match pat with
  | [] => Some l
  | u :: t =>
      match next_single_qubit_gate l q with
      | Some (u', l') =>
          if match_gate u u'
          then remove_single_qubit_pattern l' q t
          else None
      | _ => None
      end
  end.

(* If the next sequence of gates applied to qubit q matches 'pat', then replace
   'pat' with 'rep'. *)
Definition replace_single_qubit_pattern {dim} (l : gate_list dim) (q : nat) (pat rep : single_qubit_pattern) : option (gate_list dim) :=
  match (remove_single_qubit_pattern l q pat) with
  | Some l' => Some ((single_qubit_pattern_to_program rep q) ++ l')
  | None => None
  end.
     
(* Simple tests *)
Definition test : gate_list 4 := (_H 1) :: (_X 0) :: (_CNOT 2 3) :: (_Z 0) :: (_H 0) :: (_Z 1) :: (_Z 2) :: (_CNOT 0 2) :: [].
Compute (next_single_qubit_gate test 0).
Compute (next_single_qubit_gate test 1).
Compute (next_single_qubit_gate test 2).
Compute (next_two_qubit_gate test 2).
Compute (next_two_qubit_gate test 3).
Compute (next_single_qubit_gate test 4).
Compute (replace_single_qubit_pattern test 0 (fU_X :: fU_PI4 4 :: []) (fU_H :: fU_H :: [])).
Compute (replace_single_qubit_pattern test 0 (fU_X :: fU_H :: []) (fU_PI4 4:: fU_PI4 4 :: [])).

Lemma remove_single_qubit_pattern_correct : forall {dim} (l l' : gate_list dim) (q : nat) (pat : single_qubit_pattern),
  remove_single_qubit_pattern l q pat = Some l' ->
  l =l= (single_qubit_pattern_to_program pat q) ++ l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction pat; intros.
  - inversion H; subst. reflexivity.
  - simpl in H. 
    remember (next_single_qubit_gate l q) as next_gate.
    symmetry in Heqnext_gate.
    destruct next_gate; try easy.
    destruct p. 
    remember (match_gate a f) as gate_match.
    destruct gate_match; try easy.
    symmetry in Heqgate_match.
    rewrite match_gate_refl in Heqgate_match; subst.
    simpl.
    rewrite <- (IHpat _ _ H). 
    apply (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
Qed.

Lemma remove_single_qubit_pattern_correct' : forall {dim} (l l' : gate_list dim) (q : nat) (pat : single_qubit_pattern),
  remove_single_qubit_pattern l q pat = Some l' ->
  l ≅l≅ ((single_qubit_pattern_to_program pat q) ++ l').
Proof.
  exists 0%R. rewrite eulers0. rewrite Mscale_1_l.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction pat; intros.
  - inversion H; subst. reflexivity.
  - simpl in H. 
    remember (next_single_qubit_gate l q) as next_gate.
    symmetry in Heqnext_gate.
    destruct next_gate; try easy.
    destruct p. 
    remember (match_gate a f) as gate_match.
    destruct gate_match; try easy.
    symmetry in Heqgate_match.
    rewrite match_gate_refl in Heqgate_match; subst.
    simpl.
    rewrite <- (IHpat _ _ H). 
    apply (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
Qed.

Lemma replace_single_qubit_pattern_sound : forall {dim} (l l' : gate_list dim) (q : nat) (pat rep : single_qubit_pattern),
  @uc_equiv_l dim (single_qubit_pattern_to_program pat q) (single_qubit_pattern_to_program rep q) ->
  replace_single_qubit_pattern l q pat rep = Some l' ->
  l =l= l'.
Proof.
  intros.
  unfold replace_single_qubit_pattern in H0.
  remember (remove_single_qubit_pattern l q pat) as remove_pat.
  destruct remove_pat; try easy.
  symmetry in Heqremove_pat.
  apply remove_single_qubit_pattern_correct in Heqremove_pat.
  inversion H0; subst.
  rewrite Heqremove_pat.
  rewrite H.
  reflexivity.
Qed.

Lemma replace_single_qubit_pattern_sound' : forall {dim} (l l' : gate_list dim) (q : nat) (pat rep : single_qubit_pattern),
  @uc_cong_l dim (single_qubit_pattern_to_program pat q) (single_qubit_pattern_to_program rep q) ->
  replace_single_qubit_pattern l q pat rep = Some l' ->
  l ≅l≅ l'.
Proof.
  intros.
  unfold replace_single_qubit_pattern in H0.
  remember (remove_single_qubit_pattern l q pat) as remove_pat.
  destruct remove_pat; try easy.
  symmetry in Heqremove_pat.
  apply remove_single_qubit_pattern_correct' in Heqremove_pat.
  inversion H0; subst.
  rewrite Heqremove_pat. rewrite H. reflexivity.
Qed.

(* TODO: We might also want to prove something along the lines of: the resulting
   program contains 'rep'. *)

(* Given a list of rewrite rules, try to apply each rule until one succeeds. 
   Return None if no rewrite succeeds. *)
Fixpoint try_rewrites {dim} l (rules : list (gate_list dim -> option (gate_list dim))) :=
  match rules with
  | [] => None
  | h :: t => match (h l) with
            | Some l' => Some l'
            | None => try_rewrites l t
            end
  end.

Lemma try_apply_rewrites_sound : forall {dim} (l l' : gate_list dim) rules,
  (forall r, In r rules -> (forall l l', r l = Some l' -> l =l= l')) ->
  try_rewrites l rules = Some l' ->
  l =l= l'.
Proof.
  intros.
  induction rules.
  - inversion H0.
  - simpl in H0.
    remember (a l) as al. 
    destruct al; inversion H0; subst.
    + symmetry in Heqal.
      assert (In a (a :: rules)) by (apply in_eq).
      apply (H a H1 l l' Heqal).
    + apply IHrules; try assumption.
      intros.
      apply (H r).
      apply in_cons; assumption.
      assumption.
Qed.

Lemma try_apply_rewrites_sound_cong : forall {dim} (l l' : gate_list dim) rules,
  (forall r, In r rules -> (forall l l', r l = Some l' -> l ≅l≅ l')) ->
  try_rewrites l rules = Some l' ->
  l ≅l≅ l'.
Proof.
  intros.
  induction rules.
  - inversion H0.
  - simpl in H0.
    remember (a l) as al. 
    destruct al; inversion H0; subst.
    + symmetry in Heqal.
      assert (In a (a :: rules)) by (apply in_eq).
      apply (H a H1 l l' Heqal).
    + apply IHrules; try assumption.
      intros.
      apply (H r).
      apply in_cons; assumption.
      assumption.
Qed.


(*******************************************)
(** Optimization: hadamard gate reduction **)
(*******************************************)

(** CURRENTLY NOT VERIFIED **)

(* This optimization pass reduces the number of H gates in a program
   using a variety of rewrite rules. *)

(* Hadamard Reduction Optimization
   
   Try to apply each the following equivalences to c. If one
   of the equivalences applies, then return the circuit resulting from
   the appropriate substitution.

   #1  - H q; P q; H q ≡ P† q; H q; P† q 
   #2  - H q; P† q; H q ≡ P q; H q; P q 
   #3a - H q1; H q2; CNOT q1 q2; H q1; H q1 ≡ CNOT q2 q1 
   #3b - H q2; H q1; CNOT q1 q2; H q1; H q2 ≡ CNOT q2 q1 
   #4  - H q2; P q2; CNOT q1 q2; P† q2; H q2 ≡ P† q2; CNOT q1 q2; P q2 
   #5  - H q2; P† q2; CNOT q1 q2; P q2; H q2 ≡ P q2; CNOT q1 q2; P† q2 
*)

Definition apply_H_equivalence1 {dim} q (l : gate_list dim) := 
  replace_single_qubit_pattern l q 
    (fU_H  :: fU_P :: fU_H :: []) 
    (fU_PDAG :: fU_H :: fU_PDAG :: []).

Definition apply_H_equivalence2 {dim} q (l : gate_list dim) := 
  replace_single_qubit_pattern l q 
    (fU_H :: fU_PDAG :: fU_H :: []) 
    (fU_P :: fU_H :: fU_P :: []).

Definition apply_H_equivalence3 {dim} q (l : gate_list dim) := 
  match (next_single_qubit_gate l q) with
  | Some (fU_H, l1) =>
      match (next_two_qubit_gate l1 q) with
      | Some (l2, m, n, l3) => 
          match (next_single_qubit_gate l3 q) with
          | Some (fU_H, l4) =>
              if (q =? m)
              (* case 3a *)
              then match (next_single_qubit_gate (rev l2) n) with
                   | Some (fU_H, l5) => 
                       match (next_single_qubit_gate l4 n) with
                       | Some (fU_H, l6) => 
                           Some ((rev l5) ++ [_CNOT n m] ++ l6)
                       | _ => None
                       end
                   | _ => None
                   end
              (* case 3b *)
              else match (next_single_qubit_gate (rev l2) m) with
                   | Some (fU_H, l5) => 
                       match (next_single_qubit_gate l4 m) with
                       | Some (fU_H, l6) => 
                           Some ((rev l5) ++ [_CNOT n m] ++ l6)
                       | _ => None
                       end
                   | _ => None
                   end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition apply_H_equivalence4 {dim} q (l : gate_list dim) :=
  match (remove_single_qubit_pattern l q (fU_H :: fU_P :: [])) with
  | None => None
  | Some l1 =>
      match (next_two_qubit_gate l1 q) with
      | None => None
      | Some (l2, q1, q2, l3) =>
          if q =? q2 
          then match (remove_single_qubit_pattern l3 q (fU_PDAG :: fU_H :: [])) with
               | None => None
               | Some l4 =>
                   Some (l2 ++ (_PDAG q2 :: _CNOT q1 q2 :: _P q2 :: []) ++ l4)
               end
          else None
      end
  end.

Definition apply_H_equivalence5 {dim} q (l : gate_list dim) :=
  match (remove_single_qubit_pattern l q (fU_H :: fU_PDAG :: [])) with
  | Some l1 =>
      match (next_two_qubit_gate l1 q) with
      | Some (l2, q1, q2, l3) =>
          if q =? q2 
          then match (remove_single_qubit_pattern l3 q (fU_P :: fU_H :: [])) with
               | Some l4 =>
                   Some (l2 ++ (_P q2 :: _CNOT q1 q2 :: _PDAG q2 :: []) ++ l4)
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition apply_H_equivalence {dim} (l : gate_list dim) (q : nat) : option (gate_list dim) :=
  try_rewrites l ((apply_H_equivalence1 q) :: (apply_H_equivalence2 q) :: (apply_H_equivalence3 q) :: (apply_H_equivalence4 q) :: (apply_H_equivalence5 q) :: []).

(* For each H gate, try to apply a rewrite rule. If some rewrite rule
   succeeds, then make the recursive call on the circuit returned by
   apply_equivalence. 
 
   The n argument is needed to convince Coq of termination. We start with
   n = 2 * (length l), which is an overapproximation of the necessary
   number of iterations. Note that the starting value of n is greater than
   (length l) because apply_equivalence will sometimes return a program
   of the same size as the input program.

   If we wanted to do a proper proof of termination, we would need to show
   that each call to apply_H_equivalence (strictly) reduces the number of H 
   gates in the program. *)
Fixpoint apply_H_equivalences {dim} (l : gate_list dim) (n: nat) : gate_list dim :=
  match n with
  | 0 => l
  | S n' => 
      match l with
      | [] => []
      | (App1 fU_H q) :: t => 
          match apply_H_equivalence l q with
          | None => (_H q) :: (apply_H_equivalences t n')
          | Some l' => apply_H_equivalences l' n'
          end
      | g :: t => g :: (apply_H_equivalences t n')
      end
  end.

Definition hadamard_reduction {dim} (l : gate_list dim) : gate_list dim := 
  apply_H_equivalences l (2 * (length l)).


(* New C_field_simplify/nonzero that deal with Ci *)
Ltac nonzero :=
  repeat split;
   try match goal with
       | |- not (@eq _ ?x (RtoC (IZR Z0))) => apply RtoC_neq
       | |- not (@eq _ Ci (RtoC (IZR Z0))) => apply C0_snd_neq; simpl
       end;
   repeat
    match goal with
    | |- not (@eq _ (sqrt ?x) (IZR Z0)) => apply sqrt_neq_0_compat
    | |- not (@eq _ (Rinv ?x) (IZR Z0)) => apply Rinv_neq_0_compat
    end; match goal with
         | |- not (@eq _ _ _) => lra
         | |- Rlt _ _ => lra
         end.

Ltac C_field_simplify := repeat field_simplify_eq [ Csqrt2_sqrt Csqrt2_inv Ci2].

Lemma apply_H_equivalence1_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence1 q l = Some l' ->
  l ≅l≅ l'. 
Proof.
  intros.
  eapply replace_single_qubit_pattern_sound'.
  2 : { apply H. }
  exists (PI / 4)%R.
  unfold uc_eval, ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try (remove_zero_gates; trivial).
  Msimpl. 
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  assert (hadamard × phase_shift (2 * PI / 4) × hadamard = (Cexp (PI / 4)%R) .* (phase_shift (6 * PI / 4) × hadamard  × phase_shift (6 * PI / 4))).
  { solve_matrix. 
    all: autorewrite with Cexp_db.
    all: C_field_simplify; try nonzero.
  }
  rewrite H1.
  repeat rewrite Mscale_mult_dist_l.
  repeat rewrite Mscale_kron_dist_r.  
  rewrite Mscale_kron_dist_l.
  reflexivity.
  rewrite Mscale_0_r.
  reflexivity.
Qed.

(* TODO: remove *)
Hint Rewrite Cexp_PIm4 : Cexp_db.

Lemma apply_H_equivalence2_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence2 q l = Some l' ->
  l ≅l≅ l'.
Proof. 
  intros.
  eapply replace_single_qubit_pattern_sound'; try apply H.
  exists (- PI / 4)%R.
  unfold uc_eval, ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try (remove_zero_gates; trivial).
  - Msimpl.
    restore_dims_strong; repeat rewrite kron_mixed_product.
    Msimpl.
    assert (hadamard × phase_shift (6 * PI / 4) × hadamard = (Cexp (- PI / 4)%R) .* phase_shift (2 * PI / 4) × hadamard × phase_shift (2 * PI / 4)).
    { solve_matrix. 
      all: autorewrite with Cexp_db.
      all: C_field_simplify; try nonzero.
    }
    rewrite H1.
    repeat rewrite Mscale_mult_dist_l.
    repeat rewrite Mscale_kron_dist_r.
    rewrite Mscale_kron_dist_l.
    reflexivity.
  - rewrite Mscale_0_r. reflexivity.
Qed.

Lemma apply_H_equivalence3_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence3 q l = Some l' ->
  l ≅l≅ l'.
Proof.
Admitted.

Lemma apply_H_equivalence4_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence4 q l = Some l' ->
  l ≅l≅ l'.
Proof.
Admitted.

Lemma apply_H_equivalence5_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence5 q l = Some l' ->
  l ≅l≅ l'.
Proof.
Admitted.

Lemma apply_H_equivalence_sound : forall {dim} (l l' : gate_list dim) q,
  apply_H_equivalence l q = Some l' -> 
  l ≅l≅ l'.
Proof. 
  unfold apply_H_equivalence.
  intros dim l l' q.
  apply try_apply_rewrites_sound_cong.
  intros. 
  inversion H.
  subst; apply (apply_H_equivalence1_sound _ _ _ H0).
  inversion H1. 
  subst; apply (apply_H_equivalence2_sound _ _ _ H0). 
  inversion H2. 
  subst; apply (apply_H_equivalence3_sound _ _ _ H0). 
  inversion H3. 
  subst; apply (apply_H_equivalence4_sound _ _ _ H0). 
  inversion H4. 
  subst; apply (apply_H_equivalence5_sound _ _ _ H0). 
  inversion H5.
Qed.

Lemma apply_H_equivalences_sound: forall {dim} (l : gate_list dim) n, 
  l ≅l≅ apply_H_equivalences l n.
Proof. 
  intros.
  generalize dependent l.
  induction n; try easy.
  intros.
  destruct l; try easy.
  destruct g; simpl.
  - dependent destruction f;
    remember (apply_H_equivalence (App1 fU_H n0 :: l) n0) as res; symmetry in Heqres;
    destruct res;
    rewrite <- IHn;
    try apply (apply_H_equivalence_sound _ _ _ Heqres);
    reflexivity.
  - rewrite <- IHn; reflexivity.
Qed.

Lemma hadamard_reduction_sound: forall {dim} (l : gate_list dim), 
  l ≅l≅ hadamard_reduction l.
Proof. intros. apply apply_H_equivalences_sound. Qed.

(* TODO: We should also be able to prove that the Hadamard reduction optimization 
   reduces the number of Hadamard gates in the program. *)


(*******************************************************)
(** Optimization: simple cancellation and combination **)
(*******************************************************)

(* 'cancel_gates_simple' is my first pass at the full one- and two-qubit 
   gate cancellation routines. This function cancels unitaries adjacent to 
   their inverses and combines adjacent z-rotation gates. It does not
   consider any commutation relationships. 

   The extra n argument is to help Coq recognize termination.
   We start with n = (length l). *)

Fixpoint cancel_gates_simple' {dim} (l acc : gate_list dim) (n: nat) : gate_list dim :=
  match n with
  | 0 => (rev acc) ++ l
  | S n' => match l with
           | [] => rev acc
           | App1 fU_H q :: t => 
               match next_single_qubit_gate t q with
               | Some (fU_H, t') => cancel_gates_simple' t' acc n'
               | _ => cancel_gates_simple' t (_H q :: acc) n'
               end
           | App1 fU_X q :: t => 
               match next_single_qubit_gate t q with
               | Some (fU_X, t') => cancel_gates_simple' t' acc n'
               | _ => cancel_gates_simple' t (_X q :: acc) n'
               end
           | App1 (fU_PI4 k) q :: t => 
               match next_single_qubit_gate t q with
               | Some (fU_PI4 k', t') => 
                 let k'' := (k + k')%Z in
                 if (k'' =? 8)%Z then cancel_gates_simple' t' acc n' else 
                 if (k'' <? 8)%Z then cancel_gates_simple' (_PI4 k'' q :: t') acc n'
                 else cancel_gates_simple' (_PI4 (k'' - 8)%Z q :: t') acc n' 
               | _ => cancel_gates_simple' t (_PI4 k q :: acc) n'
               end
           | App2 fU_CNOT q1 q2 :: t => 
               match next_two_qubit_gate t q1 with
               | Some (l1, q1', q2', l2) => 
                   if (q1 =? q1') && (q2 =? q2') && (does_not_reference l1 q2)
                   then cancel_gates_simple' (l1 ++ l2) acc n'
                   else cancel_gates_simple' t (_CNOT q1 q2 :: acc) n'
               | _ => cancel_gates_simple' t (_CNOT q1 q2 :: acc) n'
               end
           | _ => [] (* impossible case for well-formed gate_list *)
           end
  end.

Definition cancel_gates_simple {dim} (l : gate_list dim) : gate_list dim := 
  cancel_gates_simple' l [] (List.length l).


(* Useful identities. *)
   
(* TODO: These proofs are all just copied & pasted from each other, so
   there is definitely some cleaning that needs to be done. Once they're
   cleaned up, they should be moved to Equivalences.v *)

Lemma H_H_cancel : forall {dim} (l : gate_list dim) q, 
  q < dim -> _H q :: _H q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try lia.
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  replace (hadamard × hadamard) with (I (2 ^ 1)) by solve_matrix.
  Msimpl.
  unify_pows_two.
  replace (q + 1 + (dim - 1 - q)) with dim by lia.
  apply Mmult_1_r; auto with wf_db.
Qed.

Lemma X_X_cancel : forall {dim} (l : gate_list dim) q, 
  q < dim -> _X q :: _X q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try lia.
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  replace (σx × σx) with (I (2 ^ 1)) by solve_matrix.
  Msimpl.
  unify_pows_two.
  replace (q + 1 + (dim - 1 - q)) with dim by lia.
  apply Mmult_1_r; auto with wf_db.
Qed.

(* Not used *)
Lemma Z_Z_cancel : forall {dim} (l : gate_list dim) q, 
  q < dim -> _Z q :: _Z q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try lia.
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  replace (phase_shift (4 * PI / 4) × phase_shift (4 * PI / 4)) with (I (2 ^ 1)).
  2:{ solve_matrix. autorewrite with Cexp_db. lca. }
  Msimpl.
  unify_pows_two.
  replace (q + 1 + (dim - 1 - q)) with dim by lia.
  apply Mmult_1_r; auto with wf_db.
Qed.

Lemma PI4_PI4_combine : forall {dim} (l : gate_list dim) q k k', 
  _PI4 k q :: _PI4 k' q :: l =l= _PI4 (k+k') q :: l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try (remove_zero_gates; trivial).
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite phase_mul. 
  repeat rewrite <- Rmult_div_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite plus_IZR.
  rewrite Rplus_comm.
  reflexivity.
Qed.

Lemma PI4_PI4_m8_combine : forall {dim} (l : gate_list dim) q k k', 
  _PI4 k q :: _PI4 k' q :: l =l= _PI4 (k+k'-8) q :: l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestruct (q + 1 <=? dim); try (remove_zero_gates; trivial).
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite phase_mul. 
  repeat rewrite <- Rmult_div_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- plus_IZR.
  repeat rewrite Rmult_div_assoc.
  rewrite phase_PI4_m8.
  rewrite Zplus_comm.
  reflexivity.
Qed.
  
Lemma PI4_PI4_cancel : forall {dim} (l : gate_list dim) q k k', 
  q < dim -> 
  (k + k' = 8)%Z ->
  _PI4 k q :: _PI4 k' q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestructΩ (q + 1 <=? dim); try (remove_zero_gates; trivial).
  rewrite Mmult_assoc.
  restore_dims_strong; repeat rewrite kron_mixed_product.
  Msimpl.
  rewrite phase_mul. 
  repeat rewrite <- Rmult_div_assoc.
  rewrite <- Rmult_plus_distr_r.
  rewrite <- plus_IZR.
  repeat rewrite Rmult_div_assoc.
  rewrite Zplus_comm.
  rewrite H0.
  replace (8 * PI / 4)%R with (2 * PI)%R by lra.
  rewrite phase_2pi.
  Msimpl. replace (2 ^ q * 2 * 2 ^ (dim - 1 - q))%nat with (2^dim) by unify_pows_two.
  Msimpl.
  reflexivity.
Qed.

Lemma PI4_0_rem : forall {dim} (l : gate_list dim) q, 
  q < dim -> _PI4 0 q :: l =l= l.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  unfold ueval1, pad; simpl.
  bdestructΩ (q + 1 <=? dim); try (remove_zero_gates; trivial).
  unfold Rdiv. repeat rewrite Rmult_0_l. 
  rewrite phase_0.
  Msimpl. replace (2 ^ q * 2 * 2 ^ (dim - 1 - q))%nat with (2^dim) by unify_pows_two.
  Msimpl.
  reflexivity.
Qed.

  
Lemma CNOT_CNOT_cancel : forall {dim} (l1 l2 : gate_list dim) q1 q2, 
  q1 < dim -> q2 < dim -> q1 <> q2 -> l1 ++ [_CNOT q1 q2] ++ [_CNOT q1 q2] ++ l2 =l= l1 ++ l2.
Proof.
  intros.
  unfold uc_equiv_l, uc_equiv; simpl.
  rewrite list_to_ucom_append; simpl.
  unfold ueval_cnot, pad; simpl.
  bdestruct (q3 <? q4).
  - bdestruct (q3 + S (q4 - q3 - 1 + 1) <=? dim); try lia.
    replace (2 ^ (q4 - q3)) with (2 ^ (q4 - q3 - 1) * 2) by unify_pows_two.
    repeat rewrite <- id_kron.
    repeat rewrite <- kron_assoc.
    rewrite (Mmult_assoc (uc_eval (list_to_ucom l2))). 
    restore_dims_strong; repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite Mmult_plus_distr_r. 
    repeat rewrite Mmult_plus_distr_l.
    restore_dims_strong; repeat rewrite kron_mixed_product.
    Msimpl.
    replace (∣1⟩⟨1∣ × ∣1⟩⟨1∣) with (∣1⟩⟨1∣) by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
    remove_zero_gates.
    rewrite Mplus_0_l. 
    rewrite Mplus_0_r.
    replace (σx × σx) with (I 2) by solve_matrix.
    repeat rewrite kron_assoc.
    repeat rewrite id_kron.
    unify_pows_two.
    replace (2 ^ (q4 - q3 - 1 + 1 + 1)) with (2 * 2 ^ (q4 - q3 - 1 + 1)) by unify_pows_two.
    rewrite <- kron_plus_distr_r.
    replace (∣1⟩⟨1∣ .+ ∣0⟩⟨0∣) with (I 2) by solve_matrix.
    Msimpl.
    restore_dims_strong.
    Msimpl.
    replace (2 ^ q3 * (2 * 2 ^ (q4 - q3 - 1 + 1) * 2 ^ (dim - S (q4 - q3 - 1 + 1) - q3))) with (2 ^ dim) by unify_pows_two.
    rewrite Mmult_1_r; auto with wf_db.
    rewrite list_to_ucom_append; reflexivity.
  - bdestruct (q4 <? q3); try lia.
    bdestruct (q4 + S (q3 - q4 - 1 + 1) <=? dim); try lia.
    replace (2 ^ (q3 - q4)) with (2 * 2 ^ (q3 - q4 - 1)) by unify_pows_two.
    repeat rewrite <- id_kron.
    repeat rewrite <- kron_assoc.
    rewrite (Mmult_assoc (uc_eval (list_to_ucom l2))). 
    restore_dims_strong; repeat rewrite kron_mixed_product.
    Msimpl.
    rewrite Mmult_plus_distr_r. 
    repeat rewrite Mmult_plus_distr_l.
    restore_dims_strong; repeat rewrite kron_mixed_product.
    Msimpl.
    replace (∣1⟩⟨1∣ × ∣1⟩⟨1∣) with (∣1⟩⟨1∣) by solve_matrix.
    replace (∣1⟩⟨1∣ × ∣0⟩⟨0∣) with (@Zero 2 2) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣1⟩⟨1∣) with (@Zero 2 2) by solve_matrix.
    replace (∣0⟩⟨0∣ × ∣0⟩⟨0∣) with (∣0⟩⟨0∣) by solve_matrix.
    remove_zero_gates.
    rewrite Mplus_0_l. 
    rewrite Mplus_0_r.
    replace (σx × σx) with (I 2) by solve_matrix.
    repeat rewrite id_kron.
    unify_pows_two.
    replace (2 ^ (q3 - q4 - 1 + 1 + 1)) with (2 ^ (S (q3 - q4 - 1)) * 2) by unify_pows_two.
    rewrite <- kron_plus_distr_l.
    replace (∣1⟩⟨1∣ .+ ∣0⟩⟨0∣) with (I 2) by solve_matrix.
    Msimpl.
    restore_dims_strong.
    Msimpl.
    replace (2 ^ q4 * (2 ^ S (q3 - q4 - 1) * 2) * 2 ^ (dim - S (q3 - q4 - 1 + 1) - q4)) with (2 ^ dim) by unify_pows_two.
    rewrite Mmult_1_r; auto with wf_db.
    rewrite list_to_ucom_append; reflexivity.
Qed.

Lemma cancel_gates_simple'_sound : forall {dim} (l acc : gate_list dim) n,
  uc_well_typed_l l -> (rev acc) ++ l =l= cancel_gates_simple' l acc n.
Proof.
  intros.
  generalize dependent acc.
  generalize dependent l.
  induction n; try easy.
  intros l WT; simpl.
  destruct l; intros; try (rewrite app_nil_r; reflexivity).
  destruct g.
  - dependent destruction f;
    remember (next_single_qubit_gate l n0) as next_gate;
    symmetry in Heqnext_gate; inversion WT.
    + (* H *)
      destruct next_gate.
      2: { rewrite <- IHn; try assumption.
           simpl; rewrite <- app_assoc. 
           reflexivity. }
      destruct p; dependent destruction f; rewrite <- IHn;
      try (simpl; rewrite <- app_assoc; reflexivity);
      try assumption.
      rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
      apply app_congruence; try reflexivity.
      apply H_H_cancel; assumption.
      apply (nsqg_WT _ _ _ _ Heqnext_gate H3).
    + (* X *)
      destruct next_gate.
      2: { rewrite <- IHn; try assumption.
           simpl; rewrite <- app_assoc. 
           reflexivity. }
      destruct p; dependent destruction f; rewrite <- IHn;
      try (simpl; rewrite <- app_assoc; reflexivity);
      try assumption.
      rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
      apply app_congruence; try reflexivity.
      apply X_X_cancel; assumption.
      apply (nsqg_WT _ _ _ _ Heqnext_gate H3).
    + (* PI4 *)
      destruct next_gate.
      2: { rewrite <- IHn; try assumption.
           simpl; rewrite <- app_assoc. 
           reflexivity. }
      destruct p; dependent destruction f;
      [| | destruct (k + k0 =? 8)%Z eqn:E; [|destruct (k + k0 <? 8)%Z]];
      try rewrite <- IHn;
      try rewrite (nsqg_preserves_semantics _ _ _ _ Heqnext_gate);
      try (simpl; rewrite <- app_assoc; reflexivity);
      try constructor;
      try apply (nsqg_WT _ _ _ _ Heqnext_gate);
      try assumption;
      try apply app_congruence; try reflexivity.
      apply Z.eqb_eq in E.
      apply PI4_PI4_cancel; lia.
      apply PI4_PI4_combine.
      apply PI4_PI4_m8_combine.
  - (* CNOT *)
    dependent destruction f.
    remember (next_two_qubit_gate l n0) as next_gate;
    symmetry in Heqnext_gate; 
    inversion WT.
    destruct next_gate.
    2: { rewrite <- IHn; try assumption.
         simpl; rewrite <- app_assoc. 
         reflexivity. }
    destruct p; destruct p; destruct p.
    bdestruct (n0 =? n4); bdestruct (n1 =? n3); simpl;
    try (rewrite <- IHn; try assumption; simpl; rewrite <- app_assoc; reflexivity).
    subst.
    remember (does_not_reference g0 n3) as dnr; symmetry in Heqdnr.
    destruct dnr; simpl; 
    try (rewrite <- IHn; try assumption; simpl; rewrite <- app_assoc; reflexivity).
    specialize (ntqg_preserves_semantics _ _ _ _ _ _ Heqnext_gate) as H7.
    rewrite H7.
    rewrite <- IHn.
    specialize (ntqg_l1_does_not_reference _ _ _ _ _ _ Heqnext_gate) as H8.
    rewrite app_comm_cons.
    rewrite app_assoc.
    rewrite (does_not_reference_commutes_app2 g0 fU_CNOT n4 n3 H8 Heqdnr).
    repeat rewrite <- app_assoc.
    apply app_congruence; try reflexivity.
    apply CNOT_CNOT_cancel; assumption.
    specialize (ntqg_WT _ _ _ _ _ _ Heqnext_gate H6) as [H8 H9].
    apply uc_well_typed_l_app; assumption.
Qed.

Lemma cancel_gates_simple_sound : forall {dim} (l : gate_list dim),
  uc_well_typed_l l -> l =l= cancel_gates_simple l.
Proof. 
  intros. 
  unfold cancel_gates_simple.
  rewrite <- cancel_gates_simple'_sound.
  reflexivity. 
  assumption. 
Qed.

(* Small test *)
Definition test1 : gate_list 4 := (_H 1) :: (_P 0) :: (_CNOT 2 3) :: (_P 0) :: (_H 1) :: (_Z 1) :: (_PDAG 0) :: (_CNOT 2 3) :: (_T 0) :: [].
Compute (cancel_gates_simple test1).


(**************************************************)
(** Optimization: single-qubit gate cancellation **)
(**************************************************)

(** CURRENTLY NOT VERIFIED **)

(* Single-qubit Gate Cancellation
   
   Cancel gates adjacent to their inverse and combine z-rotations. Similar
   to not propagation, propagate z-rotation gates right using a set of 
   commutation rules.

   Cancellation rules:
   - Z, Z
   - P, PDAG
   - T, TDAG 

   z-rotation combination rules: (may not be exhaustive!)
   (Recall: Z = PI, P = PI/2, T = PI/4)
   - Z + PDAG    -> P
   - Z + P       -> PDAG
   - P + P       -> Z
   - PDAG + PDAG -> Z
   - P + TDAG    -> T
   - PDAG + T    -> TDAG
   - T + T       -> P
   - TDAG + TDAG -> PDAG
 
   Commutation rules for Rz gates (i.e. Z, P, PDAG, T, TDAG):
   #1 - Rz b ; H b ; CNOT a b ; H b ≡ H b ; CNOT a b ; H b ; Rz b
   #2 - Rz b ; CNOT a b ; Rz' b ; CNOT a b ≡ CNOT a b ; Rz' b ; CNOT a b ; Rz b
   #3 - Rz a ; CNOT a b ≡ CNOT a b ; Rz a
*)

(* TODO: Write a general function that searches for patterns on mulitple qubits. 
   (The search_for_patX functions all have similar structures.) *)

Definition search_for_pat1 {dim} (l : gate_list dim) q :=
  match (next_single_qubit_gate l q) with
  | Some (fU_H, l') => 
      match (next_two_qubit_gate l' q) with
      | Some (l1, q1, q2, l2) =>
          if q =? q2
          then match (next_single_qubit_gate l2 q) with
               | Some (fU_H, l2') => Some ([_H q] ++ l1 ++ [_CNOT q1 q] ++ [ _H q], l2') 
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition search_for_pat2 {dim} (l : gate_list dim) q :=
  match (next_two_qubit_gate l q) with
  | Some (l1, q1, q2, l2) => 
      if q =? q2
      then match (next_single_qubit_gate l2 q) with
           | Some (fU_PI4 k as u, l2') =>
               match (next_two_qubit_gate l2' q) with
               | Some (l3, q3, q4, l4) => 
                   if (q =? q4) && (q1 =? q3) && (does_not_reference l3 q3)
                   then Some (l1 ++ [_CNOT q1 q] ++ [App1 u q] ++ l3 ++ [_CNOT q1 q], l4)
                   else None 
               | _ => None
               end
           | _ => None
      end
      else None
  | _ => None
  end.

Definition search_for_pat3 {dim} (l : gate_list dim) q :=
  match (next_two_qubit_gate l q) with
  | Some (l1, q1, q2, l2) => 
      if q =? q1
      then Some (l1 ++ [_CNOT q1 q2], l2)
      else None
  | _ => None
  end.

Definition search_for_commuting_pat {dim} (l : gate_list dim) q :=
  match search_for_pat1 l q with
  | Some (l1, l2) => Some (l1, l2)
  | None => match search_for_pat2 l q with
           | Some (l1, l2) => Some (l1, l2)
           | None => match search_for_pat3 l q with
                    | Some (l1, l2) => Some (l1, l2)
                    | None => None
                    end
           end
  end.

Fixpoint propagate_PI4 {dim} k (l : gate_list dim) (q n : nat) : option (gate_list dim) :=
  match n with
  | O => Some l
  | S n' => 
      match next_single_qubit_gate l q with
      | Some (fU_PI4 k', l') => 
                 let k'' := (k + k')%Z in
                 (* Cancel *)
                 if (k'' =? 8)%Z then Some l' else 
                 (* Combine *)
                 if (k'' <? 8)%Z then Some (_PI4 k'' q :: l')
                 else Some (_PI4 (k'' - 8)%Z q :: l') 
      (* Commute *)
      | _ =>
          match search_for_commuting_pat l q with
          | Some (l1, l2) => match (propagate_PI4 k l2 q n') with
                            | Some l' => Some (l1 ++ l')
                            | None => None
                            end
          | None =>  None
          end
      end
  end.

(* Call a propagation function on PI4 rotation gates. 
   
   The extra n argument is to help Coq recognize termination.
   We start with n = (length l). *)
Fixpoint cancel_gates {dim} (l : gate_list dim) (n: nat) : gate_list dim :=
  match n with
  | 0 => l
  | S n' => match l with
           | [] => []
           | App1 (fU_PI4 k) q :: t => 
               match propagate_PI4 k t q (length t) with
               | None => (_PI4 k q) :: (cancel_gates t n')
               | Some l' => cancel_gates l' n'
               end
           | h :: t => h :: (cancel_gates t n')
           end
  end.

Definition single_qubit_gate_cancellation {dim} (l : gate_list dim) := 
  cancel_gates l (length l).


(***********************************************)
(** Optimization: two-qubit gate cancellation **)
(***********************************************)

(** CURRENTLY NOT VERIFIED **)

(* Two-qubit Gate Cancellation
   
   Cancel adjacent CNOT gates while propagating CNOT gates right using 
   a set of commutation rules.
 
   Commutation rules:
   #1 - CNOT a c ; CNOT b c ≡ CNOT b c ; CNOT a c
   #2 - CNOT a c ; CNOT a b ≡ CNOT a b ; CNOT a c
   #3 - Rz a ; CNOT a b ≡ CNOT a b ; Rz a
*)

