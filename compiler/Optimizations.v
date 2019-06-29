Require Import UnitarySem.
Require Import Representations.
Require Import Equivalences.
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

(* NOTE: all optimizations after this point use the list representation of
   programs from Representations.v *)

(* Propagate an X gate on qubit q as far right as possible, cancelling
   the gate if possible.
   
   This will return None if no cancellation is possible or (Some l') 
   where l' is the result of removing the appropriate X gate from l. *)
Fixpoint propagate_not {dim} (l : gate_list dim) (q : nat) : option (gate_list dim) :=
  match l with
  | (App1 U_X q') :: t => 
      if q =? q' then Some t 
      else match propagate_not t q with
           | None => None
           | Some l' => Some ((App1 U_X q') :: l')
           end
  | (App2 U_CNOT q1 q2) :: t => 
      if q =? q1 then None 
      else match propagate_not t q with
           | None => None
           | Some l' => Some ((App2 U_CNOT q1 q2) :: l')
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
           | (App1 U_X q) :: t => 
               match propagate_not t q with
               | None => (App1 U_X q) :: (propagate_nots t n')
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
Definition example1 : gate_list 3 := (App1 U_X q0) :: (App1 U_H q1) :: (App1 U_X q0) :: (App1 U_X q1) :: (App2 U_CNOT q2 q1) :: (App1 U_X q1) :: [].
Compute (rm_nots example1).
Definition example2 : gate_list 3 := (App1 U_X q0) :: (App1 U_X q1) :: (App1 U_X q2) :: [].
Compute (rm_nots example2).

(* propagate_not preserves well-typedness. *)
Lemma propagate_not_WT : forall {dim} (l l' : gate_list dim) q,
  uc_well_typed (list_to_ucom l) ->
  propagate_not l q = Some l' ->
  uc_well_typed (list_to_ucom l').
Proof.
  intros.
  generalize dependent l'.
  induction l; try easy.
  simpl; intros.
  destruct a. 
  dependent destruction u; 
  (* u = H, Y, Z, R *)
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
    dependent destruction u.
    destruct (q =? n); try easy.
    destruct (propagate_not l q); try easy.
    inversion H; inversion H0; subst.
    constructor; try apply IHl; easy.
Qed.

(* propagate_not is semantics-preserving. *)
Lemma propagate_not_sound : forall {dim} (l l' : gate_list dim) q,
  q < dim ->
  propagate_not l q = Some l' ->
  l' =l= (App1 U_X q) :: l.
Proof.
  intros.
  generalize dependent l'.
  induction l; try easy.
  simpl; intros.   
  destruct a.
  dependent destruction u;
  (* u = H, Y, Z, R *)
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
    dependent destruction u.
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
  uc_well_typed (list_to_ucom l) -> l =l= propagate_nots l n.
Proof.
  intros.
  generalize dependent l.
  induction n; try easy.
  intros l WT.
  destruct l; try easy.
  destruct g.
  inversion WT; subst.
  simpl.
  dependent destruction u;
  (* u = H, Y, Z, R *)
  try (apply (cons_congruence _ l (propagate_nots l n));
       apply IHn; assumption).
  (* u = X *)
  - specialize (@propagate_not_sound dim) as H3.
    remember (propagate_not l n0) as x.
    destruct x.
    + symmetry in Heqx.
      inversion H1; subst.
      specialize (H3 l g n0  H0 Heqx).
      rewrite <- H3.
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
Lemma rm_nots_sound : forall {dim} (c : ucom dim), 
  uc_well_typed c -> c ≡ list_to_ucom (rm_nots (ucom_to_list c)).
Proof.
  intros dim c WT.
  unfold rm_nots.
  unfold uc_equiv.
  rewrite <- propagate_nots_sound.
  apply ucom_list_equiv.
  apply ucom_to_list_WT; assumption.
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

(* Boolean equality over built-in untaries. *)
Require Import Coq.Reals.ROrderedType.
Definition match_gate {n n'} (U : Unitary n) (U' : Unitary n') : bool :=
  match U, U' with
  | U_H, U_H | U_X, U_X | U_Y, U_Y | U_Z, U_Z => true
  | U_R θ, U_R θ' => Reqb θ θ'
  | U_CNOT, U_CNOT => true
  | _, _ => false
  end.

(* This lemma only applies to the (Unitary 1) type -- can we write something
   similar for the (Unitary n) type? *)
Lemma match_gate_refl : forall (U U' : Unitary 1), match_gate U U' = true <-> U = U'. 
Proof.
  intros U U'.
  split; intros.
  - dependent destruction U; dependent destruction U';
    try inversion H; try reflexivity.
    apply Reqb_eq in H1; subst; reflexivity.
  - subst. dependent destruction U'; try reflexivity.
    simpl; apply Reqb_eq; reflexivity.
Qed.

Lemma match_gate_different_dims : forall {n n'} (U : Unitary n) (U' : Unitary n'),
  n <> n' -> match_gate U U' = false.
Proof.
  intros. destruct U; destruct U'; easy.
Qed.

(* If the next sequence of gates applied to qubit q matches 'pat', then remove
   'pat' from the program. *)
Fixpoint remove_single_qubit_pattern {dim} (l : gate_list dim) (q : nat) (pat : gate_list dim) : option (gate_list dim) :=
  match pat with
  | [] => Some l
  | (App1 u q')::pat' =>
      match next_single_qubit_gate l q with
      | Some (App1 u' _, l') =>
          if match_gate u u'
          then remove_single_qubit_pattern l' q pat'
          else None
      | _ => None
      end
  | _ => None
  end.

(* If the next sequence of gates applied to qubit q matches 'pat', then replace
   'pat' with 'rep'. *)
Definition replace_single_qubit_pattern {dim} (l : gate_list dim) (q : nat) (pat rep : gate_list dim) : option (gate_list dim) :=
  match (remove_single_qubit_pattern l q pat) with
  | Some l' => Some (rep ++ l')
  | None => None
  end.

(* Simple tests *)
Definition test : gate_list 4 := (App1 U_H 1) :: (App1 U_X 0) :: (App2 U_CNOT 2 3) :: (App1 U_Y 0) :: (App1 U_H 0) :: (App1 U_Y 1) :: (App1 U_Y 2) :: (App2 U_CNOT 0 2) :: [].
Compute (next_single_qubit_gate test 0).
Compute (next_single_qubit_gate test 1).
Compute (next_single_qubit_gate test 2).
Compute (next_two_qubit_gate test 2).
Compute (next_two_qubit_gate test 3).
Compute (next_single_qubit_gate test 4).
Compute (replace_single_qubit_pattern test 0 ((App1 U_X 0) :: (App1 U_Y 0) :: []) ((App1 U_H 0) :: (App1 U_H 0) :: [])).
Compute (replace_single_qubit_pattern test 0 ((App1 U_X 0) :: (App1 U_H 0) :: []) ((App1 U_Y 0) :: (App1 U_Y 0) :: [])).

(* Describe a program that only contains single-qubit gates that act on qubit q. *)
Inductive single_qubit_program {dim} : nat -> gate_list dim -> Prop :=
  | sq_nil : forall q, single_qubit_program q []
  | sq_cons : forall q (u : Unitary 1) l, single_qubit_program q l -> single_qubit_program q ((App1 u q) :: l).

Lemma remove_single_qubit_pattern_correct : forall {dim} (l l' : gate_list dim) (q : nat) (pat : gate_list dim),
  single_qubit_program q pat ->
  remove_single_qubit_pattern l q pat = Some l' ->
  l =l= pat ++ l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction pat; intros.
  - inversion H0; subst. reflexivity.
  - simpl in H0. 
    destruct a; try easy.
    remember (next_single_qubit_gate l q) as next_gate.
    destruct next_gate; try easy.
    destruct p.
    destruct g; try easy.
    remember (match_gate u u0) as gate_match.
    destruct gate_match; try easy.
    symmetry in Heqgate_match.
    rewrite match_gate_refl in Heqgate_match; subst.
    symmetry in  Heqnext_gate.
    specialize (nsqg_returns_single_qubit_gate _ _ _ _ Heqnext_gate) as H1.
    destruct H1. inversion H1; subst.
    inversion H; subst.
    simpl. rewrite <- IHpat with (l:=g0); try assumption.
    apply (nsqg_preserves_semantics _ _ _ _ Heqnext_gate).
Qed.

Lemma replace_single_qubit_pattern_sound : forall {dim} (l l' : gate_list dim) (q : nat) (pat rep : gate_list dim),
  single_qubit_program q pat ->
  single_qubit_program q rep ->
  pat =l= rep ->
  replace_single_qubit_pattern l q pat rep = Some l' ->
  l =l= l'.
Proof.
  intros.
  unfold replace_single_qubit_pattern in H2.
  remember (remove_single_qubit_pattern l q pat) as remove_pat.
  destruct remove_pat; try easy.
  symmetry in Heqremove_pat.
  apply (remove_single_qubit_pattern_correct _ _ _ _ H) in Heqremove_pat.
  inversion H2; subst.
  rewrite Heqremove_pat.
  rewrite H1.
  reflexivity.
Qed.

(* TODO: along with verifying soundness, we should prove that 
   replace_single_qubit_pattern actually does what it's supposed to 
   - it should replace 'pat' with 'rep'. *)

