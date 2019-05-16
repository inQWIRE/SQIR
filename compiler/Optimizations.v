Require Import UnitarySem.
Require Import Equivalences.
Open Scope ucom.

(********************************)
(** Optimization: remove skips **)
(********************************)

Fixpoint rm_uskips (c : ucom) : ucom :=
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
Lemma WT_rm_uskips : forall c dim, uc_well_typed dim c <-> uc_well_typed dim (rm_uskips c).
Proof.
  intros c dim.
  split; intros H.
  - induction H.
    + constructor.
    + simpl.
      destruct (rm_uskips c1), (rm_uskips c2); auto with type_db.
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
    + simpl in H; easy.
Qed.      

(* rm_uskips is semantics-preserving. *)
Lemma rm_uskips_sound : forall c,
  c ≡ (rm_uskips c).
Proof.
  induction c; intros dim; trivial.
  simpl.
  destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; trivial;
    rewrite IHc1, IHc2; simpl; Msimpl; easy.
Qed.

(* Alternate proof using congruence instead of Msimpl. *)
Lemma rm_uskips_sound' : forall c,
  c ≡ (rm_uskips c).
Proof.
  induction c; try easy.
  simpl.
  destruct (rm_uskips c1); destruct (rm_uskips c2);
    rewrite IHc1, IHc2; 
    try apply uskip_id_l; try apply uskip_id_r;
    reflexivity.
Qed.

(* The output of rm_uskips is either a single skip intruction, or a program
   that contains no skip instructions. *)
Inductive skip_free : ucom -> Prop :=
  | SF_seq : forall c1 c2, skip_free c1 -> skip_free c2 -> skip_free (c1; c2)
  | SF_app : forall n l (u : Unitary n), skip_free (uapp u l).

Lemma rm_uskips_correct : forall c,
  (rm_uskips c) = uskip \/ skip_free (rm_uskips c).
Proof.
  intro c.
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
  - right; simpl. apply SF_app.
Qed.

(* The output of rm_uskips has no more operations than the input program. *)
Local Close Scope C_scope.
Local Close Scope R_scope.

Fixpoint count_ops (c : ucom) : nat :=
  match c with
  | c1; c2 => (count_ops c1) + (count_ops c2)
  | _ => 1
  end.

Lemma rm_uskips_reduces_count : forall c,
  count_ops (rm_uskips c) <= count_ops c.
Proof.
  intro c.
  induction c.
  - simpl. lia.
  - simpl. destruct (rm_uskips c1); try lia; 
    destruct (rm_uskips c2); 
    simpl; simpl in IHc1; simpl in IHc2;
    lia.
  - simpl. lia.
Qed.


(**************************)
(** Flattening sequences **)
(**************************)
(* This is a useful pre-processing transformation for other optimizations
   (e.g. not propagation). *)

Fixpoint flat_append (c1 c2 : ucom) : ucom := 
  match c1 with
  | c1'; c2' => c1' ; (flat_append c2' c2)
  | _ => c1 ; c2
  end.

Fixpoint flatten (c: ucom) : ucom :=
  match c with
  | c1; c2 => flat_append (flatten c1) (flatten c2)
  | _ => c
  end.

Lemma flat_append_WT : forall c1 c2 dim,
  uc_well_typed dim c1 -> uc_well_typed dim c2 
    -> uc_well_typed dim (flat_append c1 c2).
Proof.
  intros c1 c2 dim WTc1 WTc2.
  induction WTc1; simpl; apply WT_seq;
  try apply WT_uskip; 
  try apply WT_app; 
  try apply IHWTc1_2;
  assumption.
Qed.

Lemma flatten_WT : forall c dim,
  uc_well_typed dim c -> uc_well_typed dim (flatten c).
Proof.
  intros c dim WT.
  induction WT; simpl.
  - apply WT_uskip.
  - apply flat_append_WT; assumption.
  - apply WT_app; assumption.
Qed.

Lemma denote_flat_append : forall c1 c2,
  flat_append c1 c2 ≡ c1 ; c2.
Proof.
  intros.
  induction c1; try easy.
  simpl.
  rewrite IHc1_2.
  rewrite useq_assoc.
  reflexivity.
Qed.

Lemma flatten_sound : forall c,  
  c ≡ flatten c.
Proof.
  intros c.
  induction c; try easy.
  simpl.
  rewrite denote_flat_append.
  rewrite <- IHc1, <- IHc2.
  reflexivity.
Qed.


(***********************************)
(** Optimization: not propagation **)
(***********************************)

Require Export List.

(* Propagate an X gate on qubit q as far right as possible, cancelling
   the gate if possible.
   
   This will return None if no cancellation is possible or (Some c') 
   where c' is the result of removing the appropriate X gate from c. *)
Fixpoint propagate_not (c : ucom) (q : nat) : option ucom :=
  match c with
  | q' *= U_X ; c2 => 
      if q =? q' then Some c2 
      else match propagate_not c2 q with
           | None => None
           | Some c2' => Some (X q' ; c2')
           end
  | uapp U_CNOT (q1::q2::nil) ; c2 => 
      if q =? q1 then None 
      else match propagate_not c2 q with
           | None => None
           | Some c2' => Some (CNOT q1 q2 ; c2')
           end
  | q' *= U ; c2 => 
      if (q =? q')
      then None
      else match propagate_not c2 q with
           | None => None
           | Some c2' => Some (q' *= U ; c2')
           end
  | _ => None
  end.

(* Call propagate_not on all X gates in the circuit. 
   
   The extra n argument is to help Coq recognize termination.
   We start with n = (count_ops c), which is the maximum
   number of times that propagate_nots will be called. *)
Fixpoint propagate_nots (c : ucom) (n: nat) : ucom :=
  match n with
  | 0 => c
  | S n' => match c with
           | uapp U_X [q] ; c2 => 
               match propagate_not c2 q with
               | None => X q ; (propagate_nots c2 n')
               | Some c2' => propagate_nots c2' n'
               end
           | c1; c2 => c1; (propagate_nots c2 n')
           | _ => c
           end
  end.

Definition rm_nots (c : ucom) : ucom := 
  let c' := flatten c in
  propagate_nots c' (count_ops c').

(* Small test cases. *)
Definition q1 : nat := 1.
Definition q2 : nat := 2.
Definition q3 : nat := 3.
Definition example1 : ucom := ((X q1; H q2); ((X q1; X q2); (CNOT q3 q2; X q2))).
Compute (flatten example1).
Compute (rm_nots example1).
Definition example2 : ucom := ((X q1; X q2); X q3).
Compute (flatten example2).
Compute (rm_nots example2).

(* Weaker congruence relationship, needed in propagate_not because dim
   is directly referenced in the well-typedness constraint. *)
Lemma useq_congruence' : forall c1 c1' c2 c2' dim,
    uc_eval dim c1 = uc_eval dim c1' ->
    uc_eval dim c2 = uc_eval dim c2' ->
    uc_eval dim (c1 ; c2) = uc_eval dim (c1' ; c2').
Proof.
  intros c1 c1' c2 c2' dim Ec1 Ec2.
  simpl.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

(* propagate_not preserves well-typedness. *)
Lemma propagate_not_WT : forall c c' q dim,
  uc_well_typed dim c ->
  propagate_not c q = Some c' ->
  uc_well_typed dim c'.
Proof.
  intros c c' q dim WT.
  generalize dependent c'.
  induction c; try easy.
  - inversion WT; subst.
    specialize (IHc2 H3).
    clear - IHc2 H2 H3. 
    intros c' H.
    destruct c1; try easy.
    destruct u;
    (* U = H, Y, Z, R, P, PDAG *)
    try (destruct l; try destruct l; simpl in H; try easy;
         destruct (q =? n); try easy;
         destruct (propagate_not c2 q); try easy;
         inversion H; constructor; try easy;
         apply IHc2; easy);
    subst.
    (* U = X *)
    + destruct l; try destruct l; try (inversion H2; contradict H5; easy).
      simpl in H. bdestruct (q =? n).
      * inversion H; subst; easy.
      * destruct (propagate_not c2 q); inversion H.
        constructor; try easy.
        apply IHc2; easy.
    (* U = CNOT *)
    + destruct l; try destruct l; try destruct l; 
        try (inversion H2; contradict H5; easy).
      simpl in H. bdestruct (q =? n); try easy.
      bdestruct (q =? n0).
      * subst. destruct (propagate_not c2 n0); inversion H.
        constructor; try easy.
        apply IHc2; easy.
      * destruct (propagate_not c2 q); inversion H.
        constructor; try easy.
        apply IHc2; easy.
Qed.

(* propagate_not is semantics-preserving. *)
Lemma propagate_not_sound : forall c c' q dim,
  uc_well_typed dim (X q) ->
  propagate_not c q = Some c' ->
  uc_eval dim c' = uc_eval dim (X q; c).
Proof.
  intros c c' q dim WT_X.
  generalize dependent c'.
  induction c; try easy.
  - clear IHc1.
    intros c' H.
    destruct c1; try easy.
    remember u as U.
    destruct u;
    (* U = H, Y, Z, R, P, PDAG *)
    try (rewrite HeqU in H; simpl in H; rewrite <- HeqU in H;
         destruct l; try destruct l; try easy;
         bdestruct (q =? n); try easy;
         destruct (propagate_not c2 q); try easy;
         inversion H;
         rewrite (useq_congruence' _ (n *= U) u (X q; c2));
         try apply IHc2; try easy;
         repeat rewrite <- useq_assoc;
         apply useq_congruence;
         try reflexivity;
         apply U_V_comm; apply Nat.neq_sym; assumption);
    subst.
    (* U = X *)
    + (* solve the cases where l is empty or has >1 element *)
      destruct l; simpl in H; try destruct l;
      try destruct ((n =? q) || inb q (n0 :: l)); try easy;
      try (destruct (propagate_not c2 q); 
           inversion H; simpl; remove_zero_gates; reflexivity).
      (* solve the case where l has exactly 1 element *)
      bdestruct (q =? n).
      * inversion H; subst.
        rewrite <- useq_assoc.
        rewrite (useq_congruence' _ uskip _ c'); 
        try rewrite uskip_id_l; 
        try reflexivity.
        symmetry; apply XX_id; assumption.
      * destruct (propagate_not c2 q); inversion H.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ (X n; X q) c2 c2); try easy.
        rewrite useq_assoc.
        rewrite (useq_congruence' _ (X n) u (X q; c2)); try apply IHc2; easy.
        apply U_V_comm; easy.
    (* U = CNOT *)
    + (* solve the cases where l has <2 or >2 elements *)
      destruct l; simpl in H; try destruct l; simpl in H; try destruct l; try easy;
      try (destruct (q =? n); try easy;
           destruct (propagate_not c2 q); try easy;
           inversion H; simpl; remove_zero_gates; reflexivity).
      (* solve the case where l has exactly 2 elements *)
      bdestruct (q =? n); try easy.
      bdestruct (q =? n0).
      * subst. destruct (propagate_not c2 n0); inversion H.
        rewrite (useq_congruence' _ (CNOT n n0) u (X n0; c2)); try apply IHc2; try easy.
        repeat rewrite <- useq_assoc.
        apply useq_congruence; try reflexivity.
        symmetry; apply X_CNOT_comm.
      * destruct (propagate_not c2 q); inversion H.
        rewrite (useq_congruence' _ (CNOT n n0) u (X q; c2)); try apply IHc2; try easy.
        repeat rewrite <- useq_assoc.
        apply useq_congruence; try reflexivity.
        symmetry; apply U_CNOT_comm; assumption.
Qed.   

(* propagate_nots is semantics-preserving. *)
Lemma propagate_nots_sound : forall c n dim, 
  uc_well_typed dim c -> uc_eval dim c = uc_eval dim (propagate_nots c n).
Proof.
  intros c n dim.
  generalize dependent c.
  induction n; try easy.
  intros c WT.
  destruct c; try easy.
  destruct c1; 
  try destruct u; 
  try destruct l; try destruct l;
  try (inversion WT; subst; simpl; rewrite <- IHn; easy).
  simpl; destruct (propagate_not c2 n0) eqn:H.
  - inversion WT; subst.
    specialize (propagate_not_sound c2 u n0 dim H3 H) as H'.
    simpl in H'; rewrite <- H'.
    apply IHn.
    apply (propagate_not_WT c2 _ n0); assumption.
  - inversion WT; subst. simpl. rewrite <- IHn; easy.
Qed.

(* rm_nots is semantics-preserving. 
   
   The well-typedness constraint is required because rm_nots can actually
   return a well-typed circuit given a circuit that is not well-typed.
     ==> Consider the program X 4; X 4 where dim = 3
   The output of the denotation function may change in this case. 
*)
Lemma rm_nots_sound : forall c dim, 
  uc_well_typed dim c -> uc_eval dim c = uc_eval dim (rm_nots c).
Proof.
  intros c dim WT.
  unfold rm_nots.
  rewrite <- propagate_nots_sound.
  apply flatten_sound.
  apply flatten_WT; assumption.
Qed.

(* TODO: Define similar propagation functions for "single-qubit gate cancellation"
   and "two-qubit gate cancellation". *)

(**************************)
(** List representation  **)
(**************************)
(* Represent a unitary circuit as a list of gate applications. Similar to
   flattening, this is a useful preprocessing step for optimizations. *)

(* TODO: make 'not propagation' use this representation instead of flatten. *)

Require Import Setoid.

Inductive gate : Set :=
| Gate : forall {n}, Unitary n -> list nat -> gate.

Fixpoint ucom_to_list (c: ucom) : list gate :=
  match c with
  | c1; c2 => (ucom_to_list c1) ++ (ucom_to_list c2)
  | uapp U l => [Gate U l]
  | uskip => []
  end.

Fixpoint list_to_ucom (l : list gate) : ucom :=
  match l with
  | [] => uskip
  | (Gate U l)::t => (uapp U l) ; (list_to_ucom t)
  end.

Definition uc_eval_l (dim : nat) (l : list gate) := uc_eval dim (list_to_ucom l).

Lemma list_to_ucom_append : forall l1 l2,
  list_to_ucom (l1 ++ l2) ≡ list_to_ucom l1 ; list_to_ucom l2.
Proof.
  intros l1 l2 dim.
  induction l1; simpl.
  - Msimpl. reflexivity.
  - destruct a; simpl.
    rewrite IHl1; simpl.
    rewrite Mmult_assoc.
    reflexivity.
Qed.

Lemma ucom_to_list_sound : forall (c : ucom),
  c ≡ list_to_ucom (ucom_to_list c).
Proof.
  intros c dim.
  induction c; simpl.
  - reflexivity.
  - repeat rewrite list_to_ucom_append; simpl.
    rewrite IHc1, IHc2.
    reflexivity.
  - Msimpl. reflexivity.
Qed.

(* Equivalences that allow us to do rewriting. *)

Definition uc_equiv_l (l1 l2 : list gate) := forall dim, 
  uc_eval_l dim l1 = uc_eval_l dim l2.
Infix "≡" := uc_equiv_l. (* over-rides the previous notation *)

Lemma uc_equiv_l_refl : forall l1, l1 ≡ l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_sym : forall l1 l2, l1 ≡ l2 -> l2 ≡ l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_trans : forall l1 l2 l3, l1 ≡ l2 -> l2 ≡ l3 -> l1 ≡ l3.
Proof. intros l1 l2 l3 H12 H23 dim. rewrite H12. easy. Qed.

Lemma uc_eval_l_cons : forall {n} (dim : nat) (U : Unitary n) (l : list nat) (t : list gate),
  uc_eval_l dim ((Gate U l)::t) = uc_eval_l dim t × ueval dim U l.
Proof. easy. Qed.

Lemma uc_eval_l_app : forall (dim : nat) (l1 l2 : list gate),
  uc_eval_l dim (l1 ++ l2) = uc_eval_l dim l2 × uc_eval_l dim l1.
Proof.
  intros.
  unfold uc_eval_l. 
  induction l1.
  - simpl. Msimpl. reflexivity.
  - simpl. destruct a. simpl.
    rewrite IHl1. rewrite Mmult_assoc. reflexivity.
Qed.

Lemma cons_congruence : forall g l l',
  l ≡ l' ->
  g :: l ≡ g :: l'.
Proof.
  intros g l l' Hl dim.
  destruct g.
  repeat rewrite uc_eval_l_cons.
  rewrite Hl.
  reflexivity.
Qed.

Lemma app_congruence : forall l1 l1' l2 l2',
  l1 ≡ l1' ->
  l2 ≡ l2' ->
  l1 ++ l2 ≡ l1' ++ l2'.
Proof.
  intros l1 l1' l2 l2' Hl1 Hl2 dim.
  repeat rewrite uc_eval_l_app.
  rewrite Hl1, Hl2.
  reflexivity.
Qed.

Add Relation (list gate) uc_equiv_l
  reflexivity proved by uc_equiv_l_refl
  symmetry proved by uc_equiv_l_sym
  transitivity proved by uc_equiv_l_trans
  as uc_equiv_l_rel.

Add Morphism cons
  with signature eq ==> (@uc_equiv_l) ==> (@uc_equiv_l) as cons_mor.
Proof. intros y x0 y0 H0. apply cons_congruence; easy. Qed.

Add Morphism (@app gate)
  with signature (@uc_equiv_l) ==> (@uc_equiv_l) ==> (@uc_equiv_l) as app_mor.
Proof. intros x y H x0 y0 H0. apply app_congruence; easy. Qed.


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

(* Describe a program that only contains single-qubit gates that act on qubit q. *)
Inductive single_qubit_program : nat -> list gate -> Prop :=
  | sq_nil : forall q, single_qubit_program q []
  | sq_cons : forall q (U : Unitary 1) l, single_qubit_program q l -> single_qubit_program q ((Gate U [q])::l).

(* Get the next gate applied to qubit q.
   
   Returns None if there is no next gate on qubit q. Otherwise, it 
   returns Some (l1, g, l2) where g is the application of the gate,
   l1 is the portion of the program before g, and l2 is the portion 
   of the program after g.
   
   Correctness properties: 
     (1) next_gate l q = Some (l1, g, l2) -> uc_equiv_l l (l1 ++ [g] ++ l2)
     (2) No gate in l1 references q
   
   This second propery implies that any program l 'that satisfies 
   (single_qubit_program q l') commutes with l1.
*)
Fixpoint next_gate (l : list gate) (q : nat) : option (list gate * gate * list gate) :=
  match l with
  | (Gate U qs) :: t => if existsb (Nat.eqb q) qs
                      then Some ([], Gate U qs, t) 
                      else match (next_gate t q) with
                           | None => None
                           | Some (l1, g, l2) => Some ((Gate U qs) :: l1, g, l2)
                           end
  | _ => None
  end.

Lemma next_gate_sound : forall l q l1 g l2,
  next_gate l q = Some (l1, g, l2) -> l ≡ l1 ++ [g] ++ l2.
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a.
  destruct (existsb (Nat.eqb q) l0).
  inversion H; subst. reflexivity.
  destruct (next_gate l q); try easy.
  destruct p; destruct p; inversion H; subst.
  simpl in *.
  rewrite <- IHl; reflexivity.
Qed.

Lemma next_gate_returns_q : forall {n} l q l1 l2 (U : Unitary n) q',
  next_gate l q = Some (l1, Gate U [q'], l2) -> q = q'.
Proof.
  intros n l q.
  induction l; try easy; intros.
  simpl in H.
  destruct a.
  remember (existsb (Nat.eqb q) l0) as res1.
  destruct res1.
  - inversion H; subst. 
    simpl in Heqres1.  
    symmetry in Heqres1. 
    apply orb_prop in Heqres1 as [Heq | Heq]; try easy.
    apply Nat.eqb_eq in Heq; subst; reflexivity.
  - remember (next_gate l q) as res2.
    destruct res2; try easy.
    destruct p; destruct p.
    apply (IHl l4 l3 U q').
    inversion H; subst.
    reflexivity.
Qed.

(* General disjoint-qubit commutativity lemma for list representation. *)
Lemma single_qubit_gate_commutes : forall {n m : nat} (u1 : Unitary n) (u2 : Unitary m) q qs l,
  existsb (Nat.eqb q) qs = false ->
  (Gate u1 [q])::(Gate u2 qs)::l ≡ (Gate u2 qs)::(Gate u1 [q])::l.
Proof.
  intros n m u1 u2 q qs l H dim.
  unfold uc_eval_l.
  simpl.
  destruct n, m; try easy. 
  simpl. 
  destruct n; try destruct n; remove_zero_gates; try reflexivity.
  destruct m.
  - destruct qs; try destruct qs; remove_zero_gates; try reflexivity.
    simpl in H.
    apply orb_false_elim in H as [H _].
    apply beq_nat_false in H.
    specialize (U_V_comm q n u1 u2 H dim) as Hcomm.
    simpl in Hcomm.
    repeat rewrite Mmult_assoc.
    rewrite Hcomm.
    reflexivity.
  - destruct m; remove_zero_gates; try reflexivity.
    destruct qs; try destruct qs; try destruct qs; remove_zero_gates; try reflexivity.
    simpl in H.
    apply orb_false_elim in H as [H1 H2].
    apply orb_false_elim in H2 as [H2 _].
    apply beq_nat_false in H1.
    apply beq_nat_false in H2.
    specialize (U_CNOT_comm q n n0 u1 H1 H2 dim) as Hcomm.
    simpl in Hcomm.
    repeat rewrite Mmult_assoc.
    rewrite Hcomm.
    reflexivity.
Qed.    

Lemma next_gate_commutes' : forall l q l1 g l2 (U : Unitary 1),
  next_gate l q = Some (l1, g, l2) -> [Gate U [q]] ++ l1 ≡ l1 ++ [Gate U [q]].
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a.
  remember (existsb (Nat.eqb q) l0) as b.
  destruct b.
  inversion H; subst. reflexivity.
  destruct (next_gate l q); try easy. 
  destruct p; destruct p; inversion H; subst. 
  simpl in *.
  rewrite <- IHl; try reflexivity.
  rewrite single_qubit_gate_commutes; easy.
Qed.

Lemma next_gate_commutes : forall l q l1 g l2 l',
  single_qubit_program q l' ->
  next_gate l q = Some (l1, g, l2) -> l' ++ l1 ≡ l1 ++ l'.
Proof. 
  intros.
  induction H.
  - rewrite app_nil_r. reflexivity.
  - replace (l1 ++ Gate U [q] :: l0) with (l1 ++ [Gate U [q]] ++ l0) by easy.
    replace ((Gate U [q] :: l0) ++ l1) with ([Gate U [q]] ++ l0 ++ l1) by easy.
    rewrite (app_assoc l1).
    rewrite <- next_gate_commutes' with (l:=l) (g:=g) (l2:=l2); try assumption.
    rewrite <- app_assoc.
    rewrite IHsingle_qubit_program; try assumption.
    reflexivity.
Qed.

(* Boolean equality over built-in untaries. *)
Require Import Coq.Reals.ROrderedType.
Definition match_gate {n n'} (U : Unitary n) (U' : Unitary n') : bool :=
  match U, U' with
  | U_H, U_H | U_X, U_X | U_Y, U_Y | U_Z, U_Z | U_P, U_P | U_PDAG, U_PDAG => true
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
Fixpoint remove_single_qubit_pattern (l : list gate) (q : nat) (pat : list gate) : option (list gate) :=
  match pat with
  | [] => Some l
  | (Gate U [_])::pat' =>
      match next_gate l q with
      | Some (l1, Gate U' [_], l2) =>
          if match_gate U U'
          then match remove_single_qubit_pattern l2 q pat' with
               | Some l' => Some (l1 ++ l')
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

(* If the next sequence of gates applied to qubit q matches 'pat', then replace
   'pat' with 'rep'. *)
Definition replace_single_qubit_pattern (l : list gate) (q : nat) (pat rep : list gate) : option (list gate) :=
  match (remove_single_qubit_pattern l q pat) with
  | Some l' => Some (rep ++ l')
  | None => None
  end.

(* Simple tests *)
Definition test := (Gate U_H [1])::(Gate U_X [0])::(Gate U_CNOT (2::3::nil))::(Gate U_Y [0])::(Gate U_H [0])::(Gate U_Y [1])::(Gate U_Y [2])::(Gate U_CNOT (0::2::nil))::[].
Compute (next_gate test 0).
Compute (next_gate test 1).
Compute (next_gate test 2).
Compute (next_gate test 4).
Compute (replace_single_qubit_pattern test 0 ((Gate U_X [0])::(Gate U_Y [0])::nil) ((Gate U_P [0])::(Gate U_PDAG [0])::nil)).
Compute (replace_single_qubit_pattern test 0 ((Gate U_X [0])::(Gate U_H [0])::[]) ((Gate U_P [0])::(Gate U_PDAG [0])::nil)).

Lemma remove_single_qubit_pattern_correct : forall (l l' : list gate) (q : nat) (pat : list gate),
  single_qubit_program q pat ->
  remove_single_qubit_pattern l q pat = Some l' ->
  l ≡ pat ++ l'.
Proof.
  intros.
  generalize dependent l'.
  generalize dependent l.
  induction pat; intros.
  - inversion H0; subst. reflexivity.
  - simpl in *. 
    destruct a, l0; try destruct l0; try easy.
    remember (next_gate l q) as res1.
    destruct res1; try easy.
    destruct p; destruct p.
    destruct g, l2; try destruct l2; try easy.
    remember (match_gate u u0) as res2.
    destruct res2; try easy.
    remember (remove_single_qubit_pattern l0 q pat) as res3.
    destruct res3; try easy.
    inversion H0; subst; clear H0.
    dependent destruction H.
    destruct n1; try destruct n1;
    try (rewrite (match_gate_different_dims u u0) in Heqres2; easy).
    symmetry in Heqres2.
    rewrite match_gate_refl in Heqres2; subst.
    symmetry in Heqres1.
    specialize (next_gate_returns_q _ _ _ _ _ _ Heqres1) as H0; subst.
    rewrite (next_gate_sound _ _ _ _ _ Heqres1).
    symmetry in Heqres3.
    rewrite (IHpat H l0 l2 Heqres3).
    rewrite (app_assoc l1).
    rewrite <- (next_gate_commutes' l n2 l1 (Gate u0 [n2]) l0 u0 Heqres1).
    rewrite <- app_assoc.
    rewrite (app_assoc l1).
    rewrite <- (next_gate_commutes l n2 l1 (Gate u0 [n2]) l0 pat H Heqres1).
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma replace_single_qubit_pattern_sound : forall (l l' : list gate) (q : nat) (pat rep : list gate),
  single_qubit_program q pat ->
  single_qubit_program q rep ->
  pat ≡ rep ->
  replace_single_qubit_pattern l q pat rep = Some l' ->
  l ≡ l'.
Proof.
  intros.
  unfold replace_single_qubit_pattern in H2.
  remember (remove_single_qubit_pattern l q pat) as res.
  destruct res; try easy.
  symmetry in Heqres.
  apply (remove_single_qubit_pattern_correct _ _ _ _ H) in Heqres.
  inversion H2; subst.
  rewrite Heqres.
  rewrite H1.
  reflexivity.
Qed.

(* TODO: along with verifying soundness, we should prove that 
   replace_single_qubit_pattern actually does what it's supposed to 
   - it should replace 'pat' with 'rep'. *)

(*******************************************)
(** Optimization: hadamard gate reduction **)
(*******************************************)

(* IN PROGRESS *)

(* This optimization pass reduces the number of H gates in a program
   using a variety of rewrite rules. *)

Definition H q := Gate U_H [q].
Definition P q := Gate U_P [q].
Definition PDAG q := Gate U_PDAG [q].
Definition CNOT q1 q2:= Gate U_CNOT (q1::q2::nil).

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

Definition apply_equivalence1 l q := 
  replace_single_qubit_pattern l q (H q :: P q :: H q :: []) (PDAG q :: H q :: PDAG q :: []).

Definition apply_equivalence2 l q := 
  replace_single_qubit_pattern l q (H q :: PDAG q :: H q :: []) (P q :: H q :: P q :: []).

(* TODO *)
Definition apply_equivalence3 (l : list gate) (q : nat) : option (list gate) := None.

Definition apply_equivalence4 l q :=
  match (remove_single_qubit_pattern l q (H q :: P q :: nil)) with
  | Some l1 =>
      match (next_gate l1 q) with
      | Some (l2, Gate U_CNOT (q1::q2::nil), l3) =>
          if q =? q2 
          then match (remove_single_qubit_pattern l3 q (PDAG q :: H q :: nil)) with
               | Some l4 =>
                   Some (l2 ++ (PDAG q2 :: CNOT q1 q2 :: P q2 :: nil) ++ l4)
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition apply_equivalence5 l q :=
  match (remove_single_qubit_pattern l q (H q :: PDAG q :: nil)) with
  | Some l1 =>
      match (next_gate l1 q) with
      | Some (l2, Gate U_CNOT (q1::q2::nil), l3) =>
          if q =? q2 
          then match (remove_single_qubit_pattern l3 q (P q :: H q :: nil)) with
               | Some l4 =>
                   Some (l2 ++ (P q2 :: CNOT q1 q2 :: PDAG q2 :: nil) ++ l4)
               | _ => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.

Definition apply_equivalence (l : list gate) (q : nat) : option (list gate) :=
  match apply_equivalence1 l q with
  | Some l' => Some l'
  | _ => match apply_equivalence2 l q with
       | Some l' => Some l'
       | _ => match apply_equivalence3 l q with
             | Some l' => Some l'
             | _ => match apply_equivalence4 l q with
                   | Some l' => Some l'
                   | _ => match apply_equivalence5 l q with
                         | Some l' => Some l'
                         | _ => None
                         end
                   end
             end
       end
  end.

Lemma apply_equivalence_sound : forall l q l',
  apply_equivalence l q = Some l' -> l ≡ l'.
Proof. Admitted.

(* For each H gate, try to apply a rewrite rule. If some rewrite rule
   succeeds, then make the recursive call on the circuit returned by
   apply_equivalence. 
 
   The n argument is needed to convince Coq of termination. We start with
   n = 2 * (count_ops c), which is an overapproximation of the necessary
   number of iterations. Note that the starting value of n is greater than
   (count_ops c) because apply_equivalence will sometimes return a circuit
   of the same size as the input circuit.

   If we wanted to do a proper proof of termination, we would need to show
   that each call to apply_equivalence (strictly) reduces the number of H 
   gates in the program. *)
Fixpoint apply_equivalences (l : list gate) (n: nat) : list gate :=
  match n with
  | 0 => l
  | S n' => 
      match l with
      | [] => []
      | Gate U_H [q] :: t => 
          match apply_equivalence l q with
          | None => H q :: (apply_equivalences t n')
          | Some l' => apply_equivalences l' n'
          end
      | g :: t => g :: (apply_equivalences t n')
      end
  end.

Lemma apply_equivalences_sound: forall l n, l ≡ apply_equivalences l n.
Proof. Admitted.

Definition hadamard_reduction (l : list gate) : list gate := 
  apply_equivalences l (2 * (length l)).

Lemma hadamard_reduction_sound: forall l, l ≡ hadamard_reduction l.
Proof. Admitted.

(* TODO: Add examples. Also do some more testing to make sure that these
   functions are doing the right thing. We've verified that these functions
   are sound, but not that they are performing the optimization we intended... *)

(* TODO: We should also be able to prove that the Hadamard reduction optimization 
   reduces the number of Hadamard gates in the program. *)