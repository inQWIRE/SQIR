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

Lemma denote_flat_append : forall c1 c2 dim,
  uc_eval dim (flat_append c1 c2) = uc_eval dim c2 × uc_eval dim c1.
Proof.
  intros c1 c2 dim.
  induction c1; try easy.
  simpl.
  rewrite IHc1_2.
  apply Mmult_assoc.
Qed.

Lemma flatten_sound : forall c,  
  c ≡ flatten c.
Proof.
  intros c dim.
  induction c; try easy.
  simpl.
  rewrite IHc1, IHc2.
  rewrite denote_flat_append.
  reflexivity.
Qed.


(***********************************)
(** Optimization: not propagation **)
(***********************************)

Require Export List.

(* Propagate an X gate on qubit q as far right as possible, cancelling
   the gate if possible.
   
   This will return None if no cancellation is possible or (Some c') 
   where c' is the result of removing the appropriate X gate from c.
   
   This function will insert an extra uskip instruction if the cancelled
   gate is at the end of the circuit. *)
Fixpoint propagate_not (c : ucom) (q : nat) : option ucom :=
  match c with
  | q' *= U_X => 
      if q =? q' then Some uskip else None
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

Definition rm_nots (c : ucom) : ucom := propagate_nots (flatten c) (count_ops c).

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
    (* U = H, Y, Z, R *)
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
  - destruct u; try easy. 
    destruct l; try destruct l; try easy.
    simpl. bdestruct (q =? n); try easy; subst.
    intros c' H. 
    inversion H.
    constructor.
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
    (* U = H, Y, Z, R *)
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
  - destruct u; try easy. 
    destruct l; try destruct l; try easy.
    simpl. bdestruct (q =? n); try easy; subst.
    intros c' H.
    inversion H.
    apply XX_id; assumption.
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
