Require Export UnitarySem.


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
Close Scope C_scope.
Close Scope R_scope.

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
  | uapp U l ; c2 => 
      if (inb q l)
      then None
      else match propagate_not c2 q with
           | None => None
           | Some c2' => Some (uapp U l ; c2')
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
    try (simpl in H;
         destruct (inb q l); try easy;
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
         remember (inb q l) as b; destruct b; try easy;
         destruct (propagate_not c2 q); try easy;
         inversion H;
         rewrite (useq_congruence' _ (uapp U l) u (X q; c2));
         try apply IHc2; try easy;
         repeat rewrite <- useq_assoc;
         apply useq_congruence;
         try reflexivity;
         symmetry; apply slide12; easy);
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
        apply slide1; easy.
    (* U = CNOT *)
    + (* solve the cases where l has <2 or >2 elements *)
      destruct l; simpl in H; try destruct l; simpl in H; try destruct l;
      [ | destruct ((n =? q) || false) | | destruct ((n =? q) || ((n0 =? q) || (inb q (n1::l)))) ];
      try (destruct (propagate_not c2 q);
           inversion H; simpl; remove_zero_gates; reflexivity). 
      (* solve the case where l has exactly 2 elements *)
      bdestruct (q =? n); try easy.
      bdestruct (q =? n0).
      * subst. destruct (propagate_not c2 n0); inversion H.
        rewrite (useq_congruence' _ (CNOT n n0) u (X n0; c2)); try apply IHc2; try easy.
        repeat rewrite <- useq_assoc.
        apply useq_congruence; try reflexivity.
        symmetry; apply X_CNOT_comm.
      * assert (inb q (n::n0::[]) = false). 
        { apply not_eq_sym in H0; apply beq_nat_false_iff in H0.
          apply not_eq_sym in H1; apply beq_nat_false_iff in H1.
          simpl. repeat apply orb_false_intro; easy. }
        destruct (propagate_not c2 q); inversion H.
        rewrite (useq_congruence' _ (CNOT n n0) u (X q; c2)); try apply IHc2; try easy.
        repeat rewrite <- useq_assoc.
        apply useq_congruence; try reflexivity.
        symmetry; apply slide12; assumption.
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


(*****************************)
(** Circuit Mapping Example **)
(*****************************)

(* Naive mapping algorithm. *)
Fixpoint move_target_left (base dist : nat) : ucom :=
  match dist with 
  | O => CNOT base (base + 1)
  | S n' => SWAP (base + dist) (base + dist + 1); 
           move_target_left base n'; 
           SWAP (base + dist) (base + dist + 1)
  end.

Fixpoint move_target_right (base dist : nat) : ucom :=
  match dist with 
  | O => CNOT (base + 1) base
  | S n' => SWAP (base - dist) (base - dist + 1); 
           move_target_right base n'; 
           SWAP (base - dist) (base - dist + 1)
  end.

Fixpoint map_to_lnn (c : ucom) : ucom :=
  match c with
  | c1; c2 => map_to_lnn c1; map_to_lnn c2
  | uapp U_CNOT (n1::n2::[]) =>
      if n1 <? n2
      then move_target_left n1 (n2 - n1 - 1)
      else if n2 <? n1
           then move_target_right (n1 - 1) (n1 - n2 - 1)
           else CNOT n1 n2 (* badly-typed case, n1=n2 *)
  | _ => c
  end.

(* Small test case. *)
Definition q4 : nat := 4.
Definition q5 : nat := 5.
Definition example3 : ucom := CNOT q1 q4; CNOT q5 q2.
Compute (map_to_lnn example3).

(* There are many more interesting & general properties we can prove about SWAP, e.g.

       forall a b, SWAP a b; U b; SWAP a b ≡ U a

   but the properties below are sufficient for this problem.

   For reference, the general definition of the swap matrix for m < n is:

   @pad (1+(n-m-1)+1) m dim 
        ( ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨0∣ .+
          ∣0⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨0∣ .+
          ∣1⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨1∣ .+
          ∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨1∣ )
*)

(* TODO: clean up denote_swap_adjacent by adding the lemmas below to M_db. *)
Lemma swap_spec_general : forall (A B : Matrix 2 2),
  WF_Matrix A -> WF_Matrix B -> swap × (A ⊗ B) × swap = B ⊗ A.
Proof.
  intros A B WF_A WF_B.
  solve_matrix.
Qed.

Lemma rewrite_ket_prod00 : forall (q1 :  Matrix 2 1) (q2 : Matrix 1 2),
  WF_Matrix q1 -> WF_Matrix q2 -> (q1 × ⟨0∣) × (∣0⟩ × q2) = q1 × q2.
Proof. intros. solve_matrix. Qed.

Lemma rewrite_ket_prod01 : forall (q1 :  Matrix 2 1) (q2 : Matrix 1 2),
  (q1 × ⟨0∣) × (∣1⟩ × q2) = Zero.
Proof. intros. solve_matrix. Qed.

Lemma rewrite_ket_prod10 : forall (q1 :  Matrix 2 1) (q2 : Matrix 1 2),
  (q1 × ⟨1∣) × (∣0⟩ × q2) = Zero.
Proof. intros. solve_matrix. Qed.

Lemma rewrite_ket_prod11 : forall (q1 :  Matrix 2 1) (q2 : Matrix 1 2),
  WF_Matrix q1 -> WF_Matrix q2 -> (q1 × ⟨1∣) × (∣1⟩ × q2) = q1 × q2.
Proof. intros. solve_matrix. Qed.

(* Show that SWAP ≡ swap. *)
Lemma denote_SWAP_adjacent : forall n dim,
  uc_well_typed dim (SWAP n (n + 1)) ->
  uc_eval dim (SWAP n (n + 1)) = (I (2 ^ n)) ⊗ swap ⊗ (I (2 ^ (dim - 2 - n))).
Proof.
  intros n dim WT.
  assert (n + 1 < dim).
  { inversion WT; inversion H3; subst.
    apply H9. right. left. easy. }
  clear WT.
  simpl; unfold ueval_cnot, pad.
  replace (n <? n + 1) with true by (symmetry; apply Nat.ltb_lt; lia).
  bdestruct (n + 1 <? n); try (contradict H; lia).
  replace (n + 1 - n) with 1 by lia; simpl.
  replace (n + 2 <=? dim) with true by (symmetry; apply leb_iff; lia). 
  clear H0.
  restore_dims_strong; Msimpl.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mmult_plus_distr_r. 
  restore_dims_strong; Msimpl.
  repeat rewrite Mmult_plus_distr_l.
  restore_dims_strong; Msimpl.
  replace (σx × ∣1⟩⟨1∣) with (∣0⟩⟨1∣) by (rewrite <- Mmult_assoc; Msimpl; reflexivity).
  replace (σx × ∣0⟩⟨0∣) with (∣1⟩⟨0∣) by (rewrite <- Mmult_assoc; Msimpl; reflexivity).
  replace (∣0⟩⟨0∣ × σx) with (∣0⟩⟨1∣) by (rewrite Mmult_assoc; Msimpl; reflexivity).
  replace (∣1⟩⟨1∣ × σx) with (∣1⟩⟨0∣) by (rewrite Mmult_assoc; Msimpl; reflexivity).
  repeat rewrite rewrite_ket_prod00; try auto with wf_db.
  repeat rewrite rewrite_ket_prod11; try auto with wf_db.
  repeat rewrite rewrite_ket_prod01.
  repeat rewrite rewrite_ket_prod10.
  repeat rewrite kron_0_l. 
  repeat rewrite Mplus_0_l, Mplus_0_r.
  replace (σx × ∣0⟩⟨1∣) with (∣1⟩⟨1∣) by (rewrite <- Mmult_assoc; Msimpl; reflexivity).
  repeat rewrite <- Mplus_assoc.
  assert (swap = ∣1⟩⟨1∣ ⊗ ∣1⟩⟨1∣ .+ ∣0⟩⟨1∣ ⊗ ∣1⟩⟨0∣ .+ ∣1⟩⟨0∣ ⊗ ∣0⟩⟨1∣ .+ ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣) by solve_matrix.
  rewrite H0.
  reflexivity.
Qed.

Lemma swap_adjacent_WT: forall b dim,
  b + 1 < dim -> uc_well_typed dim (SWAP b (b + 1)).
Proof.
  intros b dim H.
  repeat apply WT_seq; apply WT_app; 
    try (unfold in_bounds; intros; repeat destruct H0; subst; lia);
    try easy;
    repeat apply NoDup_cons; try apply NoDup_nil; try easy;
    intros [H0 | H0];  contradict H0; lia.
Qed.

Lemma swap_adjacent_not_WT: forall b dim,
  b + 1 >= dim -> uc_eval dim (SWAP b (b + 1)) = Zero.
Proof.
  intros b dim H.
  simpl; unfold ueval_cnot, pad.
  replace (b <? b + 1) with true by (symmetry; apply Nat.ltb_lt; lia).
  bdestruct (b + (1 + (b + 1 - b - 1) + 1) <=? dim).
  contradict H0. lia.
  remove_zero_gates; trivial.
Qed.

Lemma swap_swap_id_adjacent: forall a dim,
  uc_well_typed dim (SWAP a (a+1)) ->
  uc_eval dim (SWAP a (a+1); SWAP a (a+1)) = uc_eval dim uskip.
Proof.
  intros a dim WT.
  assert (a + 1 < dim).
  { inversion WT; inversion H3; subst. 
    apply H9. right. left. easy. }
  remember (SWAP a (a+1)) as s; simpl; subst.
  rewrite denote_SWAP_adjacent; try assumption.
  replace (2 ^ dim) with (2 ^ a * (2 ^ 1 * 2 ^ 1) * 2 ^ (dim - 2 - a)) by unify_pows_two.
  replace (2 ^ 1) with 2 by easy.
  repeat rewrite kron_mixed_product.
  rewrite swap_swap.
  Msimpl.
  repeat rewrite id_kron.
  reflexivity.
Qed.

Opaque SWAP.
Lemma swap_cnot_adjacent_left : forall a b,
  a < b ->
  SWAP b (b+1); CNOT a b; SWAP b (b+1) ≡ CNOT a (b+1).
Proof.
  intros a b H dim.
  simpl; unfold ueval_cnot, pad.
  replace (a <? b) with true by (symmetry; apply Nat.ltb_lt; assumption).
  replace (a <? b + 1) with true  by (symmetry; apply Nat.ltb_lt; lia).
  remember (b - a - 1) as i.
  replace (b + 1 - a - 1) with (i + 1) by lia.
  bdestruct (a + (1 + (i + 1) + 1) <=? dim).
  2: { rewrite swap_adjacent_not_WT; try lia; remove_zero_gates; trivial. }
  replace (a + (1 + i + 1) <=? dim) with true by (symmetry; apply Nat.leb_le; lia).
  assert (b + 1 < dim) by lia.
  rewrite denote_SWAP_adjacent.
  2: { apply swap_adjacent_WT; assumption. }
  (* 1: rewrite identity matrices *)
  replace (2 ^ (dim - (1 + i + 1) - a)) with (2 * 2 ^ (dim - (1 + (i + 1) + 1) - a)) by unify_pows_two.
  replace (dim - (1 + (i + 1) + 1) - a) with (dim - 2 - b) by lia.
  replace (2 ^ (b - a)) with (2 ^ i * 2) by unify_pows_two.
  replace (2 ^ (i + 1)) with (2 ^ i * 2) by unify_pows_two.
  replace (2 ^ (b + 1 - a)) with (2 ^ i * 2 ^ 2) by unify_pows_two.
  replace (2 ^ b) with (2 ^ a * 2 * 2 ^ i) by unify_pows_two.  
  repeat rewrite <- id_kron.
  replace (2 ^ dim) with (2 ^ a * (2 ^ 1 * 2 ^ i * (2 ^ 2)) * 2 ^ (dim - 2 - b)) by unify_pows_two.
  replace (2 ^ 1) with 2 by easy.
  replace (2 ^ 2) with (2 * 2) by easy.
  clear.
  (* 2: manually mess with associativity *)
  rewrite (kron_assoc _ (I 2) _).
  restore_dims_strong.
  rewrite (kron_assoc _ _ swap).
  rewrite <- (kron_assoc ∣0⟩⟨0∣ _ (I 2)).
  rewrite <- (kron_assoc ∣0⟩⟨0∣ _ (I (2 ^ 2))).
  rewrite <- (kron_assoc ∣1⟩⟨1∣ _ (I 2)).
  restore_dims_strong.
  rewrite (kron_assoc _ (I 2) σx).
  rewrite <- (kron_assoc _ (I 2) (I (2 ^ (dim - 2 - b)))).
  rewrite (kron_assoc (I (2 ^ a)) _ (I 2)).
  rewrite kron_plus_distr_r.
  rewrite (kron_assoc _ σx (I 2)).
  rewrite (kron_assoc _ (I 2) (I 2)).
  (* 3: simplify *)
  replace (2 ^ a * (2 * 2 ^ i * 2) * 2) with (2 ^ a * (2 * 2 ^ i * (2 * 2))) by rewrite_assoc.
  replace (2 * 2 ^ i * 2 * 2) with (2 * 2 ^ i * (2 * 2)) by rewrite_assoc.
  Msimpl. 
  rewrite Mmult_plus_distr_r.
  rewrite Mmult_plus_distr_l.
  Msimpl. 
  repeat rewrite <- (Mmult_assoc swap _ swap).
  repeat rewrite swap_spec_general; try auto with wf_db.
  replace (2 ^ 2) with (2 * 2) by easy.
  rewrite id_kron.
  replace (2 * (2 ^ i * 2) * 2) with (2 * 2 ^ i * (2 * 2)) by rewrite_assoc.
  reflexivity.
Qed.

Lemma swap_cnot_adjacent_right : forall a b,
  b + 1 < a ->
  SWAP b (b+1); CNOT a (b+1); SWAP b (b+1) ≡ CNOT a b.
Proof.
  intros a b H dim.
  simpl; unfold ueval_cnot, pad.
  replace (b + 1 <? a) with true by (symmetry; apply Nat.ltb_lt; assumption).
  replace (b <? a) with true by (symmetry; apply Nat.ltb_lt; lia).
  bdestruct (a <? b + 1). contradict H0. lia.
  bdestruct (a <? b). contradict H1. lia.
  remember (a - b - 1) as i.
  remember (dim - (1 + i + 1) - b) as j.
  replace (a - (b + 1)) with i by lia.
  replace (dim - (1 + (i - 1) + 1) - (b + 1)) with j by lia.
  replace (b + 1 + (1 + (i - 1) + 1)) with (b + (1 + i + 1)) by lia.
  bdestruct (b + (1 + i + 1) <=? dim).
  2: { remove_zero_gates; trivial. }
  rewrite denote_SWAP_adjacent.
  2: { apply swap_adjacent_WT. lia. }
  (* 1: rewrite identity matrices *)
  replace (2 ^ (b + 1)) with (2 ^ b * 2) by unify_pows_two.
  replace (2 ^ i) with (2 * 2 ^ (i - 1)) by unify_pows_two.
  replace (2 ^ (a - b)) with ((2 ^ 2) * 2 ^ (i - 1)) by unify_pows_two.
  replace (2 ^ (dim - 2 - b)) with (2 ^ (i - 1) * 2 * 2 ^ j) by unify_pows_two.
  repeat rewrite <- id_kron.
  replace (2 ^ dim) with (2 ^ b * (2 ^ 2 * 2 ^ (i - 1) * 2) * 2 ^ j) by unify_pows_two.
  replace (2 ^ 2) with (2 * 2) by easy.
  replace (2 ^ (1 + i + 1)) with (2 ^ 1 * 2 ^ 1 * 2 ^ (i - 1) * 2 ^ 1) by unify_pows_two.
  replace (2 ^ 1) with 2 by easy.
  clear.
  (* 2: manually mess with associativity *)
  rewrite (kron_assoc _ swap _).
  rewrite <- (kron_assoc swap _ _).
  replace (2 * 2 * (2 ^ (i - 1) * 2 * 2 ^ j)) with (2 * 2 * 2 ^ (i - 1) * 2 * 2 ^ j) by rewrite_assoc.
  replace (2 * 2 * (2 ^ (i - 1) * 2)) with (2 * 2 * 2 ^ (i - 1) * 2) by rewrite_assoc.
  rewrite <- (kron_assoc (I (2 ^ b)) _ _).
  rewrite <- (kron_assoc swap _ _).
  rewrite <- (kron_assoc σx _ _).
  rewrite (kron_assoc (I (2 ^ b)) (I 2) _).
  restore_dims_strong.
  rewrite kron_plus_distr_l.
  repeat rewrite <- (kron_assoc (I 2) _ _).
  (* 3: simplify *)
  replace (2 ^ b * (2 * (2 * 2 ^ (i - 1) * 2))) with (2 ^ b * (2 * 2 * 2 ^ (i - 1) * 2)) by rewrite_assoc. 
  replace (2 * (2 * 2 ^ (i - 1) * 2)) with (2 * 2 * 2 ^ (i - 1) * 2) by rewrite_assoc.
  Msimpl.
  rewrite Mmult_plus_distr_r.
  rewrite Mmult_plus_distr_l.
  restore_dims_strong.
  Msimpl. 
  repeat rewrite <- (Mmult_assoc swap _ swap).
  repeat rewrite swap_spec_general; try auto with wf_db.
  rewrite id_kron.
  reflexivity.
Qed.

Lemma move_target_left_equiv_cnot : forall base dist,
  move_target_left base dist ≡ CNOT base (base + dist + 1).
Proof.
  intros base dist.
  induction dist.
  - replace (base + 0 + 1) with (base + 1) by lia; easy.
  - simpl.
    rewrite IHdist.
    replace (base + S dist) with (base + dist + 1) by lia.
    apply swap_cnot_adjacent_left.
    lia.
Qed. 

Lemma move_target_right_equiv_cnot : forall base dist,
   base >= dist -> move_target_right base dist ≡ CNOT (base + 1) (base - dist).
Proof.
  intros base dist H.
  induction dist.
  - replace (base - 0) with base by lia; easy.
  - simpl.
    rewrite IHdist; try lia.
    replace (base - dist) with (base - S dist + 1) by lia.
    apply swap_cnot_adjacent_right.
    lia.
Qed.

(* map_to_lnn is semantics-preserving *)
Lemma map_to_lnn_sound : forall c, c ≡ map_to_lnn c.
Proof.
  induction c; try easy.
  - simpl. rewrite <- IHc1. rewrite <- IHc2. reflexivity.
  - simpl.
    destruct u; try easy.
    repeat (destruct l; try easy).
    bdestruct (n <? n0).
    + rewrite (move_target_left_equiv_cnot n (n0 - n - 1)).
      replace (n + (n0 - n - 1) + 1) with n0 by lia.
      easy.
    + bdestruct (n0 <? n); try easy.
      rewrite (move_target_right_equiv_cnot (n - 1) (n - n0 - 1)) by lia.
      replace (n - 1 - (n - n0 - 1)) with n0 by lia.
      replace (n - 1 + 1) with n by lia.
      easy.
Qed.

(* linear nearest neighbor: 'all CNOTs are on adjacent qubits' *)
Inductive respects_LNN : ucom -> Prop :=
  | LNN_skip : respects_LNN uskip
  | LNN_seq : forall c1 c2, 
      respects_LNN c1 -> respects_LNN c2 -> respects_LNN (c1; c2)
  | LNN_app_u : forall (u : Unitary 1) q, respects_LNN (q *= u)
  | LNN_app_cnot_left : forall n, respects_LNN (CNOT n (n+1))
  | LNN_app_cnot_right : forall n, respects_LNN (CNOT (n+1) n).

Transparent SWAP.
Lemma move_target_left_respects_lnn : forall base dist,
  respects_LNN (move_target_left base dist).
Proof.
  intros base dist.
  induction dist.
  - simpl. apply LNN_app_cnot_left.
  - simpl. 
    repeat apply LNN_seq; 
    try apply LNN_app_cnot_left;
    try apply LNN_app_cnot_right.
    apply IHdist.
Qed. 

Lemma move_target_right_respects_lnn : forall base dist,
   base >= dist -> 
   respects_LNN (move_target_right base dist).
Proof.
  intros base dist H.
  induction dist.
  - simpl. apply LNN_app_cnot_right.
  - simpl.
    repeat apply LNN_seq; 
    try apply LNN_app_cnot_left;
    try apply LNN_app_cnot_right.
    apply IHdist.
    lia.
Qed.

(* map_to_lnn produces programs that satisfy the LNN constraint. 

   The well-typedness constraint is necessary because gates applied
   to the incorrect number of arguments do not satisfy our LNN 
   property. (We can change this if we want). *)
Lemma map_to_lnn_correct : forall c dim, 
  uc_well_typed dim c -> respects_LNN (map_to_lnn c).
Proof.
  intros c dim WT.
  induction WT.
  - apply LNN_skip.
  - simpl. apply LNN_seq; assumption.
  - destruct u; destruct l; try destruct l; try destruct l; 
    try inversion H; try apply LNN_app_u.
    simpl. 
    bdestruct (n <? n0).
    apply move_target_left_respects_lnn.
    bdestruct (n0 <? n).
    apply move_target_right_respects_lnn; lia.
    inversion H1; subst. contradict H6. left. lia.
Qed.


(*********************************)
(** Boolean Circuit Compilation **)
(*********************************)
(* The plan is to reproduce QWIRE/Oracles.v, time permitting.
   Nothing is done yet. *)

Inductive bexp := 
| b_t   : bexp
| b_f   : bexp
| b_var : nat -> bexp
| b_not : bexp -> bexp
| b_and : bexp -> bexp -> bexp 
| b_xor : bexp -> bexp -> bexp.

Reserved Notation "⌈ b | f ⌉" (at level 0). 

Fixpoint interpret_bexp (b : bexp) (f : nat -> bool) : bool :=
  match b with
  | b_t         => true 
  | b_f         => false 
  | b_var v     => f v 
  | b_not b     => ¬ ⌈ b | f ⌉
  | b_and b1 b2 => ⌈ b1 | f⌉ && ⌈ b2 | f⌉
  | b_xor b1 b2 => ⌈ b1 | f⌉ ⊕ ⌈ b2 | f⌉
  end where "⌈ b | f ⌉" := (interpret_bexp b f).  

(* This def. of Toffoli is from https://en.wikipedia.org/wiki/Toffoli_gate *)
Definition TDAG a := uapp (U_R (- PI / 4)) [a].
Definition TOFFOLI (a b c : nat) : ucom :=
  H c; CNOT b c; TDAG c; CNOT a c; T c; CNOT b c; TDAG c; CNOT a c; T b; T c; CNOT a b; H c; T a; TDAG b; CNOT a b.

(* TODO: prove that the Toffoli gate implements the Toffoli spec. *)


