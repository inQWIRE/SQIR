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

(* Alternative (verbose) soundness proof using congruence. *)
Lemma rm_uskips_sound' : forall c,
  c ≡ (rm_uskips c).
Proof.
  induction c; try easy.
  simpl.
  destruct (rm_uskips c1); destruct (rm_uskips c2); intros dim.
  - rewrite (useq_congruence _ uskip _ uskip); try easy.
    apply uskip_id_l.
  - rewrite (useq_congruence _ uskip _ (u1;u2)); try easy.
    apply uskip_id_l.
  - rewrite (useq_congruence _ uskip _ (uapp u l)); try easy.
    apply uskip_id_l.
  - rewrite (useq_congruence _ (u1;u2) _ uskip); try easy.
    apply uskip_id_r.
  - rewrite (useq_congruence _ (u1;u2) _ (u3;u4)); easy.
  - rewrite (useq_congruence _ (u1;u2) _ (uapp u l)); easy.
  - rewrite (useq_congruence _ (uapp u l) _ uskip); try easy.
    apply uskip_id_r.
  - rewrite (useq_congruence _ (uapp u l) _ (u0_1;u0_2)); easy.
  - rewrite (useq_congruence _ (uapp u l) _ (uapp u0 l0)); easy.
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
  - simpl. omega.
  - simpl. destruct (rm_uskips c1); try omega; 
    destruct (rm_uskips c2); 
    simpl; simpl in IHc1; simpl in IHc2;
    omega.
  - simpl. omega.
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

(* propagate_not is semantics-preserving. *)
Lemma propagate_not_sound : forall c c' q,
  propagate_not c q = Some c' ->
  c' ≡ (X q; c).
Proof.
  intros c c' q.
  generalize dependent c'.
  induction c.
  - easy.
  - clear IHc1.
    intros c' H.
    destruct c1; try easy.
    remember u as U.
    destruct u;
    (* U = H, Y, Z, R *)
    try (rewrite HeqU in H; simpl in H; rewrite <- HeqU in H;
         remember (inb q l) as b; 
         destruct b; try easy;
         destruct (propagate_not c2 q); try easy;
         inversion H;
         intros dim;
         rewrite <- useq_assoc;
         rewrite (useq_congruence _ (uapp U l; X q) c2 c2);
         try apply slide12; try easy;
         rewrite useq_assoc;
         rewrite (useq_congruence (uapp U l) (uapp U l) _ (X q; c2)); 
         try apply IHc2; easy);
    subst.
    (* U = X *)
    + (* solve the cases where l is empty or has >1 element *)
      destruct l; simpl in H; try destruct l;
      try destruct ((n =? q) || inb q (n0 :: l)); try easy;
      try (destruct (propagate_not c2 q); 
           inversion H; intros dim;
           simpl; rewrite (IHc2 u); 
           remove_id_gates; easy).
      (* solve the case where l has exactly 1 element *)
      bdestruct (q =? n).
      * inversion H; subst.
        intros dim.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ uskip _ c'); try easy.
        rewrite uskip_id_l; easy.
        apply uc_equiv_sym.
        apply XX_id.
      * destruct (propagate_not c2 q); inversion H.
        intros dim.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ (X n; X q) c2 c2); try easy.
        rewrite useq_assoc.
        rewrite (useq_congruence _ (X n) u (X q; c2)); try apply IHc2; easy.
        apply slide1; easy.
    (* U = CNOT *)
    + (* solve the cases where l has <2 or >2 elements *)
      destruct l; simpl in H; try destruct l; simpl in H; try destruct l;
      [ | destruct ((n =? q) || false) | | destruct ((n =? q) || ((n0 =? q) || (inb q (n1::l)))) ];
      try (destruct (propagate_not c2 q); 
           inversion H; intros dim;
           simpl; rewrite IHc2;
           remove_id_gates; easy).
      (* solve the case where l has exactly 2 elements *)
      bdestruct (q =? n); try easy.
      bdestruct (q =? n0).
      * subst. destruct (propagate_not c2 n0); inversion H.
        intros dim.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ (CNOT n n0; X n0) c2 c2); try easy.
        rewrite useq_assoc.
        rewrite (useq_congruence _ (CNOT n n0) u (X n0; c2)); try apply IHc2; easy.
        apply X_CNOT_comm.
      * assert (inb q (n::n0::[]) = false). 
        { apply not_eq_sym in H0; apply beq_nat_false_iff in H0.
          apply not_eq_sym in H1; apply beq_nat_false_iff in H1.
          simpl. repeat apply orb_false_intro; easy. }
        destruct (propagate_not c2 q); inversion H.
        intros dim.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ (CNOT n n0; X q) c2 c2); try easy.
        rewrite useq_assoc.
        rewrite (useq_congruence _ (CNOT n n0) u (X q; c2)); try apply IHc2; easy.
        apply slide12; easy.
  - destruct u; try easy. 
    destruct l; try destruct l; try easy.
    simpl. bdestruct (q =? n); try easy; subst.
    intros c' H.
    inversion H.
    apply XX_id.
Qed.   
    
(* propagate_nots is semantics-preserving. *)
Lemma propagate_nots_sound : forall c n, c ≡ propagate_nots c n.
Proof.
  intros c n dim.
  generalize dependent c.
  induction n; try easy.
  intros c.
  destruct c; try easy.
  destruct c1; 
  try destruct u; 
  try destruct l; try destruct l; 
  try (simpl; rewrite <- IHn; easy).
  simpl.
  destruct (propagate_not c2 n0) eqn:H.
  - specialize (propagate_not_sound c2 u n0 H) as H1.
    unfold uc_equiv in H1. simpl in H1.
    rewrite <- H1.
    apply IHn.
  - simpl; rewrite <- IHn; easy.
Qed.

(* rm_nots is semantics-preserving. *)
Lemma rm_nots_sound : forall c, c ≡ rm_nots c.
Proof.
  intros c dim.
  unfold rm_nots.
  rewrite <- propagate_nots_sound.
  apply flatten_sound.
Qed.


(*****************************)
(** Circuit Mapping Example **)
(*****************************)

(* Naive mapping algorithm.

   Note that this definition requires the input programs to be well-typed 
   in order to make sense. For one thing, the map_to_lnn function doesn't
   do anything smart when a CNOT gate is applied to two arguments that are
   the same (n1 = n2). Another issue is that move_target_left and 
   move_target_right can produce circuits containing gate applications
   that are well-typed starting from a CNOT that is not well-typed.
   For example, consider the mapping of (CNOT 2 5) where dim = 4.

   As a result, our soundness and correctness lemmas will need to have
   assumptions about the well-typedness of the input circuit. *)
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
  WF_Matrix 2 2 A -> WF_Matrix 2 2 B -> swap × (A ⊗ B) × swap = B ⊗ A.
Proof.
  intros A B WF_A WF_B.
  solve_matrix.
Qed.

Lemma rewrite_ket_prod00 : forall (q1 :  Matrix 2 1) (q2 : Matrix 1 2),
  WF_Matrix 2 1 q1 -> WF_Matrix 1 2 q2 -> (q1 × ⟨0∣) × (∣0⟩ × q2) = q1 × q2.
Proof. intros. solve_matrix. Qed.

Lemma rewrite_ket_prod01 : forall (q1 :  Matrix 2 1) (q2 : Matrix 1 2),
  (q1 × ⟨0∣) × (∣1⟩ × q2) = Zero.
Proof. intros. solve_matrix. Qed.

Lemma rewrite_ket_prod10 : forall (q1 :  Matrix 2 1) (q2 : Matrix 1 2),
  (q1 × ⟨1∣) × (∣0⟩ × q2) = Zero.
Proof. intros. solve_matrix. Qed.

Lemma rewrite_ket_prod11 : forall (q1 :  Matrix 2 1) (q2 : Matrix 1 2),
  WF_Matrix 2 1 q1 -> WF_Matrix 1 2 q2 -> (q1 × ⟨1∣) × (∣1⟩ × q2) = q1 × q2.
Proof. intros. solve_matrix. Qed.

(* Show that SWAP ≡ swap. *)
Lemma denote_SWAP_adjacent : forall n dim,
  n + 1 < dim ->
  uc_eval dim (SWAP n (n + 1)) = (I (2 ^ n)) ⊗ swap ⊗ (I (2 ^ (dim - 2 - n))).
Proof.
  intros n dim HWT.
  simpl; unfold ueval_cnot, pad.
  replace (n <? n + 1) with true by (symmetry; apply Nat.ltb_lt; omega).
  bdestruct (n + 1 <? n); try (contradict H; omega).
  replace (n + 1 - n) with 1 by omega; simpl.
  replace (n + 2 <=? dim) with true by (symmetry; apply leb_iff; omega). 
  Msimpl'.
  repeat rewrite Mmult_plus_distr_l.
  repeat rewrite Mmult_plus_distr_r.
  Msimpl'; try easy.
  repeat rewrite Mmult_plus_distr_l.
  Msimpl'; try easy.
  replace (σx × ∣1⟩⟨1∣) with (∣0⟩⟨1∣) by (rewrite <- Mmult_assoc; Msimpl'; easy).
  replace (σx × ∣0⟩⟨0∣) with (∣1⟩⟨0∣) by (rewrite <- Mmult_assoc; Msimpl'; easy).
  replace (∣0⟩⟨0∣ × σx) with (∣0⟩⟨1∣) by (rewrite Mmult_assoc; Msimpl'; easy).
  replace (∣1⟩⟨1∣ × σx) with (∣1⟩⟨0∣) by (rewrite Mmult_assoc; Msimpl'; easy).
  repeat rewrite rewrite_ket_prod00; try auto with wf_db.
  repeat rewrite rewrite_ket_prod11; try auto with wf_db.
  repeat rewrite rewrite_ket_prod01.
  repeat rewrite rewrite_ket_prod10.
  repeat rewrite kron_0_l. 
  repeat rewrite Mplus_0_l, Mplus_0_r.
  replace (σx × ∣0⟩⟨1∣) with (∣1⟩⟨1∣) by (rewrite <- Mmult_assoc; Msimpl'; easy).
  repeat rewrite <- Mplus_assoc.
  assert (swap = ∣1⟩⟨1∣ ⊗ ∣1⟩⟨1∣ .+ ∣0⟩⟨1∣ ⊗ ∣1⟩⟨0∣ .+ ∣1⟩⟨0∣ ⊗ ∣0⟩⟨1∣ .+ ∣0⟩⟨0∣ ⊗ ∣0⟩⟨0∣) by solve_matrix.
  rewrite H0.
  reflexivity.
Qed.

Lemma swap_swap_id_adjacent: forall a,
  SWAP a (a+1); SWAP a (a+1) ≡ uskip.
Proof.
  intros a dim.
  remember (SWAP a (a+1)) as s.
  simpl.
  bdestruct (a + 1 <? dim).
  - subst; rewrite denote_SWAP_adjacent; try easy.
    Msimpl'.
    replace (2 ^ 2) with 4 by easy.
    rewrite swap_swap.
    rewrite id_kron.
    replace (2 ^ a * 4) with (2 ^ (a + 2)) by unify_pows_two.
    rewrite id_kron.
    replace (2 ^ (a + 2) * 2 ^ (dim - 2 - a)) with (2 ^ dim) by unify_pows_two.
    reflexivity.
  - subst. simpl; unfold ueval_cnot, pad.
    replace (a <? a + 1) with true by (symmetry; apply Nat.ltb_lt; omega).
    replace (a + (1 + (a + 1 - a - 1) + 1)) with (a + 2) by omega.
    bdestruct (a + 2 <=? dim); bdestruct (a + 1 <? a);
    try (contradict H0; omega);
    try (contradict H1; omega).
    remove_id_gates.
Qed.

Lemma swap_cnot_adjacent1 : forall a b dim,
  uc_well_typed dim (CNOT a (b+1)) -> 
  uc_eval dim (SWAP b (b+1); CNOT a b; SWAP b (b+1)) = uc_eval dim (CNOT a (b+1)).
Proof.
  intros a b dim WT.
  inversion WT.
(*  remember (SWAP b (b + 1)) as s.
  simpl; unfold ueval_cnot, pad.
  bdestruct (a <? b).
  - replace (a <? b + 1) with true  by (symmetry; apply Nat.ltb_lt; omega).
    remember (b - a - 1) as i.
    replace (b + 1 - a - 1) with (i + 1) by omega.
    replace (a + (1 + i + 1) <=? dim) with true.
    2: { symmetry; apply Nat.leb_le. omega. }
    replace (a + (1 + (i + 1) + 1) <=? dim) with true.
    2: { symmetry; apply Nat.leb_le. omega. }
    (* step 1: rewrite I matrices so that the dimensions will line up *)
    replace (2 ^ (b - a)) with (2 ^ i * 2) by unify_pows_two.
    replace (2 ^ (i + 1)) with (2 ^ i * 2) by unify_pows_two.
    replace (2 ^ (b + 1 - a)) with (2 ^ i * 2 ^ 2) by unify_pows_two.
    remember (dim - (1 + (i + 1) + 1) - a) as j.
    replace (2 ^ (dim - (1 + i + 1) - a)) with (2 * 2 ^ j) by unify_pows_two.
    subst s. rewrite denote_SWAP_adjacent; try omega.
    replace (2 ^ b) with (2 ^ a * 2 * 2 ^ i) by unify_pows_two.
    replace (2 ^ (dim - 2 - b)) with (2 ^ j) by unify_pows_two.
    repeat rewrite <- id_kron.
    (* step 2: manually fuss with association of kronecker product *)
    rewrite (kron_assoc _ _ _ _ _ _ _ (I 2) _).
    replace (2 ^ a * 2 * 2 ^ i) with (2 ^ a * (2 * 2 ^ i)) by rewrite_assoc.
    rewrite (kron_assoc _ _ _ _ _ _ _ _ swap).
    rewrite <- (kron_assoc _ _ _ _ _ _ ∣0⟩⟨0∣ _ (I 2)).
    rewrite <- (kron_assoc _ _ _ _ _ _ ∣0⟩⟨0∣ _ (I (2 ^ 2))).
    rewrite <- (kron_assoc _ _ _ _ _ _ ∣1⟩⟨1∣ _ (I 2)).
    replace (2 * (2 ^ i * 2)) with (2 * 2 ^ i * 2) by rewrite_assoc.
    rewrite (kron_assoc _ _ _ _ _ _ _ (I 2) σx).
    rewrite <- (kron_assoc _ _ _ _ _ _ _ (I 2) (I (2 ^ j))).
    rewrite (kron_assoc _ _ _ _ _ _ (I (2 ^ a)) _ (I 2)).
    replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two.
    rewrite kron_plus_distr_r.
    rewrite (kron_assoc _ _ _ _ _ _ _ σx (I 2)).
    rewrite (kron_assoc _ _ _ _ _ _ _ (I 2) (I 2)).
    (* step 3: simplify! *)
    Msimpl'.
    rewrite Mmult_plus_distr_r.
    replace (2 ^ (S i + 1 + 1)) with (2 ^ (S i) * (2 ^ 2)) by unify_pows_two.
    replace (2 ^ (S i + 2)) with (2 ^ (S i) * (2 ^ 2)) by unify_pows_two.
    replace (2 ^ 2) with (2 * 2) by easy.
    rewrite Mmult_plus_distr_l.
    Msimpl'; try easy.
    (* step 4: apply swap_spec_general *)
    repeat rewrite <- (Mmult_assoc _ _ _ _ swap _ swap).
    repeat rewrite swap_spec_general; try auto with wf_db.
    (* step 5: fuss with types to get relfexivity to hold *)
    rewrite <- id_kron.
    show_dimensions.
    replace (2 ^ (a + 1 + i + 1 + 1)) with (2 ^ (a + S i + 2)) by unify_pows_two.
    replace (2 ^ (1 + i + 1 + 1)) with (2 ^ (S i) * (2 ^ 2)) by unify_pows_two.
    replace (2 ^ 2) with (2 * 2) by easy.
    reflexivity.
  - 
*)
Admitted.


(*Lemma swap_cnot_adjacent2 : forall a b,
  SWAP b (b+1); CNOT a (b+1); SWAP b (b+1) ≡ CNOT a b.
Proof.
  intros a b dim.
  remember (SWAP b (b+1)) as s.
  remember (CNOT a (b+1)) as c.
  remember (CNOT a b) as c'.
  rewrite (useq_congruence _ (s; (s; c'; s)) s s); try easy.
  2: { unfold uc_equiv. 
       apply (useq_congruence s s _ ((s; c'); s)); try easy.
       apply uc_equiv_sym. subst. apply swap_cnot_adjacent1. }
  rewrite (useq_congruence _ (((s; s); c'); s) s s); try easy.
  2: { intros dim0. 
       rewrite <- useq_assoc.
       rewrite (useq_congruence _ ((s; s); c') s s); try easy.
       intros dim1. rewrite useq_assoc. reflexivity. }
  rewrite useq_assoc.
  rewrite (useq_congruence _ (uskip; c') _ uskip).
  2: { intros dim0; rewrite (useq_congruence _ uskip _ c'); try easy.
       subst; apply swap_swap_id_adjacent. }
  2: { subst; apply swap_swap_id_adjacent. }
  rewrite uskip_id_r.
  apply uskip_id_l.  
Qed.*)


Opaque SWAP.
Lemma move_target_left_equiv_cnot : forall base dist dim,
  uc_well_typed dim (CNOT base (base + dist + 1)) -> 
  uc_eval dim (move_target_left base dist) = uc_eval dim (CNOT base (base + dist + 1)).
Proof.
  intros base dist dim WT.
  induction dist.
  - replace (base + 0 + 1) with (base + 1) by omega; easy.
  - remember (SWAP (base + S dist) (base + S dist + 1)) as s.
    rewrite (useq_congruence _ (s; CNOT base (base + dist + 1)) s s); try easy. 
    2: { intros dim'. apply useq_congruence; easy. }
    subst.
    replace (base + S dist) with (base + dist + 1) by omega.
    apply (swap_cnot_adjacent1 base (base + dist + 1)). 


    simpl; intros dim.
    remember (SWAP (base + S dist) (base + S dist + 1)) as s.
    rewrite (useq_congruence _ (s; CNOT base (base + dist + 1)) s s); try easy. 
    2: { intros dim'. apply useq_congruence; easy. }
    subst.
    replace (base + S dist) with (base + dist + 1) by omega.
    apply (swap_cnot_adjacent1 base (base + dist + 1)). 
Qed. 

Lemma move_target_right_equiv_cnot : forall base dist,
   base >= dist -> move_target_right base dist ≡ CNOT (base + 1) (base - dist).
Proof.
  intros base dist H.
  induction dist.
  - replace (base - 0) with base by omega; easy.
  - simpl; intros dim.
    remember (SWAP (base - S dist) (base - S dist + 1)) as s.
    rewrite (useq_congruence _ (s; CNOT (base + 1) (base - dist)) s s); try easy. 
    2: { intros dim'. apply useq_congruence; try easy. 
         apply IHdist. omega. }
    subst.
    replace (base - dist) with (base - S dist + 1) by omega.
    apply (swap_cnot_adjacent2 (base + 1) (base - S dist)). 
Qed.

(* map_to_lnn is semantics-preserving *)
Lemma map_to_lnn_sound : forall c dim, 
  uc_well_typed dim c -> uc_eval dim c = uc_eval dim (map_to_lnn c).
Proof.
  intros c dim.
  induction c.
  - easy.
  - simpl. rewrite IHc1, IHc2. easy.
  - simpl.
    destruct u; try easy.
    repeat (destruct l; try easy).
    bdestruct (n <? n0).
    + rewrite (move_target_left_equiv_cnot n (n0 - n - 1)).
      replace (n + (n0 - n - 1) + 1) with n0 by omega.
      easy.
    + bdestruct (n0 <? n); try easy.
      rewrite (move_target_right_equiv_cnot (n - 1) (n - n0 - 1)) by omega.
      replace (n - 1 - (n - n0 - 1)) with n0 by omega.
      replace (n - 1 + 1) with n by omega.
      easy.
Qed.

(* linear nearest neighbor: 'all CNOTs are on adjacent qubits' *)
Inductive respects_LNN : nat -> ucom -> Prop :=
  | LNN_skip : forall dim, respects_LNN dim uskip
  | LNN_seq : forall dim c1 c2, 
      respects_LNN dim c1 -> respects_LNN dim c2 -> respects_LNN dim (c1; c2)
  | LNN_app_cnot : forall dim n1 n2, 
      n1 < dim -> n2 < dim -> 
        n1 = n2 - 1 \/ n1 = n2 + 1 -> respects_LNN dim (CNOT n1 n2)
  | LNN_app_u : forall dim u n, n < dim -> respects_LNN dim (@uapp 1 u [n]).

Lemma move_target_left_respects_lnn : forall base dist dim,
  base + dist + 1 < dim ->
  respects_LNN dim (move_target_left base dist).
Proof.
  intros base dist dim H.
  induction dist.
  - simpl. apply LNN_app_cnot; omega. 
  - simpl. 
    repeat apply LNN_seq; try apply LNN_app_cnot; try omega.
    apply IHdist; omega.
Qed. 

Lemma move_target_right_respects_lnn : forall base dist dim,
   base >= dist -> base + 1 < dim -> 
   respects_LNN dim (move_target_right base dist).
Proof.
  intros base dist dim H1 H2.
  induction dist.
  - simpl. apply LNN_app_cnot; omega. 
  - simpl.
    repeat apply LNN_seq; try apply LNN_app_cnot; try omega.
    apply IHdist; omega.
Qed.

(* map_to_lnn produces programs that satisfy the LNN constraint.

   The well-typedness constraint is necessary because respects_LNN
   requires some aspects of well-typedness that are not enforced
   by map_to_lnn (namely, for CNOT n1 n2, n1 <> n2 and n1 and n2 
   are bounded by dim). *)
Lemma map_to_lnn_correct : forall c dim, 
  uc_well_typed dim c -> respects_LNN dim (map_to_lnn c).
Proof.
  intros c dim c_WT.
  induction c_WT.
  - apply LNN_skip.
  - simpl. apply LNN_seq; easy.
  - destruct u; destruct l; try destruct l; inversion H;
    try (apply LNN_app_u; apply H0; left; reflexivity).
    destruct l; inversion H.
    simpl. 
    assert (n < dim). { apply H0. left. reflexivity. }
    assert (n0 < dim). { apply H0. right. left. reflexivity. }
    assert (n <> n0). { inversion H1; subst. simpl in H7. omega. }
    bdestruct (n <? n0).
    + apply move_target_left_respects_lnn; omega.
    + bdestruct (n0 <? n); try (contradict H5; omega).
      apply move_target_right_respects_lnn; omega. 
Qed.


(*********************************)
(** Boolean Circuit Compilation **)
(*********************************)
(* This is a trimmed down version of QWIRE/Oracles.v. *)

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















Fixpoint compile (b : bexp) (dim : nat) : ucirc :=
  match b with
  | b_t          => TRUE ∥ id_circ 
  | b_f          => FALSE ∥ id_circ
  | b_var v      => CNOT_at (1 + ⟦Γ⟧) (1 + position_of v Γ) 0
  | b_not b      => init_at true (1 + ⟦Γ⟧) 1 ;;
                   id_circ ∥ (compile b Γ)  ;;
                   CNOT_at (2 + ⟦Γ⟧) 1 0    ;;
                   id_circ ∥ (compile b Γ)  ;;
                   assert_at true (1+⟦Γ⟧) 1 
  | b_and b1 b2  => init_at false (1 + ⟦Γ⟧) 1        ;;
                   id_circ ∥ compile b1 Γ           ;;
                   init_at false (2 + ⟦Γ⟧) 2        ;;
                   id_circ ∥ id_circ ∥ compile b2 Γ ;;
                   Toffoli_at (3 + ⟦Γ⟧) 1 2 0       ;;
                   id_circ ∥ id_circ ∥ compile b2 Γ ;;
                   assert_at false (2 + ⟦Γ⟧) 2      ;;
                   id_circ ∥ compile b1 Γ           ;;
                   assert_at false (1 + ⟦Γ⟧) 1 
  | b_xor b1 b2  => init_at false (1 + ⟦Γ⟧) 1 ;;
                   id_circ ∥ compile b1 Γ    ;;
                   CNOT_at (2 + ⟦Γ⟧) 1 0     ;;                    
                   id_circ ∥ compile b1 Γ    ;; 
                   id_circ ∥ compile b2 Γ    ;; (* reusing ancilla *)
                   CNOT_at (2 + ⟦Γ⟧) 1 0     ;;                    
                   id_circ ∥ compile b2 Γ    ;;
                   assert_at false (1 + ⟦Γ⟧) 1
  end.
