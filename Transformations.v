Require Export UnitarySem.


(** Optimization: remove skips **)

Fixpoint rm_uskips (c : ucom) : ucom :=
  match c with
  | c1 ; c2 => match rm_uskips c1, rm_uskips c2 with
              | uskip, c2' => c2'
              | c1', uskip => c1'
              | c1', c2'   => c1'; c2'
              end
  | c'      => c'
  end.

(* We don't really need this anymore *)
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

Lemma rm_uskips_sound : forall c,
  c ≡ (rm_uskips c).
Proof.
  induction c; intros dim; trivial.
  simpl.
  destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; trivial;
    rewrite IHc1, IHc2; simpl; Msimpl; easy.
Qed.

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
  
(** Flattening sequences **)

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

(** Optimization: 'not propagation' **)

Require Export List.

(* Propagate an X gate on qubit q as far right as possible, cancelling
   the gate if possible.
   
   This will return None if no cancellation is possible or (Some c') 
   where c' is the result of removing the appropriate X gate from c.
   
   This function will insert an extra uskip instruction if the cancelled
   gate is at the end of the circuit... I should probably fix that. *)
Fixpoint propagate_not (c : ucom) (q : nat) : option ucom :=
  match c with
  | q' *= U_X => 
      if q =? q' then Some uskip else None
  | q' *= U_X ; c2 => 
      if q =? q' then Some c2 
      else match propagate_not c2 q with
           | None => None
           | Some c2' => Some (q' *= U_X ; c2')
           end
  | uapp U_CNOT (q1::q2::nil) ; c2 => 
      if q =? q1 then None 
      else match propagate_not c2 q with
           | None => None
           | Some c2' => Some (uapp U_CNOT (q1::q2::nil) ; c2')
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
   number of times that propagate_nots can be called. *)
Fixpoint propagate_nots (c : ucom) (n: nat) : ucom :=
  match n with
  | 0 => c
  | S n' => match c with
           | q *= U_X ; c2 => 
               match propagate_not c2 q with
               | None => q *= U_X ; (propagate_nots c2 n')
               | Some c2' => propagate_nots c2' n'
               end
           | c1; c2 => c1; (propagate_nots c2 n')
           | _ => c
           end
  end.

Definition rm_nots (c : ucom) : ucom := propagate_nots (flatten c) (count_ops c).

(* Is there a more natural way to write this property? *)
Lemma propagate_not_sound : forall c q,
  match propagate_not c q with
  | None => True
  | Some c' => c' ≡ (q *= U_X; c)
  end.
Proof.
  intros c q.
  induction c.
  - easy.
  - clear IHc1.
    destruct c1; try easy.
    remember u as U.
    destruct u;
    (* U = H, Y, Z, R *)
    try (rewrite HeqU; simpl; rewrite <- HeqU;
         remember (inb q l) as b; 
         destruct b; try easy;
         destruct (propagate_not c2 q); try easy;
         intros dim;
         rewrite <- useq_assoc;
         rewrite (useq_congruence _ (uapp U l; q *= U_X) c2 c2);
         try apply slide12; try easy;
         rewrite useq_assoc;
         rewrite (useq_congruence (uapp U l) (uapp U l) _ (q *= U_X; c2)); 
         easy);
    subst.
    (* U = X *)
    + (* solve the cases where l is empty, or l has >1 element *)
      destruct l; simpl; try destruct l;
      try destruct ((n =? q) || inb q (n0 :: l)); try easy;
      try (destruct (propagate_not c2 q); easy);
      try (destruct (propagate_not c2 q); try easy;
           intros dim; simpl; remove_id_gates;
           unfold uc_equiv in IHc2; simpl in IHc2;
           easy).
      (* solve the case where l has exactly 1 element *)
      bdestruct (q =? n).
      * subst. 
        intros dim.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ uskip _ c2); try easy.
        rewrite uskip_id_l; easy.
        apply uc_equiv_sym.
        apply XX_id.
      * destruct (propagate_not c2 q); try easy.
        intros dim.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ (n *= U_X; q *= U_X) c2 c2); try easy.
        rewrite useq_assoc.
        rewrite (useq_congruence (n *= U_X) (n *= U_X) _ (q *= U_X; c2)); try easy.
        apply slide1; easy.
    (* U = CNOT *)
    + (* solve the cases where l has <2 or >2 elements *)
      destruct l; simpl; try destruct l; simpl; try destruct l;
      [ | destruct ((n =? q) || false) | | destruct ((n =? q) || ((n0 =? q) || (inb q (n1::l)))) ];
      try easy;
      try (destruct (propagate_not c2 q); easy);
      try (destruct (propagate_not c2 q); try easy;
           intros dim; simpl; remove_id_gates;
           unfold uc_equiv in IHc2; simpl in IHc2;
           easy).
      (* solve the case where l has exactly 2 elements *)
      bdestruct (q =? n); try easy.
      bdestruct (q =? n0).
      * subst.
        destruct (propagate_not c2 n0); try easy.
        intros dim.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ (uapp U_CNOT (n::n0::[]); n0 *= U_X) c2 c2); try easy.
        rewrite useq_assoc.
        rewrite (useq_congruence _ (uapp U_CNOT (n::n0::[])) u (n0 *= U_X; c2)); try easy.
        apply X_CNOT_comm.
      * assert (forall n m : nat, (n =? m) = (m =? n)).
        { induction n1; destruct m; auto. apply IHn1. }
        assert (inb q (n::n0::[]) = false). 
        { simpl. 
          apply beq_nat_false_iff in H.
          apply beq_nat_false_iff in H0.
          repeat apply orb_false_intro;
          try rewrite H1;
          easy. }
        destruct (propagate_not c2 q); try easy.
        intros dim.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ (uapp U_CNOT (n::n0::[]); q *= U_X) c2 c2); try easy.
        rewrite useq_assoc.
        rewrite (useq_congruence _ (uapp U_CNOT (n::n0::[])) u (q *= U_X; c2)); try easy.
        apply slide12; easy.
  - destruct u; try easy. 
    destruct l; try destruct l; try easy.
    simpl. bdestruct (q =? n); try easy; subst.
    apply XX_id.
Qed.   
    
Lemma propagate_nots_sound : forall c n, c ≡ propagate_nots c n.
Proof.
  intros c n dim.
  generalize dependent c.
  induction n; try easy.
  intros c.
  induction c; try easy.
  induction c1; 
  try destruct u; 
  try destruct l; try destruct l; 
  try (simpl; rewrite <- IHn; easy).
  simpl.
  specialize (propagate_not_sound c2 n0 ) as H.
  destruct (propagate_not c2 n0).
  - unfold uc_equiv in H. simpl in H.
    rewrite <- H.
    apply IHn.
  - simpl; rewrite <- IHn; easy.
Qed.
 
Lemma rm_nots_sound : forall c, c ≡ rm_nots c.
Proof.
  intros c dim.
  unfold rm_nots.
  rewrite <- propagate_nots_sound.
  apply flatten_sound.
Qed.

Definition q1 : nat := 1.
Definition q2 : nat := 2.
Definition q3 : nat := 3.
Definition example1 : ucom := ((X q1; H q2); ((X q1; X q2); (CNOT q3 q2; X q2))).
Compute (flatten example1).
Compute (rm_nots example1).
Definition example2 : ucom := ((X q1; X q2); X q3).
Compute (flatten example2).
Compute (rm_nots example2).

(** Circuit mapping example **)

(* linear nearest neighbor: 'all CNOTs are on adjacent qubits' *)
Inductive respects_LNN : nat -> ucom -> Prop :=
  | LNN_skip : forall dim, respects_LNN dim uskip
  | LNN_seq : forall dim c1 c2, respects_LNN dim c1 -> respects_LNN dim c2 -> respects_LNN dim (c1; c2)
  | LNN_app_cnot : forall dim n1 n2, n1 < dim -> n2 < dim -> n1 = n2 - 1 \/ n1 = n2 + 1 -> respects_LNN dim (uapp U_CNOT (n1::n2::[]))
  | LNN_app_u : forall dim u n, n < dim -> respects_LNN dim (@uapp 1 u [n]).

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
           else uapp U_CNOT (n1::n2::[])
  | _ => c
  end.

Definition q4 : nat := 4.
Definition q5 : nat := 5.
Definition example3 : ucom := CNOT q1 q4; CNOT q5 q2.
Compute (move_target_left 1 2).
Compute (move_target_right 4 2).
Compute (map_to_lnn example3).

(* This is messier than it needs to be. The lemmas below might be 
   useful to add to Quantum.v *)

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

(* Show that SWAP ≡ swap. Needs to be cleaned up. *)
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

(* It would be more interesting to prove the general verison of this lemma:

    forall a b c, SWAP b c; CNOT a b; SWAP b c ≡ CNOT a c

Or, for single qubit gates,

    forall a b, SWAP a b; U b; SWAP a b ≡ U a

For reference, the general definition of the swap matrix for m < n is:

@pad (1+(n-m-1)+1) m dim 
     ( ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨0∣ .+
       ∣0⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨0∣ .+
       ∣1⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨1∣ .+
       ∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨1∣ )


(Note similarity to the general definition of CNOT.) *)

Lemma swap_cnot_adjacent : forall a b,
  SWAP b (b+1); CNOT a b; SWAP b (b+1) ≡ CNOT a (b+1).
Proof.
  intros a b dim.
  remember (SWAP b (b + 1)) as s.
  simpl; unfold ueval_cnot, pad.
  bdestruct (a <? b).
  - replace (a <? b + 1) with true  by (symmetry; apply Nat.ltb_lt; omega).
    replace (a + (1 + (b - a - 1) + 1)) with (b + 1) by omega.
    replace (a + (1 + (b + 1 - a - 1) + 1)) with (b + 2) by omega.
    bdestruct (b + 2 <=? dim).
    + replace (b + 1 <=? dim) with true by (symmetry; apply Nat.leb_le; omega).
      subst; rewrite denote_SWAP_adjacent; try omega.
      remember (b - a - 1) as i.
      replace (b + 1 - a - 1) with (i + 1) by omega.
      replace (2 ^ (dim - (1 + i + 1) - a)) with (2 * 2 ^ (dim - (1 + (i + 1) + 1) - a)) by unify_pows_two.
      replace (dim - (1 + (i + 1) + 1) - a) with (dim - 2 - b) by omega.
      replace (2 ^ (b - a)) with (2 ^ i * 2) by unify_pows_two.
      replace (2 ^ (i + 1)) with (2 ^ i * 2) by unify_pows_two.
      replace (2 ^ (b + 1 - a)) with (2 ^ i * 2 ^ 2) by unify_pows_two.
      replace (2 ^ b) with (2 ^ a * 2 * 2 ^ i) by unify_pows_two.      
      repeat rewrite <- id_kron.
      rewrite (kron_assoc _ _ _ _ _ _ _ (I 2) _).
      replace (2 ^ a * 2 * 2 ^ i) with (2 ^ a * (2 * 2 ^ i)) by rewrite_assoc.
      rewrite (kron_assoc _ _ _ _ _ _ _ _ swap).
      rewrite <- (kron_assoc _ _ _ _ _ _ ∣0⟩⟨0∣ _ (I 2)).
      rewrite <- (kron_assoc _ _ _ _ _ _ ∣0⟩⟨0∣ _ (I (2 ^ 2))).
      rewrite <- (kron_assoc _ _ _ _ _ _ ∣1⟩⟨1∣ _ (I 2)).
      replace (2 * (2 ^ i * 2)) with (2 * 2 ^ i * 2) by rewrite_assoc.
      rewrite (kron_assoc _ _ _ _ _ _ _ (I 2) σx).
      rewrite <- (kron_assoc _ _ _ _ _ _ _ (I 2) (I (2 ^ (dim - 2 - b)))).
      rewrite (kron_assoc _ _ _ _ _ _ (I (2 ^ a)) _ (I 2)).
      replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two.
      rewrite kron_plus_distr_r.
      rewrite (kron_assoc _ _ _ _ _ _ _ σx (I 2)).
      rewrite (kron_assoc _ _ _ _ _ _ _ (I 2) (I 2)).
      Msimpl'.
      (*replace (2 ^ (S i + 1 + 1)) with (2 ^ (S i) * (2 ^ 2)) by unify_pows_two.
      replace (2 * 2) with (2 ^ 2) by easy.
      replace (2 ^ (S i + 2)) with (2 ^ (S i) * (2 ^ 2)) by unify_pows_two.*)
      rewrite Mmult_plus_distr_r.
      replace (2 ^ (S i + 1 + 1)) with (2 ^ (S i) * (2 ^ 2)) by unify_pows_two.
      replace (2 ^ (S i + 2)) with (2 ^ (S i) * (2 ^ 2)) by unify_pows_two.
      replace (2 ^ 2) with (2 * 2) by easy.
      rewrite Mmult_plus_distr_l.
      Msimpl'; try easy.
      repeat rewrite <- (Mmult_assoc _ _ _ _ swap _ swap).
      repeat rewrite swap_spec_general; try auto with wf_db.
      rewrite <- id_kron.
      simpl.
      (* almost there *)
      admit.
Admitted.

Lemma move_target_left_equiv_cnot : forall base dist,
  move_target_left base dist ≡ CNOT base (base + dist + 1).
Proof.
  intros base dist.
  induction dist.
  - replace (base + 0 + 1) with (base + 1) by omega; easy.
  - simpl; intros dim.
    remember (SWAP (base + S dist) (base + S dist + 1)) as s.
    rewrite (useq_congruence _ (s; CNOT base (base + dist + 1)) s s); try easy. 
    2: { intros dim'. apply useq_congruence; easy. }
    subst.
    replace (base + S dist) with (base + dist + 1) by omega.
    apply (swap_cnot_adjacent base (base + dist + 1)). 
Qed.

Lemma move_target_right_equiv_cnot : forall base dist,
   move_target_right base dist ≡ CNOT (base + 1) (base - dist).
Proof.
  intros base dist.
  induction dist.
  - replace (base - 0) with base by omega; easy.
  - simpl; intros dim.
    remember (SWAP (base - S dist) (base - S dist + 1)) as s.
    rewrite (useq_congruence _ (s; CNOT (base + 1) (base - dist)) s s); try easy. 
    2: { intros dim'. apply useq_congruence; easy. }
Admitted.

Lemma map_to_lnn_sound : forall c, c ≡ map_to_lnn c.
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
     rewrite (move_target_right_equiv_cnot (n - 1) (n - n0 - 1)).
     replace (n - 1 - (n - n0 - 1)) with n0 by omega.
     replace (n - 1 + 1) with n by omega.
     easy.
Qed.

Lemma map_to_lnn_correct : forall c dim, 
  uc_well_typed dim c -> respects_LNN dim (map_to_lnn c).
Proof.
  intros c dim c_WT.
  induction c_WT; try constructor; try easy.
  destruct u.
  simpl. repeat (destruct l; try easy).
Admitted.