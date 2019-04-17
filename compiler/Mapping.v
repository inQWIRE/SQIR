Require Export UnitarySem.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.

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
Definition q1 : nat := 1.
Definition q2 : nat := 2.
Definition q3 : nat := 3.
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

