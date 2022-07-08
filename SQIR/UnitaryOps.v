Require Export UnitarySem.
Require Export QuantumLib.VectorStates.

(* This file contains useful operations over unitary programs including:
   - inversion
   - control
   - iteration
   - parallel composition 
   
   It also contains a definition for projecting a qubit into a classical state, which
   is useful for defining the behavior of control. *)

Local Open Scope ucom.

(** Inversion **)

Fixpoint invert {dim} (c : base_ucom dim) : base_ucom dim :=
  match c with
  | c1 ; c2 => invert c2 ; invert c1
  | uapp1 (U_R θ ϕ λ) n => uapp1 (U_R (- θ) (- λ) (- ϕ)) n
  | uapp2 U_CNOT m n => uapp2 U_CNOT m n
  | _ => SKIP
  end.

Lemma uc_well_typed_invert : forall (dim : nat) (c : base_ucom dim),
  uc_well_typed c <-> uc_well_typed (invert c).
Proof.
  intros dim c. 
  split; intro H.
  induction c; try dependent destruction u; 
    inversion H; subst; constructor; auto.
  induction c; try dependent destruction u;
    inversion H; subst; constructor; auto.
Qed.

Lemma invert_correct : forall (dim : nat) (c : base_ucom dim),
  (uc_eval c)† = uc_eval (invert c).
Proof.
  intros.
  induction c; try dependent destruction u; simpl.
  - Msimpl. rewrite IHc1. rewrite IHc2. reflexivity.
  - unfold pad_u, pad.
    bdestruct (n + 1 <=? dim); try apply zero_adjoint_eq.
    repeat setoid_rewrite kron_adjoint; Msimpl.
    rewrite rotation_adjoint.
    reflexivity.
  - autorewrite with eval_db.
    gridify. 
    Qsimpl. reflexivity.
    Qsimpl. reflexivity.
Qed.

(* A few common inverses *)

Hint Rewrite sin_neg cos_neg : trig_db.

Lemma invert_CNOT : forall dim m n, invert (@CNOT dim m n) ≡ CNOT m n.
Proof. intros. reflexivity. Qed.

Local Transparent X.
Lemma invert_X : forall dim n, invert (@X dim n) ≡ X n.
Proof.
  intros dim n.
  unfold uc_equiv. simpl. 
  unfold pad_u, pad.
  gridify.
  do 2 (apply f_equal2; try reflexivity).
  unfold rotation. 
  solve_matrix; try rewrite Ropp_div; autorewrite with Cexp_db trig_db; lca.
Qed.
Local Opaque X.

Local Transparent H.
Lemma invert_H : forall dim n, invert (@H dim n) ≡ H n.
Proof.
  intros dim n.
  unfold uc_equiv. simpl. 
  unfold pad_u, pad.
  gridify.
  do 2 (apply f_equal2; try reflexivity).
  unfold rotation. 
  solve_matrix; try rewrite Ropp_div; autorewrite with Cexp_db trig_db; lca.
Qed.
Local Opaque H.

Local Transparent Rz.
Lemma invert_Rz : forall dim n r, (invert (@Rz dim r n) ≡ Rz (- r) n)%ucom.
Proof.
  intros dim n r.
  unfold uc_equiv. simpl. 
  autorewrite with eval_db.
  gridify.
  do 2 (apply f_equal2; try reflexivity).
  unfold rotation. 
  solve_matrix; autorewrite with R_db Cexp_db trig_db; lca.
Qed.
Local Opaque Rz.

(** Programs with arbitrary control **)

(* Standard decomposition; see Qiskit's cu3 gate or Ch.4 of N & C *)
Definition CU {dim} θ ϕ λ c t : base_ucom dim :=
  Rz ((λ + ϕ)/2) c ;
  Rz ((λ - ϕ)/2) t ;
  CNOT c t ;
  uapp1 (U_R (-θ/2) 0 (-(ϕ + λ)/2)) t ;
  CNOT c t ;
  uapp1 (U_R (θ/2) ϕ 0) t.

(* Convert a program to be controlled by qubit q *)
Fixpoint control {dim} q (c : base_ucom dim) : base_ucom dim :=
  match c with
  | c1; c2 => control q c1; control q c2
  | uapp1 (U_R θ ϕ λ) n => CU θ ϕ λ q n
  | uapp2 U_CNOT m n => CCX q m n
  | _ => SKIP
  end.

Inductive is_fresh {U dim} : nat -> ucom U dim -> Prop :=
  | fresh_seq  : forall q c1 c2, is_fresh q c1 -> is_fresh q c2 -> is_fresh q (c1; c2)
  | fresh_app1 : forall q u n, q <> n -> is_fresh q (uapp1 u n)
  | fresh_app2 : forall q u m n, q <> m -> q <> n -> is_fresh q (uapp2 u m n)
  | fresh_app3 : forall q u m n p,  q <> m -> q <> n -> q <> p -> is_fresh q (uapp3 u m n p).

Fixpoint is_fresh_b {U dim} q (c : ucom U dim) :=
  match c with
  | c1 ; c2 => is_fresh_b q c1 && is_fresh_b q c2
  | uapp1 _ m => negb (m =? q)
  | uapp2 _ m n => negb (m =? q) && negb (n =? q)
  | uapp3 _ m n p => negb (m =? q) && negb (n =? q) && negb (p =? q)
  end.

Ltac simpl_fresh_b :=
  repeat match goal with
  | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : (_ =? _) = false |- _ => apply Nat.eqb_neq in H
  | |- _ && _ = true => apply andb_true_iff; split
  | |- negb _ = true => apply negb_true_iff
  | |- (_ =? _) = false => apply Nat.eqb_neq
  end.

Lemma is_fresh_b_equiv : forall U dim q (c : ucom U dim),
  is_fresh_b q c = true <-> is_fresh q c.
Proof.
  intros U dim q c.
  split; intro H.
  - induction c; simpl in H; simpl_fresh_b; constructor; auto.
  - induction c; inversion H; subst; simpl; simpl_fresh_b; auto.
Qed.

Lemma uc_well_typed_control : forall dim q (c : base_ucom dim),
  ((q < dim)%nat /\ is_fresh q c /\ uc_well_typed c) <-> 
  uc_well_typed (control q c).
Proof.
  intros dim q c.
  split.
  - intros [H [Hfr WT]].
    induction c; try dependent destruction u; simpl;
      inversion Hfr; inversion WT; subst.
    constructor.
    apply IHc1; auto.
    apply IHc2; auto.  
    1,2: repeat constructor; try assumption.
    all: try apply uc_well_typed_Rz; try apply uc_well_typed_CNOT; auto.
    1,2: apply uc_well_typed_H; auto.
  - intro H.
    induction c; try dependent destruction u.
    inversion H; subst.
    apply IHc1 in H2 as [? [? ?]].
    apply IHc2 in H3 as [_ [? ?]].
    repeat split; try constructor; auto.
    inversion H; subst.
    inversion H2; subst.
    apply uc_well_typed_CNOT in H5 as [? [? ?]].
    repeat split; try constructor; auto.
    inversion H; subst.
    repeat match goal with
       | H : uc_well_typed (_ ; _) |- _ => inversion H; subst; clear H
       end. 
    repeat split; auto.
    apply uc_well_typed_Rz in H7; auto. 
    apply uc_well_typed_CNOT in H8 as [? [? ?]].
    apply uc_well_typed_CNOT in H11 as [? [? ?]].
    constructor; auto.
Qed.  

Local Transparent SQIR.H X U1 Rz CNOT.
Lemma fresh_U1: forall dim r q1 q2, q1 <> q2 <-> is_fresh q1 (@U1 dim r q2).
Proof. 
  intros.
  split; intro H.
  constructor. auto. 
  inversion H. auto.
Qed.

Lemma fresh_X: forall dim q1 q2, q1 <> q2 <-> is_fresh q1 (@X dim q2).
Proof. 
  intros.
  split; intro H.
  constructor. auto. 
  inversion H. auto.
Qed.

Lemma fresh_H: forall dim q1 q2, q1 <> q2 <-> is_fresh q1 (@H dim q2).
Proof. 
  intros.
  split; intro H0.
  constructor. auto. 
  inversion H0. auto.
Qed.

Lemma fresh_CNOT: forall dim a b c, a <> b /\ a <> c <-> is_fresh a (@CNOT dim b c).
Proof. 
  intros.
  split; intro H.
  destruct H.
  constructor; auto. 
  inversion H; auto.
Qed.

Lemma fresh_CU : forall {dim} θ ϕ λ q c t,
  q <> c -> q <> t -> @is_fresh _ dim q (CU θ ϕ λ c t).
Proof. intros. repeat constructor; auto. Qed.

Ltac invert_is_fresh :=
  repeat match goal with
  | H : is_fresh _ _ |- _ => inversion H; subst; clear H
  end; clear_dups.

Lemma fresh_CCX : forall {dim} q c1 c2 t,
  q <> c1 /\ q <> c2 /\ q <> t <-> @is_fresh _ dim q (CCX c1 c2 t).
Proof. 
  intros. split. 
  intros [? [? ?]]. 
  repeat constructor; auto. 
  intro.
  invert_is_fresh. auto. 
Qed.

Lemma fresh_control : forall {dim} q1 q2 c,
  (q1 <> q2 /\ @is_fresh _ dim q1 c) <-> @is_fresh _ dim q1 (control q2 c).
Proof.
  intros dim q1 q2 c.
  split. 
  - intros [H1 H2].
    induction H2; simpl; try dependent destruction u.
    apply fresh_seq; auto.
    apply fresh_CU; auto.
    apply fresh_CCX; auto.
  - intro H.
    split.
    induction c; try dependent destruction u; inversion H; subst.
    auto.
    invert_is_fresh; auto.
    invert_is_fresh; auto. 
    induction c; try dependent destruction u; inversion H; subst.
    constructor; auto.
    constructor. invert_is_fresh; auto.
    constructor; invert_is_fresh; auto. 
Qed.
Local Opaque SQIR.H X U1 Rz CNOT.

(* Project onto the space where qubit q is in classical state b.
   TODO: possibly move to QuantumLib *)
Definition proj q dim (b : bool) := pad_u dim q (bool_to_matrix b).

Lemma WF_proj : forall q dim b, WF_Matrix (proj q dim b).
Proof. intros. unfold proj. auto with wf_db. Qed.
#[export] Hint Resolve WF_proj : wf_db.

Lemma f_to_vec_proj_eq : forall f q n b,
  (q < n)%nat -> f q = b -> 
  proj q n b × (f_to_vec n f) = f_to_vec n f.
Proof.
  intros f q n b ? ?.
  rewrite (f_to_vec_split 0 n q) by lia. 
  replace (n - 1 - q)%nat with (n - (q + 1))%nat by lia.
  unfold proj, pad_u, pad.
  gridify. 
  do 2 (apply f_equal2; try reflexivity). 
  destruct (f q); solve_matrix.
Qed.

Lemma f_to_vec_proj_neq : forall f q n b,
  (q < n)%nat -> f q <> b ->
  proj q n b × (f_to_vec n f) = Zero.
Proof.
  intros f q n b ? H.
  rewrite (f_to_vec_split 0 n q) by lia. 
  replace (n - 1 - q)%nat with (n - (q + 1))%nat by lia.
  unfold proj, pad_u, pad.
  gridify. 
  destruct (f q); destruct b; try easy; lma.
Qed.

(* We can use 'proj' to state that qubit q is in classical state b. *)
Definition classical {dim} q b (ψ : Vector (2 ^ dim)) := proj q dim b × ψ = ψ.

Lemma f_to_vec_classical : forall n q f,
  (q < n)%nat -> classical q (f q) (f_to_vec n f).
Proof.
  intros n q f Hq.
  unfold classical, proj.
  induction n; try lia.
  unfold pad_u, pad.
  replace (q + 1)%nat with (S q) by lia. 
  bdestructΩ (S q <=? S n); clear H.
  bdestruct (q =? n).
  - subst. replace (n - n)%nat with O by lia.
    simpl. Msimpl_light.
    restore_dims.
    rewrite kron_mixed_product.
    Msimpl_light; apply f_equal2; auto.
    destruct (f n); solve_matrix.
  - remember (n - q - 1)%nat as x.
    replace (n - q)%nat with (x + 1)%nat by lia.
    replace n with (q + 1 + x)%nat by lia.
    replace (2 ^ (x + 1))%nat with (2 ^ x * 2)%nat by unify_pows_two.
    rewrite <- id_kron.
    rewrite <- kron_assoc by auto with wf_db.
    replace (2 ^ (q + 1 + x) + (2 ^ (q + 1 + x) + 0))%nat with (2 ^ (q + 1 + x) * 2)%nat by lia.
    repeat rewrite Nat.pow_add_r.
    replace 1%nat with (1 * 1)%nat by lia. 
    rewrite kron_mixed_product; simpl.
    replace (q + 1 + x)%nat with n by lia.
    subst.
    Msimpl_light.
    rewrite <- IHn at 2; try lia.
    unfold pad_u, pad. 
    bdestructΩ (q + 1 <=? n); clear H0.
    replace (n - (q + 1))%nat with (n - q - 1)%nat by lia.
    restore_dims. reflexivity.
Qed.

Lemma proj_commutes_1q_gate : forall dim u q n b,
  q <> n ->
  proj q dim b × ueval_r dim n u = ueval_r dim n u × proj q dim b. 
Proof.
  intros dim u q n b neq.
  dependent destruction u; simpl.
  unfold proj.
  apply pad_A_B_commutes; auto with wf_db.
Qed.

Lemma proj_commutes_2q_gate : forall dim q n1 n2 b,
  q <> n1 -> q <> n2 ->
  proj q dim b × ueval_cnot dim n1 n2 = ueval_cnot dim n1 n2 × proj q dim b. 
Proof.
  intros dim q n1 n2 b neq1 neq2.
  unfold proj, ueval_cnot.
  apply pad_A_ctrl_commutes; auto with wf_db.
Qed.

Lemma proj_commutes : forall dim q1 q2 b1 b2,
  proj q1 dim b1 × proj q2 dim b2 = proj q2 dim b2 × proj q1 dim b1.
Proof.
  intros dim q1 q2 b1 b2.
  unfold proj, pad_u, pad.
  gridify; trivial.
  destruct b1; destruct b2; simpl; Qsimpl; reflexivity. 
Qed.

Lemma proj_twice_eq : forall dim q b,
  proj q dim b × proj q dim b = proj q dim b.
Proof.
  intros dim q b.
  unfold proj, pad_u, pad.
  gridify.
  destruct b; simpl; Qsimpl; reflexivity.
Qed.

Lemma proj_twice_neq : forall dim q b1 b2,
  b1 <> b2 -> proj q dim b1 × proj q dim b2 = Zero.
Proof.
  intros dim q b1 b2 neq.
  unfold proj, pad_u, pad.
  gridify.
  destruct b1; destruct b2; try contradiction; simpl; Qsimpl; reflexivity.
Qed.

(* TODO: move to QuantumLib *)

Lemma bra0_phase : forall ϕ, bra 0 × phase_shift ϕ = bra 0.
Proof. intros; solve_matrix. Qed.

Lemma bra1_phase : forall ϕ, bra 1 × phase_shift ϕ = Cexp ϕ .* bra 1.
Proof. intros; solve_matrix. Qed.

Hint Rewrite bra0_phase bra1_phase : bra_db.

Lemma braketbra_same : forall x y, bra x × (ket x × bra y) = bra y. 
Proof. intros. destruct x; destruct y; solve_matrix. Qed.

Lemma braketbra_diff : forall x y z, (x + y = 1)%nat -> bra x × (ket y × bra z) = Zero. 
Proof. intros. destruct x; destruct y; try lia; solve_matrix. Qed.

Hint Rewrite braketbra_same braketbra_diff using lia : bra_db.

(* Auxiliary proofs about the semantics of CU and TOFF *)
Lemma CU_correct : forall (dim : nat) θ ϕ λ c t,
  (t < dim)%nat -> c <> t ->
  uc_eval (CU θ ϕ λ c t) = proj c dim false .+ (proj c dim true) × (ueval_r dim t (U_R θ ϕ λ)).
Proof.
  intros.
  unfold proj; simpl.
  autorewrite with eval_db.
  unfold pad_u, pad.
  gridify. (* slow *)
  all: clear.
  all: autorewrite with M_db_light ket_db bra_db.
  all: rewrite Mplus_comm;
       repeat (apply f_equal2; try reflexivity).
  (* A little messy because we need to apply trig identities; 
     goal #1 = goal #3 and goal #2 = goal #4 *)
  - solve_matrix; autorewrite with R_db C_db RtoC_db Cexp_db trig_db;
      try lca; field_simplify_eq; try nonzero; group_Cexp.
    + simpl. rewrite Rplus_comm; setoid_rewrite sin2_cos2; easy.
    + rewrite Copp_mult_distr_l, Copp_mult_distr_r. 
      repeat rewrite <- Cmult_assoc; rewrite <- Cmult_plus_distr_l.  
      autorewrite with RtoC_db. rewrite Ropp_involutive.
      setoid_rewrite sin2_cos2. rewrite Cmult_1_r.
      apply f_equal; lra.
  - rewrite <- Mscale_kron_dist_l.
    repeat rewrite <- Mscale_kron_dist_r.
    repeat (apply f_equal2; try reflexivity).
    (* Note: These destructs shouldn't be necessary - weakness in destruct_m_eq'. 
       The mat_equiv branch takes a more principled approach (see lma there, port). *)
    solve_matrix; destruct x0; try destruct x0; simpl;
    autorewrite with R_db C_db Cexp_db trig_db; try lca;
    rewrite RtoC_opp; field_simplify_eq; try nonzero; group_Cexp;
    repeat rewrite <- Cmult_assoc. 
    + unfold Cminus.
      rewrite Copp_mult_distr_r, <- Cmult_plus_distr_l. 
      apply f_equal2; [apply f_equal; lra|].
      autorewrite with RtoC_db.
      rewrite <- Rminus_unfold, <- cos_plus.
      apply f_equal. apply f_equal. lra.
    + apply f_equal2; [apply f_equal; lra|].
      apply c_proj_eq; simpl; try lra.
      R_field_simplify.
      rewrite <- sin_2a.
      apply f_equal; lra.
    + rewrite Copp_mult_distr_r.
      apply f_equal2; [apply f_equal; lra|].
      apply c_proj_eq; simpl; try lra.
      R_field_simplify.
      replace (-2)%R with (-(2))%R by lra.
      repeat rewrite <- Ropp_mult_distr_l. 
      apply f_equal.
      rewrite <- sin_2a.
      apply f_equal; lra.
    + rewrite Copp_mult_distr_r.
      rewrite <- Cmult_plus_distr_l.
      apply f_equal2; [apply f_equal; lra|].
      autorewrite with RtoC_db.      
      rewrite Rplus_comm; rewrite <- Rminus_unfold, <- cos_plus.
      apply f_equal; apply f_equal; lra.
  - solve_matrix; autorewrite with R_db C_db RtoC_db Cexp_db trig_db; try lca;
      field_simplify_eq; try nonzero; group_Cexp.
    + rewrite Rplus_comm; setoid_rewrite sin2_cos2; easy.
    + rewrite Copp_mult_distr_l, Copp_mult_distr_r. 
      repeat rewrite <- Cmult_assoc; rewrite <- Cmult_plus_distr_l.  
      autorewrite with RtoC_db. rewrite Ropp_involutive.
      setoid_rewrite sin2_cos2. rewrite Cmult_1_r.
      apply f_equal; lra.
  - rewrite <- 3 Mscale_kron_dist_l.
    repeat rewrite <- Mscale_kron_dist_r.
    repeat (apply f_equal2; try reflexivity).
    solve_matrix; destruct x; try destruct x; simpl;
    autorewrite with R_db C_db Cexp_db trig_db; try lca;
    try rewrite RtoC_opp; field_simplify_eq; try nonzero; group_Cexp;
    repeat rewrite <- Cmult_assoc. 
    + unfold Cminus.
      rewrite Copp_mult_distr_r, <- Cmult_plus_distr_l. 
      apply f_equal2; [apply f_equal; lra|].
      autorewrite with RtoC_db.
      rewrite <- Rminus_unfold, <- cos_plus.
      apply f_equal. apply f_equal. lra.
    + apply f_equal2; [apply f_equal; lra|].
      apply c_proj_eq; simpl; try lra.
      R_field_simplify.
      rewrite <- sin_2a.
      apply f_equal; lra.
    + rewrite Copp_mult_distr_r.
      apply f_equal2; [apply f_equal; lra|].
      apply c_proj_eq; simpl; try lra.
      R_field_simplify.
      replace (-2)%R with (-(2))%R by lra.
      repeat rewrite <- Ropp_mult_distr_l. 
      apply f_equal.
      rewrite <- sin_2a.
      apply f_equal; lra.
    + rewrite Copp_mult_distr_r.
      rewrite <- Cmult_plus_distr_l.
      apply f_equal2; [apply f_equal; lra|].
      autorewrite with RtoC_db.      
      rewrite Rplus_comm; rewrite <- Rminus_unfold, <- cos_plus.
      apply f_equal; apply f_equal; lra.
Qed.

Lemma UR_not_WT : forall (dim a b : nat) r r0 r1,
  ~ uc_well_typed (@uapp1 _ dim (U_R r r0 r1) b) ->
  uc_eval (@CU dim r r0 r1 a b) = Zero.
Proof.
  intros dim a b r r0 r1 H.
  simpl. unfold pad_u.
  assert (@pad 1 b dim (rotation (r / 2) r0 0) = Zero).
  { unfold pad. gridify. 
    assert (uc_well_typed (@uapp1 _ (b + 1 + d) (U_R r r0 r1) b)).
    constructor; lia.
    contradiction. }
  rewrite H0.
  Msimpl_light.
  reflexivity.
Qed.

Lemma UR_not_fresh : forall (dim a b : nat) r r0 r1,
  ~ is_fresh a (@uapp1 _ dim (U_R r r0 r1) b) ->
  uc_eval (@CU dim r r0 r1 a b) = Zero.
Proof.
  intros dim a b r r0 r1 H.
  simpl. 
  assert (uc_eval (@CNOT dim a b) = Zero).
  { assert (a = b).
    apply Classical_Prop.NNPP.
    intro contra. contradict H.
    constructor; assumption.
    autorewrite with eval_db. gridify. }
  rewrite H0.
  Msimpl_light.
  reflexivity.
Qed.

Lemma UR_a_geq_dim : forall (dim a b : nat) r r0 r1,
  (dim <= a)%nat ->
  uc_eval (@CU dim r r0 r1 a b) = Zero.
Proof.
  intros dim a b r r0 r1 H.
  simpl. 
  assert (uc_eval (@Rz dim ((r1 + r0) / 2) a) = Zero).
  { autorewrite with eval_db. gridify. }
  rewrite H0.
  Msimpl_light.
  reflexivity.
Qed.
Local Opaque CU.

Lemma f_to_vec_X : forall (n i : nat) (f : nat -> bool), (i < n)%nat ->
  (uc_eval (X i)) × (f_to_vec n f) = f_to_vec n (update f i (¬ (f i))).
Proof.
  intros. rewrite denote_X. apply f_to_vec_σx. auto.
Qed.

Lemma f_to_vec_CNOT : forall (n i j : nat) (f : nat -> bool),
  (i < n)%nat -> (j < n)%nat -> i <> j ->
  (uc_eval (SQIR.CNOT i j)) × (f_to_vec n f) = f_to_vec n (update f j (f j ⊕ f i)).
Proof.
   intros. rewrite denote_cnot. unfold ueval_cnot. apply f_to_vec_cnot; auto.
Qed.

Lemma f_to_vec_SWAP : forall (n i j : nat) (f : nat -> bool),
  (i < n)%nat -> (j < n)%nat -> i <> j ->
  uc_eval (SWAP i j) × (f_to_vec n f) = f_to_vec n (fswap f i j).
Proof.
   intros. rewrite denote_swap_alt. apply f_to_vec_swap; auto.
Qed.

Lemma f_to_vec_Rz : forall (n i : nat) (θ : R) (f : nat -> bool),
  (i < n)%nat ->
  (uc_eval (SQIR.Rz θ i)) × (f_to_vec n f) = 
    (Cexp (b2R (f i) * θ)) .* f_to_vec n f.
Proof.
   intros. rewrite denote_Rz. apply f_to_vec_phase_shift; auto.
Qed.

Lemma f_to_vec_H : forall (n i : nat) (f : nat -> bool),
  (i < n)%nat ->
  (uc_eval (SQIR.H i)) × (f_to_vec n f) 
      = /√2 .* ((f_to_vec n (update f i false)) 
                .+ (Cexp (b2R (f i) * PI)) .* f_to_vec n (update f i true)).
Proof.
   intros. rewrite denote_H. apply f_to_vec_hadamard; auto.
Qed.

Hint Rewrite f_to_vec_CNOT f_to_vec_Rz f_to_vec_X using lia : f_to_vec_db.

Ltac f_to_vec_simpl_body :=
  autorewrite with f_to_vec_db;
  try match goal with
      | |- context [uc_eval (SQIR.H _) × f_to_vec _ _] =>
            rewrite f_to_vec_H by lia
      end;
  distribute_scale;
  distribute_plus;
  try match goal with
      | |- context [update (update (update _ ?x _) ?y _) ?z _ ] => 
            rewrite (update_twice_neq _ x y) by lia
      end.

Ltac f_to_vec_simpl := repeat f_to_vec_simpl_body.

Lemma f_to_vec_CCX : forall (dim a b c : nat) (f : nat -> bool),
   (a < dim)%nat -> (b < dim)%nat -> (c < dim)%nat -> a <> b -> a <> c -> b <> c ->
  (uc_eval (CCX a b c)) × (f_to_vec dim f) 
      = f_to_vec dim (update f c (f c ⊕ (f a && f b))).
Proof. 
  intros.
  unfold CCX, T, TDAG.
  simpl uc_eval.
  repeat rewrite Mmult_assoc.
  f_to_vec_simpl.
  rewrite (update_same _ b).
  2: destruct (f a); destruct (f b); reflexivity.
  destruct (f a); destruct (f b); destruct (f c); simpl.
  all: autorewrite with R_db C_db Cexp_db.
  all: cancel_terms (Cexp (PI * / 4)).
  all: group_Cexp.
  all: repeat match goal with 
       | |- context [Cexp ?r] => field_simplify r
       end.
  all: autorewrite with R_db C_db Cexp_db.
  all: rewrite Mscale_plus_distr_r.
  all: distribute_scale; group_radicals.
  all: lma.
Qed.

Lemma CCX_a_geq_dim : forall (dim a b c : nat),
  (dim <= a)%nat -> uc_eval (@CCX dim a b c) = Zero.
Proof.
  intros dim a b c H.
  unfold CCX.
  simpl.
  rewrite (denote_cnot dim a b).
  unfold ueval_cnot, pad_ctrl, pad.
  gridify.
Qed.

Lemma CCX_not_WT : forall (dim a b c : nat),
  ~ uc_well_typed (@CNOT dim b c) -> uc_eval (@CCX dim a b c) = Zero.
Proof.
  intros dim a b c H.
  unfold CCX.
  simpl.
  assert (uc_eval (@CNOT dim b c) = Zero).
  { autorewrite with eval_db.
    gridify.
    assert (uc_well_typed (@CNOT (b + (1 + d + 1) + d0) b (b + 1 + d))).
    apply uc_well_typed_CNOT; repeat split; lia.  
    contradiction. 
    assert (uc_well_typed (@CNOT (c + (1 + d + 1) + d0) (c + 1 + d) c)).
    apply uc_well_typed_CNOT; repeat split; lia.  
    contradiction. }
  rewrite H0.
  Msimpl_light.
  reflexivity.
Qed.

Local Transparent CNOT.
Lemma CCX_not_fresh : forall (dim a b c : nat),
  ~ is_fresh a (@CNOT dim b c) -> uc_eval (@CCX dim a b c) = Zero.
Proof.
  intros dim a b c H.
  unfold CCX.
  simpl.
  assert (ueval_cnot dim  a b = Zero \/ ueval_cnot dim  a c = Zero).
  { assert (a = b \/ a = c).
    apply Classical_Prop.NNPP.
    intro contra. contradict H.
    apply Classical_Prop.not_or_and in contra as [? ?].
    constructor; assumption.
    destruct H0.
    left. autorewrite with eval_db. gridify.
    right. autorewrite with eval_db. gridify. }
  destruct H0; rewrite H0; Msimpl_light; reflexivity.
Qed.
Local Opaque CNOT.
Local Opaque CCX.

Lemma CCX_correct : forall (dim : nat) a b c,
  (b < dim)%nat -> (c < dim)%nat -> a <> b -> a <> c -> b <> c ->
  uc_eval (CCX a b c) = proj a dim false .+ (proj a dim true) × (ueval_cnot dim b c).
  intros dim a b c ? ? ? ? ?.
  bdestruct (a <? dim).
  2: { rewrite CCX_a_geq_dim by assumption.
       unfold proj, pad_u, pad. gridify. }
  eapply equal_on_basis_states_implies_equal; auto with wf_db.
  intro f.
  rewrite f_to_vec_CCX by auto.
  rewrite Mmult_plus_distr_r.
  rewrite proj_commutes_2q_gate by auto.
  rewrite Mmult_assoc.
  destruct (f a) eqn:fa. 
  - rewrite (f_to_vec_proj_eq _ _ _ true); auto. 
    rewrite (f_to_vec_proj_neq _ _ _ false); auto. 
    2: rewrite fa; easy.
    setoid_rewrite f_to_vec_CNOT; auto.
    rewrite andb_true_l.
    Msimpl_light; reflexivity.
  - rewrite (f_to_vec_proj_eq _ _ _ false); auto. 
    rewrite (f_to_vec_proj_neq _ _ _ true); auto. 
    2: rewrite fa; easy.
    rewrite andb_false_l, xorb_false_r.
    rewrite update_same by auto.
    Msimpl_light; reflexivity.
Qed.

(* generalization of proj_commutes_1q_gate and proj_commutes_2q_gate *)
Lemma proj_fresh_commutes : forall dim q b (c : base_ucom dim),
  is_fresh q c ->
  proj q dim b × uc_eval c = uc_eval c × proj q dim b.
Proof.
  intros.
  induction c; simpl; inversion H; subst.
  rewrite <- (Mmult_assoc (proj _ _ _)).
  rewrite (Mmult_assoc _ _ (proj _ _ _)).
  rewrite <- IHc1, IHc2 by auto.
  rewrite Mmult_assoc. reflexivity.
  apply proj_commutes_1q_gate; auto.
  apply proj_commutes_2q_gate; auto.
  Msimpl_light. reflexivity.
Qed.

Lemma control_correct : forall (dim : nat) q (c : base_ucom dim),
  is_fresh q c -> uc_well_typed c -> 
  uc_eval (control q c) = proj q dim false .+ (proj q dim true) × (uc_eval c).
Proof.
  intros dim q c Hfr WT.
  induction c; try dependent destruction u; simpl;
  inversion WT; inversion Hfr; subst.
  rewrite IHc1, IHc2 by auto.
  distribute_plus.
  rewrite Mmult_assoc. 
  rewrite <- proj_fresh_commutes by auto.
  rewrite Mmult_assoc, <- (Mmult_assoc (uc_eval c2)).
  rewrite <- proj_fresh_commutes by auto.
  repeat rewrite <- Mmult_assoc.
  rewrite 2 proj_twice_eq.
  rewrite 2 proj_twice_neq; try easy.
  Msimpl_light. reflexivity.
  apply CU_correct; auto.
  apply CCX_correct; auto.
Qed.

Lemma control_not_WT : forall {dim} n (c : base_ucom dim),
  not (uc_well_typed c) -> uc_eval (control n c) = Zero.
Proof.
  intros dim n c nWT.
  induction c; try dependent destruction u.
  - assert (not (uc_well_typed c1) \/ not (uc_well_typed c2)).
    apply Classical_Prop.not_and_or.
    intros [contra1 contra2].
    contradict nWT.
    constructor; auto.
    simpl.
    destruct H as [H | H].
    rewrite IHc1 by assumption.
    Msimpl. reflexivity.
    rewrite IHc2 by assumption.
    Msimpl. reflexivity.
  - apply UR_not_WT. assumption.
  - apply CCX_not_WT. assumption.
Qed.

Lemma control_not_fresh : forall {dim} n (c : base_ucom dim),
  not (is_fresh n c) -> uc_eval (control n c) = Zero.
Proof.
  intros dim n c nfr.
  induction c; try dependent destruction u.
  - assert (not (is_fresh n c1) \/ not (is_fresh n c2)).
    apply Classical_Prop.not_and_or.
    intros [contra1 contra2].
    contradict nfr.
    constructor; auto.
    simpl.
    destruct H as [H | H].
    rewrite IHc1 by assumption.
    Msimpl. reflexivity.
    rewrite IHc2 by assumption.
    Msimpl. reflexivity.
  - apply UR_not_fresh. assumption.
  - apply CCX_not_fresh. assumption.
Qed.

Lemma control_q_geq_dim : forall {dim} q (c : base_ucom dim),
  (dim <= q)%nat -> uc_eval (control q c) = Zero.
Proof.
  intros dim q c Hq.
  induction c; try dependent destruction u; simpl.
  - rewrite IHc1. Msimpl_light. trivial. 
  - apply UR_a_geq_dim. assumption.
  - apply CCX_a_geq_dim. assumption.
Qed.

(* c ≡ c' implies (uc_well_typed c <-> uc_well_typed c' *)
Lemma control_cong : forall {dim} n (c c' : base_ucom dim),
  c ≡ c' -> (is_fresh n c <-> is_fresh n c') -> control n c ≡ control n c'.
Proof.
  intros dim n c c' H Hfr.
  unfold uc_equiv in *.
  destruct (uc_well_typed_b c) eqn:WT.
  2: { rewrite <- not_true_iff_false in WT.
       rewrite uc_well_typed_b_equiv in WT.
       rewrite control_not_WT by assumption.
       rewrite <- uc_eval_zero_iff in WT.
       rewrite WT in H.
       symmetry in H.
       rewrite uc_eval_zero_iff in H.
       rewrite control_not_WT by assumption.
       reflexivity. }
  apply uc_well_typed_b_equiv in WT.
  assert (uc_well_typed c').
  { apply WT_if_nonzero.
    intro contra.
    rewrite contra in H.
    rewrite <- uc_eval_nonzero_iff in WT.
    contradiction. }
  destruct (is_fresh_b n c) eqn:Hfr'.
  2: { rewrite <- not_true_iff_false in Hfr'.
       rewrite is_fresh_b_equiv in Hfr'.
       rewrite control_not_fresh by assumption.
       rewrite Hfr in Hfr'.
       rewrite control_not_fresh by assumption.
       reflexivity. }
  apply is_fresh_b_equiv in Hfr'.
  assert (is_fresh n c').
  { apply Hfr. assumption. }
  rewrite 2 control_correct by assumption.
  rewrite H.
  reflexivity.
Qed.

(* Sanity check *)
Local Transparent X CU.
Lemma CNOT_is_control_X : forall dim c t,
  uc_eval (@CNOT dim c t) = uc_eval (control c (X t)).
Proof.
  intros dim c t.
  bdestruct (c <? dim).
  2: simpl; autorewrite with eval_db; gridify.
  bdestruct (t <? dim).
  2: simpl; autorewrite with eval_db; gridify.
  bdestruct (c =? t).
  simpl; autorewrite with eval_db; gridify.
  rewrite control_correct; try constructor; auto.
  unfold proj.
  autorewrite with eval_db.
  gridify.
  all: rewrite Mplus_comm; reflexivity.
Qed.
Local Opaque X CU.

Lemma invert_fresh : forall dim q (u : base_ucom dim),
  is_fresh q u <-> is_fresh q (invert u).
Proof.
  intros dim q u.
  split; intro H.
  induction u; try dependent destruction u; inversion H; subst; constructor; auto.
  induction u; try dependent destruction u; inversion H; subst; constructor; auto.
Qed.

Lemma proj_adjoint : forall dim q b, (proj q dim b) † = proj q dim b.
Proof.
  intros.
  unfold proj, pad_u, pad.
  gridify.
  destruct b; simpl; Msimpl; reflexivity.
Qed.

Lemma invert_control : forall dim q (u : base_ucom dim),
  invert (control q u) ≡ control q (invert u).
Proof.
  intros dim q u.
  unfold uc_equiv.
  destruct (uc_well_typed_b u) eqn:WT.
  2: { rewrite <- not_true_iff_false in WT.
       rewrite uc_well_typed_b_equiv in WT.
       rewrite <- invert_correct.
       rewrite (control_not_WT _ u) by assumption.
       rewrite uc_well_typed_invert in WT.
       rewrite (control_not_WT _ (invert _)) by assumption.
       lma. }
  rewrite uc_well_typed_b_equiv in WT.
  destruct (is_fresh_b q u) eqn:Hfr.
  2: { rewrite <- not_true_iff_false in Hfr.
       rewrite is_fresh_b_equiv in Hfr.
       rewrite <- invert_correct.
       rewrite (control_not_fresh _ u) by assumption.
       rewrite invert_fresh in Hfr.
       rewrite (control_not_fresh _ (invert _)) by assumption.
       lma. }
  rewrite is_fresh_b_equiv in Hfr.
  assert (uc_well_typed (invert u)).
  rewrite <- uc_well_typed_invert; auto.
  assert (is_fresh q (invert u)).
  rewrite <- invert_fresh; auto.
  rewrite <- invert_correct.
  rewrite control_correct by assumption.
  rewrite control_correct by assumption.
  rewrite <- invert_correct.
  distribute_adjoint.
  rewrite 2 proj_adjoint.
  rewrite invert_correct.
  rewrite proj_fresh_commutes by assumption.
  reflexivity.
Qed.


Lemma proj_control_true : forall {dim} q c,
  is_fresh q c ->
  uc_eval (control q c) × proj q dim true = proj q dim true × uc_eval c.
Proof. 
  intros.
  destruct (uc_well_typed_b c) eqn:WT.
  apply uc_well_typed_b_equiv in WT.
  rewrite control_correct by auto.
  rewrite Mmult_plus_distr_r.
  rewrite proj_fresh_commutes by auto.
  rewrite proj_twice_neq.
  rewrite Mmult_assoc, proj_twice_eq.
  Msimpl. reflexivity.
  easy.
  apply not_true_iff_false in WT.
  rewrite uc_well_typed_b_equiv in WT.
  rewrite control_not_WT by auto.
  apply uc_eval_zero_iff in WT.
  rewrite WT.
  Msimpl. reflexivity.
Qed.

Lemma proj_control_false : forall {dim} q c,
  is_fresh q c -> uc_well_typed c ->
  uc_eval (control q c) × proj q dim false = proj q dim false.
Proof.
  intros.
  rewrite control_correct by auto.
  rewrite Mmult_plus_distr_r.
  rewrite proj_fresh_commutes by auto.
  rewrite proj_twice_eq.
  rewrite Mmult_assoc, proj_twice_neq.
  Msimpl. reflexivity.
  easy.
Qed.

Lemma proj_CNOT_ctl_true : forall dim m n,
  m <> n ->
  uc_eval (CNOT m n) × proj m dim true = proj m dim true × uc_eval (X n).
Proof.
  intros dim m n H.
  unfold proj.
  autorewrite with eval_db.
  gridify; Qsimpl; reflexivity.
Qed.

Lemma proj_CNOT_ctl_false : forall dim m n,
  (n < dim)%nat -> m <> n ->
  uc_eval (CNOT m n) × proj m dim false = proj m dim false.
Proof.
  intros dim m n H1 H2.
  unfold proj.
  autorewrite with eval_db.
  gridify; Qsimpl; reflexivity.
Qed.

Lemma proj_X : forall dim q b,
  uc_eval (X q) × proj q dim b = proj q dim (negb b) × uc_eval (X q).
Proof. 
  intros.
  unfold proj.
  autorewrite with eval_db.
  gridify.
  destruct b; simpl; Qsimpl; reflexivity.
Qed.

(** n iterations of a program **)

Fixpoint niter {dim} n (c : base_ucom dim) : base_ucom dim :=
  match n with
  | 0    => SKIP
  | 1    => c 
  | S n' => niter n' c ; c
  end.

Lemma uc_well_typed_niter : forall {d} (c : base_ucom d) i,
  uc_well_typed c -> uc_well_typed (niter i c).
Proof.
  intros.
  induction i; simpl.
  apply uc_well_typed_ID.
  apply uc_well_typed_implies_dim_nonzero in H.
  assumption.
  destruct i; try assumption.
  constructor; assumption.
Qed.

Lemma niter_correct : forall dim (c : base_ucom dim) n,
  (dim > 0)%nat -> uc_eval (niter n c) = n ⨉ (uc_eval c).
Proof.
  intros dim c n Hdim.
  induction n; simpl.
  apply denote_SKIP; auto.
  destruct n. simpl. Msimpl. reflexivity.
  remember (S n) as n'.
  simpl. rewrite IHn.
  reflexivity.
Qed.

Lemma niter_control_commute : forall d (c : base_ucom d) i j,
  (i > 0)%nat ->
  niter i (control j c) ≡ control j (niter i c).
Proof.
  intros d c i j Hi.
  destruct i; try lia.
  induction i. 
  reflexivity.
  replace (niter (S (S i)) (control j c)) with (niter (S i) (control j c) ; control j c) by reflexivity.
  rewrite IHi; try lia.
  reflexivity.
Qed.

Lemma is_fresh_niter : forall {d} (c : base_ucom d) q i,
  (i > 0)%nat -> is_fresh q c -> is_fresh q (niter i c).
Proof.
  intros.
  destruct i; try lia.
  induction i. 
  simpl. assumption.
  replace (niter (S (S i)) c) with (niter (S i) c ; c) by reflexivity. 
  constructor; try assumption.
  apply IHi. lia.
Qed.

(** Padding lemmas to ease composition **)

(* General qubit re-labeling function. *)
Fixpoint map_qubits {U dim} (f : nat -> nat) (c : ucom U dim) : ucom U dim :=
  match c with
  | c1; c2 => map_qubits f c1; map_qubits f c2
  | uapp1 u n => uapp1 u (f n)
  | uapp2 u m n => uapp2 u (f m) (f n)
  | uapp3 u m n p => uapp3 u (f m) (f n) (f p)
  end.
  
(* Change a program's dimension *)
(* TODO: Is there a nicer way to write this? *)
Fixpoint cast {U dim} (c : ucom U dim) dim' : ucom U dim' := 
  match c with 
  | c1; c2 => cast c1 dim' ; cast c2 dim'
  | uapp1 u n => uapp1 u n
  | uapp2 u m n => uapp2 u m n
  | uapp3 u m n p => uapp3 u m n p
  end.                                                     

Lemma typed_cast : forall {U n} (c : ucom U n) (n' : nat),
  uc_well_typed c -> (n <= n')%nat -> uc_well_typed (cast c n').
Proof.
  intros.
  induction H; simpl; constructor; try lia.
  apply IHuc_well_typed1. apply IHuc_well_typed2.
Qed.

Lemma uc_well_typed_map_qubits : forall U dim k (c : ucom U dim),
  uc_well_typed c -> uc_well_typed (cast (map_qubits (fun q => k + q)%nat c) (k + dim)%nat) .
Proof.
  intros U dim k c WT.
  induction c; simpl; inversion WT; subst; constructor; try lia.
  apply IHc1; auto.
  apply IHc2; auto.
Qed.

Lemma cast_control_commute : forall d d' (c : base_ucom d) i,
  cast (control i c) d' = control i (cast c d').
Proof.
  intros d d' c i.
  induction c; try dependent destruction u; try reflexivity.
  simpl. rewrite IHc1, IHc2. reflexivity.
Qed.

Lemma cast_niter_commute : forall d d' (c : base_ucom d) i,
  cast (niter i c) d' = niter i (cast c d').
Proof.
  intros d d' c i.
  induction i; simpl.
  reflexivity.
  destruct i; try reflexivity.
  remember (S i) as i'.
  simpl cast. rewrite IHi. reflexivity.
Qed.

Lemma map_qubits_fresh : forall k n q (c : base_ucom n) n',
  (q < k)%nat ->
  is_fresh q (cast (map_qubits (fun i => k + i) c)%nat n').
Proof.
  intros k n q c n' Hq.
  induction c; try dependent destruction u; simpl; constructor; 
  try assumption; try lia.
Qed.
                                                     
Lemma pad_dims_r : forall {dim} (c : base_ucom dim) (k : nat),
  uc_well_typed c ->
  (uc_eval c) ⊗ I (2^k) = uc_eval (cast c (dim + k)).  
Proof.
  intros dim c k H.
  induction c; try dependent destruction u.
  - inversion H; subst.
    simpl. rewrite <- IHc1, <- IHc2; trivial.
    restore_dims; Msimpl; reflexivity.
  - simpl. inversion H; subst.
    autorewrite with eval_db.
    gridify; reflexivity.
  - simpl. inversion H; subst.
    autorewrite with eval_db.
    gridify; reflexivity.
Qed.

Lemma pad_dims_l : forall {dim} (c : base_ucom dim) (k : nat),
  I (2^k) ⊗ (uc_eval c) = uc_eval (cast (map_qubits (fun q => k + q) c) (k + dim))%nat.  
Proof.
  intros.
  induction c; try dependent destruction u; simpl.
  - rewrite <- IHc1, <- IHc2.
    restore_dims; Msimpl. reflexivity.
  - autorewrite with eval_db.
    gridify; reflexivity.
  - autorewrite with eval_db.
    gridify; reflexivity.
Qed.

Lemma cast_cong_r : forall {dim} (u u' : base_ucom dim) n,
  uc_well_typed u -> (u ≡ u')%ucom -> (cast u (dim + n) ≡ cast u' (dim + n))%ucom.
Proof.
  intros dim u u' n WT H.
  unfold uc_equiv in *. 
  rewrite <- 2 pad_dims_r.
  rewrite H. reflexivity.
  apply uc_eval_nonzero_iff.
  apply uc_eval_nonzero_iff in WT.
  rewrite <- H; assumption.
  assumption.
Qed.

Lemma cast_cong_l : forall {dim} (u u' : base_ucom dim) n,
  (u ≡ u')%ucom -> 
  (cast (UnitaryOps.map_qubits (fun q : nat => (n + q)%nat) u) (n + dim) ≡ 
   cast (UnitaryOps.map_qubits (fun q : nat => (n + q)%nat) u') (n + dim))%ucom.
Proof.
  intros dim u u' n H.
  unfold uc_equiv in *. 
  rewrite <- 2 pad_dims_l.
  rewrite H. reflexivity.
Qed.

(** n copies of a gate in parallel **)

Fixpoint npar' dim n (U : base_Unitary 1) : base_ucom dim :=
  match n with
  | 0 => SKIP 
  | S n' => npar' dim n' U ; uapp1 U n'
  end.
Definition npar n U := npar' n n U.

Lemma npar_correct : forall n U,
  (n > 0)%nat -> uc_eval (npar n U) = n ⨂ (@uc_eval 1 (uapp1 U 0)).
Proof.
  assert (H : forall dim n U,
    (0 < dim)%nat -> (n <= dim)%nat -> 
    uc_eval (npar' dim n U) = (n ⨂ (@uc_eval 1 (uapp1 U 0))) ⊗ I (2 ^ (dim - n))).
  { intros dim n U Hdim Hn. 
    induction n.
    - replace (dim - 0)%nat with dim by lia. 
      Msimpl_light. simpl. rewrite denote_SKIP; auto.
    - simpl.
      rewrite IHn; try lia. 
      simpl.
      dependent destruction U.
      autorewrite with eval_db.
      bdestruct_all.       
      replace (dim - (n + 1))%nat with (dim - (S n))%nat by lia.
      replace (2 ^ (dim - n))%nat with (2 * 2 ^ (dim - (S n)))%nat by unify_pows_two.
      rewrite <- id_kron.
      rewrite <- kron_assoc by auto with wf_db.
      simpl I. Msimpl_light. 
      replace (2 ^ dim)%nat with (2 ^ n * 2 * 2 ^ (dim - S n))%nat by unify_pows_two.
      repeat rewrite kron_mixed_product.
      Msimpl_light. 
      reflexivity. }
  intros.
  unfold npar.
  rewrite H; auto.
  replace (n - n)%nat with O by lia.
  simpl I. rewrite kron_1_r.
  reflexivity.
Qed.

Lemma npar_WT : forall n U, (n > 0)%nat -> uc_well_typed (npar n U).
Proof.
  assert (H: forall dim n U, (0 < dim)%nat -> (n <= dim)%nat -> 
    uc_well_typed (npar' dim n U)).
  { intros dim n U Hdim Hn.
    induction n; simpl. apply uc_well_typed_ID. auto. 
    constructor. apply IHn. lia.
    constructor. lia. }
  intros.
  unfold npar.
  apply H; auto.
Qed.

(* Common use case: *)
Lemma npar_H : forall n,
  (n > 0)%nat -> uc_eval (npar n U_H) = n ⨂ hadamard.
Proof.
  intros.
  rewrite npar_correct by auto. 
  simpl. rewrite hadamard_rotation.
  unfold pad_u, pad. bdestruct_all.
  simpl I. Msimpl_light.
  reflexivity.
Qed.

(** Compose arbitrary programs in parallel **)

Definition inPar {U dim1 dim2} (c1 : ucom U dim1) (c2 : ucom U dim2) :=
  (cast c1 (dim1 + dim2)); (cast (map_qubits (fun q => dim1 + q)%nat c2) (dim1 + dim2)).

Lemma inPar_WT : forall {U dim1 dim2} (c1 : ucom U dim1) (c2 : ucom U dim2),
  uc_well_typed c1 -> uc_well_typed c2 -> uc_well_typed (inPar c1 c2).
Proof.
  intros U dim1 dim2 c1 c2 WTc1 WTc2.
  unfold inPar.
  apply WT_seq.
  - clear - WTc1.
    induction WTc1; simpl; constructor; try lia; assumption.
  - clear - WTc2. 
    induction WTc2; simpl; constructor; try lia; assumption.
Qed.

Lemma inPar_correct : forall {dim1 dim2} (c1 : base_ucom dim1) (c2 : base_ucom dim2),
  uc_well_typed c1 -> uc_eval (inPar c1 c2) = (uc_eval c1) ⊗ (uc_eval c2).
Proof.
  intros dim1 dim2 c1 c2 WTc1.
  simpl.
  rewrite <- (pad_dims_r c1); try assumption.
  rewrite <- pad_dims_l.
  restore_dims.
  rewrite kron_mixed_product.
  Msimpl.
  reflexivity.
Qed.
