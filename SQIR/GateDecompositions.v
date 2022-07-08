Require Export Equivalences.

Local Open Scope ucom_scope.

(** Proofs of decompositions for useful multi-qubit gates. 
    Used in ExtractionGateSet. **)

Definition P8 {dim} n : base_ucom dim := Rz (PI / 8) n.

Definition P8DAG {dim} n : base_ucom dim := Rz (- (PI / 8)) n.

Definition CH {dim} (a b : nat) : base_ucom dim := 
  U3 (PI/4) 0 0 b ; CNOT a b ; U3 (- (PI/4)) 0 0 b. 

Definition CU1 {dim} r1 (a b : nat) : base_ucom dim := 
  U1 (r1/2) a ; U1 (r1/2) b ; CNOT a b ; U1 (- (r1/2)) b ; CNOT a b.

Definition CU2 {dim} r1 r2 (a b : nat) : base_ucom dim := 
  U1 ((r2+r1)/2) a ; U1 ((r2-r1)/2) b ; CNOT a b ;
  U3 (-(PI/4)) 0 (-(r1+r2)/2) b ; CNOT a b ; U3 (PI/4) r1 0 b.

Definition CU3 {dim} r1 r2 r3 (a b : nat) : base_ucom dim := 
  U1 ((r3+r2)/2) a ; U1 ((r3-r2)/2) b ; CNOT a b ;
  U3 (-(r1/2)) 0 (-(r2+r3)/2) b ; CNOT a b ; U3 (r1/2) r2 0 b.

Definition CCU1 {dim} r1 (a b c : nat) : base_ucom dim := 
  CU1 (r1/2) a b ; CNOT b c ; CU1 (-r1/2) a c ; CNOT b c ; CU1 (r1/2) a c.

Definition CSWAP {dim} (a b c : nat) : base_ucom dim := 
  CNOT c b ; CCX a b c ; CNOT c b.

(* From https://qiskit.org/documentation/_modules/qiskit/circuit/library/standard_gates/x.html#C3XGate *)
Definition C3X {dim} (a b c d : nat) : base_ucom dim := 
  H d ; P8 a ; P8 b ; P8 c ; P8 d ;
  CNOT a b ; P8DAG b ; CNOT a b ; CNOT b c ; P8DAG c ; 
  CNOT a c ; P8 c ; CNOT b c ; P8DAG c ; CNOT a c ; 
  CNOT c d ; P8DAG d ; CNOT b d ; P8 d ; CNOT c d ; 
  P8DAG d ; CNOT a d ; P8 d ; CNOT c d ; P8DAG d ; 
  CNOT b d ; P8 d ; CNOT c d ; P8DAG d ; CNOT a d ; H d.

(* From https://qiskit.org/documentation/_modules/qiskit/circuit/library/standard_gates/x.html#C4XGate 
   which is based on the constructions in arxiv:1508.03273, arxiv:quant-ph/9503016 *)
Definition RC3X {dim} (a b c d : nat) : base_ucom dim := 
  H d ; T d ; CNOT c d ; TDAG d ; H d ;
  CNOT a d ; T d ; CNOT b d ; TDAG d ; CNOT a d ;
  T d ; CNOT b d ; TDAG d ; H d ; T d ;
  CNOT c d ; TDAG d ; H d.

Definition RTX {dim} r q : base_ucom dim := 
  H q ; U1 r q ; H q.

Definition CRTX {dim} (r : R) (a b : nat) : base_ucom dim := 
  H b ; CU1 r a b ; H b.

Definition C3SQRTX {dim} (a b c d : nat) : base_ucom dim := 
  CRTX (PI/8) a d ; CNOT a b ;
  CRTX (-PI/8) b d ; CNOT a b ;
  CRTX (PI/8) b d ; CNOT b c ;
  CRTX (-PI/8) c d ; CNOT a c ;
  CRTX (PI/8) c d ; CNOT b c ;
  CRTX (-PI/8) c d ; CNOT a c ;
  CRTX (PI/8) c d.

Definition C4X {dim} (a b c d e : nat) : base_ucom dim := 
  CRTX (PI/2) d e ; 
  RC3X a b c d ;
  CRTX (-PI/2) d e ; 
  invert (RC3X a b c d) ;
  C3SQRTX a b c e.

Hint Rewrite <- RtoC_minus : RtoC_db.

Local Transparent H U3.
Lemma CH_is_control_H : forall dim a b, @CH dim a b ≡ control a (H b).
Proof.
  assert (aux1 : rotation (- (PI / 4)) 0 0 × (σx × rotation (PI / 4) 0 0) =
                 Cexp (PI / 2) .* (rotation (PI / 2 / 2) 0 0 ×
                   (σx × (rotation (- (PI / 2) / 2) 0 (- PI / 2) × 
                     (σx × phase_shift (PI / 2)))))).
  { (* messy :) should make better automation -KH *)
    solve_matrix; repeat rewrite RIneq.Ropp_div; autorewrite with Cexp_db trig_db; 
      repeat rewrite RtoC_opp; field_simplify_eq; try nonzero.
    replace (((R1 + R1)%R, (R0 + R0)%R) * cos (PI / 4 / 2) * sin (PI / 4 / 2)) 
      with (2 * sin (PI / 4 / 2) * cos (PI / 4 / 2)) by lca.
    2: replace (((- (R1 + R1))%R, (- (R0 + R0))%R) * Ci * Ci * 
                  cos (PI / 2 / 2 / 2) * sin (PI / 2 / 2 / 2))
         with (2 * sin (PI / 2 / 2 / 2) * cos (PI / 2 / 2 / 2)) by lca.
    3: replace (- sin (PI / 4 / 2) * sin (PI / 4 / 2) + 
                  cos (PI / 4 / 2) * cos (PI / 4 / 2)) 
         with (cos (PI / 4 / 2) * cos (PI / 4 / 2) - 
                 sin (PI / 4 / 2) * sin (PI / 4 / 2)) by lca.
    3: replace ((R1 + R1)%R, (R0 + R0)%R) with (RtoC 2) by lca.
    4: replace (((- (R1 + R1))%R, (- (R0 + R0))%R) * sin (PI / 4 / 2) * 
                  cos (PI / 4 / 2)) 
         with (- (2 * sin (PI / 4 / 2) * cos (PI / 4 / 2))) by lca.
    4: replace (- Ci * Ci * sin (PI / 2 / 2 / 2) * sin (PI / 2 / 2 / 2) + 
                  Ci * Ci * cos (PI / 2 / 2 / 2) * cos (PI / 2 / 2 / 2))
         with (- (cos (PI / 2 / 2 / 2) * cos (PI / 2 / 2 / 2) - 
                 sin (PI / 2 / 2 / 2) * sin (PI / 2 / 2 / 2))) by lca.
    all: autorewrite with RtoC_db; rewrite <- sin_2a; rewrite <- cos_2a;
         replace (2 * (PI / 4 / 2))%R with (PI / 4)%R by lra;
         replace (2 * (PI / 2 / 2 / 2))%R with (PI / 4)%R by lra;
         autorewrite with trig_db; reflexivity. }
  assert (aux2 : rotation (- (PI / 4)) 0 0 × rotation (PI / 4) 0 0 =
                 rotation (PI / 2 / 2) 0 0 × 
                   (rotation (- (PI / 2) / 2) 0 (- PI / 2) × phase_shift (PI / 2))).
  { assert (aux: forall x, (x * x = x²)%R) by (unfold Rsqr; reflexivity).
    solve_matrix; repeat rewrite RIneq.Ropp_div; autorewrite with Cexp_db trig_db; 
      repeat rewrite RtoC_opp; field_simplify_eq; try nonzero; 
      autorewrite with RtoC_db; repeat rewrite aux.
    rewrite 2 (Rplus_comm ((cos _)²)).
    rewrite 2 sin2_cos2.
    reflexivity.
    rewrite 2 sin2_cos2.
    reflexivity. }
  intros dim a b.
  unfold H, CH, uc_equiv.
  simpl.
  autorewrite with eval_db.
  gridify; trivial; autorewrite with ket_db bra_db. (* slow! *)
  - rewrite Rminus_0_r, Rplus_0_l, Rplus_0_r.
    apply f_equal2.
    + rewrite <- Mscale_kron_dist_l.
      rewrite <- Mscale_kron_dist_r.
      do 2 (apply f_equal2; try reflexivity).
      apply aux1.
    + rewrite aux2.
      reflexivity.
  - rewrite Rminus_0_r, Rplus_0_l, Rplus_0_r.
    apply f_equal2.
    + rewrite <- 3 Mscale_kron_dist_l.
      rewrite <- Mscale_kron_dist_r.
      do 4 (apply f_equal2; try reflexivity).
      apply aux1.
    + rewrite aux2.
      reflexivity.
Qed.
Local Opaque H U3.

Local Transparent Rz U1.
Lemma CU1_is_control_U1 : forall dim r a b, @CU1 dim r a b ≡ control a (U1 r b).
Proof.
  intros dim r a b.
  unfold U1, CU1, uc_equiv.
  simpl.
  autorewrite with R_db.
  repeat rewrite phase_shift_rotation.
  rewrite phase_0.
  bdestruct (b <? dim).
  unfold pad_u.
  rewrite pad_id by assumption.
  Msimpl. reflexivity.
  unfold pad_u, pad.
  gridify.
Qed.
Local Opaque Rz U1.

Local Transparent U2.
Lemma CU2_is_control_U2 : forall dim r1 r2 a b, 
  @CU2 dim r1 r2 a b ≡ control a (U2 r1 r2 b).
Proof.
  intros dim r1 r2 a b.
  unfold U2, CU2, uc_equiv.
  simpl.
  replace (PI / 2 / 2)%R with (PI / 4)%R by lra.
  replace (- (PI / 2) / 2)%R with (- (PI / 4))%R by lra.
  reflexivity.
Qed.
Local Opaque U2.

Local Transparent U3.
Lemma CU3_is_control_U3 : forall dim r1 r2 r3 a b,
  @CU3 dim r1 r2 r3 a b ≡ control a (U3 r1 r2 r3 b).
Proof.
  intros dim r1 r2 r3 a b.
  unfold U3, CU3, uc_equiv.
  simpl.
  replace (- r1 / 2)%R with (- (r1 / 2))%R by lra.
  reflexivity.
Qed.
Local Opaque U3.

Ltac invert_WT :=
  repeat match goal with
  | H : uc_well_typed (UnitaryOps.control _ _)%ucom |- _ => idtac
  | H : uc_well_typed _ |- _ => inversion H; clear H; subst
  end.

Local Transparent H CNOT Rz ID.
Lemma uc_well_typed_CCX: forall dim a b c : nat,
  (a < dim)%nat /\ (b < dim)%nat /\ (c < dim)%nat /\ a <> b /\ a <> c /\ b <> c 
    <-> uc_well_typed (@CCX dim a b c).
Proof.
  intros dim a b c.
  split; intro H.
  destruct H as [? [? [? [? [? ?]]]]]. 
  repeat constructor; assumption. 
  invert_WT. 
  repeat split; assumption. 
Qed.
Local Opaque H CNOT Rz ID CCX.

Local Transparent SWAP.
Lemma CSWAP_is_control_SWAP : forall dim a b c, @CSWAP dim a b c ≡ control a (SWAP b c).
Proof.
  intros dim a b c.
  destruct (@uc_well_typed_b _ dim (CCX a b c)) eqn:WT.
  apply uc_well_typed_b_equiv in WT.
  apply equal_on_basis_states_implies_equal; auto with wf_db.
  intro f.
  apply uc_well_typed_CCX in WT as [? [? [? [? [? ?]]]]].
  simpl.
  repeat rewrite Mmult_assoc.
  replace (control a (CNOT b c)) with (@CCX dim a b c) by reflexivity.
  replace (control a (CNOT c b)) with (@CCX dim a c b) by reflexivity.
  rewrite f_to_vec_CNOT by auto.
  repeat rewrite f_to_vec_CCX by auto.
  rewrite f_to_vec_CNOT by auto.
  repeat rewrite update_index_eq.
  repeat rewrite update_index_neq by auto.
  rewrite update_index_eq.
  repeat rewrite update_index_neq by auto.
  rewrite update_index_eq.
  repeat rewrite update_index_neq by auto.
  rewrite update_twice_neq by auto.
  rewrite update_twice_eq.
  rewrite (update_twice_neq _ c b) by auto.
  rewrite update_twice_eq.
  replace ((f b ⊕ f c) ⊕ (f c ⊕ (f a && f b ⊕ f c))) 
    with (f b ⊕ (f a && f c ⊕ (f a && f b))).
  replace (f c ⊕ (f a && f b ⊕ f c)) 
    with ((f c ⊕ (f a && f b)) ⊕ (f a && f b ⊕ (f a && f c ⊕ (f a && f b)))).
  reflexivity.
  destruct (f a); destruct (f b); destruct (f c); reflexivity.
  destruct (f a); destruct (f b); destruct (f c); reflexivity.
  (* ill-typed case *)
  apply not_true_iff_false in WT.
  rewrite uc_well_typed_b_equiv in WT.
  unfold CSWAP, uc_equiv; simpl.
  replace (control a (CNOT b c)) with (@CCX dim a b c) by reflexivity.
  apply uc_eval_zero_iff in WT.
  rewrite WT.
  Msimpl. reflexivity.
Qed.
Local Opaque SWAP.

(** qubit q is in classical state b *)
Definition classical_1q_state {dim} (q : nat) (b : bool) (v : Vector (2^dim)) :=
  proj q dim b × v = v.

Lemma classical_1q_state_f_to_vec : forall dim q b f,
  (q < dim)%nat -> b = f q -> classical_1q_state q b (f_to_vec dim f).
Proof.
  intros.
  unfold classical_1q_state.
  rewrite f_to_vec_proj_eq; auto.
Qed.

Ltac solve_fresh :=
  repeat (apply fresh_control; split);
  try apply fresh_U1;
  try apply fresh_X;
  try apply fresh_H;
  try (apply fresh_CNOT; split);
  auto.

Ltac solve_WT := 
  try (apply uc_well_typed_control; repeat split); 
  try apply uc_well_typed_X; 
  try apply uc_well_typed_Rz;
  solve_fresh.

Ltac commute_proj :=
  try rewrite proj_control_true by solve_fresh;
  try rewrite proj_control_false by repeat solve_WT;
  try rewrite <- proj_fresh_commutes by solve_fresh;
  try rewrite <- proj_Rz_comm;
  try rewrite proj_CNOT_ctl_true by auto;
  try rewrite proj_CNOT_ctl_false by auto;
  try (rewrite proj_X; simpl);
  try rewrite (Mmult_assoc (proj _ _ _));
  try rewrite <- (Mmult_assoc _ (proj _ _ _)).

Local Opaque CU1.

Lemma CCU1_is_control_CU1 : forall dim r a b c,
  @CCU1 dim r a b c ≡ control a (control b (U1 r c)).
Proof.
  intros dim r a b c.
  (* manually handle all the ill-typed cases *)
  bdestruct (a <? dim).
  2: { unfold CCU1, uc_equiv. simpl.
       rewrite CNOT_is_control_X, CU1_is_control_U1.
       repeat rewrite (control_q_geq_dim a) by auto.
       Msimpl. reflexivity. }
  bdestruct (b <? dim).
  2: { unfold CCU1, uc_equiv. simpl.
       repeat rewrite CNOT_is_control_X, CU1_is_control_U1.
       repeat rewrite (control_q_geq_dim b) by auto.
       rewrite (control_not_WT _ (control _ _)).
       Msimpl. reflexivity.
       intro contra.
       apply uc_well_typed_control in contra as [? [? ?]]. lia. }
  bdestruct (c <? dim).
  2: { unfold CCU1, uc_equiv. simpl.
       rewrite CU1_is_control_U1.
       rewrite (control_not_WT _ (control _ _)).
       rewrite (control_not_WT a _).
       Msimpl. reflexivity.
       intro contra.
       apply uc_well_typed_Rz in contra. lia.
       intro contra.
       apply uc_well_typed_control in contra as [? [? contra]]. 
       apply uc_well_typed_Rz in contra. lia. }
  bdestruct (a =? b). subst.
  unfold CCU1, uc_equiv. simpl.
  repeat rewrite CU1_is_control_U1.
  rewrite (control_not_fresh b (U1 (r / 2) b)).
  rewrite (control_not_fresh b (control _ _)).
  Msimpl. reflexivity.
  intro contra.
  apply fresh_control in contra as [? ?]. lia.
  intro contra.
  apply fresh_U1 in contra. lia.
  bdestruct (a =? c). subst.
  unfold CCU1, uc_equiv. simpl.
  repeat rewrite CU1_is_control_U1.
  rewrite (control_not_fresh c (U1 (r / 2) c)).
  rewrite (control_not_fresh c (control _ _)).
  Msimpl. reflexivity.
  intro contra.
  apply fresh_control in contra as [? contra]. 
  apply fresh_U1 in contra. lia.
  intro contra.
  apply fresh_U1 in contra. lia.
  bdestruct (b =? c). subst.
  unfold CCU1, uc_equiv. simpl.
  repeat rewrite CNOT_is_control_X.
  rewrite (control_not_fresh c (X c)).
  rewrite (control_not_WT _ (control _ _)).
  Msimpl. reflexivity.
  intro contra.
  apply uc_well_typed_control in contra as [? [contra ?]].
  apply fresh_U1 in contra. lia.
  intro contra.
  apply fresh_X in contra. lia.
  (* now onto the main proof... *)
  apply equal_on_basis_states_implies_equal.
  unfold CCU1, uc_equiv. simpl. 
  auto 20 with wf_db.
  auto with wf_db.
  intro f.
  unfold CCU1, uc_equiv. simpl.
  repeat rewrite Mmult_assoc.
  repeat rewrite CU1_is_control_U1.
  (* destruct on possible values of the control qubits *)
  destruct (f a) eqn:fa; destruct (f b) eqn:fb.
  - assert (Ha : classical_1q_state a true (f_to_vec dim f)).
    { apply classical_1q_state_f_to_vec; auto. }
    unfold classical_1q_state in Ha.
    rewrite <- Ha.
    rewrite <- 2 (Mmult_assoc _ (proj _ _ _)).
    repeat commute_proj.
    apply f_equal2; auto.
    assert (Hb : classical_1q_state b true (f_to_vec dim f)).
    { apply classical_1q_state_f_to_vec; auto. }
    unfold classical_1q_state in Hb.
    rewrite <- Hb.
    rewrite <- 2 (Mmult_assoc _ (proj _ _ _)).
    repeat commute_proj.
    apply f_equal2; auto.
    f_to_vec_simpl.
    rewrite update_same.
    apply f_equal2; auto.
    rewrite fb; destruct (f c); simpl.
    repeat rewrite <- Cexp_add.
    apply f_equal. lra.
    repeat rewrite <- Cexp_add.
    apply f_equal. lra.
    destruct (f c); reflexivity.
  - assert (Ha : classical_1q_state a true (f_to_vec dim f)).
    { apply classical_1q_state_f_to_vec; auto. }
    unfold classical_1q_state in Ha.
    rewrite <- Ha.
    rewrite <- 2 (Mmult_assoc _ (proj _ _ _)).
    repeat commute_proj.
    apply f_equal2; auto.
    assert (Hb : classical_1q_state b false (f_to_vec dim f)).
    { apply classical_1q_state_f_to_vec; auto. }
    unfold classical_1q_state in Hb.
    rewrite <- Hb.
    rewrite <- 2 (Mmult_assoc _ (proj _ _ _)).
    repeat commute_proj.
    apply f_equal2; auto.
    f_to_vec_simpl.
    rewrite <- Mscale_1_l.
    apply f_equal2; auto.
    repeat rewrite <- Cexp_add.
    rewrite fb; destruct (f c); simpl; autorewrite with R_db.
    field_simplify (- (r * / 2) + r * / 2)%R.
    autorewrite with R_db. rewrite Cexp_0. reflexivity.
    rewrite Cexp_0. reflexivity.
  - assert (Ha : classical_1q_state a false (f_to_vec dim f)).
    { apply classical_1q_state_f_to_vec; auto. }
    unfold classical_1q_state in Ha.
    rewrite <- Ha.
    rewrite <- 2 (Mmult_assoc _ (proj _ _ _)).
    repeat commute_proj.
    apply f_equal2; auto.
    assert (Hb : classical_1q_state b true (f_to_vec dim f)).
    { apply classical_1q_state_f_to_vec; auto. }
    unfold classical_1q_state in Hb.
    rewrite <- Hb.
    rewrite <- (Mmult_assoc _ (proj _ _ _)).
    repeat commute_proj.
    apply f_equal2; auto.
    f_to_vec_simpl.
    rewrite update_same. reflexivity.
    destruct (f c); reflexivity.
  - assert (Ha : classical_1q_state a false (f_to_vec dim f)).
    { apply classical_1q_state_f_to_vec; auto. }
    unfold classical_1q_state in Ha.
    rewrite <- Ha.
    rewrite <- 2 (Mmult_assoc _ (proj _ _ _)).
    repeat commute_proj.
    apply f_equal2; auto.
    assert (Hb : classical_1q_state b false (f_to_vec dim f)).
    { apply classical_1q_state_f_to_vec; auto. }
    unfold classical_1q_state in Hb.
    rewrite <- Hb.
    rewrite <- (Mmult_assoc _ (proj _ _ _)).
    repeat commute_proj.
    reflexivity.
Qed.

Lemma f_to_vec_C3X : forall (dim a b c d : nat) (f : nat -> bool),
  (a < dim)%nat -> (b < dim)%nat -> (c < dim)%nat -> (d < dim)%nat -> 
  a <> b -> a <> c -> a <> d -> b <> c -> b <> d -> c <> d ->
  uc_eval (@C3X dim a b c d) × (f_to_vec dim f) 
      = f_to_vec dim (update f d (f d ⊕ (f a && f b && f c))).
Proof. 
  intros.
  unfold C3X, P8, P8DAG.
  simpl.
  repeat rewrite Mmult_assoc.
  (* TODO: why does "repeat" get stuck here? The term doesn't seem to
     change with more than 18 iterations. *)
  do 18 f_to_vec_simpl_body.
  repeat rewrite update_twice_eq.
  repeat rewrite update_index_eq.
  rewrite (update_twice_neq _ d b) by auto.
  rewrite (update_twice_neq _ d c) by auto.
  rewrite 2 update_twice_eq.
  rewrite (update_same _ b).
  2: destruct (f a); destruct (f b); reflexivity.
  rewrite (update_same _ c).
  2: destruct (f a); destruct (f b); destruct (f c); reflexivity.
  destruct (f a) eqn:fa; destruct (f b) eqn:fb; 
    destruct (f c) eqn:fc; destruct (f d) eqn:fd; simpl.
  all: autorewrite with R_db C_db Cexp_db.
  all: group_Cexp.
  all: try match goal with 
       | |- context [Cexp ?r] => field_simplify r
       end; try lra.
  all: autorewrite with R_db C_db Cexp_db.
  all: group_Cexp.
  all: try match goal with 
       | |- context [Cexp ?r] => field_simplify r
       end.
  all: replace (8 * PI / 8)%R with PI by lra.
  all: autorewrite with R_db C_db Cexp_db.
  all: rewrite Mscale_plus_distr_r.
  all: distribute_scale; group_radicals.
  all: lma.
Qed.

Lemma C3X_not_fresh : forall (dim a b c d : nat),
  ~ is_fresh a (@CCX dim b c d) -> uc_eval (@C3X dim a b c d) = Zero.
Proof.
  intros dim a b c d H.
  simpl.
  assert (H0 : uc_eval (@CNOT dim a b) = Zero \/ 
               uc_eval (@CNOT dim a c) = Zero \/
               uc_eval (@CNOT dim a d) = Zero).
  { assert (H0 : a = b \/ a = c \/ a = d).
    apply Classical_Prop.NNPP.
    intro contra. contradict H.
    apply fresh_CCX; repeat split; auto.
    destruct H0 as [H0 | [H0 | H0]]; subst.
    left. autorewrite with eval_db. gridify.
    right. left. autorewrite with eval_db. gridify.
    right. right. autorewrite with eval_db. gridify. }
  destruct H0 as [H0 | [H0 | H0]]; rewrite H0; Msimpl_light; trivial.
Qed.

Lemma C3X_not_WT : forall (dim a b c d : nat),
  ~ uc_well_typed (@SQIR.CCX dim b c d) -> uc_eval (@C3X dim a b c d) = Zero.
Proof.
  intros dim a b c d H.
  simpl.
  assert (H0 : UnitarySem.uc_eval (@CNOT dim b c) = Zero \/ 
               UnitarySem.uc_eval (@CNOT dim b d) = Zero \/ 
               UnitarySem.uc_eval (@CNOT dim c d) = Zero).
  { rewrite <- uc_well_typed_CCX in H.
    autorewrite with eval_db.
    gridify; auto. }
  destruct H0 as [H0 | [H0 | H0]]; rewrite H0; Msimpl_light; trivial.
Qed.

Lemma C3X_a_geq_dim : forall dim a b c d : nat,
  (dim <= a)%nat -> uc_eval (@C3X dim a b c d) = Zero.
Proof.
  intros dim a b c d H.
  simpl.
  assert (H0 : UnitarySem.uc_eval (@P8 dim a) = Zero).
  { unfold P8. autorewrite with eval_db. gridify. }
  rewrite H0.
  Msimpl_light. 
  trivial.
Qed.

Lemma C3X_is_control_CCX : forall dim a b c d,
  @C3X dim a b c d ≡ control a (CCX b c d).
Proof.
  intros dim a b c d.
  unfold uc_equiv.
  bdestruct (a <? dim).
  destruct (@is_fresh_b _ dim a (CCX b c d)) eqn:Hfr.
  apply is_fresh_b_equiv in Hfr.
  destruct (@uc_well_typed_b _ dim (CCX b c d)) eqn:HWT.
  apply uc_well_typed_b_equiv in HWT.
  (* in the one well-typed case, we can use f_to_vec_C3X *)
  apply equal_on_basis_states_implies_equal. 
  simpl.
  auto 40 with wf_db.
  auto with wf_db.
  intro f.
  apply uc_well_typed_CCX in HWT as [? [? [? [? [? ?]]]]].
  apply fresh_CCX in Hfr as [? [? ?]].
  rewrite f_to_vec_C3X by assumption.
  rewrite control_correct.
  rewrite Mmult_plus_distr_r.
  rewrite Mmult_assoc.
  rewrite f_to_vec_CCX by assumption.
  destruct (f a) eqn:fa.
  rewrite f_to_vec_proj_neq; auto.
  rewrite f_to_vec_proj_eq; auto.
  rewrite andb_true_l.
  lma.
  rewrite update_index_neq; auto.
  rewrite fa.
  apply diff_true_false. 
  rewrite (f_to_vec_proj_neq _ _ _ true); auto.
  rewrite f_to_vec_proj_eq; auto.
  rewrite andb_false_l.
  rewrite xorb_false_r.
  rewrite update_same; auto.
  lma.
  rewrite update_index_neq; auto.
  rewrite fa.
  apply diff_false_true. 
  apply fresh_CCX; auto.
  apply uc_well_typed_CCX; repeat split; auto.
  (* ill-typed cases *)
  apply not_true_iff_false in HWT.
  rewrite uc_well_typed_b_equiv in HWT.
  rewrite control_not_WT by assumption.
  apply C3X_not_WT. assumption.
  apply not_true_iff_false in Hfr.
  rewrite is_fresh_b_equiv in Hfr.
  rewrite control_not_fresh by assumption.
  apply C3X_not_fresh. assumption.
  rewrite control_q_geq_dim by assumption.
  apply C3X_a_geq_dim. assumption.
Qed.

Definition phase_func (a b c d : bool) : R :=
  if a && b then
    if c 
    then if d then 0 else PI
    else if d then (3 * PI / 2)%R else (PI / 2)%R
  else 0.

(* Not included in older versions of Coq (e.g., 8.12) *)
Lemma IZR_NEG : forall p, IZR (Zneg p) = Ropp (IZR (Zpos p)).
Proof. reflexivity. Qed.

Lemma f_to_vec_RC3X : forall (dim a b c d : nat) (f : nat -> bool),
   (a < dim)%nat -> (b < dim)%nat -> (c < dim)%nat -> (d < dim)%nat -> 
   a <> b -> a <> c -> a <> d -> b <> c -> b <> d -> c <> d ->
   uc_eval (@RC3X dim a b c d) × (f_to_vec dim f) 
      = Cexp (phase_func (f a) (f b) (f c) (f d)) 
             .* f_to_vec dim (update f d (f d ⊕ (f a && f b && f c))).
Proof. 
  intros.
  unfold uc_equiv, RC3X, T, TDAG.
  simpl.
  repeat rewrite Mmult_assoc.
  f_to_vec_simpl.
  repeat rewrite xorb_assoc.
  replace (f a ⊕ (f b ⊕ f a)) with (f b).
  replace (f a ⊕ (f b ⊕ (f a ⊕ f b))) with false.
  2: destruct (f a); destruct (f b); reflexivity.
  2: destruct (f a); destruct (f b); reflexivity.
  repeat rewrite xorb_false_l.
  repeat rewrite xorb_false_r.
  replace (b2R false) with 0 by reflexivity.
  replace (b2R true) with 1 by reflexivity.
  group_Cexp.
  remember (PI / 4)%R as PI4.
  autorewrite with R_db C_db.
  remember (b2R (f a) * PI4 + - (b2R (f a ⊕ f b) * PI4) + b2R (f b) * PI4)%R as e1.
  rewrite 2 (Rplus_assoc (b2R (f c) * PI)).
  rewrite 2 (Rplus_assoc (b2R (true ⊕ f c) * PI)).
  remember (b2R (true ⊕ f a) * PI4 + - (b2R (true ⊕ (f a ⊕ f b)) * PI4) 
            + b2R (true ⊕ f b) * PI4)%R as e2.
  repeat rewrite Mscale_plus_distr_r.
  repeat rewrite Mscale_assoc.
  group_Cexp.
  repeat rewrite <- Cmult_assoc.
  remember (/ √ 2 * (/ √ 2 * (/ √ 2 * / √ 2)))%C as k.
  assert (swap : forall m n (a b c : Matrix m n), a .+ (b .+ c) = b .+ (a .+ c)).
  { intros. lma. }
  repeat rewrite Mplus_assoc.
  repeat match goal with 
         | |- context [ (_ .* f_to_vec dim (update f d true) 
                          .+ (_ .* f_to_vec dim (update f d false) .+ _)) ] =>
             rewrite (swap _ _  (_ .* f_to_vec dim (update f d true)) 
                           (_ .* f_to_vec dim (update f d false)));
             repeat rewrite Mplus_assoc
         end.
  repeat rewrite <- Mscale_plus_distr_l.
  repeat rewrite <- Mplus_assoc.
  repeat rewrite <- Mscale_plus_distr_l.
  repeat rewrite <- Cmult_plus_distr_r.
  rewrite <- 2 (Mscale_assoc _ _ _ k).
  remember (k .* f_to_vec dim (update f d false)) as kfalse.
  remember (k .* f_to_vec dim (update f d true)) as ktrue.
  repeat rewrite (Rplus_comm _ e1); repeat rewrite <- Rplus_assoc.
  repeat rewrite (Rplus_comm _ e2); repeat rewrite Rplus_assoc.
  repeat rewrite (Cexp_add e1).
  repeat rewrite (Cexp_add e2).
  repeat rewrite (Cexp_add (b2R (f d) * PI)).
  repeat rewrite Cmult_assoc.
  repeat rewrite (Cmult_comm _ (Cexp (b2R (f d) * PI))).
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cplus_assoc.
  repeat rewrite <- (Cmult_plus_distr_l (Cexp (b2R (f d) * PI))).
  replace (b2R (true ⊕ f c)) with  (1 - b2R (f c))%R.
  2: destruct (f c); simpl; lra.
  subst PI4.
  repeat match goal with 
         | |- context [ Cexp (?r1 + ?r2)  ] => field_simplify (r1 + r2)%R
         end.
  autorewrite with R_db C_db Cexp_db.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Cexp_add.
  repeat rewrite IZR_NEG.
  repeat rewrite <- Ropp_mult_distr_l.
  repeat rewrite (Rmult_comm _ (b2R (f c))); repeat rewrite Rmult_assoc.
  replace (2 * (PI * / 4))%R with (PI/2)%R by lra.
  replace (4 * (PI * / 4))%R with PI by lra.
  replace (- (b2R (f c) * (PI / 2)))%R with (b2R (f c) * ((PI / 2) - PI))%R by lra.
  replace (- (PI * / 4))%R with (3 * (PI * / 4) - PI)%R by lra.
  rewrite Cexp_minus_PI.
  replace (- (b2R (f c) * PI))%R with (b2R (f c) * (0 - PI))%R by lra.
  replace (7 * (PI * / 4))%R with (3 * (PI * / 4) + PI)%R by lra.
  rewrite Cexp_plus_PI.
  replace (6 * (PI * / 4))%R with (PI / 2 + PI)%R by lra.
  replace (11 * (PI * / 4))%R with (3 * (PI * / 4) + PI + PI)%R by lra.
  rewrite 2 Cexp_plus_PI.
  replace (- (b2R (f c) * (PI / 2 + PI)))%R 
    with (b2R (f c) * (PI / 2 - PI - PI))%R by lra.
  remember (PI * / 4)%R as PI4.
  remember (PI / 2)%R as PI2.
  assert (e1 = if f a && f b then PI2 else 0).
  { subst e1 PI2. destruct (f a); destruct (f b); simpl; lra. }
  clear Heqe1.
  assert (e2 = if f a && f b then (- PI4)%R else PI4).
  { subst e2 PI4. destruct (f a); destruct (f b); simpl; lra. }
  clear Heqe2.
  assert (k = / 4).
  { subst k. field_simplify_eq; try nonzero.
    rewrite Csqrt_sqrt by lra. 
    rewrite <- Cmult_assoc.
    rewrite Csqrt_sqrt by lra. 
    lca. }
  clear Heqk.
  repeat rewrite <- Copp_mult_distr_r.
  repeat rewrite (Cmult_comm (Cexp e2)).
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- (Cexp_add _ e2).
  unfold phase_func.
  destruct (f a && f b); subst e1 e2 k.
  - (* f a & f b = true *)
    replace (3 * PI4 + - PI4)%R with PI2 by (subst; lra).
    destruct (f c) eqn:fc; destruct (f d) eqn:fd; simpl;
      autorewrite with R_db Cexp_db;
      subst PI2; autorewrite with Cexp_db;
      repeat rewrite IZR_NEG;
      repeat rewrite RtoC_opp;
      match goal with 
      | |- context [ ?c .* kfalse ] => field_simplify c
      end;
      try match goal with 
          | |- context [ ?c .* ktrue ] => field_simplify c
          end.
    all: autorewrite with R_db.
    all: field_simplify (R1 + R1)%R.
    all: try (apply C0_fst_neq; simpl; lra).
    2: rewrite Cdiv_unfold, Cmult_0_l.
    all: rewrite Mscale_0_l; Msimpl_light.
    all: subst ktrue kfalse; repeat rewrite Mscale_assoc.
    + (* f c = true, f d = true *)
      rewrite <- Mscale_1_l.
      apply f_equal2; auto.
      field_simplify_eq.
      rewrite <- Cmult_assoc.
      rewrite Ci2.
      lca.
      split; try nonzero.
      apply C0_fst_neq; simpl; lra.
    + (* f c = true, f d = false *)
      apply f_equal2; auto.
      field_simplify_eq; try nonzero.
      rewrite <- Cmult_assoc.
      rewrite Ci2.
      lca.
    + (* f c = false, f d = true *)
      apply f_equal2; auto.
      rewrite <- Rdiv_unfold, Cexp_3PI2.
      lca.
    + (* f c = false, f d = false *)
      apply f_equal2; auto.
      rewrite <- Rdiv_unfold, Cexp_PI2.
      lca.
  - (* f a & f b = false *)
    replace (3 * PI4 + PI4)%R with PI by (subst; lra).
    destruct (f c) eqn:fc; destruct (f d) eqn:fd; simpl;
      autorewrite with R_db Cexp_db;
      subst PI2; autorewrite with Cexp_db;
      repeat rewrite IZR_NEG;
      repeat rewrite RtoC_opp;
      match goal with 
      | |- context [ ?c .* kfalse ] => field_simplify c
      end;
      try match goal with 
          | |- context [ ?c .* ktrue ] => field_simplify c
          end.
    all: autorewrite with R_db.
    all: field_simplify (R1 + R1)%R.
    all: try (apply C0_fst_neq; simpl; lra).
    rewrite Cdiv_unfold, Cmult_0_l.
    all: rewrite Mscale_0_l; Msimpl_light.
    all: subst ktrue kfalse; repeat rewrite Mscale_assoc.
    all: rewrite <- Mscale_1_l.
    + (* f c = true, f d = true *)
      apply f_equal2; auto. lca.
    + (* f c = true, f d = false *)
      apply f_equal2; auto.
      field_simplify_eq.
      lca.
      split. nonzero.
      apply C0_fst_neq; simpl; lra.
    + (* f c = false, f d = true *)
      apply f_equal2; auto. lca.
    + (* f c = false, f d = false *)
      apply f_equal2; auto. lca.
Qed.

Local Opaque RC3X.

Lemma proj_CRTX_control_true : forall (dim a b : nat) r,
  (a < dim)%nat -> a <> b ->
  uc_eval (CRTX r a b) × proj a dim true = proj a dim true × uc_eval (RTX r b).
Proof. 
  intros.
  unfold CRTX, RTX; simpl.
  rewrite CU1_is_control_U1.
  repeat rewrite Mmult_assoc.
  repeat commute_proj.
  reflexivity.
Qed.

Lemma proj_CRTX_control_false : forall (dim a b : nat) r,
  (a < dim)%nat -> (b < dim)%nat -> a <> b ->
  uc_eval (CRTX r a b) × proj a dim false = proj a dim false.
Proof. 
  intros.
  unfold CRTX, RTX; simpl.
  rewrite CU1_is_control_U1.
  repeat rewrite Mmult_assoc.
  repeat commute_proj.
  specialize (@H_H_id dim) as Hr.
  unfold uc_equiv in Hr; simpl in Hr.
  rewrite Hr, denote_ID.
  unfold pad_u. 
  rewrite pad_id by assumption.
  Msimpl. reflexivity.
Qed.

Lemma f_to_vec_CRTX : forall (dim a b : nat) r (f : nat -> bool),
  (a < dim)%nat -> (b < dim)%nat -> a <> b ->
  uc_eval (@CRTX dim r a b) × f_to_vec dim f =
    if f a 
    then uc_eval (RTX r b) × f_to_vec dim f
    else f_to_vec dim f.
Proof. 
  intros. 
  destruct (f a) eqn:fa.
  assert (Ha : classical_1q_state a true (f_to_vec dim f)).
  { apply classical_1q_state_f_to_vec; auto. }
  unfold classical_1q_state in Ha.
  rewrite <- Ha.
  rewrite <- 2 Mmult_assoc.
  rewrite proj_CRTX_control_true by auto.
  rewrite <- proj_fresh_commutes. 
  reflexivity.
  unfold RTX. repeat constructor; solve_fresh.
  assert (Ha : classical_1q_state a false (f_to_vec dim f)).
  { apply classical_1q_state_f_to_vec; auto. }
  unfold classical_1q_state in Ha.
  rewrite <- Ha.
  rewrite <- Mmult_assoc.
  rewrite proj_CRTX_control_false by auto.
  reflexivity.
Qed.

Lemma RTX_RTX_add : forall dim q r1 r2, @RTX dim r1 q ; RTX r2 q ≡ RTX (r1 + r2) q.
Proof.
  intros.
  unfold RTX.
  repeat rewrite useq_assoc.
  rewrite <- (useq_assoc (H q) (H q)).
  rewrite H_H_id.
  bdestruct (q <? dim).
  rewrite ID_equiv_SKIP by auto.
  rewrite SKIP_id_l.
  rewrite <- (useq_assoc (U1 _ _)).
  rewrite Rz_Rz_add.
  reflexivity.
  unfold uc_equiv; simpl.
  autorewrite with eval_db. 
  bdestruct_all.
  Msimpl. reflexivity.
Qed.

Lemma RTX_PI : forall dim q, @RTX dim PI q ≡ X q.
Proof.
  intros.
  unfold RTX.
  rewrite H_comm_Z.
  rewrite useq_assoc.
  rewrite H_H_id.
  bdestruct (q <? dim).
  rewrite ID_equiv_SKIP by auto.
  apply SKIP_id_r.
  unfold uc_equiv; simpl.
  autorewrite with eval_db. 
  bdestruct_all.
  Msimpl. reflexivity.
Qed.

Lemma RTX_0 : forall dim q, @RTX dim 0 q ≡ ID q.
Proof.
  intros.
  unfold RTX.
  rewrite Rz_0_id.
  bdestruct (q <? dim).
  rewrite ID_equiv_SKIP by auto.
  rewrite SKIP_id_r.
  rewrite H_H_id.
  rewrite ID_equiv_SKIP by auto.
  reflexivity.
  unfold uc_equiv; simpl.
  autorewrite with eval_db. 
  bdestruct_all.
  Msimpl. reflexivity.
Qed.

Lemma fresh_RTX: forall dim a b r, a <> b <-> is_fresh a (@RTX dim r b).
Proof. 
  intros.
  split; intro H.
  repeat constructor; solve_fresh.
  invert_is_fresh; auto.
Qed.

Local Transparent CU1 U1 SQIR.H CNOT.
Lemma fresh_CRTX: forall dim a b c r, a <> b /\ a <> c <-> is_fresh a (@CRTX dim r b c).
Proof. 
  intros.
  split; intro H.
  destruct H.
  repeat constructor; solve_fresh.
  invert_is_fresh; auto.
Qed.
Local Opaque CU1 U1 SQIR.H CNOT.

Local Transparent SQIR.H U1.
Lemma RTX_1q_comm : forall dim r a u b, 
  a <> b ->
  @RTX dim r a ; uapp1 u b ≡ uapp1 u b ; RTX r a.
Proof.
  intros.
  unfold RTX, SQIR.H, U1.
  repeat rewrite useq_assoc.
  rewrite U_V_comm by auto.
  rewrite <- (useq_assoc _ (uapp1 u _)).
  rewrite U_V_comm by auto.
  repeat rewrite <- useq_assoc.
  rewrite U_V_comm by auto.
  reflexivity.
Qed.

Lemma RTX_2q_comm : forall dim r a b c, 
  a <> b -> a <> c ->
  @RTX dim r a ; CNOT b c ≡ CNOT b c ; RTX r a.
Proof.
  intros.
  unfold RTX, SQIR.H, U1.
  repeat rewrite useq_assoc.
  rewrite U_CNOT_comm by auto.
  rewrite <- (useq_assoc _ (CNOT _ _)).
  rewrite U_CNOT_comm by auto.
  repeat rewrite <- useq_assoc.
  rewrite U_CNOT_comm by auto.
  reflexivity.
Qed.
Local Opaque SQIR.H U1.

Local Transparent X.
Lemma RTX_X_comm : forall dim r a b, 
  a <> b ->
  @RTX dim r a ; X b ≡ X b ; RTX r a.
Proof. intros. apply RTX_1q_comm. auto. Qed.
Local Opaque X.

Local Opaque RTX CRTX.

Ltac commute_proj2 :=
  try rewrite proj_CRTX_control_true by auto;
  try rewrite proj_CRTX_control_false by auto;
  try rewrite <- proj_fresh_commutes by (apply fresh_RTX; auto);
  try rewrite <- proj_fresh_commutes by (apply fresh_CRTX; auto);
  commute_proj.

Lemma C3SQRTX_semantics : forall dim a b c d b1 b2 b3 v,
  (a < dim)%nat -> (b < dim)%nat -> (c < dim)%nat -> (d < dim)%nat -> 
  a <> b -> a <> c -> a <> d -> b <> c -> b <> d -> c <> d ->
  classical_1q_state a b1 v -> 
  classical_1q_state b b2 v ->
  classical_1q_state c b3 v ->
  WF_Matrix v ->
  uc_eval (@C3SQRTX dim a b c d) × v = 
    if b1 && b2 && b3 then uc_eval (RTX (PI/2) d) × v else v.
Proof. 
  intros.
  unfold C3SQRTX.
  simpl.
  repeat rewrite Mmult_assoc.
  unfold classical_1q_state in *.
  rewrite <- H9, <- H10, <- H11.
  rewrite <- 2 (Mmult_assoc _ (proj a _ _)).
  specialize (@X_X_id dim) as Hr1.
  specialize (@RTX_RTX_add dim) as Hr2.
  specialize (@RTX_X_comm dim) as Hr3.
  unfold uc_equiv in *; simpl in *.
  destruct b1; destruct b2; destruct b3; simpl.
  - (* b1 = true, b2 = true, b3 = true *)
    repeat commute_proj2.
    rewrite Mmult_assoc.
    apply f_equal2; auto.
    rewrite <- (Mmult_assoc _ (proj b _ _)).
    repeat commute_proj2.
    rewrite Mmult_assoc.
    apply f_equal2; auto.
    rewrite <- (Mmult_assoc _ (proj c _ _)).
    repeat commute_proj2.
    apply f_equal2; auto.
    repeat rewrite <- (Mmult_assoc (uc_eval (X _))). 
    repeat rewrite Hr1.
    repeat rewrite denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl.
    repeat rewrite <- (Mmult_assoc (uc_eval (RTX _ _))).
    repeat rewrite Hr2.
    rewrite <- (Mmult_assoc (uc_eval (RTX _ _))), Hr2.
    field_simplify (PI / 8 + PI / 8 + (PI / 8 + PI / 8))%R.
    replace (4 * PI / 8)%R with (PI / 2)%R by lra.
    reflexivity.
  - (* b1 = true, b2 = true, b3 = false *)
    repeat commute_proj2.
    rewrite Mmult_assoc.
    apply f_equal2; auto.
    apply f_equal2; auto.
    rewrite <- (Mmult_assoc _ (proj c _ _)).
    repeat commute_proj2.
    apply f_equal2; auto.
    repeat rewrite <- (Mmult_assoc (uc_eval (X _))). 
    repeat rewrite Hr1.
    repeat rewrite denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl.
    repeat rewrite Mmult_assoc.
    rewrite <- (Mmult_assoc (uc_eval (X _))).
    rewrite Hr3 by auto.
    rewrite (Mmult_assoc _ (uc_eval (X _))).
    rewrite <- (Mmult_assoc (uc_eval (X _))).
    rewrite Hr3 by auto.
    rewrite (Mmult_assoc _ (uc_eval (X _))).
    rewrite <- (Mmult_assoc (uc_eval (X _))).
    rewrite Hr1.
    rewrite denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl.
    repeat rewrite <- (Mmult_assoc (uc_eval (RTX _ _))).
    repeat rewrite Hr2.
    repeat rewrite <- Mmult_assoc.
    rewrite Hr2.
    field_simplify (PI / 8 + PI / 8 + (- PI / 8 + - PI / 8))%R.
    replace (0 / 8)%R with 0 by lra.
    rewrite RTX_0, denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl. reflexivity.
  - (* b1 = true, b2 = false, b3 = true *)
    repeat commute_proj2.
    rewrite Mmult_assoc.
    apply f_equal2; auto.
    apply f_equal2; auto.
    rewrite <- (Mmult_assoc _ (proj c _ _)).
    repeat commute_proj2.
    apply f_equal2; auto.
    repeat rewrite <- (Mmult_assoc (uc_eval (X _))). 
    repeat rewrite Hr1.
    repeat rewrite denote_ID.
    unfold pad_u. repeat rewrite pad_id by lia.
    Msimpl.
    repeat rewrite Mmult_assoc.
    rewrite <- (Mmult_assoc (uc_eval (X _))).
    rewrite Hr3 by auto.
    rewrite (Mmult_assoc _ (uc_eval (X _))).
    rewrite <- (Mmult_assoc (uc_eval (X _))).
    rewrite Hr1.
    rewrite denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl.
    repeat rewrite <- (Mmult_assoc (uc_eval (RTX _ _))).
    repeat rewrite Hr2.
    repeat rewrite <- Mmult_assoc.
    rewrite Hr2.
    field_simplify (PI / 8 + - PI / 8 + (- PI / 8 + PI / 8))%R.
    replace (0 / 8)%R with 0 by lra.
    rewrite RTX_0, denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl. reflexivity.
  - (* b1 = true, b2 = false, b3 = false *)
    repeat commute_proj2.
    rewrite Mmult_assoc.
    apply f_equal2; auto.
    apply f_equal2; auto.
    rewrite <- (Mmult_assoc _ (proj c _ _)).
    repeat commute_proj2.
    apply f_equal2; auto.
    repeat rewrite Mmult_assoc.
    rewrite <- (Mmult_assoc (uc_eval (X _))).
    rewrite Hr3 by auto.
    rewrite (Mmult_assoc _ (uc_eval (X _))).
    rewrite <- (Mmult_assoc (uc_eval (X _))).
    rewrite Hr3 by auto.
    rewrite (Mmult_assoc _ (uc_eval (X _))).
    rewrite <- (Mmult_assoc (uc_eval (X _))).
    rewrite Hr1.
    rewrite <- (Mmult_assoc (uc_eval (X _))).
    rewrite Hr3 by auto.
    rewrite (Mmult_assoc _ (uc_eval (X _))).
    rewrite <- (Mmult_assoc (uc_eval (X _))).
    rewrite Hr1.
    repeat rewrite denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl.
    repeat rewrite <- (Mmult_assoc (uc_eval (RTX _ _))).
    repeat rewrite Hr2.
    repeat rewrite <- Mmult_assoc.
    rewrite Hr2.
    field_simplify (PI / 8 + - PI / 8 + (PI / 8 + - PI / 8))%R.
    replace (0 / 8)%R with 0 by lra.
    rewrite RTX_0, denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl. reflexivity.
  - (* b1 = false, b2 = true, b3 = true *)
    repeat commute_proj2.
    rewrite Mmult_assoc.
    apply f_equal2; auto.
    apply f_equal2; auto.
    rewrite <- (Mmult_assoc _ (proj c _ _)).
    repeat commute_proj2.
    apply f_equal2; auto.
    repeat rewrite <- (Mmult_assoc (uc_eval (X _))). 
    repeat rewrite Hr1.
    repeat rewrite <- (Mmult_assoc (uc_eval (RTX _ _))).
    repeat rewrite Hr2.
    replace (- PI / 8 + PI / 8)%R with 0 by lra.
    repeat rewrite RTX_0.
    repeat rewrite denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl.
    reflexivity.
  - (* b1 = false, b2 = true, b3 = false *)
    repeat commute_proj2.
    rewrite Mmult_assoc.
    apply f_equal2; auto.
    apply f_equal2; auto.
    rewrite <- (Mmult_assoc _ (proj c _ _)).
    repeat commute_proj2.
    apply f_equal2; auto.
    repeat rewrite <- (Mmult_assoc (uc_eval (RTX _ _))).
    repeat rewrite Hr2.
    replace (- PI / 8 + PI / 8)%R with 0 by lra.
    repeat rewrite RTX_0.
    repeat rewrite denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl.
    repeat rewrite <- (Mmult_assoc (uc_eval (X _))). 
    repeat rewrite Hr1.
    repeat rewrite denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl.
    reflexivity.
  - (* b1 = false, b2 = false, b3 = true *)
    repeat commute_proj2.
    rewrite Mmult_assoc.
    apply f_equal2; auto.
    apply f_equal2; auto.
    rewrite <- (Mmult_assoc _ (proj c _ _)).
    repeat commute_proj2.
    apply f_equal2; auto.
    repeat rewrite <- (Mmult_assoc (uc_eval (RTX _ _))).
    repeat rewrite Hr2.
    replace (- PI / 8 + PI / 8)%R with 0 by lra.
    repeat rewrite RTX_0.
    repeat rewrite denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl.
    reflexivity.
  - (* b1 = false, b2 = false, b3 = false *)
    repeat commute_proj2.
    rewrite Mmult_assoc.
    apply f_equal2; auto.
    apply f_equal2; auto.
    rewrite <- (Mmult_assoc _ (proj c _ _)).
    repeat commute_proj2.
    reflexivity.
Qed.

Local Opaque C3SQRTX.

Local Transparent RC3X SQIR.H T TDAG Rz.
Lemma RC3X_RTX_comm : forall dim a b c d e r,
  a <> e -> b <> e -> c <> e -> d <> e ->
  @RC3X dim a b c d ; RTX r e ≡ RTX r e ; RC3X a b c d.
Proof.
  intros.
  unfold RC3X, SQIR.H, T, TDAG, Rz.
  repeat rewrite useq_assoc.
  rewrite <- RTX_1q_comm by auto.
  rewrite <- (useq_assoc _ (RTX _ _)).
  repeat (try rewrite <- RTX_1q_comm by auto;
          try rewrite <- RTX_2q_comm by auto;
          rewrite (useq_assoc (RTX _ _));
          rewrite <- (useq_assoc _ (RTX _ _))).
  rewrite <- RTX_1q_comm by auto.
  rewrite useq_assoc.
  reflexivity.
Qed.

Lemma inv_RC3X_RTX_comm : forall dim a b c d e r,
  a <> e -> b <> e -> c <> e -> d <> e ->
  invert (@RC3X dim a b c d) ; RTX r e ≡ RTX r e ; invert (RC3X a b c d).
Proof.
  intros.
  unfold RC3X, SQIR.H, T, TDAG, Rz.
  simpl.
  repeat rewrite useq_assoc.
  repeat rewrite invert_CNOT.
  rewrite <- RTX_1q_comm by auto.
  rewrite <- (useq_assoc _ (RTX _ _)).
  repeat (try rewrite <- RTX_1q_comm by auto;
          try rewrite <- RTX_2q_comm by auto;
          rewrite (useq_assoc (RTX _ _));
          rewrite <- (useq_assoc _ (RTX _ _))).
  rewrite <- RTX_1q_comm by auto.
  rewrite useq_assoc.
  reflexivity.
Qed.
Local Opaque RC3X RTX SQIR.H T TDAG Rz.

(* We can remove the WT constraint if we have a lemma that says that 
   f_to_vec n f <> Zero for any n, f. *)
Lemma f_to_vec_invert : forall dim (c : base_ucom dim) f1 f2 r,
  uc_well_typed c ->
  uc_eval c × f_to_vec dim f1 = Cexp r .* f_to_vec dim f2 ->
  uc_eval (invert c) × f_to_vec dim f2 = Cexp (- r) .* f_to_vec dim f1.
Proof.
  intros.
  rewrite <- invert_correct.
  assert ((uc_eval c) † × uc_eval c × f_to_vec dim f1 = 
            Cexp r .* (uc_eval c) † × f_to_vec dim f2).
  rewrite Mmult_assoc, H0.
  distribute_scale. reflexivity.
  assert (WF_Unitary (uc_eval c)).
  apply uc_eval_unitary_iff.
  assumption.
  destruct H2 as [_ ?].
  rewrite H2 in H1.
  rewrite Mmult_1_l in H1; auto with wf_db.
  rewrite H1.
  distribute_scale.
  rewrite <- Cexp_add.
  replace (-r + r)%R with 0 by lra.
  rewrite Cexp_0, Mscale_1_l.
  reflexivity.
Qed.

Local Transparent RC3X SQIR.H T TDAG Rz CNOT.
Lemma uc_well_typed_RC3X: forall dim a b c d : nat,
  (a < dim)%nat /\ (b < dim)%nat /\ (c < dim)%nat /\ (d < dim)%nat /\ a <> d /\ b <> d /\ c <> d 
  <-> uc_well_typed (@RC3X dim a b c d).
Proof.
  intros dim a b c d.
  split; intro H.
  destruct H as [? [? [? [? [? [? ?]]]]]].
  repeat constructor; auto.
  invert_WT. 
  repeat split; auto. 
Qed.
Local Opaque RC3X SQIR.H T TDAG Rz CNOT.

Lemma f_to_vec_invert_RC3X : forall (dim a b c d : nat) (f : nat -> bool),
   (a < dim)%nat -> (b < dim)%nat -> (c < dim)%nat -> (d < dim)%nat -> 
   a <> b -> a <> c -> a <> d -> b <> c -> b <> d -> c <> d ->
   uc_eval (invert (@RC3X dim a b c d)) × f_to_vec dim f 
      = Cexp (- phase_func (f a) (f b) (f c) (f d ⊕ (f a && f b && f c))) 
             .* f_to_vec dim (update f d (f d ⊕ (f a && f b && f c))).
Proof.
  intros.
  apply f_to_vec_invert.
  apply uc_well_typed_RC3X; repeat split; auto.
  rewrite f_to_vec_RC3X by auto.
  repeat rewrite update_index_eq.
  repeat rewrite update_index_neq by auto.
  rewrite update_twice_eq.
  rewrite update_same.
  reflexivity.
  destruct (f a && f b && f c); destruct (f d); reflexivity.
Qed.

Lemma f_to_vec_C4X : forall (dim a b c d e : nat) (f : nat -> bool),
  (a < dim)%nat -> (b < dim)%nat -> (c < dim)%nat -> (d < dim)%nat -> (e < dim)%nat ->
  a <> b -> a <> c -> a <> d -> a <> e -> b <> c -> b <> d -> b <> e -> c <> d -> c <> e -> d <> e ->
  uc_eval (@C4X dim a b c d e) × (f_to_vec dim f) 
      = f_to_vec dim (update f e (f e ⊕ (f a && f b && f c && f d))).
Proof.
  intros.
  simpl.
  repeat rewrite Mmult_assoc.
  specialize RC3X_RTX_comm as Hr1.
  specialize RTX_RTX_add as Hr2.
  specialize inv_RC3X_RTX_comm as Hr3.
  unfold uc_equiv in *; simpl in *.
  assert (Ha : classical_1q_state a (f a) (f_to_vec dim f)).
  { apply classical_1q_state_f_to_vec; auto. }
  assert (Hb : classical_1q_state b (f b) (f_to_vec dim f)).
  { apply classical_1q_state_f_to_vec; auto. }
  assert (Hc : classical_1q_state c (f c) (f_to_vec dim f)).
  { apply classical_1q_state_f_to_vec; auto. }
  rewrite <- Mscale_1_l.
  destruct (f a && f b && f c) eqn:fabc; destruct (f d) eqn:fd; simpl.
  - (* f a && f b && f c = true, f d = true *)
    rewrite f_to_vec_CRTX, fd by auto.
    rewrite <- (Mmult_assoc (uc_eval (RC3X _ _ _ _)) (uc_eval (RTX _ _))).
    rewrite <- Hr1 by auto.
    rewrite Mmult_assoc.
    rewrite f_to_vec_RC3X by auto.
    distribute_scale.
    rewrite fabc, fd; simpl.
    assert (Hd : classical_1q_state d false (f_to_vec dim (update f d false))).
    { apply classical_1q_state_f_to_vec; auto. rewrite update_index_eq. auto. }
    unfold classical_1q_state in Hd.
    rewrite <- Hd.
    rewrite <- (Mmult_assoc _ (proj _ _ _)).
    rewrite <- proj_fresh_commutes by (apply fresh_RTX; auto).
    rewrite (Mmult_assoc (proj _ _ _)).
    rewrite <- (Mmult_assoc _ (proj _ _ _)).
    rewrite proj_CRTX_control_false by auto.
    rewrite <- (Mmult_assoc (proj _ _ _)).
    rewrite proj_fresh_commutes by (apply fresh_RTX; auto).
    rewrite (Mmult_assoc _ (proj _ _ _)).
    rewrite Hd.
    rewrite <- (Mmult_assoc _ (uc_eval (RTX _ _))).
    rewrite <- Hr3 by auto.
    rewrite Mmult_assoc.
    rewrite f_to_vec_invert_RC3X by auto.
    distribute_scale.
    repeat rewrite update_index_eq.
    repeat rewrite update_index_neq by auto.
    rewrite update_twice_eq.
    rewrite fabc; simpl.
    rewrite (update_same _ d) by auto.
    rewrite C3SQRTX_semantics with (b1:=f a) (b2:=f b) (b3:= f c); auto with wf_db.
    rewrite fabc.
    rewrite <- (Mmult_assoc (uc_eval (RTX _ _))), Hr2.
    replace (PI / 2 + PI / 2)%R with PI by lra.
    rewrite RTX_PI.
    rewrite f_to_vec_X by auto.
    apply f_equal2; try reflexivity.
    unfold phase_func.
    apply andb_prop in fabc as [fab fc].
    rewrite fab, fc.
    autorewrite with R_db Cexp_db. lca.
    unfold classical_1q_state in *.
    rewrite <- Ha.
    rewrite <- (Mmult_assoc _ (proj _ _ _)).
    commute_proj2.
    rewrite proj_twice_eq.
    reflexivity.
    unfold classical_1q_state in *.
    rewrite <- Hb.
    rewrite <- (Mmult_assoc _ (proj _ _ _)).
    commute_proj2.
    rewrite proj_twice_eq.
    reflexivity.
    unfold classical_1q_state in *.
    rewrite <- Hc.
    rewrite <- (Mmult_assoc _ (proj _ _ _)).
    commute_proj2.
    rewrite proj_twice_eq.
    reflexivity.
  - (* f a && f b && f c = true, f d = false *)
    rewrite f_to_vec_CRTX, fd by auto.
    rewrite f_to_vec_RC3X by auto.
    distribute_scale.
    rewrite fabc, fd; simpl.
    rewrite f_to_vec_CRTX by auto.
    rewrite update_index_eq.
    rewrite <- (Mmult_assoc (uc_eval (invert (RC3X _ _ _ _))) (uc_eval (RTX _ _))).
    rewrite <- Hr3 by auto.
    rewrite Mmult_assoc.
    rewrite f_to_vec_invert_RC3X by auto.
    distribute_scale.
    repeat rewrite update_index_eq.
    repeat rewrite update_index_neq by auto.
    rewrite update_twice_eq.
    rewrite fabc; simpl.
    rewrite (update_same _ d) by auto.
    rewrite C3SQRTX_semantics with (b1:=f a) (b2:=f b) (b3:= f c); auto with wf_db.
    rewrite fabc.
    rewrite <- (Mmult_assoc (uc_eval (RTX _ _))), Hr2.
    replace (- PI / 2 + PI / 2)%R with 0 by lra.
    rewrite RTX_0.
    rewrite denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl.
    rewrite xorb_false_r.
    rewrite (update_same _ e) by auto.
    rewrite <- Mscale_1_l.
    apply f_equal2; try reflexivity.
    unfold phase_func.
    apply andb_prop in fabc as [fab fc].
    rewrite fab, fc.
    autorewrite with Cexp_db. lca.
    unfold classical_1q_state in *.
    rewrite <- Ha.
    rewrite <- (Mmult_assoc _ (proj _ _ _)).
    commute_proj2.
    rewrite proj_twice_eq.
    reflexivity.
    unfold classical_1q_state in *.
    rewrite <- Hb.
    rewrite <- (Mmult_assoc _ (proj _ _ _)).
    commute_proj2.
    rewrite proj_twice_eq.
    reflexivity.
    unfold classical_1q_state in *.
    rewrite <- Hc.
    rewrite <- (Mmult_assoc _ (proj _ _ _)).
    commute_proj2.
    rewrite proj_twice_eq.
    reflexivity.
  - (* f a && f b && f c = false, f d = true *)
    rewrite f_to_vec_CRTX, fd by auto.
    rewrite <- (Mmult_assoc (uc_eval (RC3X _ _ _ _)) (uc_eval (RTX _ _))).
    rewrite <- Hr1 by auto.
    rewrite Mmult_assoc.
    rewrite f_to_vec_RC3X by auto.
    distribute_scale.
    rewrite fabc, fd; simpl.
    assert (Hd : classical_1q_state d true (f_to_vec dim (update f d true))).
    { apply classical_1q_state_f_to_vec; auto. rewrite update_index_eq. auto. }
    unfold classical_1q_state in Hd.
    rewrite <- Hd.
    rewrite <- (Mmult_assoc _ (proj _ _ _)).
    rewrite <- proj_fresh_commutes by (apply fresh_RTX; auto).
    rewrite (Mmult_assoc (proj _ _ _)).
    rewrite <- (Mmult_assoc _ (proj _ _ _)).
    rewrite proj_CRTX_control_true by auto.
    rewrite proj_fresh_commutes by (apply fresh_RTX; auto).
    rewrite (Mmult_assoc _ (proj _ _ _)).
    rewrite <- (Mmult_assoc (proj _ _ _)).
    rewrite proj_fresh_commutes by (apply fresh_RTX; auto).
    rewrite (Mmult_assoc _ (proj _ _ _)).
    rewrite Hd.
    rewrite <- (Mmult_assoc (uc_eval (RTX _ _))), Hr2.
    replace (PI / 2 + - PI / 2)%R with 0 by lra.
    rewrite RTX_0.
    rewrite denote_ID.
    unfold pad_u. repeat rewrite pad_id by auto.
    Msimpl.
    rewrite f_to_vec_invert_RC3X by auto.
    distribute_scale.
    repeat rewrite update_index_eq.
    repeat rewrite update_index_neq by auto.
    rewrite update_twice_eq.
    rewrite fabc; simpl.
    rewrite (update_same _ d) by auto.
    rewrite C3SQRTX_semantics with (b1:=f a) (b2:=f b) (b3:= f c); auto with wf_db.
    rewrite fabc.
    rewrite xorb_false_r.
    rewrite (update_same _ e) by auto.
    rewrite <- Mscale_1_l.
    apply f_equal2; try reflexivity.
    unfold phase_func.
    destruct (f a && f b); destruct (f c); try inversion fabc.
    rewrite <- Cexp_add.
    replace (3 * PI / 2 + - (3 * PI / 2))%R with 0 by lra.
    autorewrite with Cexp_db. lca.
    autorewrite with Cexp_db. lca.
    autorewrite with Cexp_db. lca.
  - (* f a && f b && f c = false, f d = false *)
    rewrite f_to_vec_CRTX, fd by auto.
    rewrite f_to_vec_RC3X by auto.
    distribute_scale.
    rewrite fabc, fd; simpl.
    rewrite update_same by auto.
    rewrite f_to_vec_CRTX, fd by auto.
    rewrite f_to_vec_invert_RC3X by auto.
    distribute_scale.
    rewrite fabc, fd; simpl.
    rewrite update_same by auto.
    rewrite C3SQRTX_semantics with (b1:=f a) (b2:=f b) (b3:= f c); auto with wf_db.
    rewrite fabc.
    rewrite xorb_false_r.
    rewrite (update_same _ e) by auto.
    apply f_equal2; try reflexivity.
    unfold phase_func.
    destruct (f a && f b); destruct (f c); try inversion fabc.
    rewrite <- Cexp_add.
    replace (PI / 2 + - (PI / 2))%R with 0 by lra.
    autorewrite with Cexp_db. lca.
    autorewrite with Cexp_db. lca.
    autorewrite with Cexp_db. lca.
Qed.

Local Transparent SQIR.H CNOT Rz.
Lemma uc_well_typed_C3X : forall dim a b c d : nat,
    (a < dim)%nat /\ (b < dim)%nat /\ (c < dim)%nat /\ (d < dim)%nat /\
      a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d
    <-> uc_well_typed (@C3X dim a b c d).
Proof.
  intros dim a b c d.
  split; intro H.
  destruct H as [? [? [? [? [? [? [? [? [? ?]]]]]]]]]. 
  repeat constructor; auto.
  invert_WT. 
  repeat split; assumption. 
Qed. 

Lemma fresh_C3X : forall {dim} q a b c d,
  q <> a /\ q <> b /\ q <> c /\ q <> d <-> @is_fresh _ dim q (C3X a b c d).
Proof. 
  intros. split. 
  intros [? [? [? ?]]]. 
  repeat constructor; auto. 
  intro.
  invert_is_fresh. auto. 
Qed.
Local Opaque SQIR.H CNOT Rz.

Local Transparent C3SQRTX RC3X CRTX CU1.
Lemma C4X_not_fresh : forall (dim a b c d e : nat),
  ~ is_fresh a (@C3X dim b c d e) -> uc_eval (@C4X dim a b c d e) = Zero.
Proof.
  intros dim a b c d e H.
  simpl.
  assert (H0 : uc_eval (@CNOT dim a b) = Zero \/ 
               uc_eval (@CNOT dim a c) = Zero \/
               uc_eval (@CNOT dim a d) = Zero \/
               uc_eval (@CNOT dim a e) = Zero).
  { assert (H0 : a = b \/ a = c \/ a = d \/ a = e).
    apply Classical_Prop.NNPP.
    intro contra. contradict H.
    apply Decidable.not_or in contra as [? contra].
    apply Decidable.not_or in contra as [? contra].
    apply Decidable.not_or in contra as [? contra].
    apply fresh_C3X; repeat split; auto.
    destruct H0 as [H0 | [H0 | [H0 | H0]]]; subst.
    left. autorewrite with eval_db. gridify.
    right. left. autorewrite with eval_db. gridify.
    right. right. left. autorewrite with eval_db. gridify.
    right. right. right. autorewrite with eval_db. gridify. }
  destruct H0 as [H0 | [H0 | [H0 | H0]]]; rewrite H0; Msimpl_light; trivial.
Qed.

Lemma C4X_not_WT : forall (dim a b c d e : nat),
  ~ uc_well_typed (@C3X dim b c d e) -> uc_eval (@C4X dim a b c d e) = Zero.
Proof.
  intros dim a b c d e H.
  simpl.
  assert (H0 : uc_eval (@CNOT dim b c) = Zero \/ 
               uc_eval (@CNOT dim b d) = Zero \/ 
               uc_eval (@CNOT dim b e) = Zero \/ 
               uc_eval (@CNOT dim c d) = Zero \/ 
               uc_eval (@CNOT dim c e) = Zero \/ 
               uc_eval (@CNOT dim d e) = Zero).
  { rewrite <- uc_well_typed_C3X in H.
    apply Classical_Prop.not_and_or in H as [H | H].
    left.
    autorewrite with eval_db; gridify; auto.
    apply Classical_Prop.not_and_or in H as [H | H].
    left.
    autorewrite with eval_db; gridify; auto. 
    apply Classical_Prop.not_and_or in H as [H | H].
    right. left.
    autorewrite with eval_db; gridify; auto.
    apply Classical_Prop.not_and_or in H as [H | H].
    right. right. left.
    autorewrite with eval_db; gridify; auto.
    apply Classical_Prop.not_and_or in H as [H | H].
    left.
    autorewrite with eval_db; gridify; auto. 
    apply Classical_Prop.not_and_or in H as [H | H].
    right. left.
    autorewrite with eval_db; gridify; auto. 
    apply Classical_Prop.not_and_or in H as [H | H].
    right. right. left.
    autorewrite with eval_db; gridify; auto. 
    apply Classical_Prop.not_and_or in H as [H | H].
    right. right. right. left.
    autorewrite with eval_db; gridify; auto. 
    apply Classical_Prop.not_and_or in H as [H | H].
    right. right. right. right. left.
    autorewrite with eval_db; gridify; auto. 
    right. right. right. right. right.
    autorewrite with eval_db; gridify; auto. }
  destruct H0 as [H0 | [H0 | [H0 | [H0 | [H0 | H0]]]]]; 
    rewrite H0; Msimpl_light; trivial.
Qed.

Lemma C4X_a_geq_dim : forall dim a b c d e : nat,
  (dim <= a)%nat -> uc_eval (@C4X dim a b c d e) = Zero.
Proof.
  intros dim a b c d e H.
  simpl.
  assert (H0 : uc_eval (@CNOT dim a c) = Zero).
  { autorewrite with eval_db. gridify. }
  rewrite H0.
  Msimpl_light. 
  trivial.
Qed.
Local Opaque C3SQRTX RC3X CRTX CU1.

Lemma C4X_is_control_C3X : forall dim a b c d e,
  @C4X dim a b c d e ≡ control a (C3X b c d e).
Proof.
  intros dim a b c d e.
  unfold uc_equiv.
  bdestruct (a <? dim).
  destruct (@is_fresh_b _ dim a (C3X b c d e)) eqn:Hfr.
  apply is_fresh_b_equiv in Hfr.
  destruct (@uc_well_typed_b _ dim (C3X b c d e)) eqn:HWT.
  apply uc_well_typed_b_equiv in HWT.
  (* main proof *)
  apply equal_on_basis_states_implies_equal; auto with wf_db.
  intro f.
  apply uc_well_typed_C3X in HWT as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
  apply fresh_C3X in Hfr as [? [? [? ?]]].
  rewrite f_to_vec_C4X by auto.
  rewrite control_correct.
  rewrite Mmult_plus_distr_r.
  rewrite Mmult_assoc.
  rewrite f_to_vec_C3X by auto.
  destruct (f a) eqn:fa.
  rewrite f_to_vec_proj_neq; auto.
  rewrite f_to_vec_proj_eq; auto.
  rewrite andb_true_l.
  lma.
  rewrite update_index_neq; auto.
  rewrite fa.
  apply diff_true_false. 
  rewrite (f_to_vec_proj_neq _ _ _ true); auto.
  rewrite f_to_vec_proj_eq; auto.
  rewrite andb_false_l.
  rewrite xorb_false_r.
  rewrite update_same; auto.
  lma.
  rewrite update_index_neq; auto.
  rewrite fa.
  apply diff_false_true. 
  apply fresh_C3X; auto.
  apply uc_well_typed_C3X; repeat split; auto.
  (* handling for ill-typed cases *)
  apply not_true_iff_false in HWT.
  rewrite uc_well_typed_b_equiv in HWT.
  rewrite control_not_WT by assumption.
  apply C4X_not_WT. assumption.
  apply not_true_iff_false in Hfr.
  rewrite is_fresh_b_equiv in Hfr.
  rewrite control_not_fresh by assumption.
  apply C4X_not_fresh. assumption.
  rewrite control_q_geq_dim by assumption.
  apply C4X_a_geq_dim. assumption.
Qed.
