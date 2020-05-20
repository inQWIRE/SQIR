Require Export UnitarySem.
Require Export VectorStates.

(* This file contains useful operations over unitary programs including:
   - inversion
   - control
   - iteration
   - parallel composition *)

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
  uc_well_typed c -> uc_well_typed (invert c).
Proof.
  intros dim c WT.
  induction c; try dependent destruction u; 
  inversion WT; subst; constructor; auto.
Qed.

Lemma invert_correct : forall (dim : nat) (c : base_ucom dim),
  (uc_eval c)† = uc_eval (invert c).
Proof.
  intros.
  induction c; try dependent destruction u; simpl.
  - Msimpl. rewrite IHc1. rewrite IHc2. reflexivity.
  - autorewrite with eval_db.
    bdestruct (n + 1 <=? dim); try apply zero_adjoint_eq.
    repeat setoid_rewrite kron_adjoint; Msimpl.
    rewrite rotation_adjoint.
    reflexivity.
  - autorewrite with eval_db.
    gridify. 
    Qsimpl. reflexivity.
    Qsimpl. reflexivity.
Qed.

(** Programs with arbitrary control **)

(* Standard decomposition; see Qiskit's cu3 gate or Ch.4 of N & C *)
Definition CU {dim} θ ϕ λ c t : base_ucom dim :=
  Rz ((λ + ϕ)/2) c ;
  Rz ((λ - ϕ)/2) t ;
  CNOT c t ;
  uapp1 (U_R (-θ/2) 0 (-(ϕ + λ)/2)) t ;
  CNOT c t ;
  uapp1 (U_R (θ/2) ϕ 0) t.

(* Standard Toffoli decomposition *)
Definition CCX {dim} a b c : base_ucom dim :=
  H c ; CNOT b c ; TDAG c ; CNOT a c ; 
  T c ; CNOT b c ; TDAG c ; CNOT a c ; 
  CNOT a b ; TDAG b ; CNOT a b ; 
  T a ; T b ; T c ; H c. 

(* Convert a program to be controlled by qubit q *)
Fixpoint control {dim} q (c : base_ucom dim) : base_ucom dim :=
  match c with
  | c1; c2 => control q c1; control q c2
  | uapp1 (U_R θ ϕ λ) n => CU θ ϕ λ q n
  | uapp2 U_CNOT m n => CCX q m n
  | _ => SKIP
  end.

(* Move to: Dirac.v *)
(* Lemmas 3 and 4 may not be appropriate for ket db since they don't operate on kets. *)
(* For Q_db? *)
Lemma ket0_phase : forall ϕ, phase_shift ϕ × ket 0 = ket 0.
Proof. intros; solve_matrix. Qed.

Lemma ket1_phase : forall ϕ, phase_shift ϕ × ket 1 = Cexp ϕ .* ket 1.
Proof. intros; solve_matrix. Qed.

Lemma bra0_phase : forall ϕ, bra 0 × phase_shift ϕ = bra 0.
Proof. intros; solve_matrix. Qed.

Lemma bra1_phase : forall ϕ, bra 1 × phase_shift ϕ = Cexp ϕ .* bra 1.
Proof. intros; solve_matrix. Qed.

Hint Rewrite ket0_phase ket1_phase bra0_phase bra1_phase : ket_db.

Lemma WF_bra : forall x, WF_Matrix (bra x).
Proof. intros []; show_wf. Qed.

Lemma WF_ket : forall x, WF_Matrix (ket x).
Proof. intros []; show_wf. Qed.

Hint Resolve WF_bra WF_ket : wf_db.

Lemma braket_same : forall x, bra x × ket x = I 1.
Proof. destruct x; solve_matrix. Qed.

Lemma braket_diff : forall x y, (x + y = 1)%nat -> bra x × ket y = Zero.
Proof. intros [] [] H; try lia; solve_matrix. Qed.

Lemma braketbra_same : forall x y, bra x × (ket x × bra y) = bra y. 
Proof. intros. rewrite <- Mmult_assoc, braket_same; Msimpl; easy. Qed.

Lemma braketbra_diff : forall x y z, (x + y = 1)%nat -> bra x × (ket y × bra z) = Zero. 
Proof. intros. rewrite <- Mmult_assoc, braket_diff; Msimpl; easy. Qed.

Hint Rewrite braket_same braket_diff braketbra_same braketbra_diff using lia : ket_db.

Hint Rewrite <- RtoC_opp RtoC_mult RtoC_plus : CR_db.

(* Improved group_Cexp based on group_radicals *)
Ltac group_Cexp :=
  repeat rewrite <- Cexp_neg;
  repeat match goal  with
  | _ => rewrite <- Cexp_add
  | _ => rewrite <- Copp_mult_distr_l
  | _ => rewrite <- Copp_mult_distr_r
  | |- context [ ?x * ?y ] => tryif has_term Cexp x then fail 
                            else (has_term Cexp y; rewrite (Cmult_comm x y)) 
  | |- context [ ?x * ?y * ?z ] =>
    tryif has_term Cexp y then fail 
    else (has_term Cexp x; has_term Cexp z; rewrite <- (Cmult_assoc x y z)) 
  | |- context [ ?x * (?y * ?z) ] => 
    has_term Cexp x; has_term Cexp y; rewrite (Cmult_assoc x y z)
  end.    

Hint Rewrite <- Copp_plus_distr : C_db.

Inductive is_fresh {U dim} : nat -> ucom U dim -> Prop :=
  | fresh_seq  : forall q c1 c2, is_fresh q c1 -> is_fresh q c2 -> is_fresh q (c1; c2)
  | fresh_app1 : forall q u n, q <> n -> is_fresh q (uapp1 u n)
  | fresh_app2 : forall q u m n, q <> m -> q <> n -> is_fresh q (uapp2 u m n)
  | fresh_app3 : forall q u m n p,  q <> m -> q <> n -> q <> p -> is_fresh q (uapp3 u m n p).

Lemma uc_well_typed_control : forall dim q (c : base_ucom dim),
  (q < dim)%nat -> is_fresh q c -> uc_well_typed c -> 
  uc_well_typed (control q c).
Proof.
  intros dim q c ? Hfr WT.
  induction c; try dependent destruction u; simpl;
  inversion Hfr; inversion WT; subst.
  constructor.
  apply IHc1; auto.
  apply IHc2; auto.  
  1,2: repeat constructor; try assumption.
  all: try apply uc_well_typed_Rz; try apply uc_well_typed_CNOT; auto.
  all: apply uc_well_typed_H; auto.
Qed.  

(* Auxiliary proofs about the semantics of CU and TOFF *)
Lemma CU_correct : forall (dim : nat) θ ϕ λ c t,
  (c < dim)%nat -> (t < dim)%nat -> c <> t ->
  uc_eval (CU θ ϕ λ c t) = proj c dim false .+ (proj c dim true) × (ueval_r dim t (U_R θ ϕ λ)).
Proof.
  intros.
  unfold proj; simpl.
  autorewrite with eval_db.
  gridify. (* slow *)
  all: clear.
  all: autorewrite with M_db_light ket_db.
  all: rewrite Mplus_comm;
       repeat (apply f_equal2; try reflexivity).
  (* A little messy because we need to apply trig identities; 
     goal #1 = goal #3 and goal #2 = goal #4 *)
  - solve_matrix; autorewrite with R_db C_db CR_db Cexp_db trig_db; try lca;
      field_simplify_eq; try nonzero; group_Cexp.
    + rewrite Rplus_comm; setoid_rewrite sin2_cos2; easy.
    + rewrite Copp_mult_distr_l, Copp_mult_distr_r. 
      repeat rewrite <- Cmult_assoc; rewrite <- Cmult_plus_distr_l.  
      autorewrite with CR_db. rewrite Ropp_involutive.
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
      autorewrite with CR_db.
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
      autorewrite with CR_db.      
      rewrite Rplus_comm; rewrite <- Rminus_unfold, <- cos_plus.
      apply f_equal; apply f_equal; lra.
  - solve_matrix; autorewrite with R_db C_db CR_db Cexp_db trig_db; try lca;
      field_simplify_eq; try nonzero; group_Cexp.
    + rewrite Rplus_comm; setoid_rewrite sin2_cos2; easy.
    + rewrite Copp_mult_distr_l, Copp_mult_distr_r. 
      repeat rewrite <- Cmult_assoc; rewrite <- Cmult_plus_distr_l.  
      autorewrite with CR_db. rewrite Ropp_involutive.
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
      autorewrite with CR_db.
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
      autorewrite with CR_db.      
      rewrite Rplus_comm; rewrite <- Rminus_unfold, <- cos_plus.
      apply f_equal; apply f_equal; lra.
Qed.

Local Opaque CU.

Lemma f_to_vec_CCX : forall (dim a b c : nat) (f : nat -> bool),
  (a < dim)%nat -> (b < dim)%nat -> (c < dim)%nat -> a <> b -> a <> c -> b <> c ->
 (uc_eval (CCX a b c)) × (f_to_vec dim f) 
      = f_to_vec dim (update f c (f c ⊕ (f a && f b))).
Proof. 
  intros.
  unfold CCX, T, TDAG.
  simpl uc_eval.
  repeat rewrite Mmult_assoc.
  (* automated evaluation using f_to_vec lemmas -- should be made into a tactic *)
  rewrite f_to_vec_H by auto.
  rewrite Mscale_plus_distr_r.
  repeat (rewrite Mmult_plus_distr_l;
          repeat rewrite Mscale_mult_dist_r;
          repeat rewrite f_to_vec_CNOT by auto;
          repeat rewrite f_to_vec_Rz by auto;
          repeat rewrite f_to_vec_H by auto;
          repeat (try rewrite update_index_eq; try rewrite update_index_neq by auto);
          repeat rewrite update_twice_eq; 
          repeat rewrite Mscale_assoc).
  (* some clean up *)
  rewrite 2 (update_twice_neq _ c b) by auto; rewrite 2 update_twice_eq.
  rewrite 2 (update_twice_neq _ b c) by auto; rewrite 2 update_twice_eq.
  replace ((f b ⊕ f a) ⊕ f a) with (f b) by (destruct (f a); destruct (f b); auto).
  repeat rewrite (update_same _ b).
  2: reflexivity.
  2,3: rewrite update_index_neq; auto.
  (* now destruct (f a), (f b), (f c) and simplify *)
  destruct (f a); destruct (f b); destruct (f c); simpl;
  autorewrite with R_db C_db Cexp_db; group_radicals.
  all: replace (/ 2 * Cexp (PI * / 4) * Cexp (PI * / 4) * / Cexp (PI * / 4) * / Cexp (PI * / 4)) with (/ 2) by (field_simplify_eq; nonzero).
  all: replace (/ 2 * Cexp (PI * / 4) * Cexp (PI * / 4) * Cexp (PI * / 4) * Cexp (PI * / 4)) with (- / 2) by (field_simplify_eq; try nonzero; repeat rewrite <- Cexp_add;             replace (PI * / 4 + PI * / 4 + PI * / 4 + PI * / 4)%R with PI by lra;
         rewrite Cexp_PI; lca).
  all: replace (/ 2 * Cexp (PI * / 4) * / Cexp (PI * / 4) * / Cexp (PI * / 4) * Cexp (PI * / 4)) with (/ 2) by (field_simplify_eq; nonzero).
  all: replace (/ 2 * Cexp (PI * / 4) * / Cexp (PI * / 4) * Cexp (PI * / 4) * / Cexp (PI * / 4)) with (/ 2) by (field_simplify_eq; nonzero).
  all: lma.
Qed.
Local Opaque CCX.

Lemma CCX_correct : forall (dim : nat) a b c,
  (a < dim)%nat -> (b < dim)%nat -> (c < dim)%nat -> a <> b -> a <> c -> b <> c ->
  uc_eval (CCX a b c) = proj a dim false .+ (proj a dim true) × (ueval_cnot dim b c).
  intros dim a b c ? ? ? ? ? ?.
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
  (q < dim)%nat -> is_fresh q c -> uc_well_typed c -> 
  uc_eval (control q c) = proj q dim false .+ (proj q dim true) × (uc_eval c).
Proof.
  intros dim q c Hq Hfr WT.
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

(* Sanity check *)
Local Transparent X.
Lemma control_ucom_X : forall (dim : nat) c t,
  uc_well_typed (@CNOT dim c t) ->
  uc_eval (control c (@X dim t)) = ueval_cnot dim c t.
Proof.
  intros ? ? ? WT. 
  apply uc_well_typed_CNOT in WT as [? [? ?]].
  rewrite control_correct; try constructor; auto.
  unfold proj.
  autorewrite with eval_db.
  gridify.
  all: rewrite Mplus_comm; reflexivity.
Qed.
Local Opaque X.

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
  cast (control i c) d' ≡ control i (cast c d').
Proof.
  intros d d' c i.
  induction c; try dependent destruction u; try reflexivity.
  simpl. rewrite IHc1, IHc2. reflexivity.
Qed.

Lemma cast_niter_commute : forall d d' (c : base_ucom d) i,
  cast (niter i c) d' ≡ niter i (cast c d').
Proof.
  intros d d' c i.
  induction i; simpl.
  reflexivity.
  destruct i; try reflexivity.
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
      rewrite <- kron_assoc.
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
  unfold pad. bdestruct_all.
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
