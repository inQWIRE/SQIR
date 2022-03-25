Require Import QuantumLib.Permutations.
Require Import SwapRoute.
Require Import FullGateSet.
Require Import MappingGateSet.

(** Remove all SWAP gates from a program, instead performing a logical 
    relabeling of qubits. *)
Fixpoint remove_swaps' {U dim} (l : map_ucom_l U dim) (m : layout) acc
    : map_ucom_l U dim * layout :=
  match l with
  | [] => (rev_append acc [], m)
  | App1 u q :: t => remove_swaps' t m (App1 u (get_log m q) :: acc)
  | App2 UMap_CNOT q1 q2 :: t => 
      remove_swaps' t m (CNOT (get_log m q1) (get_log m q2) :: acc)
  | App2 UMap_SWAP q1 q2 :: t => remove_swaps' t (swap_log m q1 q2) acc
  | _ => ([], m) (* unreachable *)
  end.

Definition remove_swaps {U dim} (l : map_ucom_l U dim) m := remove_swaps' l m [].

(** 'check_swap_equivalence' takes two SQIR programs and their initial log->phys
    qubit mappings as input, and returns Some if the two programs are equivalent.
   
   Limitations:
   - This is not a general equivalence checker for quantum circuits; it is only 
     designed to recognize equivalence between two circuits that differ in SWAPs, 
     which is a common result of circuit routing. If our 'check_swap_equivalence' 
     function returns Some, then the two circuits are guaranteed to be equivalent. 
     If it returns None, then we provide no guarantees. 
   - (CNOT a b; CNOT b a; CNOT a b) is not the same as (SWAP a b). This means that 
     if SWAPs are decomposed into CNOTs, then translation validation will fail.
  - Equivalence checking is insensitive to "syntactic" gate reorderings
    (e.g., X 1 ; X 2 ≡ X 2 ; X 1), but will fail with "semantic" gate reorderings 
    (e.g., X 2 ; CNOT 1 2 ≡ CNOT 1 2 ; X 2). As a result, check_swap_equivalence 
    will almost certainly fail if you do optimization while mapping. *)
Definition check_swap_equivalence {U dim} (l1 l2 : map_ucom_l U dim) (m1 m2 : layout) (match_gate : forall {n}, Map_Unitary U n -> Map_Unitary U n -> bool) : option (layout * layout) :=
  let (l1',m1') := remove_swaps l1 m1 in
  let (l2',m2') := remove_swaps l2 m2 in
  if equalb l1' l2' (fun n => @match_gate n)
  then Some (m1', m2') else None.

Definition is_swap_equivalent {U dim} (l1 l2 : map_ucom_l U dim) (m1 m2 : layout) match_gate : bool :=
  match check_swap_equivalence l1 l2 m1 m2 match_gate with
  | Some _ => true
  | None => false
  end.

(** Check that a circuit satisfies connectivity constraints. 
    (Assumes SWAPs have been decomposed to CNOTs.) *)
Definition check_gate_constraint {U dim} (g : gate_app (Map_Unitary U) dim) (is_in_graph : nat -> nat -> bool) : bool :=
  match g with 
  | App1 u q => true
  | App2 UMap_CNOT q1 q2 => is_in_graph q1 q2
  | _ => false
  end.
Definition check_constraints {U dim} (l : map_ucom_l U dim) (is_in_graph : nat -> nat -> bool) : bool :=
  forallb (fun g => check_gate_constraint g is_in_graph) l.

(* Fix the 'match_gate' argument *)
Definition mg := (fun n => @match_gate (FullGateSet.U 1) n FullGateSet.match_gate).

(** A couple tests *)
Compute (is_swap_equivalent
  (CNOT 0 2 :: []) 
  (SWAP 0 1 :: CNOT 1 2 :: []) 
  (trivial_layout 3) 
  (trivial_layout 3)
  mg).

Compute (is_swap_equivalent 
  (SWAP 0 1 :: CNOT 1 2 :: []) 
  (CNOT 0 2 :: [])
  (trivial_layout 3) 
  (trivial_layout 3)
  mg).

Compute (is_swap_equivalent
  (SWAP 0 1 :: CNOT 1 2 :: UM FullGateSet.U_H 0 :: []) 
  (CNOT 0 2 :: UM FullGateSet.U_H 1 :: []) 
  (trivial_layout 4) 
  (trivial_layout 4)
  mg).

Compute (is_swap_equivalent
  (SWAP 0 1 :: UM FullGateSet.U_X 0 :: UM FullGateSet.U_H 1 :: []) 
  (UM FullGateSet.U_X 1 :: UM FullGateSet.U_H 0 :: []) 
  (trivial_layout 4) 
  (trivial_layout 4)
  mg).

Compute (is_swap_equivalent
  (SWAP 0 1 :: CNOT 1 2 :: UM FullGateSet.U_H 1 :: []) 
  (CNOT 0 2 :: UM FullGateSet.U_H 0 :: []) 
  (trivial_layout 4) 
  (trivial_layout 4)
  mg).

Compute (is_swap_equivalent
  (SWAP 1 0 :: CNOT 1 2 :: UM FullGateSet.U_H 2 :: []) 
  (CNOT 0 2 :: UM FullGateSet.U_H 2 :: []) 
  (trivial_layout 4) 
  (trivial_layout 4)
  mg).

Compute (is_swap_equivalent
  (UM FullGateSet.U_H 1 :: CNOT 1 2 :: UM FullGateSet.U_H 1 :: []) 
  (UM FullGateSet.U_H 2 :: SWAP 1 2 :: CNOT 1 0 :: UM FullGateSet.U_H 1 :: []) 
  (trivial_layout 3) 
  (list_to_layout (S (S O) :: O :: S O :: []))
  mg).

Module MappingValidationProofs (G : GateSet).

Module SRP := SwapRouteProofs G.
Import SRP.

Lemma remove_swaps'_sound : forall {dim} (l l' : ucom_l dim) m m' acc,
  uc_well_typed_l l ->
  layout_bijective dim m ->
  remove_swaps' l m acc = (l', m') ->
  exists l0, l' = rev_append acc l0 /\
        l ≡ l0 with (get_phys m) and (get_log m').
Proof.
  induction l; intros l' m m' acc WT WF H; simpl in H.
  - exists [].
    inversion H; subst.
    split; try reflexivity.
    apply uc_equiv_perm_ex_nil.
    apply uc_well_typed_l_implies_dim_nonzero in WT.
    assumption.
    apply perm_pair_get_phys_log.
    assumption.
  - destruct a; inversion WT; subst.
    + destruct (remove_swaps' l m (App1 m0 (get_log m n) :: acc)) eqn:rs.
      apply IHl in rs; auto.
      inversion H; subst.
      destruct rs as [l0 [? ?]].
      exists (App1 m0 (get_log m n) :: l0).
      subst. split.
      rewrite 2 rev_append_rev.
      simpl. rewrite (cons_to_app _ l0).
      rewrite app_assoc. reflexivity.
      replace (App1 m0 (get_log m n)) with (@map_qubits_app _ dim (get_log m) (App1 m0 n)) by reflexivity.
      apply uc_equiv_perm_ex_cons_cong; auto.
      apply perm_pair_get_phys_log; auto.
      constructor.
      assumption.
      constructor.
      apply uc_well_typed_l_implies_dim_nonzero in WT.
      assumption.
    + dependent destruction m0.
      * destruct (remove_swaps' l m (CNOT (get_log m n) (get_log m n0) :: acc)) eqn:rs.
        apply IHl in rs; auto.
        inversion H; subst.
        destruct rs as [l0 [? ?]].
        exists (CNOT (get_log m n) (get_log m n0) :: l0).
        subst. split.
        rewrite 2 rev_append_rev.
        simpl. rewrite (cons_to_app _ l0).
        rewrite app_assoc. reflexivity. 
        replace (CNOT (get_log m n) (get_log m n0)) with (@map_qubits_app _ dim (get_log m) (@CNOT (G.U 1) dim n n0)) by reflexivity.
        apply uc_equiv_perm_ex_cons_cong; auto.
        apply perm_pair_get_phys_log; auto.
        constructor; auto.
        constructor.
        apply uc_well_typed_l_implies_dim_nonzero in WT.
        assumption.
      * apply IHl in H; auto.
        destruct H as [l0 [? ?]].
        exists l0. subst. split; auto.
        rewrite (cons_to_app _ l).
        rewrite <- (app_nil_l l0).
        apply uc_equiv_perm_ex_app1 with (p1:=get_log m) (p2:=get_phys (swap_log m n n0)). 
        apply perm_pair_get_log_phys; auto.
        unfold uc_equiv_perm_ex.
        unfold MapList.eval. 
        simpl.
        rewrite denote_SKIP.
        apply equal_on_basis_states_implies_equal; auto with wf_db.
        intro f.
        rewrite Mmult_assoc.
        rewrite perm_to_matrix_permutes_qubits.
        repeat rewrite Mmult_assoc.
        rewrite f_to_vec_SWAP by assumption.
        Msimpl.
        rewrite perm_to_matrix_permutes_qubits.
        apply f_to_vec_eq.        
        intros x Hx.
        rewrite fswap_swap_log with (dim:=dim) by assumption.
        rewrite get_log_phys_inv with (n:=dim); auto.
        apply get_phys_perm.
        apply swap_log_preserves_bij; auto.
        apply get_log_perm; auto.
        apply uc_well_typed_l_implies_dim_nonzero in WT.
        assumption.
        apply H0.
        apply swap_log_preserves_bij; auto.
    + dependent destruction m0.
Qed.

(** remove_swaps preserves semantics. *)
Lemma remove_swaps_sound : forall {dim} (l l' : ucom_l dim) m m',
  uc_well_typed_l l ->
  layout_bijective dim m ->
  remove_swaps l m = (l', m') ->
  l ≡ l' with (get_phys m) and (get_log m').
Proof.
  intros dim l l' m m' WT WF H.
  specialize (remove_swaps'_sound l l' m m' [] WT WF H) as H0.
  destruct H0 as [l0 [H1 H2]].
  rewrite rev_append_rev in H1.
  simpl in H1.
  subst. assumption.
Qed.

Lemma remove_swaps'_bijective : forall {dim} (l l' : ucom_l dim) m m' acc,
  uc_well_typed_l l ->
  layout_bijective dim m ->
  remove_swaps' l m acc = (l', m') ->
  layout_bijective dim m'.
Proof.
  induction l; intros l' m m' acc WT WF H; simpl in H.
  - inversion H; subst. assumption.
  - destruct a; inversion WT; subst.
    + destruct (remove_swaps' l m (App1 m0 (get_log m n) :: acc)) eqn:rs.
      inversion H; subst.
      apply IHl in rs; auto.
    + dependent destruction m0.
      * destruct (remove_swaps' l m (CNOT (get_log m n) (get_log m n0) :: acc)) eqn:rs.
        inversion H; subst.
        apply IHl in rs; auto.
      * apply IHl in H; auto.
        apply swap_log_preserves_bij; auto.
    + dependent destruction m0.
Qed.

(** If check_swap_equivalence returns Some then l1 and l2 are equivalent programs 
    wrt to layouts m1 and m2. *)
Lemma check_swap_equivalence_implies_equivalence : forall {dim} (l1 l2 : ucom_l dim) m1 m2 m1' m2',
  uc_well_typed_l l1 -> uc_well_typed_l l2 ->
  layout_bijective dim m1 -> layout_bijective dim m2 ->
  check_swap_equivalence l1 l2 m1 m2 (fun n => @MapG.match_gate n) = Some (m1', m2') ->
  l1 ≡ l2 with (get_phys m1 ∘ get_log m2)%prg and (get_phys m2' ∘ get_log m1')%prg.
Proof.
  intros dim l1 l2 m1 m2 m1' m2' WT1 WT2 WF1 WF2 H.
  unfold check_swap_equivalence in H.
  destruct (remove_swaps l1 m1) eqn:rs1.
  destruct (remove_swaps l2 m2) eqn:rs2.
  assert (rs1':=rs1).
  assert (rs2':=rs2).
  apply remove_swaps_sound in rs1; auto.
  apply remove_swaps_sound in rs2; auto.
  apply remove_swaps'_bijective in rs1'; auto.
  apply remove_swaps'_bijective in rs2'; auto.
  destruct (equalb m m0 (fun n : nat => MapG.match_gate)) eqn:eq.
  inversion H; subst.
  apply MapList.equalb_correct in eq.
  unfold uc_equiv_perm_ex, MapList.eval in *.
  unfold MapList.uc_equiv_l, uc_equiv in *.
  rewrite rs1, rs2, eq.
  rewrite <- 2 perm_to_matrix_Mmult.
  repeat rewrite Mmult_assoc.
  apply f_equal2; try reflexivity.
  repeat rewrite <- Mmult_assoc.
  apply f_equal2; try reflexivity.
  rewrite perm_to_matrix_Mmult.
  repeat rewrite Mmult_assoc.
  rewrite perm_to_matrix_Mmult.
  rewrite 2 perm_to_matrix_I.
  Msimpl. reflexivity.
  apply permutation_compose.
  apply get_log_perm; auto.
  apply get_phys_perm; auto.
  intros x Hx.
  apply get_log_phys_inv with (n:=dim); auto.
  apply permutation_compose.
  apply get_log_perm; auto.
  apply get_phys_perm; auto.
  intros x Hx.
  apply get_log_phys_inv with (n:=dim); auto.
  all: try apply get_log_perm; auto.
  all: try apply get_phys_perm; auto.
  inversion H.
Qed.

Lemma check_constraints_implies_respect_constraints : forall {dim} (l : ucom_l dim) is_in_graph,
  check_constraints l is_in_graph = true ->
  respects_constraints_directed is_in_graph UMap_CNOT l.
Proof.
  intros dim l is_in_graph H.
  unfold check_constraints in H.
  rewrite forallb_forall in H.
  induction l.
  constructor.
  destruct a.
  constructor.
  apply IHl.
  intros x Hx.
  apply H.
  right. assumption.
  dependent destruction m.
  constructor.
  assert (@check_gate_constraint (G.U 1) dim (App2 UMap_CNOT n n0) is_in_graph = true).
  apply H.
  left. reflexivity.
  unfold check_gate_constraint in H0.
  assumption.
  apply IHl.
  intros x Hx.
  apply H.
  right. assumption.
  assert (@check_gate_constraint (G.U 1) dim (App2 UMap_SWAP n n0) is_in_graph = true).
  apply H.
  left. reflexivity.
  inversion H0.
  dependent destruction m.
Qed.

Lemma path_to_swaps_remove_swaps : forall {dim} p m m' (l l' : ucom_l dim),
 path_to_swaps p m = (l, m') ->
 remove_swaps (l ++ l') m = remove_swaps l' m'.
Proof.
  induction p; intros m m' l l' H; simpl in H.
  inversion H; subst.
  rewrite app_nil_l. reflexivity.
  destruct p.
  inversion H; subst.
  rewrite app_nil_l. reflexivity.
  destruct p.
  inversion H; subst.
  rewrite app_nil_l. reflexivity.
  destruct (path_to_swaps (k :: k0 :: p) (swap_log m a k)) eqn:pts.
  inversion H; subst.
  eapply IHp in pts.
  rewrite <- app_comm_cons.
  simpl. apply pts.
Qed.

Lemma equalb_cons_App1 : forall {dim} g n (l1 l2 : ucom_l dim),
  equalb (App1 g n :: l1) (App1 g n :: l2) (fun n => @MapG.match_gate n) =
    equalb l1 l2 (fun n => @MapG.match_gate n).
Proof.
  intros  dimg n l1 l2.
  unfold equalb. simpl.
  unfold next_single_qubit_gate. simpl.
  rewrite Nat.eqb_refl.
  rewrite MapG.match_gate_refl.
  rewrite app_nil_l.
  reflexivity.
Qed.

Lemma equalb_cons_App2 : forall {dim} g m n (l1 l2 : ucom_l dim),
  equalb (App2 g m n :: l1) (App2 g m n :: l2) (fun n => @MapG.match_gate n) =
    equalb l1 l2 (fun n => @MapG.match_gate n).
Proof.
  intros dim g m n l1 l2.
  unfold equalb. simpl.
  unfold next_gate. simpl.
  rewrite Nat.eqb_refl, orb_true_l.
  rewrite 2 Nat.eqb_refl. 
  rewrite MapG.match_gate_refl.
  simpl. reflexivity.
Qed.

Definition decompose_swaps_u {dim} (g : gate_app (Map_Unitary (G.U 1)) dim) : ucom_l dim :=
  match g with
  | App2 UMap_SWAP m n => CNOT m n :: CNOT n m :: CNOT m n :: []
  | g => [g]
  end.

Definition decompose_swaps {dim} (l : ucom_l dim) :=
  change_gate_set decompose_swaps_u l.

Definition no_swaps {dim} (g : gate_app (Map_Unitary (G.U 1)) dim) :=
  match g with
  | App2 UMap_SWAP _ _ => False
  | _ => True
  end.

Lemma decompose_swaps_gates : forall {dim} (l : ucom_l dim),
  forall_gates no_swaps (decompose_swaps l).
Proof.
  intros dim l.
  unfold decompose_swaps.
  induction l.
  - rewrite change_gate_set_nil.
    intros g H.
    inversion H.
  - rewrite change_gate_set_cons.
    intros g H.
    apply in_app_or in H as [H | H].
    destruct a; dependent destruction m.
    all: simpl in H; repeat destruct H as [H | H]; try rewrite <- H;
         simpl; auto; try contradiction. 
Qed.

Lemma decompose_swaps_sound : forall {dim} (l : ucom_l dim),
  MapList.uc_equiv_l (decompose_swaps l) l.
Proof.
  intros dim l.
  unfold decompose_swaps.
  induction l.
  - rewrite change_gate_set_nil.
    reflexivity.
  - rewrite change_gate_set_cons.
    unfold MapList.uc_equiv_l in *.
    simpl.
    rewrite MapList.list_to_ucom_append.
    destruct a; apply useq_congruence; try apply IHl;
      dependent destruction m; simpl; 
      repeat rewrite <- useq_assoc; rewrite SKIP_id_r; 
      reflexivity.
Qed.

Lemma decompose_swaps_WT : forall {dim} (l : ucom_l dim),
  uc_well_typed_l l -> uc_well_typed_l (decompose_swaps l).
Proof.
  intros dim l WT.
  eapply MapList.uc_equiv_l_implies_WT.
  symmetry.
  apply decompose_swaps_sound.
  assumption.
Qed.

(* These preconditions might be stronger than needed. -KH *)
Lemma remove_swaps_change_acc : forall {dim} (l : ucom_l dim) m l' m' acc acc',
  uc_well_typed_l l ->
  layout_bijective dim m ->
  remove_swaps' l m acc = (rev_append acc l', m') ->
  remove_swaps' l m acc' = (rev_append acc' l', m').
Proof.
  induction l; intros m l' m' acc acc' WT WF rs; simpl in *.
  inversion rs; subst. 
  rewrite 2 rev_append_rev in H0.
  apply app_inv_head in H0. subst.
  reflexivity.
  destruct a; dependent destruction m0; inversion WT; subst.
  - assert(H:=rs).
    apply remove_swaps'_sound in H; auto.
    destruct H as [l0 [H _]].
    rewrite 2 rev_append_rev in H.
    simpl in H.
    rewrite <- app_assoc in H.
    apply app_inv_head in H. 
    subst.
    rewrite IHl with (l':=l0) (m':=m') (acc:=App1 (UMap_U u) (get_log m n) :: acc); auto.
  - assert(H:=rs).
    apply remove_swaps'_sound in H; auto.
    destruct H as [l0 [H _]].
    rewrite 2 rev_append_rev in H.
    simpl in H.
    rewrite <- app_assoc in H.
    apply app_inv_head in H. 
    subst.
    rewrite IHl with (l':=l0) (m':=m') (acc:=CNOT (get_log m n) (get_log m n0) :: acc); auto.
  - eapply IHl; try apply rs; auto.
    apply swap_log_preserves_bij; auto.
Qed.

Lemma remove_swap_cons : forall {dim} (l : ucom_l dim) g m l' m',
  no_swaps g -> 
  uc_well_typed_l l ->
  layout_bijective dim m ->
  remove_swaps l m = (l', m') ->
  remove_swaps (g :: l) m = (map_qubits_app (get_log m) g :: l', m').
Proof.
  intros dim l g m l' m' NS WT WF rs. 
  unfold remove_swaps.
  destruct g; dependent destruction m0; try inversion NS; simpl.
  - erewrite remove_swaps_change_acc with (acc:=[]); auto.
    rewrite rev_append_rev.
    simpl. reflexivity.
    rewrite rev_append_rev. simpl. apply rs.
  - erewrite remove_swaps_change_acc with (acc:=[]); auto.
    rewrite rev_append_rev.
    simpl. reflexivity.
    rewrite rev_append_rev. simpl. apply rs.
Qed.

(** swap_route produces a program that passes equivalence checking. *)
(* Note: It's possible to prove this without the no_swaps assumption,
         but the extra assumption makes things simpler. It can be satisified
         with a pre-processing application of decompose_swaps (above). *)
Lemma swap_route_swap_equivalent : forall {dim} (l : ucom_l dim) (m : layout) l' m' get_path,
  uc_well_typed_l l -> uc_well_typed_l l' ->
  layout_bijective dim m -> forall_gates no_swaps l ->
  (forall n1 n2, path_well_typed (get_path n1 n2) dim) ->
  swap_route l m get_path = (l', m') -> 
  is_swap_equivalent l l' (trivial_layout dim) m (fun n => @MapG.match_gate n) = true.
Proof.
  induction l; intros m l' m' get_path WT1 WT2 WF NS WTp H; simpl in H.
  inversion H; subst.
  reflexivity.
  destruct a.
  - destruct (swap_route l m get_path) eqn:sm.
    inversion H; subst.
    inversion WT1; subst.
    inversion WT2; subst.
    apply forall_gates_drop in NS.
    apply IHl in sm; auto.
    unfold is_swap_equivalent in *.
    destruct (check_swap_equivalence l m1 (trivial_layout dim) m (fun n : nat => MapG.match_gate)) eqn:cse.
    2: inversion sm.
    unfold check_swap_equivalence in *.
    destruct (remove_swaps l (trivial_layout dim)) eqn:rs1.
    destruct (remove_swaps m1 m) eqn:rs2.
    destruct (equalb m2 m3 (fun n : nat => MapG.match_gate)) eqn:eq.
    2: inversion cse.
    erewrite remove_swap_cons; try easy.
    2: apply trivial_layout_bijective.
    2: apply rs1.
    erewrite remove_swap_cons; try easy.
    2: apply rs2.
    simpl.
    unfold get_log at 1.
    rewrite find_log_trivial_layout by auto.
    rewrite get_log_phys_inv with (n:=dim) by auto.
    rewrite equalb_cons_App1.
    rewrite eq. reflexivity.
  - destruct (path_to_swaps (get_path (get_phys m n) (get_phys m n0)) m) eqn:pts.
    destruct (swap_route l l0 get_path) eqn:sm.
    inversion H; subst.
    inversion WT1; subst.
    apply uc_well_typed_l_app in WT2 as [WT2 WT3].
    apply uc_well_typed_l_app in WT2 as [WT2 WT4].
    assert (WFl0 : layout_bijective dim l0).
    { eapply path_to_swaps_bijective; try apply pts; auto. }
    apply IHl in sm; auto.
    unfold is_swap_equivalent in *.
    destruct (check_swap_equivalence l m2 (trivial_layout dim) l0 (fun n : nat => MapG.match_gate)) eqn:cse.
    2: inversion sm.
    unfold check_swap_equivalence in *.
    destruct (remove_swaps l (trivial_layout dim)) eqn:rs1.
    destruct (remove_swaps m2 l0) eqn:rs2.
    destruct (equalb m3 m4 (fun n : nat => MapG.match_gate)) eqn:eq.
    2: inversion cse.
    dependent destruction m0; simpl.
    + eapply path_to_swaps_remove_swaps in pts.
      rewrite <- app_assoc.
      rewrite pts. simpl.
      erewrite remove_swap_cons; try easy.
      2: apply trivial_layout_bijective.
      2: apply rs1.
      erewrite remove_swap_cons; try easy.
      2: apply rs2.
      simpl.
      unfold get_log at 1.
      rewrite find_log_trivial_layout by auto.
      unfold get_log at 1.
      rewrite find_log_trivial_layout by auto.
      rewrite 2 get_log_phys_inv with (n:=dim) by auto.
      unfold CNOT.
      rewrite equalb_cons_App2.
      rewrite eq. reflexivity.
    + (* impossible case since l has no SWAP gates *)
      assert (contra : List.In (App2 UMap_SWAP n n0) (App2 UMap_SWAP n n0 :: l)).
      left. auto.
      apply NS in contra.
      simpl in contra. easy.
    + apply forall_gates_drop in NS. auto.
  - dependent destruction m0.
Qed.

(* Possibly useful: prove that check_swap_equivalence is reflexive, 
   commutative, and transitive. *)

End MappingValidationProofs.
