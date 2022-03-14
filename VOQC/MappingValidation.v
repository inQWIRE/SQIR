Require Import QuantumLib.Permutations.
Require Import SimpleMapping.
Require Import FullGateSet.
Require Import MappingGateSet.

(** Remove all SWAP gates from a program, instead performing a logical 
    relabeling of qubits. *)
Fixpoint remove_swaps {U dim} (l : map_ucom_l U dim) (m : layout) 
    : map_ucom_l U dim * layout :=
  match l with
  | [] => ([], m)
  | App1 u q :: t => 
      let (t', m') := remove_swaps t m in
      (App1 u (get_log m q) :: t', m')
  | App2 UMap_CNOT q1 q2 :: t => 
      let (t', m') := remove_swaps t m in
      (CNOT (get_log m q1) (get_log m q2) :: t', m')
  | App2 UMap_SWAP q1 q2 :: t => 
      remove_swaps t (swap_log m q1 q2)
  | _ => ([], m) (* unreachable *)
  end.

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

Module MappingValidationProofs (G : GateSet) (CG : ConnectivityGraph).

Module SMP := SimpleMappingProofs G CG.
Import SMP.

(** remove_swaps preserves semantics. *)
Lemma remove_swaps_sound : forall l l' m m',
  uc_well_typed_l l ->
  layout_bijective dim m ->
  remove_swaps l m = (l', m') ->
  l ≡ l' with (get_phys m) and (get_log m').
Proof.
  induction l; intros l' m m' WT WF H; simpl in H.
  - inversion H; subst.
    apply uc_equiv_perm_ex_nil.
    apply uc_well_typed_l_implies_dim_nonzero in WT.
    assumption.
    apply perm_pair_get_phys_log.
    assumption.
  - destruct a; inversion WT; subst.
    + destruct (remove_swaps l m) eqn:rs.
      apply IHl in rs; auto.
      inversion H; subst.
      replace (App1 m0 (get_log m n)) with (@map_qubits_app _ dim (get_log m) (App1 m0 n)) by reflexivity.
      apply uc_equiv_perm_ex_cons_cong; auto.
      apply perm_pair_get_phys_log; auto.
      constructor.
      assumption.
      constructor.
      apply uc_well_typed_l_implies_dim_nonzero in WT.
      assumption.
    + dependent destruction m0.
      * destruct (remove_swaps l m) eqn:rs.
        apply IHl in rs; auto.
        inversion H; subst. 
        replace (CNOT (get_log m n) (get_log m n0)) with (@map_qubits_app _ dim (get_log m) (@CNOT (G.U 1) dim n n0)) by reflexivity.
        apply uc_equiv_perm_ex_cons_cong; auto.
        apply perm_pair_get_phys_log; auto.
        constructor; auto.
        constructor.
        apply uc_well_typed_l_implies_dim_nonzero in WT.
        assumption.
      * apply IHl in H; auto.
        rewrite (cons_to_app _ l).
        rewrite <- (app_nil_l l').
        apply uc_equiv_perm_ex_app1 with (p1:=get_log m) (p2:=get_phys (swap_log m n n0)). 
        apply perm_pair_get_log_phys; auto.
        unfold uc_equiv_perm_ex.
        unfold SMP.MapList.eval. 
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
        rewrite fswap_swap_log by assumption.
        rewrite get_log_phys_inv with (n:=dim); auto.
        apply get_phys_perm.
        apply swap_log_preserves_bij; auto.
        apply get_log_perm; auto.
        apply uc_well_typed_l_implies_dim_nonzero in WT.
        assumption.
        apply H.
        apply swap_log_preserves_bij; auto.
    + dependent destruction m0.
Qed.

Lemma remove_swaps_bijective : forall (l l' : ucom_l dim) m m',
  uc_well_typed_l l ->
  layout_bijective dim m ->
  remove_swaps l m = (l', m') ->
  layout_bijective dim m'.
Proof.
  induction l; intros l' m m' WT WF H; simpl in H.
  - inversion H; subst. assumption.
  - destruct a; inversion WT; subst.
    + destruct (remove_swaps l m) eqn:rs.
      inversion H; subst.
      apply IHl in rs; auto.
    + dependent destruction m0.
      * destruct (remove_swaps l m) eqn:rs.
        inversion H; subst.
        apply IHl in rs; auto.
      * apply IHl in H; auto.
        apply swap_log_preserves_bij; auto.
    + dependent destruction m0.
Qed.

(** If check_swap_equivalence returns Some then l1 and l2 are equivalent programs 
    wrt to layouts m1 and m2. *)
Lemma check_swap_equivalence_implies_equivalence : forall l1 l2 m1 m2 m1' m2',
  uc_well_typed_l l1 -> uc_well_typed_l l2 ->
  layout_bijective dim m1 -> layout_bijective dim m2 ->
  check_swap_equivalence l1 l2 m1 m2 (fun n => @MapG.match_gate n) = Some (m1', m2') ->
  l1 ≡ l2 with (get_phys m1 ∘ get_log m2)%prg and (get_phys m2' ∘ get_log m1')%prg.
Proof.
  intros l1 l2 m1 m2 m1' m2' WT1 WT2 WF1 WF2 H.
  unfold check_swap_equivalence in H.
  destruct (remove_swaps l1 m1) eqn:rs1.
  destruct (remove_swaps l2 m2) eqn:rs2.
  assert (rs1':=rs1).
  assert (rs2':=rs2).
  apply remove_swaps_sound in rs1; auto.
  apply remove_swaps_sound in rs2; auto.
  apply remove_swaps_bijective in rs1'; auto.
  apply remove_swaps_bijective in rs2'; auto.
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

Lemma check_constraints_implies_respect_constraints : forall (l : ucom_l dim),
  check_constraints l CG.is_in_graph = true ->
  respects_constraints_directed CG.is_in_graph UMap_CNOT l.
Proof.
  intros l H.
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
  assert (@check_gate_constraint (G.U 1) dim (App2 UMap_CNOT n n0) CG.is_in_graph = true).
  apply H.
  left. reflexivity.
  unfold check_gate_constraint in H0.
  assumption.
  apply IHl.
  intros x Hx.
  apply H.
  right. assumption.
  assert (@check_gate_constraint (G.U 1) dim (App2 UMap_SWAP n n0) CG.is_in_graph = true).
  apply H.
  left. reflexivity.
  inversion H0.
  dependent destruction m.
Qed.

Lemma path_to_swaps_remove_swaps : forall p m m' (l l' : ucom_l dim),
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

Lemma remove_swaps_swap_log : forall (l l' : ucom_l dim) m m' n1 n2,
  layout_bijective dim m ->
  (n1 < dim)%nat -> (n2 < dim)%nat ->
  remove_swaps l m = (l', m') ->
  remove_swaps l (swap_log m n1 n2) = 
    (map (map_qubits_app (fun n => if n =? get_log m n1 then get_log m n2 else if n =? get_log m n2 then get_log m n1 else n)) l', swap_log m' n1 n2).
Proof.
  intros l l' m m' n1 n2 WF Hn1 Hn2 H.
  gen l' m m'.
  induction l; intros l' m WF m' H; simpl in *.
  inversion H; subst. reflexivity.
  destruct a.
  - destruct (remove_swaps l m) eqn:rs.
    inversion H; subst.
    eapply IHl in rs; auto.
    rewrite rs. simpl.
    do 2 (apply f_equal2; auto).
    bdestruct (n =? n1). subst.
    rewrite Nat.eqb_refl.
    unfold get_log at 1.
    rewrite find_log_swap_log_1 with (n:=dim); auto.
    bdestruct (n =? n2). subst.
    bdestruct (get_log m n2 =? get_log m n1).


Search get_log.


    eapply get_phys_neq with (m:=m) in H0; auto.
    contradiction.
admit. (* contradiction *)
    rewrite Nat.eqb_refl.
    unfold get_log at 1.
    rewrite find_log_swap_log_2 with (n:=dim); auto.
    bdestruct (get_log m n =? get_log m n1).
admit. (* contradiction *)
    bdestruct (get_log m n =? get_log m n2).
admit. (* contradiction *)
    unfold get_log.
    rewrite find_log_swap_log_3 with (n:=dim); auto.
  - dependent destruction m0.
    + destruct (remove_swaps l m) eqn:rs.
    inversion H; subst.
    eapply IHl in rs; auto.
    rewrite rs. simpl.
    do 2 (apply f_equal2; auto).
    bdestruct (n =? n1). subst.
    rewrite Nat.eqb_refl.
    unfold get_log at 1.
    rewrite find_log_swap_log_1 with (n:=dim); auto.
    bdestruct (n =? n2). subst.
    bdestruct (get_log m n2 =? get_log m n1).
admit. (* contradiction *)
    rewrite Nat.eqb_refl.
    unfold get_log at 1.
    rewrite find_log_swap_log_2 with (n:=dim); auto.
    bdestruct (get_log m n =? get_log m n1).
admit. (* contradiction *)
    bdestruct (get_log m n =? get_log m n2).
admit. (* contradiction *)
    unfold get_log.
    rewrite find_log_swap_log_3 with (n:=dim); auto.

Admitted.



Lemma equalb_cons_App1 : forall g n (l1 l2 : ucom_l dim),
  equalb (App1 g n :: l1) (App1 g n :: l2) (fun n => @MapG.match_gate n) =
    equalb l1 l2 (fun n => @MapG.match_gate n).
Proof.
  intros g n l1 l2.
  unfold equalb. simpl.
  unfold next_single_qubit_gate. simpl.
  rewrite Nat.eqb_refl.
  replace (MapG.match_gate g g) with true by admit.
  rewrite app_nil_l.
  reflexivity.
Admitted.

Lemma equalb_cons_App2 : forall g m n (l1 l2 : ucom_l dim),
  equalb (App2 g m n :: l1) (App2 g m n :: l2) (fun n => @MapG.match_gate n) =
    equalb l1 l2 (fun n => @MapG.match_gate n).
Proof.
  intros g m n l1 l2.
  unfold equalb. simpl.
  unfold next_gate. simpl.
  rewrite Nat.eqb_refl, orb_true_l.
  rewrite 2 Nat.eqb_refl. 
  replace (MapG.match_gate g g) with true by admit.
  simpl. reflexivity.
Admitted.

(** swap_route produces a program that passes equivalence checking. *)
Lemma swap_route_swap_equivalent : forall (l : ucom_l dim) (m : layout) l' m',
  uc_well_typed_l l -> layout_bijective dim m -> 
  swap_route l m CG.get_path = (l', m') -> 
  is_swap_equivalent l l' (trivial_layout dim) m (fun n => @MapG.match_gate n) = true.
Proof.
  induction l; intros m l' m' WT WF H; simpl in H.
  inversion H; subst.
  reflexivity.
  destruct a.
  - destruct (swap_route l m CG.get_path) eqn:sm.
    inversion H; subst.
    inversion WT; subst.
    apply IHl in sm; auto.
    unfold is_swap_equivalent in *.
    destruct (check_swap_equivalence l m1 (trivial_layout dim) m (fun n : nat => MapG.match_gate)) eqn:cse.
    2: inversion sm.
    unfold check_swap_equivalence in *.
    simpl.
    destruct (remove_swaps l (trivial_layout dim)) eqn:rs1.
    destruct (remove_swaps m1 m) eqn:rs2.
    destruct (equalb m2 m3 (fun n : nat => MapG.match_gate)) eqn:eq.
    2: inversion cse.
    unfold get_log at 1.
    rewrite find_log_trivial_layout by auto.
    rewrite get_log_phys_inv with (n:=dim) by auto.
    rewrite equalb_cons_App1.
    rewrite eq. reflexivity.
  - destruct (path_to_swaps (CG.get_path (get_phys m n) (get_phys m n0)) m) eqn:pts.
    destruct (swap_route l l0 CG.get_path) eqn:sm.
    inversion H; subst.
    inversion WT; subst.
    assert (WFl0 : layout_bijective dim l0).
    { eapply path_to_swaps_bijective; try apply pts; auto.
      apply CG.get_path_valid.
      apply get_phys_lt; auto.
      apply get_phys_lt; auto.
      apply get_phys_neq; auto. }
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
      rewrite rs1, rs2.
      unfold get_log at 1.
      rewrite find_log_trivial_layout by auto.
      unfold get_log at 1.
      rewrite find_log_trivial_layout by auto.
      rewrite 2 get_log_phys_inv with (n:=dim) by auto.
      unfold CNOT.
      rewrite equalb_cons_App2.
      rewrite eq. reflexivity.
    + eapply path_to_swaps_remove_swaps in pts.
      rewrite <- app_assoc.
      rewrite pts. simpl.
      eapply remove_swaps_swap_log in rs1.
      rewrite rs1; auto.
      eapply remove_swaps_swap_log in rs2.
      rewrite rs2; auto.

      rewrite rs2.
      unfold get_log at 1.
      rewrite find_log_trivial_layout by auto.
      unfold get_log at 1.
      rewrite find_log_trivial_layout by auto.
      rewrite 2 get_log_phys_inv with (n:=dim) by auto.
      unfold CNOT.
      rewrite equalb_cons_App2.
      rewrite eq. reflexivity.
  - dependent destruction m0.
Qed.

(* Possibly useful: prove that check_swap_equivalence is reflexive, 
   commutative, and transitive. *)

End MappingValidationProofs.
