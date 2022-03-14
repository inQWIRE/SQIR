Require Import QuantumLib.Permutations.
Require Export UnitaryListRepresentation.
Require Export ConnectivityGraph.
Require Export Layouts.
Require Export MappingConstraints.
Require Import FullGateSet MappingGateSet.

(** Simple strategy for mapping a program to a CNOT connectivity graph.
   When a CNOT occurs between non-adjacent qubits: (1) insert SWAPs to 
   make the qubits adjacent, (2) perform the CNOT, (3) update the 
   correspondence between logical (program) qubits and physical (machine)
   qubits. In cases where a CNOT is between adjacent qubits but in the wrong 
   orientation, insert H gates on the target and control. 

   Inputs:
     - a program over logical qubits
     - an initial mapping between logical and physical qubits
     - a CNOT connectivity graph
   Outputs:
     - a program over physical qubits
     - a final mapping between logical and physical qubits

   The proofs all assume that the number of logical and physical qubits ("dim")
   are the same. In practice, we expect that the number of physical qubits 
   will be >= the number of logical qubits. For this case, simply "cast" the input
   program to a type with the appropriate dimension.
*)

(** Mapping function definition. *)
Fixpoint path_to_swaps {U dim} p m : (map_ucom_l U dim * layout) :=
  match p with
  | n1 :: n2 :: [] => ([], m)
  | n1 :: ((n2 :: _) as t) => 
      let (l, m') := path_to_swaps t (swap_log m n1 n2) in
      (SWAP n1 n2 :: l, m')
  | _ => ([], m) (* bad input - invaid path *)
  end.

(* The input program references *logical* qubits, and the returned program
   references *physical* qubits. get_path and is_in_graph_b also reference 
   physical qubits. The output of this is a program with SWAPs that respects
   *undirected* connectivity constraints. *) 
Fixpoint swap_route {U dim} (l : map_ucom_l U dim) (m : layout) (get_path : nat -> nat -> list nat) : (map_ucom_l U dim * layout) :=
  match l with
  | [] => ([],m)
  | App1 u n :: t =>
      let (t',m') := swap_route t m get_path in
      (App1 u (get_phys m n) :: t', m')
  | App2 u n1 n2 :: t =>
      let p := get_path (get_phys m n1) (get_phys m n2) in
      let (swaps, m') := path_to_swaps p m in
      let mapped_cnot := 
        swaps ++ [App2 u (get_phys m' n1) (get_phys m' n2)] in 
      let (t',m'') := swap_route t m' get_path in
      (mapped_cnot ++ t', m'')
  | _ => ([], m) (* unreachable due to the gate set *)
  end.

(* Finally, a "decomposition" function that ensures that the output satisfies
   directed connectivity contraints. This function is specialized to the Full
   gate set where we have access to a Hadamard gate. *)
Definition H {dim} a : gate_app (Map_Unitary (Full_Unitary 1)) dim := 
  App1 (UMap_U FullGateSet.U_H) a.

Definition decompose_swaps_and_cnots_aux {dim} (is_in_graph : nat -> nat -> bool) (g : gate_app (Map_Unitary (Full_Unitary 1)) dim) : map_ucom_l (Full_Unitary 1) dim :=
  match g with
  | App2 UMap_CNOT m n => 
      if is_in_graph m n
      then [CNOT m n]
      else H n :: H m :: CNOT n m :: H n :: H m :: []
  | App2 UMap_SWAP m n => 
      if is_in_graph m n
      then CNOT m n :: H m :: H n :: CNOT m n :: H m :: H n :: CNOT m n :: []
      else CNOT n m :: H n :: H m :: CNOT n m :: H n :: H m :: CNOT n m :: []
  | g => [g]
  end.

Definition decompose_swaps_and_cnots {dim} (l : map_ucom_l (Full_Unitary 1) dim) (is_in_graph : nat -> nat -> bool) :=
  change_gate_set (decompose_swaps_and_cnots_aux is_in_graph) l.

(** * Proofs *)

Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

Definition perm_pair dim p1 p2 :=
  permutation dim p1 /\
  permutation dim p2 /\
  (forall x, x < dim -> p1 (p2 x) = x) /\
  (forall x, x < dim -> p2 (p1 x) = x).

Lemma perm_pair_get_log_phys: forall dim m,
  layout_bijective dim m ->
  perm_pair dim (get_log m) (get_phys m).
Proof.
  intros dim m.
  repeat split.
  apply get_log_perm. auto.
  apply get_phys_perm. auto.
  intros. apply get_log_phys_inv with (n:=dim); auto.
  intros. apply get_phys_log_inv with (n:=dim); auto.
Qed.

Lemma perm_pair_get_phys_log: forall dim m,
  layout_bijective dim m ->
  perm_pair dim (get_phys m) (get_log m).
Proof.
  intros dim m.
  repeat split.
  apply get_phys_perm. auto.
  apply get_log_perm. auto.
  intros. apply get_phys_log_inv with (n:=dim); auto.
  intros. apply get_log_phys_inv with (n:=dim); auto.
Qed.

Lemma permute_commutes_with_map_qubits : forall dim (u : base_ucom dim) p1 p2,
  perm_pair dim p1 p2 ->
  uc_well_typed u ->
  perm_to_matrix dim p1 × uc_eval u =
    uc_eval (map_qubits p2 u) × perm_to_matrix dim p1.
Proof.
  intros dim u p1 p2 [? [? [? ?]]] WT.
  induction u; try dependent destruction u;
  inversion WT; subst; simpl.
  - rewrite <- Mmult_assoc.
    rewrite IHu2 by assumption.
    rewrite Mmult_assoc.
    rewrite IHu1 by assumption.
    rewrite <- Mmult_assoc.
    reflexivity.
  - apply equal_on_basis_states_implies_equal; auto with wf_db.
    intro f.
    repeat rewrite Mmult_assoc.
    rewrite perm_to_matrix_permutes_qubits by assumption.
    assert (p2 n < dim).
    { destruct H1 as [? H1].
      specialize (H1 n H5).
      destruct H1. auto. }
    unfold pad_u, pad.
    bdestruct_all.
    rewrite (f_to_vec_split 0 dim n) by assumption.
    rewrite (f_to_vec_split 0 dim (p2 n)) by assumption.
    restore_dims.
    replace (dim - 1 - n) with (dim - (n + 1)) by lia.
    replace (dim - 1 - p2 n) with (dim - (p2 n + 1)) by lia. 
    Msimpl.
    rewrite H2; auto. 
    rewrite (ket_decomposition (rotation r r0 r1 × ∣ Nat.b2n (f n) ⟩)); 
      auto with wf_db.
    distribute_plus. 
    distribute_scale.
    apply f_equal2; apply f_equal2; try reflexivity.
    + remember (update f n false) as f0.
      replace (f_to_vec n f) with (f_to_vec n f0).
      replace ∣ 0 ⟩ with  ∣ Nat.b2n (f0 n) ⟩.
      replace (f_to_vec (dim - (n + 1)) (shift f (n + 1))) 
        with (f_to_vec (dim - (n + 1)) (shift f0 (n + 1))).
      replace (dim - (n + 1)) with (dim - 1 - n) by lia.
      rewrite <- f_to_vec_split by auto.
      rewrite perm_to_matrix_permutes_qubits by assumption.
      remember (update (fun x : nat => f (p1 x)) (p2 n) false) as f0'.
      replace (f_to_vec dim (fun x : nat => f0 (p1 x))) with (f_to_vec dim f0').
      rewrite (f_to_vec_split 0 dim (p2 n)) by auto.
      replace (dim - 1 - p2 n) with (dim - (p2 n + 1)) by lia.
      apply f_equal2; [apply f_equal2 |].
      all: subst. 
      1,7: apply f_to_vec_update_oob; lia.
      1,5: repeat rewrite update_index_eq; reflexivity.
      1,3: apply f_to_vec_shift_update_oob; right; lia.
      apply f_to_vec_eq.
      intros x Hx.
      unfold update.
      bdestruct (x =? p2 n); subst.
      rewrite H2 by auto.
      bdestruct_all; trivial.
      bdestruct_all; trivial.
      rewrite <- H9 in H8.
      rewrite H3 in H8 by auto.
      contradiction.
    + remember (update f n true) as f1.
      replace (f_to_vec n f) with (f_to_vec n f1).
      replace ∣ 1 ⟩ with  ∣ Nat.b2n (f1 n) ⟩.
      replace (f_to_vec (dim - (n + 1)) (shift f (n + 1))) 
        with (f_to_vec (dim - (n + 1)) (shift f1 (n + 1))).
      replace (dim - (n + 1)) with (dim - 1 - n) by lia.
      rewrite <- f_to_vec_split by auto.
      rewrite perm_to_matrix_permutes_qubits by assumption.
      remember (update (fun x : nat => f (p1 x)) (p2 n) true) as f1'.
      replace (f_to_vec dim (fun x : nat => f1 (p1 x))) with (f_to_vec dim f1').
      rewrite (f_to_vec_split 0 dim (p2 n)) by auto.
      replace (dim - 1 - p2 n) with (dim - (p2 n + 1)) by lia.
      apply f_equal2; [apply f_equal2 |].
      all: subst. 
      1,7: apply f_to_vec_update_oob; lia.
      1,5: repeat rewrite update_index_eq; reflexivity.
      1,3: apply f_to_vec_shift_update_oob; right; lia.
      apply f_to_vec_eq.
      intros x Hx.
      unfold update.
      bdestruct (x =? p2 n); subst.
      rewrite H2 by auto.
      bdestruct_all; trivial.
      bdestruct_all; trivial.
      rewrite <- H9 in H8.
      rewrite H3 in H8 by auto.
      contradiction.
  - apply equal_on_basis_states_implies_equal; auto with wf_db.
    intro f.
    repeat rewrite Mmult_assoc.
    rewrite perm_to_matrix_permutes_qubits by assumption.
    replace (ueval_cnot dim n n0) with (uc_eval (@SQIR.CNOT dim n n0)) by reflexivity.
    rewrite f_to_vec_CNOT by assumption.
    rewrite perm_to_matrix_permutes_qubits by assumption.
    replace (ueval_cnot dim (p2 n) (p2 n0)) 
      with (uc_eval (@SQIR.CNOT dim (p2 n) (p2 n0))) by reflexivity.
    assert (p2 n < dim).
    { destruct H1 as [? H1].
      specialize (H1 n H7).
      destruct H1. auto. }
    assert (p2 n0 < dim).
    { destruct H1 as [? H1].
      specialize (H1 n0 H8).
      destruct H1. auto. }
    rewrite f_to_vec_CNOT; auto.
    apply f_to_vec_eq.
    intros x Hx.
    unfold update.
    rewrite 2 H2 by auto.
    bdestruct_all; try reflexivity.
    rewrite <- H6 in H10.
    rewrite H3 in H10 by auto.
    contradiction.
    rewrite H10 in H6.
    rewrite H2 in H6 by auto.
    contradiction.
    intro contra.
    assert (p1 (p2 n) = p1 (p2 n0)) by auto.
    rewrite 2 H2 in H6 by auto.
    contradiction.
Qed.

Module SimpleMappingProofs (G : GateSet) (CG : ConnectivityGraph).

Definition dim := CG.dim.
Definition ucom_l dim := map_ucom_l (G.U 1) dim.

Module MapG := MappingGateSet G.
Module MapList := UListProofs MapG.
Import MapList.

(** Equivalence up to qubit reordering w/ explicit input and output permutations **)
Definition uc_equiv_perm_ex (l1 l2 : ucom_l dim) pin pout :=
  eval l1 = perm_to_matrix dim pout × eval l2 × perm_to_matrix dim pin.
Notation "c1 ≡ c2 'with' p1 'and' p2" := (uc_equiv_perm_ex c1 c2 p1 p2) (at level 20).

Lemma uc_equiv_perm_ex_nil : forall p1 p2,
  dim > 0 ->
  perm_pair dim p1 p2 ->
  [] ≡ [] with p1 and p2.
Proof.
  intros p1 p2 Hdim [? [? [? ?]]].
  unfold uc_equiv_perm_ex.
  unfold eval; simpl.
  rewrite denote_SKIP by assumption.
  Msimpl.
  rewrite perm_to_matrix_Mmult, perm_to_matrix_I; auto.
  apply permutation_compose; auto.
Qed.

Lemma SWAP_well_typed : forall a b,
  a < dim -> b < dim -> a <> b ->
  uc_well_typed (list_to_ucom ([@SWAP _ dim a b])).
Proof.
  intros.
  simpl.
  constructor.
  apply uc_well_typed_SWAP; lia.
  apply uc_well_typed_ID.
  lia.
Qed.

Lemma SWAP_semantics : forall a b,
  dim > 0 -> eval ([@SWAP _ dim a b]) = uc_eval (SQIR.SWAP a b).
Proof.
  intros.
  unfold eval.
  simpl.
  rewrite denote_SKIP by auto.
  Msimpl.
  reflexivity.
Qed.

Lemma path_to_swaps_bijective : forall n1 n2 p m (l : ucom_l dim) m',
  valid_path n1 n2 CG.is_in_graph dim p ->
  layout_bijective dim m ->
  path_to_swaps p m = (l, m') ->
  layout_bijective dim m'.
Proof.
  intros.
  generalize dependent l.
  generalize dependent m.
  generalize dependent n1.
  induction p; intros n1 Hpath m WFm c res; simpl in res.
  inversion res; subst. assumption.
  destruct p. inversion res; subst. assumption.
  destruct p. inversion res; subst. assumption.
  destruct (path_to_swaps (n :: n0 :: p) (swap_log m a n)) eqn:res'.
  inversion res; subst.
  destruct Hpath as [H1 [H2 [H3 [H4 H5]]]].
  inversion H1; subst.
  inversion H4; subst.
  eapply IHp; try apply res'.
  repeat split.
  inversion H2; subst. assumption.
  inversion H3; subst. assumption.
  assumption. 
  inversion H5; subst. assumption.
  apply swap_log_preserves_bij; assumption.
Qed.

Lemma fswap_swap_log : forall m (f : nat -> bool) a b x,
  a < dim -> b < dim -> x < dim -> a <> b ->
  layout_bijective dim m ->
  fswap f a b (get_phys (swap_log m a b) x) = f (get_phys m x).
Proof.
  intros m f a b x Ha Hb Hx Hab H.
  bdestruct (x =? get_log m a); bdestruct (x =? get_log m b); subst.
  - assert (get_phys m (get_log m a) = get_phys m (get_log m b)) by auto.
    erewrite 2 get_phys_log_inv in H0.
    contradiction.
    apply H. apply Hb.
    apply H. apply Ha.
  - unfold get_phys at 1.
    rewrite find_phys_swap_log_1 with (n:=dim) by auto.
    rewrite fswap_simpl2.
    erewrite get_phys_log_inv.
    reflexivity. apply H. apply Ha.
  - unfold get_phys at 1.
    rewrite find_phys_swap_log_2 with (n:=dim) by auto.
    rewrite fswap_simpl1.
    erewrite get_phys_log_inv.
    reflexivity. apply H. apply Hb.
  - unfold get_phys at 1.
    rewrite find_phys_swap_log_3 with (n:=dim); auto.
    replace (match find_phys m x with
             | Some p => p
             | None => 0
             end) with (get_phys m x) by reflexivity.
    rewrite fswap_neq.
    reflexivity.
    intro contra.
    rewrite contra in H0.
    erewrite get_log_phys_inv in H0.
    contradiction.
    apply H. apply Hx.
    intro contra.
    rewrite contra in H1.
    erewrite get_log_phys_inv in H1.
    contradiction.
    apply H. apply Hx.
    intro contra.
    unfold get_log in H0.
    rewrite contra in H0.
    contradiction.
    intro contra.
    unfold get_log in H1.
    rewrite contra in H1.
    contradiction.
Qed.

Lemma path_to_swaps_sound : forall n1 n2 p m l m',
  dim > 0 ->
  valid_path n1 n2 CG.is_in_graph dim p ->
  layout_bijective dim m ->
  path_to_swaps p m = (l, m') ->
  l ≡ [] with (get_phys m) and (get_log m').
Proof.
  intros n1 n2 p m l m' Hdim.
  generalize dependent l.
  generalize dependent m.
  generalize dependent n1.
  induction p; intros n1 m l Hpath WFm res; simpl in res.
  (* invalid path cases *)
  destruct Hpath as [H _].
  inversion H.
  destruct p.
  destruct Hpath as [_ [_ [H _]]].
  inversion H.
  destruct p.
  - (* base case *)
    inversion res; subst. 
    apply uc_equiv_perm_ex_nil; auto.
    apply perm_pair_get_phys_log.
    assumption.
  - (* inductive case *)
    destruct (path_to_swaps (n :: n0 :: p) (swap_log m a n)) eqn:res'.
    inversion res; subst.  
    destruct Hpath as [H1 [H2 [H3 [H4 H5]]]].
    inversion H1; subst.
    inversion H4; subst.
    assert (WFm':=res').
    eapply path_to_swaps_bijective in WFm'.
    eapply IHp in res'.
    unfold uc_equiv_perm_ex in *.
    rewrite cons_to_app. 
    rewrite eval_append, res'.
    repeat rewrite Mmult_assoc.
    apply f_equal2; try reflexivity.
    apply f_equal2; try reflexivity.
    apply equal_on_basis_states_implies_equal; auto with wf_db.
    unfold eval; auto with wf_db.
    intro f.
    rewrite Mmult_assoc.
    rewrite SWAP_semantics by assumption.
    rewrite f_to_vec_SWAP by assumption.
    rewrite perm_to_matrix_permutes_qubits.
    rewrite perm_to_matrix_permutes_qubits.
    apply f_to_vec_eq.
    intros x Hx.
    apply fswap_swap_log; auto.
    apply get_phys_perm; assumption.
    apply get_phys_perm.
    apply swap_log_preserves_bij; assumption.
    eapply valid_path_subpath.
    repeat split; try apply H2; try assumption.
    apply swap_log_preserves_bij; assumption.
    eapply valid_path_subpath.
    repeat split; try apply H1; try apply H2; try assumption.
    apply swap_log_preserves_bij; assumption.
Qed.

(* These uc_eq_perm_* lemmas are specific to swap_route_sound -- they help
   keep the main proof a little cleaner *)

Lemma uc_equiv_perm_ex_cons_cong : forall (g : gate_app (Map_Unitary (G.U 1)) dim) (l1 l2 : ucom_l dim) p p1 p2,
  perm_pair dim p1 p2 ->
  uc_well_typed_l [g] ->
  l1 ≡ l2 with p1 and p ->
  (g :: l1) ≡ ((map_qubits_app p2 g) :: l2) with p1 and p.
Proof.
  intros g l1 l2 p p1 p2 Hperm WT H.
  unfold uc_equiv_perm_ex in *.
  rewrite (cons_to_app _ l1).
  rewrite (cons_to_app _ l2).
  rewrite 2 eval_append.  
  rewrite H.
  repeat rewrite Mmult_assoc.
  apply f_equal2; try reflexivity.
  apply f_equal2; try reflexivity.
  unfold eval.
  rewrite map_qubits_app_equiv_map_qubits.
  apply permute_commutes_with_map_qubits.
  assumption.
  subst.
  apply list_to_ucom_WT.
  assumption.
  apply uc_well_typed_l_implies_dim_nonzero in WT.
  assumption.
  destruct Hperm as [_ [? _]].
  assumption.
Qed.

Lemma uc_equiv_perm_ex_uc_equiv_l_app : forall (l l1 l1' l2 : ucom_l dim) p_in p_out,
  uc_equiv_l l1 l1' ->
  l ≡ l1 ++ l2 with p_in and p_out ->
  l ≡ l1' ++ l2 with p_in and p_out.
Proof.
  intros l l1 l1' l2 p_in p_out H1 H2.
  unfold uc_equiv_l, uc_equiv, uc_equiv_perm_ex in *.
  rewrite eval_append in *.
  unfold eval in *.
  rewrite H2, H1.
  reflexivity.
Qed.

Lemma uc_equiv_perm_ex_app1 : forall (l1 l1' l2 l2' : ucom_l dim) p1 p1inv p2 p3,
  perm_pair dim p1 p1inv ->
  l1 ≡ l1' with p1 and p2 ->
  l2 ≡ l2' with p2 and p3 ->
  (l1' ++ l2) ≡ l1 ++ l2' with p1inv and p3.
Proof.
  intros l1 l1' l2 l2' p1 p1inv p2 p3 [H1 [H2 [_ H3]]] H4 H5.
  unfold uc_equiv_perm_ex in *.
  rewrite 2 eval_append.
  rewrite H4, H5.
  repeat rewrite Mmult_assoc.
  rewrite perm_to_matrix_Mmult by auto.
  rewrite (perm_to_matrix_I _ (p1inv ∘ p1)%prg).
  Msimpl.
  reflexivity.
  unfold eval; auto with wf_db.
  apply permutation_compose; auto.
  intros x Hx.
  apply H3. auto.
Qed.

Lemma uc_equiv_perm_ex_app2 : forall (l1 l2 : ucom_l dim) (g : gate_app (Map_Unitary (G.U 1)) dim) p1 p2 p3,
  perm_pair dim p2 p3 ->
  uc_well_typed_l [g] ->
  l1 ≡ l2 with p1 and p2 ->
  (l1 ++ [map_qubits_app p3 g]) ≡ l2 ++ [g] with p1 and p2.
Proof.
  intros l1 l2 g p1 p2 p3 Hperm WT H.
  unfold uc_equiv_perm_ex in *.
  rewrite 2 eval_append.  
  rewrite H.
  repeat rewrite <- Mmult_assoc.
  apply f_equal2; try reflexivity.
  apply f_equal2; try reflexivity.
  unfold eval.
  rewrite map_qubits_app_equiv_map_qubits.
  symmetry.
  apply permute_commutes_with_map_qubits.
  assumption.
  apply list_to_ucom_WT.
  assumption.
  apply uc_well_typed_l_implies_dim_nonzero in WT.
  assumption.
  destruct Hperm as [_ [? _]].
  assumption.  
Qed.

Lemma uc_equiv_perm_ex_trans_r : forall (l1 l2 l3 : ucom_l dim) p_in p_out,
  uc_equiv_l l2 l3 ->
  l1 ≡ l2 with p_in and p_out ->
  l1 ≡ l3 with p_in and p_out.
Proof.
  intros l1 l2 l3 p_in p_out H1 H2.
  unfold uc_equiv_l, uc_equiv, uc_equiv_perm_ex, eval in *.
  rewrite H2, H1.
  reflexivity.
Qed.

Lemma uc_equiv_perm_ex_trans_l : forall (l1 l2 l3 : ucom_l dim) p_in p_out,
  uc_equiv_l l1 l2 ->
  l2 ≡ l3 with p_in and p_out ->
  l1 ≡ l3 with p_in and p_out.
Proof.
  intros l1 l2 l3 p_in p_out H1 H2.
  unfold uc_equiv_l, uc_equiv, uc_equiv_perm_ex, eval in *.
  rewrite H1, H2.
  reflexivity.
Qed.

(* Example: Consider an architecture with 3 qubits and LNN connectivity:
       0 <-> 1 <-> 2.
   Say we want to map the following program with input layout 
   m_in={0->1, 1->2, 2->0} (where l->p means that logical qubit l is bound 
   to physical qubit p):
       P1  :=  H 1; CNOT 1 2; H 1.
   The output of mapping will be the program
       P2  :=  H 2; SWAP 1 2; CNOT 1 0; H 1 
   and the map m_out={0->2, 1->1, 2->0}.

   Running program P1 on input state ∣abc⟩, measuring all qubits, and obtaining
   result ∣def⟩ (a,b,c,d,e,f ∈ {0,1}) is equivalent to running program P2 on input 
   state ∣cab⟩ and obtaining the result ∣fed⟩.

   We express this relationship as "P1 ≡ P2 with p_in and p_out", which says that
   uc_eval P1 = p_in × uc_eval P2 × p_out where permutation p_in=(get_log m)
   is the inverse of the input logical->physical qubit map and permutation
   p_out=(get_phys m') is the output logical->physical qubit map.
*)
Lemma swap_route_sound : forall (l l' : ucom_l dim) (m m' : layout),
  uc_well_typed_l l ->
  layout_bijective dim m ->
  swap_route l m CG.get_path = (l', m') -> 
  l ≡ l' with (get_log m) and (get_phys m').
Proof.
  intros l l' m m' WT WFm H.
  generalize dependent m'.
  generalize dependent m.
  generalize dependent l'.
  induction l; intros l' m WFm m' res; simpl in res.
  - inversion res; subst. 
    apply uc_equiv_perm_ex_nil; auto.
    apply uc_well_typed_l_implies_dim_nonzero in WT.
    assumption.
    apply perm_pair_get_log_phys.
    assumption.
  - destruct a; inversion WT; subst.
    + destruct (swap_route l m) eqn:res'.
      inversion res; subst.
      apply IHl in res'; auto.
      replace (App1 m0 (get_phys m n)) with (@map_qubits_app _ dim (get_phys m) (App1 m0 n)) by reflexivity.
      apply uc_equiv_perm_ex_cons_cong; auto.
      apply perm_pair_get_log_phys.
      assumption.
      constructor.
      assumption.
      constructor.
      apply uc_well_typed_l_implies_dim_nonzero in WT.
      assumption.
    + destruct (path_to_swaps (CG.get_path (get_phys m n) (get_phys m n0)) m) eqn:pth.
      destruct (swap_route l l0) eqn:res'.
      inversion res; subst.
      assert (pth':=pth).
      assert (get_phys m n < CG.dim).
      { apply get_phys_lt; assumption. }
      assert (get_phys m n0 < CG.dim).
      { apply get_phys_lt; assumption. }
      assert (get_phys m n <> get_phys m n0).
      { apply get_phys_neq with (dim:=dim); assumption. }
      eapply path_to_swaps_bijective in pth'; auto.
      eapply path_to_swaps_sound in pth; auto.
      apply IHl in res'; auto.
      rewrite (cons_to_app _ l).
      eapply uc_equiv_perm_ex_app1. 
      apply perm_pair_get_phys_log.
      assumption.
      2: apply res'.
      replace (App2 m0 (get_phys l0 n) (get_phys l0 n0)) with (@map_qubits_app _ dim (get_phys l0) (App2 m0 n n0)) by reflexivity.
      rewrite <- (app_nil_l [App2 m0 _ _]).
      apply uc_equiv_perm_ex_app2. 
      apply perm_pair_get_log_phys.
      assumption.
      constructor; try assumption.
      constructor.
      lia.
      apply pth.
      lia.
      apply CG.get_path_valid; auto.
      apply CG.get_path_valid; auto.
    + dependent destruction m0.
Qed.

Lemma swap_route_WT : forall (l : ucom_l dim) (m : layout) l' m',
  uc_well_typed_l l ->
  layout_bijective dim m ->
  swap_route l m CG.get_path = (l', m') -> 
  uc_well_typed_l l'.
Proof. 
  intros l m l' m' WT WF res.
  apply swap_route_sound in res; auto.
  unfold uc_equiv_perm_ex, eval in res.
  apply list_to_ucom_WT. 
  apply uc_eval_nonzero_iff.
  apply list_to_ucom_WT in WT.
  apply uc_eval_nonzero_iff in WT.
  intro contra.
  rewrite contra in res.
  rewrite Mmult_0_r, Mmult_0_l in res.
  contradiction.
Qed.

Lemma path_to_swaps_respects_undirected : forall n1 n2 p m (l : ucom_l dim) m' u,
  n1 < dim -> n2 < dim ->
  valid_path (get_phys m n1) (get_phys m n2) CG.is_in_graph dim p ->
  layout_bijective dim m ->
  path_to_swaps p m = (l, m') ->
  respects_constraints_undirected CG.is_in_graph (l ++ [App2 u (get_phys m' n1) (get_phys m' n2)]).
Proof.
  intros n1 n2 p m l m' u Hn1 Hn2 Hpath WF res.
  generalize dependent l.
  generalize dependent m.
  generalize dependent n1.
  induction p; intros n1 Hn1 m Hpath WF l res; simpl in res.
  destruct Hpath as [H _].
  inversion H.
  destruct p.
  destruct Hpath as [_ [_ [H _]]].
  inversion H.
  destruct p.
  inversion res; subst.
  constructor; [| constructor].
  destruct Hpath as [H1 [H2 [H3 [H4 H5]]]].
  inversion H1; subst.
  inversion H2; subst.
  inversion H3; subst.
  inversion H7; subst.
  assumption.
  inversion H8.
  inversion H7; subst.
  assumption.
  inversion H8.
  destruct (path_to_swaps (n :: n0 :: p) (swap_log m a n)) eqn:res'.
  inversion res; subst.
  apply IHp with (n1:=n1) in res'; auto; clear IHp.
  rewrite <- app_comm_cons.
  constructor; auto.
  destruct Hpath as [_ [_ [H _]]].
  inversion H; auto.
  replace a with (get_phys m n1) in *.
  replace (get_phys (swap_log m (get_phys m n1) n) n1) with n.
  replace (get_phys (swap_log m (get_phys m n1) n) n2) with (get_phys m n2).
  apply valid_path_subpath in Hpath.
  assumption.
  unfold get_phys at 2.
  rewrite find_phys_swap_log_3 with (n:=dim); auto.
  apply get_phys_lt; auto.
  destruct Hpath as [_ [_ [_ [H _]]]].
  inversion H; auto.
  intro contra.
  assert (H : get_log m (get_phys m n1) = n2).
  unfold get_log.
  rewrite contra; auto.
  rewrite get_log_phys_inv with (n:=dim) in H; auto.
  subst.
  destruct Hpath as [_ [_ [_ [_ H]]]].
  inversion H.
  contradiction.
  intro contra.
  destruct WF as [WF _].
  apply WF in contra.
  assert (H : get_phys m n2 = n).
  unfold get_phys.
  rewrite contra; auto.
  destruct Hpath as [_ [_ [_ [_ H1]]]].
  inversion H1.
  inversion H6; subst.
  contradiction.
  contradiction.
  unfold get_phys at 1.
  rewrite <- (get_log_phys_inv dim m n1) at 2; auto.
  rewrite find_phys_swap_log_1 with (n:=dim); auto.
  apply get_phys_lt; auto.
  destruct Hpath as [_ [_ [_ [H _]]]].
  inversion H; auto.
  destruct Hpath as [H _].
  inversion H; auto.
  destruct Hpath as [_ [_ [_ [H _]]]].
  inversion H; auto.
  apply swap_log_preserves_bij; auto.
Qed.

Lemma swap_route_respects_undirected : forall l m (l' : ucom_l dim) m',
  uc_well_typed_l l ->
  layout_bijective dim m ->
  swap_route l m CG.get_path = (l', m') ->
  respects_constraints_undirected CG.is_in_graph l'.
Proof.
  intros l m l' m' WT WFm H.
  generalize dependent m'.
  generalize dependent m.
  generalize dependent l'.
  induction l; intros l' m WFm m' res; simpl in res.
  - inversion res; subst. constructor.
  - destruct a; inversion WT; subst.
    + destruct (swap_route l m) eqn:res'.
      inversion res; subst.
      constructor.
      eapply IHl. assumption. apply WFm. apply res'.
    + destruct (path_to_swaps (CG.get_path (get_phys m n) (get_phys m n0)) m) eqn:pth.
      destruct (swap_route l l0) eqn:res'.
      inversion res; subst.
      apply respects_constraints_undirected_app.
      eapply path_to_swaps_respects_undirected; auto.
      2: apply WFm.
      2: apply pth.
      apply CG.get_path_valid.
      apply get_phys_lt; auto.
      apply get_phys_lt; auto.
      apply get_phys_neq with (dim:=dim); auto.
      eapply IHl. 
      assumption.
      2: apply res'.
      eapply path_to_swaps_bijective.
      2: apply WFm.
      2: apply pth.
      apply CG.get_path_valid.
      apply get_phys_lt; auto.
      apply get_phys_lt; auto.
      apply get_phys_neq with (dim:=dim); auto.
    + dependent destruction m0.
Qed.

Lemma decompose_swaps_and_cnots_respects_directed : forall (l : map_ucom_l (Full_Unitary 1) dim),
  respects_constraints_undirected CG.is_in_graph l ->
  respects_constraints_directed CG.is_in_graph UMap_CNOT (decompose_swaps_and_cnots l CG.is_in_graph).
Proof.
  intros l H.
  unfold decompose_swaps_and_cnots.
  induction l.
  rewrite change_gate_set_nil.
  constructor.
  rewrite change_gate_set_cons.
  inversion H; subst.
  simpl. constructor.
  apply IHl. assumption.
  apply respects_constraints_directed_app.
  dependent destruction u; simpl.
  destruct (CG.is_in_graph n1 n2) eqn:?.
  constructor. assumption. constructor.
  destruct H3; try easy.
  repeat constructor.
  assumption.
  destruct (CG.is_in_graph n1 n2) eqn:?.
  repeat constructor; assumption.
  destruct H3; try easy.
  repeat constructor; assumption.
  apply IHl. assumption.
Qed.

(** Equivalence up to qubit reordering without explicit permutations **)
Definition uc_equiv_perm (l1 l2 : ucom_l dim) := exists pin pout, 
  permutation dim pin /\ permutation dim pout /\ l1 ≡ l2 with pin and pout.
Infix "≡x" := uc_equiv_perm (at level 20).

Lemma permutation_id : permutation dim (fun x : nat => x).
Proof. exists (fun x : nat => x). repeat split; auto. Qed.  

Lemma uc_equiv_perm_refl : forall (l1 : ucom_l dim), l1 ≡x l1.
Proof. 
  intros. 
  exists (fun x => x). 
  exists (fun x => x). 
  repeat split.
  apply permutation_id.
  apply permutation_id.
  unfold uc_equiv_perm_ex.
  rewrite perm_to_matrix_I; auto.
  unfold eval. Msimpl. reflexivity.
  apply permutation_id.
Qed.

Lemma uc_equiv_perm_sym : forall (l1 l2 : ucom_l dim), l1 ≡x l2 -> l2 ≡x l1.
Proof. 
  intros l1 l2 H. 
  destruct H as [p1 [p2 [Hp1 [Hp2 H]]]].
  unfold uc_equiv_perm, uc_equiv_perm_ex in *.
  destruct Hp1 as [p1inv Hp1].
  destruct Hp2 as [p2inv Hp2].
  assert (permutation dim p1inv).
  { exists p1.
    intros x Hx.
    destruct (Hp1 x Hx) as [? [? [? ?]]].
    repeat split; auto. }
  assert (permutation dim p2inv).
  { exists p2.
    intros x Hx.
    destruct (Hp2 x Hx) as [? [? [? ?]]].
    repeat split; auto. }
  exists p1inv.
  exists p2inv.
  repeat split; auto.
  rewrite H.
  repeat rewrite Mmult_assoc.
  rewrite perm_to_matrix_Mmult; auto.
  repeat rewrite <- Mmult_assoc.
  rewrite perm_to_matrix_Mmult; auto.
  rewrite 2 perm_to_matrix_I.
  unfold eval. Msimpl. reflexivity.
  apply permutation_compose; auto.
  exists p1inv. assumption.
  intros x Hx.
  destruct (Hp1 x Hx) as [_ [_ [? _]]].
  assumption.
  apply permutation_compose; auto.
  exists p2inv. assumption.
  intros x Hx.
  destruct (Hp2 x Hx) as [_ [_ [_ ?]]].
  assumption.
  exists p2inv. assumption.
  exists p1inv. assumption.
Qed.

Lemma uc_equiv_perm_trans : forall (l1 l2 l3 : ucom_l dim), 
  l1 ≡x l2 -> l2 ≡x l3 -> l1 ≡x l3.
Proof.
  intros l1 l2 l3 H1 H2.
  unfold uc_equiv_perm in *.
  destruct H1 as [p1 [p2 [Hp1 [Hp2 H1]]]].
  destruct H2 as [p3 [p4 [Hp3 [Hp4 H2]]]].
  unfold uc_equiv_perm_ex in *.
  rewrite H1, H2.
  exists (p1 ∘ p3)%prg.
  exists (p4 ∘ p2)%prg.
  repeat split.
  apply permutation_compose; auto.
  apply permutation_compose; auto.
  rewrite <- 2 perm_to_matrix_Mmult; auto.
  repeat rewrite Mmult_assoc.
  reflexivity.
Qed.
    
Add Parametric Relation: (ucom_l dim) (uc_equiv_perm)
  reflexivity proved by uc_equiv_perm_refl
  symmetry proved by uc_equiv_perm_sym
  transitivity proved by uc_equiv_perm_trans
  as uc_equiv_perm_rel.

(** Equivalence up to qubit reordering, up to a global phase **)
Definition uc_cong_perm (l1 l2 : ucom_l dim) := exists pin pout,
  permutation dim pin /\ permutation dim pout /\
  eval l1 ∝ perm_to_matrix dim pout × eval l2 × perm_to_matrix dim pin.
Infix "≅x" := uc_cong_perm (at level 20).

Lemma uc_equiv_perm_implies_uc_cong_perm : forall (l1 l2 : ucom_l dim),
  l1 ≡x l2 -> l1 ≅x l2.
Proof.
  intros l1 l2 H.
  destruct H as [p1 [p2 [Hp1 [Hp2 H]]]].
  exists p1. exists p2.
  repeat split; auto.
  exists 0%R.
  rewrite Cexp_0.
  rewrite Mscale_1_l.
  apply H.
Qed.

Lemma uc_cong_perm_uc_cong_l : forall (l1 l2 l3 : ucom_l dim),
  (l1 ≅l≅ l2)%ucom -> l2 ≅x l3 -> l1 ≅x l3.
Proof.
  intros l1 l2 l3 [r1 H1] [p1 [p2 [Hp1 [Hp2 [r2 H2]]]]].
  exists p1. exists p2.
  repeat split; auto.
  exists (r1 + r2)%R.
  unfold eval in *.
  rewrite H1, H2. 
  distribute_scale.
  rewrite <- Cexp_add.
  reflexivity.
Qed.

Lemma uc_eq_perm_uc_cong_l_alt : forall (l1 l2 l3 : ucom_l dim),
  l1 ≅x l2 -> (l2 ≅l≅ l3)%ucom -> l1 ≅x l3.
Proof.
  intros l1 l2 l3 [p1 [p2 [Hp1 [Hp2 [r1 H1]]]]] [r2 H2].
  exists p1. exists p2.
  repeat split; auto.
  exists (r1 + r2)%R.
  unfold eval in *.
  rewrite H1, H2. 
  distribute_scale.
  rewrite <- Cexp_add.
  reflexivity.
Qed.

End SimpleMappingProofs.
