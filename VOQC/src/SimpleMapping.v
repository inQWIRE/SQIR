Require Export ConnectivityGraph.
Require Export Layouts.
Require Export UnitaryListRepresentation.

(* Simple strategy for mapping a program to a CNOT connectivity graph.
   When a CNOT occurs between non-adjacent qubits: (1) insert SWAPs to 
   make the qubits adjacent, (2) perform the CNOT, (3) update the 
   correspondence between logical (program) qubits and physical (machine)
   qubits. In cases where a CNOT is between adjacent qubits but in the wrong 
   orientation, insert H gates on the target and control. 
*)

(** Mapping function definition. **)

Fixpoint path_to_swaps {U dim} p m (SWAP : nat -> nat -> gate_list U dim)
  : (gate_list U dim * qmap dim) :=
  match p with
  | n1 :: n2 :: [] => ([], m)
  | n1 :: ((n2 :: _) as t) => 
      let (l, m') := path_to_swaps t (swap_in_map m n1 n2) SWAP in
      (SWAP n1 n2 ++ l, m')
  | _ => ([], m) (* bad input case - invaid path *)
  end.

(* At this point all CNOTs should be between adjacent qubits, but
   they may not respect the direction of the edges in the connectivity
   graph. We can fix this by insert Hadamard gates before and after
   each offending CNOT. *)
Fixpoint fix_cnots {U dim} (l : gate_list U dim) 
      (is_in_graph : nat -> nat -> bool) 
      (CNOT : nat -> nat -> gate_app U dim) 
      (H : nat -> gate_app U dim)
  : gate_list U dim :=
  match l with
  | [] => l
  | App2 _ n1 n2 :: t => 
      if is_in_graph n1 n2
      then CNOT n1 n2 :: fix_cnots t is_in_graph CNOT H
      else H n1 :: H n2 :: CNOT n2 n1 :: H n1 :: H n2 :: fix_cnots t is_in_graph CNOT H
  | h :: t => h :: fix_cnots t is_in_graph CNOT H
  end.

(* The input program references *logical* qubits, and the returned program
   references *physical* qubits. get_path and is_in_graph_b also reference 
   physical qubits. *) 
Fixpoint simple_map {U dim} (l : gate_list U dim) (m : qmap dim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph : nat -> nat -> bool) 
      (CNOT : nat -> nat -> gate_app U dim) 
      (SWAP : nat -> nat -> gate_list U dim)
      (H : nat -> gate_app U dim)
  : (gate_list U dim * qmap dim) :=
  match l with
  | [] => ([],m)
  | App2 _ n1 n2 :: t =>
      let p := get_path (log2phys m n1) (log2phys m n2) in
      let (swaps, m') := path_to_swaps p m SWAP in
      let mapped_cnot := 
        fix_cnots (swaps ++ [CNOT (log2phys m' n1) (log2phys m' n2)]) 
                  is_in_graph CNOT H in 
      let (t',m'') := simple_map t m' get_path is_in_graph CNOT SWAP H in
      (mapped_cnot ++ t', m'')
  | App1 u n :: t =>
      let (t',m') := simple_map t m get_path is_in_graph CNOT SWAP H in
      (App1 u (log2phys m n) :: t', m')
  | _ => ([], m) (* unreachable *)
  end.

(** Gate set for mapping. **)

(* The mapping routine above is defined for any gate set that consists of 
   (1) the CNOT gate, (2) the H gate, and (3) any other 1-qubit gates. The 
   H gate is needed to "reverse" the direction of a CNOT (see fix_cnots). *)
Module Type MappableGateSet (G :GateSet).

  Parameter had : G.U 1.
  Parameter cnot : G.U 2.
  Axiom had_semantics : forall (dim q : nat), 
    @G.to_base dim 1 had (q :: []) (one_elem_list q) = SQIR.H q.
  Axiom cnot_semantics : forall (dim q1 q2 : nat),
    @G.to_base dim 2 cnot (q1 :: q2 :: []) (two_elem_list q1 q2) = SQIR.CNOT q1 q2.
  Axiom no_other_2_q_gates : forall (u : G.U 2), u = cnot.
  Axiom no_3_q_gates : forall (u : G.U 3), False.

End MappableGateSet.

(* For example, we can define mapping over the RzQ gate set. *)
Require Import RzQGateSet.
Module MappableRzQ <: MappableGateSet RzQGateSet.

  Definition had := URzQ_H.
  Definition cnot := URzQ_CNOT.
  Lemma had_semantics : forall (dim q : nat), 
    @to_base dim 1 had (q :: []) (one_elem_list q) = SQIR.H q.
  Proof. intros. reflexivity. Qed.
  Lemma cnot_semantics : forall (dim q1 q2 : nat),
    @to_base dim 2 cnot (q1 :: q2 :: []) (two_elem_list q1 q2) = SQIR.CNOT q1 q2.
  Proof. intros. reflexivity. Qed.  
  Lemma no_other_2_q_gates : forall (u : U 2), u = cnot.
  Proof. intros. dependent destruction u. reflexivity. Qed.
  Lemma no_3_q_gates : forall (u : U 3), False.
  Proof. intros. dependent destruction u. Qed.

End MappableRzQ.

(** Proofs **)

Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

Inductive respects_constraints_undirected {U dim} : (nat -> nat -> bool) -> gate_list U dim -> Prop :=
  | res_und_nil : forall is_in_graph,
      respects_constraints_undirected is_in_graph []
  | res_und_app1 : forall u n t is_in_graph, 
      respects_constraints_undirected is_in_graph t ->
      respects_constraints_undirected is_in_graph (App1 u n :: t)
  | res_und_app2 : forall u n1 n2 t is_in_graph, 
      is_in_graph n1 n2 = true \/ is_in_graph n2 n1 = true -> (* undirected *)
      respects_constraints_undirected is_in_graph t ->
      respects_constraints_undirected is_in_graph (App2 u n1 n2 :: t).

Inductive respects_constraints_directed {U dim} : (nat -> nat -> bool) -> gate_list U dim -> Prop :=
  | res_dir_nil : forall is_in_graph,
      respects_constraints_directed is_in_graph []
  | res_dir_app1 : forall u n t is_in_graph, 
      respects_constraints_directed is_in_graph t ->
      respects_constraints_directed is_in_graph (App1 u n :: t)
  | res_dir_app2 : forall u n1 n2 t is_in_graph, 
      is_in_graph n1 n2 = true -> (* directed *) 
      respects_constraints_directed is_in_graph t ->
      respects_constraints_directed is_in_graph (App2 u n1 n2 :: t).

Lemma respects_constraints_directed_app : forall {U dim} (l1 l2 : gate_list U dim) is_in_graph,
  respects_constraints_directed is_in_graph l1 ->
  respects_constraints_directed is_in_graph l2 ->
  respects_constraints_directed is_in_graph (l1 ++ l2).
Proof.
  intros U dim l1 l2 is_in_graph Hl1 Hl2.
  induction Hl1.
  simpl; assumption.
  rewrite <- app_comm_cons.
  constructor; auto.
  constructor; auto.
Qed.

Module SimpleMappingProofs (G : GateSet) (MG : MappableGateSet G) (CG : ConnectivityGraph).

Definition dim := CG.dim.
Definition CNOT q1 q2 := @App2 _ dim MG.cnot q1 q2.
Definition H q := @App1 _ dim MG.had q.
Definition SWAP q1 q2 := CNOT q1 q2 :: CNOT q2 q1 :: CNOT q1 q2 :: [].

Lemma path_to_swaps_well_formed : forall n1 n2 p m l m',
  valid_path n1 n2 CG.is_in_graph p ->
  layout_well_formed dim m ->
  path_to_swaps p m SWAP = (l, m') ->
  layout_well_formed dim m'.
Proof.
  intros.
  generalize dependent l.
  generalize dependent m.
  generalize dependent n1.
  induction p; intros n1 Hpath m WFm c res; simpl in res.
  inversion res; subst. assumption.
  destruct p. inversion res; subst. assumption.
  destruct p. inversion res; subst. assumption.
  destruct (path_to_swaps (n :: n0 :: p) (swap_in_map m a n) SWAP) eqn:res'.
  inversion res; subst.
  destruct Hpath as [H1 [H2 [H3 H4]]].
  inversion H1; subst.
  eapply IHp; try apply res'.
  repeat split.
  inversion H2; subst. assumption.
  inversion H3; subst. assumption. 
  inversion H4; subst. assumption.
  assert (a < dim)%nat.
  { inversion H3; subst.
    destruct H8.
    apply CG.valid_graph in H0 as [? _].
    assumption. 
    apply CG.valid_graph in H0 as [_ [? _]]. 
    assumption. }
  assert (n < dim).
  { inversion H3; subst.
    destruct H9.
    apply CG.valid_graph in H5 as [_ [? _]].
    assumption. 
    apply CG.valid_graph in H5 as [? _]. 
    assumption. }
  apply swap_in_map_well_formed; assumption.
Qed.

Lemma simple_map_w_layout_well_formed : forall (l : gate_list G.U dim) m (l' : gate_list G.U dim) m',
  uc_well_typed_l l ->
  layout_well_formed dim m ->
  simple_map l m CG.get_path CG.is_in_graph CNOT SWAP H = (l', m') ->
  layout_well_formed dim m'.
Proof.
  intros l m l' m' WT WF res.
  generalize dependent m'.
  generalize dependent l'.
  generalize dependent m.
  induction l; intros m WF l' m' res; simpl in res.
  inversion res; subst. assumption.
  destruct a.
  - destruct (simple_map l m CG.get_path CG.is_in_graph CNOT SWAP H) eqn:res1. 
    inversion res; subst.
    eapply IHl.
    inversion WT; auto.
    apply WF.
    apply res1.
  - destruct (path_to_swaps (CG.get_path (log2phys m n) (log2phys m n0)) m SWAP) eqn:res1. 
    destruct (simple_map l q CG.get_path CG.is_in_graph CNOT SWAP H) eqn:res2. 
    inversion res; subst.
    inversion WT; subst.
    eapply IHl; auto.
    eapply path_to_swaps_well_formed in res1.
    apply res1.
    apply CG.get_path_valid.
    specialize (WF n H4) as [WF _].
    apply WF.
    specialize (WF n0 H5) as [WF _].
    apply WF.
    intro contra.
    contradict H6.
    destruct (WF n H4) as [_ [_ [neqn _]]].
    destruct (WF n0 H5) as [_ [_ [neqn0 _]]].
    rewrite contra, neqn0 in neqn.
    inversion neqn; auto.
    assumption.
    apply res2.
  - assert False. 
    apply MG.no_3_q_gates.
    assumption.
    contradiction.
Qed.

(* Some facts about permutation matrices. *)

Definition implements_permutation {n} (P : Square (2^n)) (p : nat -> nat) :=
  WF_Unitary P /\ 
  finite_bijection n p /\ 
  (forall f, P × f_to_vec n f = f_to_vec n (fun x => f (p x))).
(* I'm pretty sure that the last two conjuncts ("p is a permutation
   function and P behaves like p") forces P to be unitary, but I had
   some trouble proving this. -KH *)

Lemma implements_permutation_I : forall n, implements_permutation (I (2^n)) (fun x : nat => x).
Proof.
  intro n.
  split. apply id_unitary.
  split. 
  exists (fun x : nat => x). 
  intros. 
  repeat split; auto. 
  intro f.
  Msimpl. reflexivity.
Qed.

Lemma implements_permutation_Mmult : forall n (P1 P2 : Square (2^n)) p1 p2,
  implements_permutation P1 p1 -> 
  implements_permutation P2 p2 -> 
  implements_permutation (P1 × P2) (compose p2 p1).
Proof.
  intros n P1 P2 p1 p2 [WFU1 [Hp1 HP1]] [WFU2 [Hp2 HP2]].
  split.
  apply Mmult_unitary; assumption. 
  destruct Hp1 as [f1 Hf1].
  destruct Hp2 as [f2 Hf2].
  split.
  exists (compose f1 f2).
  intros x Hx.
  unfold compose.
  repeat split.
  destruct (Hf1 x Hx) as [H0 _].
  specialize (Hf2 (p1 x) H0) as [? _].
  assumption.
  destruct (Hf2 x Hx) as [_ [H0 _]].
  specialize (Hf1 (f2 x) H0) as [_ [? _]].
  assumption.
  destruct (Hf1 x Hx) as [H0 _].
  destruct (Hf2 (p1 x) H0) as [_ [_ [H1 _]]].
  rewrite H1.
  specialize (Hf1 x Hx) as [_ [_ [? _]]].
  assumption.
  destruct (Hf2 x Hx) as [_ [H0 _]].
  destruct (Hf1 (f2 x) H0) as [_ [_ [_ H1]]].
  rewrite H1.
  specialize (Hf2 x Hx) as [_ [_ [_ ?]]].
  assumption.
  intro f.
  rewrite Mmult_assoc.
  rewrite HP2, HP1.
  reflexivity.
Qed.

Lemma implement_permutation_adjoint : forall (P : Square (2^dim)) (m1 m2 : qmap dim),
  layout_well_formed dim m1 ->
  layout_well_formed dim m2 ->
  implements_permutation P (log2phys m1 ∘ phys2log m2)%prg -> 
  implements_permutation (P†) (log2phys m2 ∘ phys2log m1)%prg.
Proof.
  intros P m1 m2 WFm1 WFm2 [WFP [_ HP]].
  split; [split |].
  destruct WFP. auto with wf_db.
  apply transpose_unitary in WFP.
  destruct WFP. auto.
  split.
  unfold compose.
  exists (fun x : nat => log2phys m1 (phys2log m2 x)).
  intros x Hx.
  repeat split.
  destruct (WFm1 x Hx) as [_ [H0 _]].
  destruct (WFm2 (phys2log m1 x) H0) as [? _].
  assumption.
  destruct (WFm2 x Hx) as [_ [H0 _]].
  specialize (WFm1 (phys2log m2 x) H0) as [? _].
  assumption.
  destruct (WFm1 x Hx) as [_ [H0 _]].
  destruct (WFm2 (phys2log m1 x) H0) as [_ [_ [H1 _]]].
  rewrite H1.
  specialize (WFm1 x Hx) as [_ [_ [_ ?]]].
  assumption.
  destruct (WFm2 x Hx) as [_ [H0 _]].
  destruct (WFm1 (phys2log m2 x) H0) as [_ [_ [H1 _]]].
  rewrite H1.
  specialize (WFm2 x Hx) as [_ [_ [_ ?]]].
  assumption.
  intro f.
  rewrite <- Mmult_1_l; auto with wf_db.
  destruct WFP.
  rewrite <- H1.
  rewrite Mmult_assoc.
  apply f_equal2; try reflexivity.
  rewrite HP.
  unfold compose.
  apply f_to_vec_eq.
  intros x Hx.
  destruct (WFm2 x Hx) as [_ [H2 _]].
  destruct (WFm1 (phys2log m2 x) H2) as [_ [_ [H3 _]]].
  rewrite H3.
  specialize (WFm2 x Hx) as [_ [_ [_ H4]]].
  rewrite H4.
  reflexivity.
Qed.

Module ULR := UListRepr G.
Import ULR.

Lemma permute_commutes_with_map_qubits : 
  forall {dim} (P : Square (2 ^ dim)) (m1 m2 : qmap dim) (c : base_ucom dim),
  layout_well_formed dim m1 ->
  layout_well_formed dim m2 ->
  implements_permutation P (fun x : nat => log2phys m2 (phys2log m1 x)) ->
  uc_well_typed c ->
  (uc_eval (UnitaryOps.map_qubits (log2phys m1) c)) × P = 
      P × (uc_eval (UnitaryOps.map_qubits (log2phys m2) c)).
Proof.
  intros dim P m1 m2 c WFm1 WFm2 [[WF _] [_ HP]] WT.
  apply equal_on_basis_states_implies_equal; auto with wf_db.
  induction c; intro f; try dependent destruction u;
  inversion WT; subst; simpl; repeat rewrite Mmult_assoc.
  - rewrite <- (Mmult_assoc _ P).  
    rewrite IHc1 by assumption.
    repeat rewrite <- Mmult_assoc.
    do 2 (apply f_equal2; try reflexivity).
    apply equal_on_basis_states_implies_equal; auto with wf_db.
  - rewrite HP. 
    remember (fun x : nat => f (log2phys m2 (phys2log m1 x))) as f'.
    remember (log2phys m1 n) as x.
    remember (log2phys m2 n) as y.
    assert (x < dim).
    { subst. destruct (WFm1 n) as [? _]; auto. }
    assert (y < dim).
    { subst. destruct (WFm2 n) as [? _]; auto. }
    unfold pad.
    bdestruct_all.
    rewrite (f_to_vec_split 0 dim x) by assumption.
    rewrite (f_to_vec_split 0 dim y) by assumption.
    replace (f' x) with (f y).
    2: { subst. apply f_equal. 
         destruct (WFm1  n H1) as [_ [_ [? _]]]; auto. }
    restore_dims.
    replace (dim - 1 - y) with (dim - (y + 1)) by lia.
    replace (dim - 1 - x) with (dim - (x + 1)) by lia. 
    Msimpl.
    rewrite (ket_decomposition (rotation r r0 r1 × ∣ Nat.b2n (f y) ⟩)); 
      auto with wf_db.
    distribute_plus. 
    distribute_scale.
    do 2 apply f_equal2; try reflexivity.
    + remember (update f y false) as f0.
      replace (f_to_vec y f) with (f_to_vec y f0).
      replace ∣ 0 ⟩ with  ∣ Nat.b2n (f0 y) ⟩.
      replace (f_to_vec (dim - (y + 1)) (shift f (y + 1))) 
        with (f_to_vec (dim - (y + 1)) (shift f0 (y + 1))).
      replace (dim - (y + 1)) with (dim - 1 - y) by lia.
      rewrite <- f_to_vec_split by auto.
      rewrite HP.
      remember (update (fun x0 : nat => f (log2phys m2 (phys2log m1 x0))) x false) as f0'.
      replace (f_to_vec dim (fun x0 : nat => f0 (log2phys m2 (phys2log m1 x0)))) with (f_to_vec dim f0').
      rewrite (f_to_vec_split 0 dim x) by auto.
      replace (dim - 1 - x) with (dim - (x + 1)) by lia. 
      apply f_equal2; [apply f_equal2 |].
      all: subst. 
      symmetry.
      1,7: apply f_to_vec_update_oob; lia.
      1,5: repeat rewrite update_index_eq; reflexivity.
      symmetry.
      1,3: apply f_to_vec_shift_update_oob; right; lia.
      apply f_to_vec_eq.
      intros x Hx.
      unfold update.
      bdestruct (x =? log2phys m1 n); subst.
      replace (phys2log m1 (log2phys m1 n)) with n.
      2: { destruct (WFm1 n H1) as [_ [_ [? _]]]; auto. }
      bdestruct_all; trivial.
      bdestruct_all; trivial.
      assert (x = log2phys m1 n).
      { assert (H7: phys2log m2 (log2phys m2 (phys2log m1 x)) = phys2log m2 (log2phys m2 n)) by auto.
        destruct (WFm1 x) as [_ [? _]]; auto.
        destruct (WFm2 (phys2log m1 x)) as [_ [_ [H9 _]]]; auto.
        destruct (WFm2 n) as [_ [_ [H10 _]]]; auto.
        rewrite H9, H10 in H7.
        assert (log2phys m1 (phys2log m1 x) = log2phys m1 n) by auto.
        destruct (WFm1 x) as [_ [_ [_ ?]]]; subst; auto. }
      contradiction.
    + remember (update f y true) as f1.
      replace (f_to_vec y f) with (f_to_vec y f1).
      replace ∣ 1 ⟩ with  ∣ Nat.b2n (f1 y) ⟩.
      replace (f_to_vec (dim - (y + 1)) (shift f (y + 1))) 
        with (f_to_vec (dim - (y + 1)) (shift f1 (y + 1))).
      replace (dim - (y + 1)) with (dim - 1 - y) by lia.
      rewrite <- f_to_vec_split by auto.
      rewrite HP.
      remember (update (fun x0 : nat => f (log2phys m2 (phys2log m1 x0))) x true) as f1'.
      replace (f_to_vec dim (fun x0 : nat => f1 (log2phys m2 (phys2log m1 x0)))) with (f_to_vec dim f1').
      rewrite (f_to_vec_split 0 dim x) by auto.
      replace (dim - 1 - x) with (dim - (x + 1)) by lia. 
      apply f_equal2; [apply f_equal2 |].
      all: subst. 
      symmetry.
      1,7: apply f_to_vec_update_oob; lia.
      1,5: repeat rewrite update_index_eq; reflexivity.
      symmetry.
      1,3: apply f_to_vec_shift_update_oob; right; lia.
      apply f_to_vec_eq.
      intros x Hx.
      unfold update.
      bdestruct (x =? log2phys m1 n); subst.
      replace (phys2log m1 (log2phys m1 n)) with n.
      2: { destruct (WFm1 n H1) as [_ [_ [? _]]]; auto. }
      bdestruct_all; trivial.
      bdestruct_all; trivial.
      assert (x = log2phys m1 n).
      { assert (H7: phys2log m2 (log2phys m2 (phys2log m1 x)) = phys2log m2 (log2phys m2 n)) by auto.
        destruct (WFm1 x) as [_ [? _]]; auto.
        destruct (WFm2 (phys2log m1 x)) as [_ [_ [H9 _]]]; auto.
        destruct (WFm2 n) as [_ [_ [H10 _]]]; auto.
        rewrite H9, H10 in H7.
        assert (log2phys m1 (phys2log m1 x) = log2phys m1 n) by auto.
        destruct (WFm1 x) as [_ [_ [_ ?]]]; subst; auto. }
      contradiction.
  - rewrite HP.
    remember (log2phys m2 n) as x.
    remember (log2phys m2 n0) as y.
    assert (x < dim).
    { subst. destruct (WFm2 n) as [? _]; auto. }
    assert (y < dim).
    { subst. destruct (WFm2 n0) as [? _]; auto. }
    assert (x <> y).
    { subst. intro contra.
      assert (H2: phys2log m2 (log2phys m2 n) = phys2log m2 (log2phys m2 n0)) by auto.
      destruct (WFm2 n) as [_ [_ [H6 _]]]; auto.
      destruct (WFm2 n0) as [_ [_ [H7 _]]]; auto.
      rewrite H6, H7 in H2.
      contradiction. }
    replace (ueval_cnot dim x y) with (uc_eval (@SQIR.CNOT dim x y)) by reflexivity.
    rewrite f_to_vec_CNOT by assumption.
    rewrite HP.
    remember (log2phys m1 n) as z.
    remember (log2phys m1 n0) as w.
    assert (z < dim).
    { subst. destruct (WFm1 n) as [? _]; auto. }
    assert (w < dim).
    { subst. destruct (WFm1 n0) as [? _]; auto. }
    assert (z <> w).
    { subst. intro contra.
      assert (H8: phys2log m1 (log2phys m1 n) = phys2log m1 (log2phys m1 n0)) by auto.
      destruct (WFm1 n) as [_ [_ [H9 _]]]; auto.
      destruct (WFm1 n0) as [_ [_ [H10 _]]]; auto.
      rewrite H9, H10 in H8.
      contradiction. }
    replace (ueval_cnot dim z w) with (uc_eval (@SQIR.CNOT dim z w)) by reflexivity.
    rewrite f_to_vec_CNOT by assumption.
    apply f_to_vec_eq.
    subst.
    intros x Hx.
    unfold update.
    bdestruct (x =? log2phys m1 n0); subst.
    replace (phys2log m1 (log2phys m1 n0)) with n0.
    2: { destruct (WFm1 n0) as [_ [_ [? _]]]; auto. }
    replace (phys2log m1 (log2phys m1 n)) with n.
    2: { destruct (WFm1 n) as [_ [_ [? _]]]; auto. }
    bdestruct_all; trivial.
    bdestruct_all; trivial.
    assert (x = log2phys m1 n0).
    { assert (H11: phys2log m2 (log2phys m2 (phys2log m1 x)) = phys2log m2 (log2phys m2 n0)) by auto.
      destruct (WFm1 x) as [_ [? _]]; auto.
      destruct (WFm2 (phys2log m1 x)) as [_ [_ [H13 _]]]; auto.
      destruct (WFm2 n0) as [_ [_ [H14 _]]]; auto.
      rewrite H13, H14 in H11.
      assert (log2phys m1 (phys2log m1 x) = log2phys m1 n0) by auto.
      destruct (WFm1 x) as [_ [_ [_ ?]]]; subst; auto. }
    contradiction.
Qed.

(** Equivalence up to qubit reordering **)

Definition uc_eq_perm (l1 l2 : gate_list G.U dim) p :=
  exists P, implements_permutation P p /\ eval l1 = P × eval l2.
Notation "c1 ≡ c2 'with' p" := (uc_eq_perm c1 c2 p) (at level 20).

Lemma uc_eq_perm_refl : forall (l1 : gate_list G.U dim), 
  l1 ≡ l1 with (fun x : nat => x).
Proof. 
  intros. 
  exists (I (2 ^ dim)).
  split. 
  apply implements_permutation_I.
  Msimpl. 
  reflexivity.
  unfold eval.
  auto with wf_db.
Qed.

(* We can also prove the following, but it's tricky to state since we don't 
   have a name for p's inverse.

Lemma uc_eq_perm_sym : forall {dim : nat} (c1 c2 : base_ucom dim) P, 
  c1 ≡ c2 with p -> c2 ≡ c1 with p^{-1}. 
*)

Lemma uc_eq_perm_trans : forall (l1 l2 l3 : gate_list G.U dim) p12 p23, 
  l1 ≡ l2 with p12 -> l2 ≡ l3 with p23 -> l1 ≡ l3 with (compose p23 p12).
Proof.
  intros l1 l2 l3 p12 p23 H12 H23. 
  destruct H12 as [P12 [HP12 H12]].
  destruct H23 as [P23 [HP23 H23]].
  exists (P12 × P23). 
  split. 
  apply implements_permutation_Mmult; assumption.
  rewrite Mmult_assoc.
  rewrite <- H23, <- H12. reflexivity.
Qed.

Lemma uc_eq_perm_replace_perm : forall (l1 l2 : gate_list G.U dim) p p',
  (forall x, x < dim -> p x = p' x) ->
  l1 ≡ l2 with p ->
  l1 ≡ l2 with p'.
Proof.
  intros l1 l2 p p' Heq [P [HP H]]. 
  exists P.
  split; auto.
  destruct HP as [WF [Hbij Hf]].
  split; auto.
  split.
  destruct Hbij as [pinv Hbij].
  exists pinv.
  intros x Hx.
  specialize (Hbij x Hx) as [? [? [? ?]]].
  repeat split; try rewrite <- Heq; auto.
  intro f.
  rewrite Hf.
  apply f_to_vec_eq.
  intros.
  rewrite Heq; auto.
Qed.

Lemma uc_eq_perm_cons_cong : forall (g : gate_app G.U dim) (l1 l2 : gate_list G.U dim) p,
  l1 ≡ l2 with p ->
  (g :: l1) ≡ (g :: l2) with p.
Proof.
  intros g l1 l2 p [P [HP H]].
  exists P.
  split; auto.
  unfold eval in *.
  destruct g; simpl; rewrite H; rewrite Mmult_assoc; reflexivity.
Qed.

Lemma uc_eq_perm_app_cong : forall (l1 l2 l1' l2' : gate_list G.U dim) p,
  uc_equiv_l l1 l1' ->
  l2 ≡ l2' with p ->
  (l1 ++ l2) ≡ (l1' ++ l2') with p.
Proof.
  intros l1 l2 l1' l2' p Heq [P [HP H]].
  exists P.
  split; auto.
  unfold eval in *.
  rewrite 2 list_to_ucom_append.
  simpl.
  rewrite H, Heq.
  rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma uc_equiv_l_implies_uc_eq_perm : forall (l1 l2 : gate_list G.U dim),
  uc_equiv_l l1 l2 -> l1 ≡ l2 with (fun x => x).
Proof.
  intros l1 l2 H.
  unfold uc_equiv_l in H.
  exists (I (2 ^ dim)).
  split. 
  apply implements_permutation_I.
  Msimpl.
  assumption.
  unfold eval.
  auto with wf_db.
Qed.  

Lemma fix_cnots_sound : forall (l : gate_list G.U dim),
  uc_equiv_l (fix_cnots l CG.is_in_graph CNOT H) l.
Proof.
  intros.
  induction l; simpl.
  reflexivity.
  destruct a.
  - rewrite IHl. reflexivity.
  - assert (u = MG.cnot).
    apply MG.no_other_2_q_gates.
    subst.
    destruct (CG.is_in_graph n n0) eqn:gr; rewrite IHl.
    reflexivity.
    repeat rewrite (cons_to_app _ l).
    repeat rewrite app_comm_cons.
    apply uc_app_congruence; try reflexivity.
    unfold uc_equiv_l; simpl.
    repeat rewrite MG.had_semantics.
    repeat rewrite MG.cnot_semantics.
    repeat rewrite <- useq_assoc.
    rewrite H_swaps_CNOT.
    reflexivity.
  - assert False.
    apply MG.no_3_q_gates.
    assumption.
    contradiction.
Qed.

Local Opaque SWAP.
Lemma path_to_swaps_sound : forall n1 n2 p m l m',
  valid_path n1 n2 CG.is_in_graph p ->
  layout_well_formed dim m ->
  path_to_swaps p m SWAP = (l, m') ->
  l ≡ [] with (compose (log2phys m) (phys2log m')).
Proof.
  intros n1 n2 p m l m'.
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
    apply uc_eq_perm_replace_perm with (p:=(fun x => x)). 
    intros x Hx.
    destruct (WFm x) as [_ [_ [_ ?]]]; auto.
    apply uc_eq_perm_refl.
  - (* inductive case *)
    destruct (path_to_swaps (n :: n0 :: p) (swap_in_map m a n) SWAP) eqn:res'.
    inversion res; subst.  
    destruct Hpath as [H1 [H2 [H3 H4]]].
    inversion H1; subst.
    assert (a < dim).
    { inversion H3; subst.
      destruct H8.
      apply CG.valid_graph in H0 as [? _].
      assumption. 
      apply CG.valid_graph in H0 as [_ [? _]]. 
      assumption. }
    assert (n < dim).
    { inversion H3; subst.
      destruct H9.
      apply CG.valid_graph in H5 as [_ [? _]].
      assumption. 
      apply CG.valid_graph in H5 as [? _]. 
      assumption. }
    assert (a <> n).
    { inversion H3; subst.
      destruct H10.
      apply CG.valid_graph in H6 as [_ [_ ?]].
      assumption. 
      apply CG.valid_graph in H6 as [_ [_ ?]]. 
      lia. }
    assert (WFm':=res').
    eapply path_to_swaps_well_formed in WFm'.
    eapply IHp in res'.
    destruct res' as [P [HP res']].
    exists (P × (eval (SWAP a n))).
    destruct HP as [? [? HP]].
    split; [split |].
    apply Mmult_unitary; auto.
    unfold eval.
    apply uc_eval_unitary.
    admit. (*apply uc_well_typed_SWAP; auto.*)
    split.
    exists (log2phys m' ∘ phys2log m)%prg.
    intros x Hx.
    unfold compose.
    destruct (WFm x Hx) as [_ [? [_ ?]]].
    destruct (WFm' x Hx) as [_ [? [_ ?]]].
    destruct (WFm (phys2log m' x)) as [? [_ [H14 _]]]; auto.
    destruct (WFm' (phys2log m x)) as [? [_ [H16 _]]]; auto.
    repeat split; auto.
    rewrite H14; auto.
    rewrite H16; auto.
    intro f.
    rewrite Mmult_assoc.
    assert (eval (SWAP a n) = uc_eval (SQIR.SWAP a n)).
    admit. rewrite H9.
    rewrite f_to_vec_SWAP by assumption.
    rewrite HP.
    apply f_equal2; try reflexivity.
    apply functional_extensionality; intro x.
    unfold compose.
    unfold swap_in_map.
    destruct m; simpl.
    bdestruct (phys2log m' x =? n3 a).
    rewrite update_index_neq by assumption.
    rewrite update_index_eq.
    apply f_equal.
    rewrite H10.
    destruct (WFm a) as [_ [_ [_ ?]]]; auto.
    bdestruct (phys2log m' x =? n3 n).
    rewrite update_index_eq.
    apply f_equal.
    rewrite H11.
    destruct (WFm n) as [_ [_ [_ ?]]]; auto.
    rewrite 2 update_index_neq.
    reflexivity.
    intro contra.
    admit. (*symmetry in contra.
    rewrite WFm in contra.
    contradict H9.
    symmetry. apply contra.*)
    intro contra.
    admit. (*symmetry in contra.
    rewrite WFm in contra.
    contradict H8.
    symmetry. apply contra. *)
    admit. (*simpl.
    rewrite res'.
    rewrite denote_SKIP by lia.
    destruct H6.
    Msimpl. reflexivity.*)
    eapply valid_path_subpath.
    repeat split; try apply H2; try assumption.
    apply swap_in_map_well_formed; assumption.
    eapply valid_path_subpath.
    repeat split; try apply H1; try apply H2; try assumption.
    apply swap_in_map_well_formed; assumption.
Admitted.

(* Say that mapping program l (with initial layout m) onto the given 
   architecture produces program l' and final layout m'. Then the behavior
   of l using layout m is the same as the behavior of l' followed by 
   a conversion between m and m'. *)
Lemma simple_map_sound : forall (l : gate_list G.U dim) (m : qmap dim) l' m',
  uc_well_typed_l l ->
  layout_well_formed dim m ->
  simple_map l m CG.get_path CG.is_in_graph CNOT SWAP H = (l', m') -> 
  map_qubits (log2phys m) l ≡ l' with ((log2phys m') ∘ (phys2log m))%prg.
Proof. 
  intros l m l' m' WT.
  generalize dependent m'.
  generalize dependent l'.
  generalize dependent m.
  induction l; intros m l' m' WFm res; simpl in res.
  - inversion res; subst.
    simpl.
    apply uc_eq_perm_replace_perm with (p:=(fun x => x)).
    intros x Hx.
    specialize (WFm x Hx) as [_ [_ [_ ?]]]; auto.
    apply uc_eq_perm_refl.
  - destruct a; inversion WT; subst.
    + destruct (simple_map l m CG.get_path CG.is_in_graph CNOT SWAP H) eqn:res'.
      inversion res; subst.
      apply IHl in res'; auto.
      simpl.
      apply uc_eq_perm_cons_cong.
      assumption.
    + destruct (path_to_swaps (CG.get_path (log2phys m n) (log2phys m n0)) m SWAP) eqn:pth.
      destruct (simple_map l q CG.get_path CG.is_in_graph CNOT SWAP H) eqn:res'.
      inversion res; subst.
      assert (pth':=pth).
      eapply path_to_swaps_well_formed in pth'; auto.
      eapply path_to_swaps_sound in pth; auto.
      apply IHl in res'; auto.


      admit.


      destruct (WFm n) as [H0 [_ [H1 _]]]; auto.
      destruct (WFm n0) as [H2 [_ [H3 _]]]; auto.
      apply CG.get_path_valid; auto.     
      intro contra.
      assert (Heq: phys2log m (log2phys m n) = phys2log m (log2phys m n0)); auto.
      rewrite H1, H3 in Heq.
      contradiction.
      destruct (WFm n) as [H0 [_ [H1 _]]]; auto.
      destruct (WFm n0) as [H2 [_ [H3 _]]]; auto.
      apply CG.get_path_valid; auto.     
      intro contra.
      assert (Heq: phys2log m (log2phys m n) = phys2log m (log2phys m n0)); auto.
      rewrite H1, H3 in Heq.
      contradiction.
    + assert False.
      apply MG.no_3_q_gates.
      assumption.
      contradiction.
Admitted.

Lemma path_to_swaps_respects_undirected : forall n1 n2 p m l m',
  n1 < dim -> n2 < dim ->
  valid_path (log2phys m n1) (log2phys m n2) CG.is_in_graph p ->
  layout_well_formed dim m ->
  path_to_swaps p m SWAP = (l, m') ->
  respects_constraints_undirected CG.is_in_graph (l ++ [CNOT (log2phys m' n1) (log2phys m' n2)]).
Proof.
  intros n1 n2 p m l m' Hn1 Hn2 Hpath WF res.
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
  constructor. 
  destruct Hpath as [H1 [H2 [H3 H4]]].
  inversion H1; subst.
  inversion H2; subst.
  inversion H3; subst.
  inversion H6; subst.
  assumption.
  inversion H7.
  inversion H6; subst.
  assumption.
  inversion H7.
  constructor.
  destruct (path_to_swaps (n :: n0 :: p) (swap_in_map m a n) SWAP) eqn:res'.
  inversion res; subst.
  destruct Hpath as [H1 [H2 [H3 H4]]].
  inversion H1; subst.
  inversion H3; subst.
  assert (log2phys m n1 < dim).
  { destruct H8 as [H0 | H0].
    apply CG.valid_graph in H0 as [H0 _].
    assumption. 
    apply CG.valid_graph in H0 as [_ [H0 _]].
    assumption. }
  assert (n < dim).
  { destruct H8 as [H5 | H5].
    apply CG.valid_graph in H5 as [_ [H5 _]].
    assumption. 
    apply CG.valid_graph in H5 as [H5 _]. 
    assumption. }
  repeat apply res_und_app2; try assumption.
  apply or_comm; assumption.
  eapply IHp; try apply res'.
  assumption.
  replace (log2phys (swap_in_map m (log2phys m n1) n) n1) with n.
  replace (log2phys (swap_in_map m (log2phys m n1) n) n2) with (log2phys m n2).
  repeat split.
  inversion H2; subst. assumption.
  inversion H3; subst. assumption. 
  inversion H4; subst. assumption.  
  unfold swap_in_map. 
  destruct m; simpl.
  bdestruct (n2 =? n4 (n3 n1)).
  subst.
  inversion H4; subst.
  contradict H11.
  destruct (WF (n3 n1)) as [_ [_ [_ ?]]]; auto. 
  bdestruct (n2 =? n4 n).
  subst.
  inversion H4; subst.
  inversion H14; subst.
  contradict H11.
  destruct (WF n) as [_ [_ [_ ?]]]; auto.
  contradict H13.
  destruct (WF n) as [_ [_ [_ ?]]]; auto.
  reflexivity.
  unfold swap_in_map. 
  destruct m; simpl.
  bdestruct (n1 =? n4 (n3 n1)).
  reflexivity.
  contradict H6.
  destruct (WF n1) as [_ [_ [? _]]]; auto.
  apply swap_in_map_well_formed; auto.
Qed.
  
Lemma fix_cnots_respects_constraints : forall (l : gate_list G.U dim),
  respects_constraints_undirected CG.is_in_graph l ->
  respects_constraints_directed CG.is_in_graph (fix_cnots l CG.is_in_graph CNOT H).
Proof.
  intros l H.
  induction H; try constructor.
  apply IHrespects_constraints_undirected; assumption.
  destruct H0; simpl.
  - rewrite H0.
    constructor; assumption.
  - destruct (is_in_graph n1 n2) eqn:?. 
    constructor; assumption. 
    repeat constructor; assumption.
Qed.

Lemma simple_map_respects_constraints_directed : forall (l : gate_list G.U dim) (m : qmap dim) l' m',
  uc_well_typed_l l ->
  layout_well_formed dim m ->
  simple_map l m CG.get_path CG.is_in_graph CNOT SWAP H = (l', m') -> 
  respects_constraints_directed CG.is_in_graph l'.
Proof. 
  intros l m l' m' WT WF res.
  generalize dependent m'.
  generalize dependent l'.
  generalize dependent m.
  induction l; intros m WF l' m' res; simpl in res.
  inversion res; subst.
  constructor.
  destruct a.
  - inversion WT; subst.
    destruct (simple_map l m CG.get_path CG.is_in_graph CNOT SWAP H) eqn:res'.
    inversion res; subst.
    constructor.
    eapply IHl; try apply res'; auto.
  - inversion WT; subst.
    destruct (path_to_swaps (CG.get_path (log2phys m n) (log2phys m n0)) m SWAP) eqn:pth.
    destruct (simple_map l q CG.get_path CG.is_in_graph CNOT SWAP H) eqn:res'.
    inversion res; subst.
    assert (log2phys m n < dim).
    { destruct (WF n) as [? _]; auto. }
    assert (log2phys m n0 < dim).
    { destruct (WF n0) as [? _]; auto. }
    assert (log2phys m n <> log2phys m n0).
    { intro contra.
      assert (H2 : phys2log m (log2phys m n) = phys2log m (log2phys m n0)) by auto.
      destruct (WF n) as [_[_ [H8 _]]]; auto.
      destruct (WF n0) as [_[_ [H9 _]]]; auto.
      rewrite H8, H9 in H2.
      contradiction. }
    apply respects_constraints_directed_app.
    apply fix_cnots_respects_constraints.
    eapply path_to_swaps_respects_undirected; try apply pth; auto.
    apply CG.get_path_valid; auto.
    eapply IHl; try apply res'; auto.
    eapply path_to_swaps_well_formed; try apply pth; auto.
    apply CG.get_path_valid; auto.
  - assert False.
    apply MG.no_3_q_gates.
    assumption.
    contradiction.
Qed.

End SimpleMappingProofs.

