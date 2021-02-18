Require Export ConnectivityGraph.
Require Export Layouts.
Require Export UnitaryListRepresentation.

(* Simple strategy for mapping a program to a CNOT connectivity graph.
   When a CNOT occurs between non-adjacent qubits: (1) insert SWAPs to 
   make the qubits adjacent, (2) perform the CNOT, (3) update the 
   correspondence between logical (program) qubits and physical (machine)
   qubits. In cases where a CNOT is between adjacent qubits but in the wrong 
   orientation, insert H gates on the target and control. 

   Inputs:
     - l: a program over logical qubits
     - m: an initial mapping between logical and physical qubits
     - get_path: given two (physical) qubits, return an undirected path between them
     - is_in_graph: is there a directed edge between two (physical) qubits?
     - CNOT, SWAP, H: functions that output an appropriate sequence of gates
   Outputs:
     - a program over physical qubits
     - a final mapping between logical and physical qubits

   The proofs all assume that the number of logical and physical qubits ("dim")
   are the same. In practice, we expect that the number of physical qubits 
   will be >= the number of logical qubits. For this case, simply "cast" the input
   program to a type with the appropriate dimension.
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
    @G.to_base _ dim had (q :: []) (one_elem_list q) = SQIR.H q.
  Axiom cnot_semantics : forall (dim q1 q2 : nat),
    @G.to_base _ dim cnot (q1 :: q2 :: []) (two_elem_list q1 q2) = SQIR.CNOT q1 q2.
  Axiom no_other_2_q_gates : forall (u : G.U 2), u = cnot.
  Axiom no_3_q_gates : forall (u : G.U 3), False.

End MappableGateSet.

(* For example, we can define mapping over the RzQ gate set. *)
Require Import RzQGateSet.
Module MappableRzQ <: MappableGateSet RzQGateSet.

  Definition had := URzQ_H.
  Definition cnot := URzQ_CNOT.
  Lemma had_semantics : forall (dim q : nat), 
    @to_base _ dim had (q :: []) (one_elem_list q) = SQIR.H q.
  Proof. intros. reflexivity. Qed.
  Lemma cnot_semantics : forall (dim q1 q2 : nat),
    @to_base _ dim cnot (q1 :: q2 :: []) (two_elem_list q1 q2) = SQIR.CNOT q1 q2.
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

(* boolean version of respected_constraints_directed *)
Fixpoint respects_constraints_directed_b {U dim} (is_in_graph : nat -> nat -> bool) (l : gate_list U dim) :=
  match l with
  | [] => true
  | App1 _ _ :: t => respects_constraints_directed_b is_in_graph t
  | App2 _ n1 n2 :: t => is_in_graph n1 n2 && respects_constraints_directed_b is_in_graph t
  | _ => false
  end.

Lemma respects_constraints_directed_b_equiv : forall {U dim} is_in_graph (l : gate_list U dim),
  respects_constraints_directed_b is_in_graph l = true <-> respects_constraints_directed is_in_graph l.
Proof.
  intros U dim f l.
  split; intro H.
  - induction l.
    constructor.
    destruct a; simpl in H.
    apply IHl in H.
    constructor; auto.
    apply andb_prop in H as [H1 H2].
    apply IHl in H2.
    constructor; auto.
    inversion H.
  - induction H; auto.
    simpl.
    rewrite H, IHrespects_constraints_directed.
    reflexivity.
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

(* Permutation matrices -- could be moved elsewhere *)

Definition perm_mat n (p : nat -> nat) : Square n :=
  (fun x y => if (x =? p y) && (x <? n) && (y <? n) then C1 else C0).

Lemma perm_mat_WF : forall n p, WF_Matrix (perm_mat n p).
Proof.
  intros n p.
  unfold WF_Matrix, perm_mat. 
  intros x y [H | H].
  bdestruct (x =? p y); bdestruct (x <? n); bdestruct (y <? n); trivial; lia.
  bdestruct (x =? p y); bdestruct (x <? n); bdestruct (y <? n); trivial; lia.
Qed. 
Hint Resolve perm_mat_WF : wf_db.

Lemma perm_mat_unitary : forall n p, 
  finite_bijection n p -> WF_Unitary (perm_mat n p).
Proof.
  intros n p [pinv Hp].
  split.
  apply perm_mat_WF.
  unfold Mmult, adjoint, perm_mat, I.
  prep_matrix_equality.
  destruct ((x =? y) && (x <? n)) eqn:H.
  apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1.
  apply Nat.ltb_lt in H2.
  subst.
  apply Csum_unique.
  exists (p y).
  destruct (Hp y) as [? _]; auto.
  split; auto.
  split.
  bdestruct_all; simpl; lca.
  intros x Hx.
  bdestruct_all; simpl; lca.
  apply Csum_0.
  intros z.
  bdestruct_all; simpl; try lca.
  subst.
  rewrite andb_true_r in H.
  apply beq_nat_false in H.
  assert (pinv (p x) = pinv (p y)) by auto.
  destruct (Hp x) as [_ [_ [H5 _]]]; auto.
  destruct (Hp y) as [_ [_ [H6 _]]]; auto.
  contradict H.
  rewrite <- H5, <- H6.
  assumption.
Qed.

Lemma perm_mat_Mmult : forall n f g,
  finite_bijection n g ->
  perm_mat n f × perm_mat n g = perm_mat n (f ∘ g)%prg.
Proof.
  intros n f g [ginv Hgbij].
  unfold perm_mat, Mmult, compose.
  prep_matrix_equality.
  destruct ((x =? f (g y)) && (x <? n) && (y <? n)) eqn:H.
  apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1.
  apply Nat.ltb_lt in H2.
  apply Nat.ltb_lt in H3.
  subst.
  apply Csum_unique.
  exists (g y).
  destruct (Hgbij y) as [? _]; auto.
  split; auto.
  split.
  bdestruct_all; simpl; lca.
  intros x Hx.
  bdestruct_all; simpl; lca.
  apply Csum_0.
  intros z.
  bdestruct_all; simpl; try lca.
  subst.
  rewrite 2 andb_true_r in H.
  apply beq_nat_false in H.
  contradiction.
Qed.

Lemma perm_mat_I : forall n f,
  (forall x, x < n -> f x = x) ->
  perm_mat n f = I n.
Proof.
  intros n f Hinv.
  unfold perm_mat, I.
  prep_matrix_equality.
  bdestruct_all; simpl; try lca.
  rewrite Hinv in H2 by assumption.
  contradiction.
  rewrite Hinv in H2 by assumption.
  contradiction.
Qed.

(* Given a permutation p over n qubits, produce a permutation over 2^n indices. *)
Definition qubit_perm_to_nat_perm n (p : nat -> nat) :=
  fun x:nat => funbool_to_nat n ((nat_to_funbool n x) ∘ p)%prg.

Lemma qubit_perm_to_nat_perm_bij : forall n p,
  finite_bijection n p -> finite_bijection (2^n) (qubit_perm_to_nat_perm n p).
Proof.
  intros n p [pinv Hp].
  unfold qubit_perm_to_nat_perm.
  exists (fun x => funbool_to_nat n ((nat_to_funbool n x) ∘ pinv)%prg).
  intros x Hx.
  repeat split.
  apply funbool_to_nat_bound.
  apply funbool_to_nat_bound.
  unfold compose.
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. 
       rewrite funbool_to_nat_inverse. 
       destruct (Hp y) as [_ [_ [_ H]]].
       assumption.
       rewrite H.
       reflexivity.
       destruct (Hp y) as [_ [? _]]; auto. }
  rewrite nat_to_funbool_inverse; auto.
  unfold compose.
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. 
       rewrite funbool_to_nat_inverse. 
       destruct (Hp y) as [_ [_ [H _]]].
       assumption.
       rewrite H.
       reflexivity.
       destruct (Hp y) as [? _]; auto. }
  rewrite nat_to_funbool_inverse; auto.
Qed.  

Definition perm_to_matrix n p :=
  perm_mat (2 ^ n) (qubit_perm_to_nat_perm n p).
 
Lemma perm_to_matrix_permutes_qubits : forall n p f, 
  finite_bijection n p ->
  perm_to_matrix n p × f_to_vec n f = f_to_vec n (fun x => f (p x)).
Proof.
  intros n p f [pinv Hp].
  rewrite 2 basis_f_to_vec.
  unfold perm_to_matrix, perm_mat, qubit_perm_to_nat_perm.
  unfold basis_vector, Mmult, compose.
  prep_matrix_equality.
  destruct ((x =? funbool_to_nat n (fun x0 : nat => f (p x0))) && (y =? 0)) eqn:H.
  apply andb_prop in H as [H1 H2].
  rewrite Nat.eqb_eq in H1.
  rewrite Nat.eqb_eq in H2.
  apply Csum_unique.
  exists (funbool_to_nat n f).
  split.
  apply funbool_to_nat_bound.
  split.
  erewrite funbool_to_nat_eq.
  2: { intros. rewrite funbool_to_nat_inverse. reflexivity.
  destruct (Hp x0) as [? _]; auto. }
  specialize (funbool_to_nat_bound n f) as ?.
  specialize (funbool_to_nat_bound n (fun x0 : nat => f (p x0))) as ?.
  bdestruct_all; lca.
  intros z Hz.
  bdestructΩ (z =? funbool_to_nat n f).
  lca.
  apply Csum_0.
  intros z.
  bdestruct_all; simpl; try lca.
  rewrite andb_true_r in H.
  apply beq_nat_false in H.
  subst z.
  erewrite funbool_to_nat_eq in H2.
  2: { intros. rewrite funbool_to_nat_inverse. reflexivity.
  destruct (Hp x0) as [? _]; auto. }
  contradiction.
Qed.

Lemma perm_to_matrix_unitary : forall n p, 
  finite_bijection n p ->
  WF_Unitary (perm_to_matrix n p).
Proof.
  intros.
  apply perm_mat_unitary.
  apply qubit_perm_to_nat_perm_bij.
  assumption.
Qed.

Lemma qubit_perm_to_nat_perm_compose : forall n f g,
  finite_bijection n f ->
  (qubit_perm_to_nat_perm n f ∘ qubit_perm_to_nat_perm n g = 
    qubit_perm_to_nat_perm n (g ∘ f))%prg.
Proof.
  intros n f g [finv Hbij].
  unfold qubit_perm_to_nat_perm, compose.
  apply functional_extensionality.
  intro x.
  apply funbool_to_nat_eq.
  intros y Hy.
  rewrite funbool_to_nat_inverse.
  reflexivity.
  destruct (Hbij y) as [? _]; auto.
Qed.

Lemma perm_to_matrix_Mmult : forall n f g,
  finite_bijection n f ->
  finite_bijection n g ->
  perm_to_matrix n f × perm_to_matrix n g = perm_to_matrix n (g ∘ f)%prg.
Proof.
  intros. 
  unfold perm_to_matrix.
  rewrite perm_mat_Mmult.
  rewrite qubit_perm_to_nat_perm_compose by assumption.
  reflexivity.
  apply qubit_perm_to_nat_perm_bij.
  assumption.
Qed.

Lemma perm_to_matrix_I : forall n f,
  finite_bijection n f ->
  (forall x, x < n -> f x = x) ->
  perm_to_matrix n f = I (2 ^ n).
Proof.
  intros n f g Hbij. 
  unfold perm_to_matrix.
  apply perm_mat_I.
  intros x Hx.
  unfold qubit_perm_to_nat_perm, compose. 
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. rewrite Hbij by assumption. reflexivity. }
  apply nat_to_funbool_inverse.
  assumption.
Qed.

Lemma perm_to_matrix_WF : forall n p, WF_Matrix (perm_to_matrix n p).
Proof. intros. apply perm_mat_WF. Qed. 
Hint Resolve perm_to_matrix_WF : wf_db.

Module UL := UListProofs G.
Import UL.

(** Equivalence up to qubit reordering **)

Definition uc_eq_perm (l1 l2 : gate_list G.U dim) pin pout :=
  eval l1 = perm_to_matrix dim pout × eval l2 × perm_to_matrix dim pin.
Notation "c1 ≡ c2 'with' p1 'and' p2" := (uc_eq_perm c1 c2 p1 p2) (at level 20).

Lemma finite_bijection_compose : forall n f g,
  finite_bijection n f ->
  finite_bijection n g ->
  finite_bijection n (f ∘ g)%prg.
Proof.
  intros n f g [finv Hfbij] [ginv Hgbij].
  exists (ginv ∘ finv)%prg.
  unfold compose.
  intros x Hx.
  destruct (Hgbij x) as [? [_ [? _]]]; auto.
  destruct (Hfbij (g x)) as [? [_ [Hinv1 _]]]; auto.
  destruct (Hfbij x) as [_ [? [_ ?]]]; auto.
  destruct (Hgbij (finv x)) as [_ [? [_ Hinv2]]]; auto.
  repeat split; auto.
  rewrite Hinv1. 
  assumption.
  rewrite Hinv2. 
  assumption.
Qed.

Lemma uc_eq_perm_nil : forall (m : qmap dim),
  dim > 0 ->
  layout_well_formed dim m ->
  [] ≡ [] with (phys2log m) and (log2phys m).
Proof.
  intros m Hdim WF.
  unfold uc_eq_perm.
  unfold eval; simpl.
  rewrite denote_SKIP by assumption.
  Msimpl.
  rewrite perm_to_matrix_Mmult, perm_to_matrix_I.
  reflexivity.
  apply finite_bijection_compose.
  1,5: apply well_formed_phys2log_bij; assumption.
  1,3: apply well_formed_log2phys_bij; assumption.
  intros x Hx.
  unfold compose.
  destruct (WF x) as [_ [_ [? _]]]; auto.
Qed.

Lemma uc_eq_perm_nil_alt : forall (m : qmap dim),
  dim > 0 ->
  layout_well_formed dim m ->
  [] ≡ [] with (log2phys m) and (phys2log m).
Proof.
  intros m Hdim WF.
  replace (log2phys m) with (phys2log (invert_layout m)). 
  replace (phys2log m) with (log2phys (invert_layout m)). 
  apply uc_eq_perm_nil.
  assumption.
  apply invert_layout_well_formed.
  assumption.
  unfold invert_layout. destruct m. reflexivity.
  unfold invert_layout. destruct m. reflexivity.
Qed.

Lemma permute_commutes_with_map_qubits : forall (m : qmap dim) (u : base_ucom dim),
  layout_well_formed dim m ->
  uc_well_typed u ->
  perm_to_matrix dim (phys2log m) × uc_eval u = 
    uc_eval (map_qubits (log2phys m) u) × perm_to_matrix dim (phys2log m).
Proof.
  intros m u WF WT.
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
    specialize (well_formed_phys2log_bij m WF) as Hbij.
    repeat rewrite Mmult_assoc.
    rewrite perm_to_matrix_permutes_qubits by assumption. 
    assert (log2phys m n < dim).
    destruct (WF n) as [? _]; auto.
    unfold pad.
    bdestruct_all.
    rewrite (f_to_vec_split 0 dim n) by assumption.
    rewrite (f_to_vec_split 0 dim (log2phys m n)) by assumption.
    restore_dims.
    replace (dim - 1 - n) with (dim - (n + 1)) by lia.
    replace (dim - 1 - log2phys m n) with (dim - (log2phys m n + 1)) by lia. 
    Msimpl.
    destruct (WF n) as [_ [_ [Hinv _]]]; auto.
    rewrite Hinv.
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
      remember (update (fun x : nat => f (phys2log m x)) (log2phys m n) false) as f0'.
      replace (f_to_vec dim (fun x : nat => f0 (phys2log m x))) with (f_to_vec dim f0').
      rewrite (f_to_vec_split 0 dim (log2phys m n)) by auto.
      replace (dim - 1 - log2phys m n) with (dim - (log2phys m n + 1)) by lia.
      apply f_equal2; [apply f_equal2 |].
      all: subst. 
      1,7: apply f_to_vec_update_oob; lia.
      1,5: repeat rewrite update_index_eq; reflexivity.
      1,3: apply f_to_vec_shift_update_oob; right; lia.
      apply f_to_vec_eq.
      intros x Hx.
      unfold update.
      bdestruct (x =? log2phys m n); subst.
      rewrite Hinv.
      bdestruct_all; trivial.
      bdestruct_all; trivial.
      contradict H4.
      rewrite <- H5.
      destruct (WF x) as [_ [_ [_ ?]]]; auto.
    + remember (update f n true) as f1.
      replace (f_to_vec n f) with (f_to_vec n f1).
      replace ∣ 1 ⟩ with  ∣ Nat.b2n (f1 n) ⟩.
      replace (f_to_vec (dim - (n + 1)) (shift f (n + 1))) 
        with (f_to_vec (dim - (n + 1)) (shift f1 (n + 1))).
      replace (dim - (n + 1)) with (dim - 1 - n) by lia.
      rewrite <- f_to_vec_split by auto.
      rewrite perm_to_matrix_permutes_qubits by assumption.
      remember (update (fun x : nat => f (phys2log m x)) (log2phys m n) true) as f1'.
      replace (f_to_vec dim (fun x : nat => f1 (phys2log m x))) with (f_to_vec dim f1').
      rewrite (f_to_vec_split 0 dim (log2phys m n)) by auto.
      replace (dim - 1 - log2phys m n) with (dim - (log2phys m n + 1)) by lia.
      apply f_equal2; [apply f_equal2 |].
      all: subst. 
      1,7: apply f_to_vec_update_oob; lia.
      1,5: repeat rewrite update_index_eq; reflexivity.
      1,3: apply f_to_vec_shift_update_oob; right; lia.
      apply f_to_vec_eq.
      intros x Hx.
      unfold update.
      bdestruct (x =? log2phys m n); subst.
      rewrite Hinv.
      bdestruct_all; trivial.
      bdestruct_all; trivial.
      contradict H4.
      rewrite <- H5.
      destruct (WF x) as [_ [_ [_ ?]]]; auto.
  - apply equal_on_basis_states_implies_equal; auto with wf_db.
    intro f.
    specialize (well_formed_phys2log_bij m WF) as Hbij.
    repeat rewrite Mmult_assoc.
    rewrite perm_to_matrix_permutes_qubits by assumption.
    replace (ueval_cnot dim n n0) with (uc_eval (@SQIR.CNOT dim n n0)) by reflexivity.
    rewrite f_to_vec_CNOT by assumption.
    rewrite perm_to_matrix_permutes_qubits by assumption.
    replace (ueval_cnot dim (log2phys m n) (log2phys m n0)) 
      with (uc_eval (@SQIR.CNOT dim (log2phys m n) (log2phys m n0))) by reflexivity.
    destruct (WF n) as [? [_ [? _]]]; auto.
    destruct (WF n0) as [? [_ [? _]]]; auto.
    rewrite f_to_vec_CNOT; auto.
    apply f_to_vec_eq.
    intros x Hx.
    unfold update.
    rewrite H1, H6.
    bdestruct_all; try reflexivity.
    contradict H8.
    rewrite <- H7.
    destruct (WF x) as [_ [_ [_ ?]]]; auto.
    contradict H7.
    rewrite H8.
    destruct (WF x) as [_ [_ [_ ?]]]; auto.
    intro contra.
    contradict H5.
    assert (phys2log m (log2phys m n) = phys2log m (log2phys m n0)) by auto.
    rewrite H1, H6 in H5.
    assumption.
Qed.

Lemma permute_commutes_with_map_qubits_alt : forall (m : qmap dim) (u : base_ucom dim),
  layout_well_formed dim m ->
  uc_well_typed u ->
  perm_to_matrix dim (log2phys m) × uc_eval u = 
    uc_eval (map_qubits (phys2log m) u) × perm_to_matrix dim (log2phys m).
Proof.
  intros m u WF WT.
  replace (log2phys m) with (phys2log (invert_layout m)). 
  replace (phys2log m) with (log2phys (invert_layout m)). 
  apply permute_commutes_with_map_qubits.
  apply invert_layout_well_formed.
  assumption.
  assumption.
  unfold invert_layout. destruct m. reflexivity.
  unfold invert_layout. destruct m. reflexivity.
Qed.

Lemma eval_append : forall (l1 l2 : gate_list G.U dim),
  eval (l1 ++ l2) = eval l2 × eval l1.
Proof.
  intros.
  unfold eval.
  rewrite list_to_ucom_append.
  reflexivity.
Qed.

Definition map_qubits_app {U dim} (f : nat -> nat) (g : gate_app U dim) : gate_app U dim :=
  match g with
  | App1 u n => App1 u (f n)
  | App2 u m n => App2 u (f m) (f n)
  | App3 u m n p => App3 u (f m) (f n) (f p)
  end.

Local Transparent SQIR.SKIP SQIR.ID.
Lemma map_qubits_app_equiv_map_qubits : forall {dim} (f : nat -> nat) (g : gate_app G.U dim),
  dim > 0 ->
  finite_bijection dim f ->
  uc_eval (list_to_ucom [map_qubits_app f g]) = 
    uc_eval (map_qubits f (list_to_ucom [g])).
Proof.
  intros dim f g Hdim [finv Hbij].
  destruct (Hbij 0) as [? _]; auto.
  destruct g; simpl;
    rewrite I_rotation; repeat rewrite pad_id; 
    try assumption; Msimpl.
  all: erewrite <- G.to_base_map_commutes; reflexivity.
Qed.
Local Opaque SQIR.ID.

Lemma SWAP_well_typed : forall a b,
  a < dim -> b < dim -> a <> b ->
  uc_well_typed (list_to_ucom (SWAP a b)).
Proof.
  intros.
  simpl.
  repeat rewrite MG.cnot_semantics.
  repeat constructor.
  all: try apply uc_well_typed_CNOT; auto.
  unfold SKIP.  
  apply uc_well_typed_ID.
  lia.
Qed.
Local Opaque SQIR.SKIP.

Local Transparent SQIR.SWAP.
Lemma SWAP_semantics : forall a b,
  dim > 0 -> eval (SWAP a b) = uc_eval (SQIR.SWAP a b).
Proof.
  intros.
  unfold eval, SWAP, SQIR.SWAP.
  simpl.
  repeat rewrite MG.cnot_semantics.
  rewrite denote_SKIP by auto.
  Msimpl.
  rewrite Mmult_assoc.
  reflexivity.
Qed.
Local Opaque SQIR.SWAP SWAP.

Lemma path_to_swaps_sound : forall n1 n2 p m l m',
  dim > 0 ->
  valid_path n1 n2 CG.is_in_graph p ->
  layout_well_formed dim m ->
  path_to_swaps p m SWAP = (l, m') ->
  l ≡ [] with (log2phys m) and (phys2log m').
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
    apply uc_eq_perm_nil_alt; auto.
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
    unfold uc_eq_perm in *.
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
    unfold swap_in_map, log2phys; destruct m.
    bdestruct (x =? n3 a).
    rewrite update_index_neq by assumption.
    rewrite update_index_eq.
    subst.
    destruct (WFm a) as [_ [_ [_ ?]]]; auto.
    bdestruct (x =? n3 n).
    rewrite update_index_eq.
    subst.
    destruct (WFm n) as [_ [_ [_ ?]]]; auto.
    rewrite update_index_neq.
    rewrite update_index_neq.
    reflexivity.
    intro contra.
    subst.
    destruct (WFm x) as [_ [_ [? _]]]; auto.
    intro contra.
    subst.
    destruct (WFm x) as [_ [_ [? _]]]; auto.
    apply well_formed_log2phys_bij; assumption.
    apply well_formed_log2phys_bij.
    apply swap_in_map_well_formed; assumption.
    eapply valid_path_subpath.
    repeat split; try apply H2; try assumption.
    apply swap_in_map_well_formed; assumption.
    eapply valid_path_subpath.
    repeat split; try apply H1; try apply H2; try assumption.
    apply swap_in_map_well_formed; assumption.
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

(* These uc_eq_perm_* lemmas are specific to simple_map_sound -- they help
   keep the main proof a little cleaner *)

Lemma uc_eq_perm_cons_cong : forall (g : gate_app G.U dim) (l1 l2 : gate_list G.U dim) (m : qmap dim) p,
  layout_well_formed dim m ->
  uc_well_typed_l [g] ->
  l1 ≡ l2 with (phys2log m) and p ->
  (g :: l1) ≡ ((map_qubits_app (log2phys m) g) :: l2) with (phys2log m) and p.
Proof.
  intros g l1 l2 m p WF WT H.
  unfold uc_eq_perm in *.
  rewrite (cons_to_app _ l1).
  rewrite (cons_to_app _ l2).
  rewrite 2 eval_append.  
  rewrite H.
  repeat rewrite Mmult_assoc.
  apply f_equal2; try reflexivity.
  apply f_equal2; try reflexivity.
  unfold eval.
  rewrite map_qubits_app_equiv_map_qubits.
  remember (list_to_ucom [g]) as u.
  apply permute_commutes_with_map_qubits.
  assumption.
  subst.
  apply list_to_ucom_WT.
  assumption.
  apply uc_well_typed_l_implies_dim_nonzero in WT.
  assumption.
  apply well_formed_log2phys_bij.
  assumption.
Qed.

Lemma uc_eq_perm_uc_equiv_l_app : forall (l l1 l1' l2 : gate_list G.U dim) p_in p_out,
  uc_equiv_l l1 l1' ->
  l ≡ l1 ++ l2 with p_in and p_out ->
  l ≡ l1' ++ l2 with p_in and p_out.
Proof.
  intros l l1 l1' l2 p_in p_out H1 H2.
  unfold uc_equiv_l, uc_equiv, uc_eq_perm in *.
  rewrite eval_append in *.
  unfold eval in *.
  rewrite H2, H1.
  reflexivity.
Qed.

Lemma uc_eq_perm_app1 : forall (l1 l1' l2 l2' : gate_list G.U dim) (m1 m2 m3 : qmap dim),
  layout_well_formed dim m1 ->
  l1 ≡ l1' with (log2phys m1) and (phys2log m2) ->
  l2 ≡ l2' with (phys2log m2) and (log2phys m3) ->
  (l1' ++ l2) ≡ l1 ++ l2' with (phys2log m1) and (log2phys m3).
Proof.
  intros l1 l1' l2 l2' m1 m2 m3 WF H1 H2.
  unfold uc_eq_perm in *.
  rewrite 2 eval_append.
  rewrite H1, H2.
  repeat rewrite Mmult_assoc.
  rewrite perm_to_matrix_Mmult.
  rewrite (perm_to_matrix_I _ (phys2log m1 ∘ log2phys m1)%prg).
  Msimpl.
  reflexivity.
  unfold eval; auto with wf_db.
  apply finite_bijection_compose.
  apply well_formed_phys2log_bij; assumption.
  apply well_formed_log2phys_bij; assumption.
  intros x Hx.
  destruct (WF x) as [_ [_ [? _]]]; auto.
  apply well_formed_log2phys_bij; assumption.
  apply well_formed_phys2log_bij; assumption.
Qed.

Lemma uc_eq_perm_app2 : forall (l1 l2 : gate_list G.U dim) (g : gate_app G.U dim) (m : qmap dim) p,
  layout_well_formed dim m ->
  uc_well_typed_l [g] ->
  l1 ≡ l2 with p and (phys2log m) ->
  (l1 ++ [map_qubits_app (log2phys m) g]) ≡ l2 ++ [g] with p and (phys2log m).
Proof.
  intros l1 l2 g m p WF WT H.
  unfold uc_eq_perm in *.
  rewrite 2 eval_append.  
  rewrite H.
  repeat rewrite <- Mmult_assoc.
  apply f_equal2; try reflexivity.
  apply f_equal2; try reflexivity.
  unfold eval.
  rewrite map_qubits_app_equiv_map_qubits.
  remember (list_to_ucom [g]) as u.
  symmetry.
  apply permute_commutes_with_map_qubits.
  assumption.
  subst.
  apply list_to_ucom_WT.
  assumption.
  apply uc_well_typed_l_implies_dim_nonzero in WT.
  assumption.
  apply well_formed_log2phys_bij.
  assumption.  
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
   uc_eval P1 = p_in × uc_eval P2 × p_out where permutation p_in=(phys2log m)
   is the inverse of the input logical->physical qubit mapping and permutation
   p_out=(log2phys m') is the output logical->physical qubit mapping.
*)
Lemma simple_map_sound : forall (l : gate_list G.U dim) (m : qmap dim) l' m',
  uc_well_typed_l l ->
  layout_well_formed dim m ->
  simple_map l m CG.get_path CG.is_in_graph CNOT SWAP H = (l', m') -> 
  l ≡ l' with (phys2log m) and (log2phys m').
Proof. 
  intros l m l' m' WT.
  generalize dependent m'.
  generalize dependent l'.
  generalize dependent m.
  induction l; intros m l' m' WFm res; simpl in res.
  - inversion res; subst.
    apply uc_eq_perm_nil; auto.
    apply uc_well_typed_l_implies_dim_nonzero in WT.
    assumption.
  - destruct a; inversion WT; subst.
    + destruct (simple_map l m CG.get_path CG.is_in_graph CNOT SWAP H) eqn:res'.
      inversion res; subst.
      apply IHl in res'; auto.
      replace (App1 u (log2phys m n)) with (@map_qubits_app _ dim (log2phys m) (App1 u n)) by reflexivity.
      apply uc_eq_perm_cons_cong; auto.
      constructor.
      assumption.
      constructor.
      apply uc_well_typed_l_implies_dim_nonzero in WT.
      assumption.
    + destruct (path_to_swaps (CG.get_path (log2phys m n) (log2phys m n0)) m SWAP) eqn:pth.
      destruct (simple_map l q CG.get_path CG.is_in_graph CNOT SWAP H) eqn:res'.
      inversion res; subst.
      assert (pth':=pth).
      eapply path_to_swaps_well_formed in pth'; auto.
      eapply path_to_swaps_sound in pth; auto.
      apply IHl in res'; auto.
      eapply uc_eq_perm_uc_equiv_l_app. 
      symmetry.
      apply fix_cnots_sound.
      rewrite (cons_to_app _ l).
      eapply uc_eq_perm_app1. 
      assumption.
      2: apply res'.
      replace (CNOT (log2phys q n) (log2phys q n0)) with (@map_qubits_app _ dim (log2phys q) (CNOT n n0)) by reflexivity.
      rewrite <- (app_nil_l [App2 u _ _]).
      assert (u = MG.cnot).
      apply MG.no_other_2_q_gates.
      subst.
      apply uc_eq_perm_app2. 
      assumption.
      constructor; try assumption.
      constructor.
      lia.
      apply pth.
      lia.
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
Qed.
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

Lemma simple_map_WT : forall (l : gate_list G.U dim) (m : qmap dim) l' m',
  uc_well_typed_l l ->
  layout_well_formed dim m ->
  simple_map l m CG.get_path CG.is_in_graph CNOT SWAP H = (l', m') -> 
  uc_well_typed_l l'.
Proof. 
  intros l m l' m' WT WF res.
  apply simple_map_sound in res; auto.
  unfold uc_eq_perm, eval in res.
  apply list_to_ucom_WT. 
  apply uc_eval_nonzero_iff.
  apply list_to_ucom_WT in WT.
  apply uc_eval_nonzero_iff in WT.
  intro contra.
  rewrite contra in res.
  rewrite Mmult_0_r, Mmult_0_l in res.
  contradiction.
Qed.

Definition uc_cong_perm (l1 l2 : gate_list G.U dim) pin pout :=
  eval l1 ∝ perm_to_matrix dim pout × eval l2 × perm_to_matrix dim pin.
Notation "c1 ≅ c2 'with' p1 'and' p2" := (uc_cong_perm c1 c2 p1 p2) (at level 20).

Lemma uc_eq_perm_implies_uc_cong_perm : forall (l1 l2 : gate_list G.U dim) p1 p2,
  l1 ≡ l2 with p1 and p2 -> l1 ≅ l2 with p1 and p2.
Proof.
  intros l1 l2 p1 p2 H.
  exists 0%R.
  rewrite Cexp_0.
  rewrite Mscale_1_l.
  apply H.
Qed.

Lemma uc_eq_perm_uc_cong_l : forall (l1 l2 l3 : gate_list G.U dim) p1 p2,
  (l1 ≅l≅ l2)%ucom ->
  l2 ≅ l3 with p1 and p2 ->
  l1 ≅ l3 with p1 and p2.
Proof.
  intros l1 l2 l3 p1 p2 [r1 H1] [r2 H2].
  exists (r1 + r2)%R.
  unfold eval in *.
  rewrite H1, H2. 
  distribute_scale.
  rewrite <- Cexp_add.
  reflexivity.
Qed.

Lemma uc_eq_perm_uc_cong_l_alt : forall (l1 l2 l3 : gate_list G.U dim) p1 p2,
  l1 ≅ l2 with p1 and p2 ->
  (l2 ≅l≅ l3)%ucom ->
  l1 ≅ l3 with p1 and p2.
Proof.
  intros l1 l2 l3 p1 p2 [r1 H1] [r2 H2].
  exists (r1 + r2)%R.
  unfold eval in *.
  rewrite H1, H2. 
  distribute_scale.
  rewrite <- Cexp_add.
  reflexivity.
Qed.

End SimpleMappingProofs.

