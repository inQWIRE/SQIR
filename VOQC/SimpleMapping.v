Require Export ConnectivityGraph.
Require Export Layouts.
Require Import StandardGateSet.
Import StdList.

(* Simple strategy for mapping a program to a CNOT connectivity graph.
   When a CNOT occurs between non-adjacent qubits: (1) insert SWAPs to 
   make the qubits adjacent, (2) perform the CNOT, (3) update the 
   correspondence between logical (program) qubits and physical (machine)
   qubits. In cases where a CNOT is between adjacent qubits but in the wrong 
   orientation, insert H gates on the target and control. 

   Inputs:
     - l: a program over logical qubits, using the "standard" gate set
     - m: an initial mapping between logical and physical qubits
     - get_path: given two (physical) qubits, return an undirected path between them
     - is_in_graph: is there a directed edge between two (physical) qubits?
   Outputs:
     - a program over physical qubits, using the "standard" gate set
     - a final mapping between logical and physical qubits

   The proofs all assume that the number of logical and physical qubits ("dim")
   are the same. In practice, we expect that the number of physical qubits 
   will be >= the number of logical qubits. For this case, simply "cast" the input
   program to a type with the appropriate dimension.
*)

(** Predicates describing a correctly mapped program (gate set independent). **)

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

Inductive respects_constraints_directed {U : nat -> Set} {dim} : (nat -> nat -> bool) -> U 2%nat -> gate_list U dim -> Prop :=
  | res_dir_nil : forall is_in_graph cnot,
      respects_constraints_directed is_in_graph cnot []
  | res_dir_app1 : forall u n t is_in_graph cnot, 
      respects_constraints_directed is_in_graph cnot t ->
      respects_constraints_directed is_in_graph cnot (App1 u n :: t)
  | res_dir_app2 : forall n1 n2 t is_in_graph cnot, 
      is_in_graph n1 n2 = true -> (* directed *) 
      respects_constraints_directed is_in_graph cnot t ->
      respects_constraints_directed is_in_graph cnot (App2 cnot n1 n2 :: t).

Lemma respects_constraints_undirected_app : forall {U dim} (l1 l2 : gate_list U dim) is_in_graph,
  respects_constraints_undirected is_in_graph l1 ->
  respects_constraints_undirected is_in_graph l2 ->
  respects_constraints_undirected is_in_graph (l1 ++ l2).
Proof.
  intros U dim l1 l2 is_in_graph Hl1 Hl2.
  induction Hl1.
  simpl; assumption.
  rewrite <- app_comm_cons.
  constructor; auto.
  constructor; auto.
Qed.

Lemma respects_constraints_directed_app : forall {U dim} (l1 l2 : gate_list U dim) is_in_graph cnot,
  respects_constraints_directed is_in_graph cnot l1 ->
  respects_constraints_directed is_in_graph cnot l2 ->
  respects_constraints_directed is_in_graph cnot (l1 ++ l2).
Proof.
  intros U dim l1 l2 is_in_graph cnot Hl1 Hl2.
  induction Hl1.
  simpl; assumption.
  rewrite <- app_comm_cons.
  constructor; auto.
  constructor; auto.
Qed.

(* boolean version of respected_constraints_directed for the std gate set *)
Fixpoint respects_constraints_directed_b {dim} (is_in_graph : nat -> nat -> bool) (l : standard_ucom_l dim) :=
  match l with
  | [] => true
  | App1 _ _ :: t => respects_constraints_directed_b is_in_graph t
  | App2 U_CX n1 n2 :: t => is_in_graph n1 n2 && respects_constraints_directed_b is_in_graph t
  | _ => false
  end.

Lemma respects_constraints_directed_b_equiv : forall {dim} is_in_graph (l : standard_ucom_l dim),
  respects_constraints_directed_b is_in_graph l = true <-> 
  respects_constraints_directed is_in_graph U_CX l.
Proof.
  intros dim f l.
  split; intro H.
  - induction l.
    constructor.
    destruct a; simpl in H.
    apply IHl in H.
    constructor; auto.
    dependent destruction s; simpl in H.
    apply andb_prop in H as [H1 H2].
    apply IHl in H2.
    constructor; auto.
    all: inversion H.
  - induction l; auto.
    destruct a; inversion H; subst; simpl; auto.
    apply andb_true_intro; auto.
Qed.


Lemma respects_constraints_directed_app_split : forall {U dim} (l1 l2 : gate_list U dim) is_in_graph cnot,

  respects_constraints_directed is_in_graph cnot (l1 ++ l2)->
  respects_constraints_directed is_in_graph cnot l2 /\
  respects_constraints_directed is_in_graph cnot l1.
Proof.
  intros U dim l1 l2 is_in_graph cnot H.
  split.
  - induction l1.
    simpl in H.
    assumption.
    rewrite <- app_comm_cons in H.
    destruct a; remember (l1 ++ l2) as l; inversion H; subst;
    try (apply IHl1 in H2); try assumption.
    + apply IHl1 in H3. assumption.
    + apply IHl1 in H7.  assumption. 
  -induction l1.
   + apply res_dir_nil.
   + rewrite <- app_comm_cons in H;   
   destruct a; remember (l1 ++ l2) as l; inversion H; subst.
   * apply IHl1 in H3.
     apply res_dir_app1 with (u0 := u) (n0 := n).
     assumption.
   * apply IHl1 in H7.
     apply res_dir_app2 with (n1 := n) (n2 := n0) in H7.
     assumption.
     assumption.

Qed.


Lemma rev_respects_constraints:
  forall {U dim} (l : gate_list U dim) (is_in_graph : nat -> nat -> bool) cnot,
    respects_constraints_directed is_in_graph cnot l ->
    respects_constraints_directed is_in_graph cnot (rev l).
Proof.
  intros.
  induction l.
  - simpl. assumption.
  - simpl.
    apply respects_constraints_directed_app.
    apply IHl.
    inversion H; subst.
    assumption. 
    assumption.
    destruct a; try constructor; try constructor.
    inversion H; subst.
    constructor; try assumption.
    constructor.
     
    inversion H; subst.
Qed. 

(* "Optimized" decomposition of SWAP chooses between (CX a b; CX b a; CX a b) 
    and (CX b a; CX a b; CX b a) depending on which will introduce fewer H gates. *)
Definition decompose_swaps_u {dim} (is_in_graph : nat -> nat -> bool) (g : gate_app Std_Unitary dim) : standard_ucom_l dim :=
  match g with
  | App2 U_SWAP m n  => if is_in_graph m n
                       then App2 U_CX m n :: App2 U_CX n m :: App2 U_CX m n :: []
                       else App2 U_CX n m :: App2 U_CX m n :: App2 U_CX n m :: []
  | g => [g]
  end.

Definition decompose_swaps {dim} (is_in_graph : nat -> nat -> bool) (l : standard_ucom_l dim) :=
  change_gate_set (decompose_swaps_u is_in_graph) l.

(** Mapping function definition. **)

Definition SWAP {dim} a b : gate_app Std_Unitary dim := App2 U_SWAP a b.
Definition CNOT {dim} a b : gate_app Std_Unitary dim := App2 U_CX a b.
Definition H {dim} a : gate_app Std_Unitary dim := App1 U_H a.

Fixpoint path_to_swaps {dim} p m : (standard_ucom_l dim * qmap dim) :=
  match p with
  | n1 :: n2 :: [] => ([], m)
  | n1 :: ((n2 :: _) as t) => 
      let (l, m') := path_to_swaps t (swap_in_map m n1 n2) in
      (SWAP n1 n2 :: l, m')
  | _ => ([], m) (* bad input case - invaid path *)
  end.

(* At this point all CNOTs should be between adjacent qubits, but
   they may not respect the direction of the edges in the connectivity
   graph. We can fix this by insert Hadamard gates before and after
   each offending CNOT. *)
Fixpoint fix_cnots {dim} (l : standard_ucom_l dim) (is_in_graph : nat -> nat -> bool) : standard_ucom_l dim :=
  match l with
  | [] => l
  | App2 U_CX n1 n2 :: t => 
      if is_in_graph n1 n2
      then CNOT n1 n2 :: fix_cnots t is_in_graph
      else H n1 :: H n2 :: CNOT n2 n1 :: H n1 :: H n2 :: fix_cnots t is_in_graph
  | h :: t => h :: fix_cnots t is_in_graph
  end.

(* The input program references *logical* qubits, and the returned program
   references *physical* qubits. get_path and is_in_graph_b also reference 
   physical qubits. The output of this is a program with SWAPs that respects
   *undirected* connectivity constraints. *) 
Fixpoint insert_swaps {dim} (l : standard_ucom_l dim) (m : qmap dim) (get_path : nat -> nat -> list nat) : (standard_ucom_l dim * qmap dim) :=
  match l with
  | [] => ([],m)
  | App2 U_CX n1 n2 :: t =>
      let p := get_path (log2phys m n1) (log2phys m n2) in
      let (swaps, m') := path_to_swaps p m in
      let mapped_cnot := swaps ++ [CNOT (log2phys m' n1) (log2phys m' n2)] in 
      let (t',m'') := insert_swaps t m' get_path in
      (mapped_cnot ++ t', m'')
  | App1 u n :: t =>
      let (t',m') := insert_swaps t m get_path in
      (App1 u (log2phys m n) :: t', m')
  | _ => ([], m) (* unreachable, assuming decompose_gates is run first *)
  end.

(* Final mapping function. Starts by applying decompose_gates and ends by
   applying decompose_SWAPs and fix_CNOTs. *)
Definition simple_map {dim} (l : standard_ucom_l dim) (m : qmap dim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph : nat -> nat -> bool) 
  : (standard_ucom_l dim * qmap dim) :=
  let l' := decompose_to_cnot l in
  let (lm, m') := insert_swaps l' m get_path in
  let lm' := decompose_swaps is_in_graph lm in
  let lfin := fix_cnots lm' is_in_graph in
  (lfin, m').

(** Proofs **)

Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

Module SimpleMappingProofs (CG : ConnectivityGraph).

Definition dim := CG.dim.

Lemma path_to_swaps_well_formed : forall n1 n2 p m l m',
  valid_path n1 n2 CG.is_in_graph dim p ->
  layout_well_formed dim m ->
  path_to_swaps p m = (l, m') ->
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
  destruct (path_to_swaps (n :: n0 :: p) (swap_in_map m a n)) eqn:res'.
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
  apply swap_in_map_well_formed; assumption.
Qed.

Lemma insert_swaps_well_formed : forall (l l' : standard_ucom_l dim) m m',
  uc_well_typed_l l ->
  layout_well_formed dim m ->
  insert_swaps l m CG.get_path = (l', m') ->
  layout_well_formed dim m'.
Proof.
  intros l l' m m' WT WF res.
  generalize dependent m'.
  generalize dependent l'.
  generalize dependent m.
  induction l; intros m WF l' m' res; simpl in res.
  inversion res; subst. assumption.
  destruct a.
  - destruct (insert_swaps l m CG.get_path) eqn:res1. 
    inversion res; subst.
    eapply IHl.
    inversion WT; auto.
    apply WF.
    apply res1.
  - dependent destruction s.
    destruct (path_to_swaps (CG.get_path (log2phys m n) (log2phys m n0)) m) eqn:res1. 
    destruct (insert_swaps l q CG.get_path) eqn:res2. 
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
    inversion res; subst.
    assumption.
    inversion res; subst.
    assumption.
  - inversion res; subst.
    assumption.
Qed.

Lemma simple_map_well_formed : forall (l l' : standard_ucom_l dim) m m',
  uc_well_typed_l l ->
  layout_well_formed dim m ->
  simple_map l m CG.get_path CG.is_in_graph = (l', m') ->
  layout_well_formed dim m'.
Proof.
  intros l m l' m' WT WF res.
  unfold simple_map in res.
  destruct (insert_swaps (decompose_to_cnot l) l' CG.get_path) eqn:sw.
  inversion res; subst.
  eapply insert_swaps_well_formed; try apply sw.
  apply decompose_to_cnot_WT; assumption.
  assumption.
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

(** Equivalence up to qubit reordering **)

Definition uc_eq_perm (l1 l2 : standard_ucom_l dim) pin pout :=
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

Lemma eval_append : forall (l1 l2 : standard_ucom_l dim),
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

Local Transparent SQIR.ID.
Lemma map_qubits_app_equiv_map_qubits : forall {dim} (f : nat -> nat) (g : gate_app Std_Unitary dim),
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
  all: erewrite <- to_base_map_commutes; reflexivity.
Qed.
Local Opaque SQIR.ID.

Lemma SWAP_well_typed : forall a b,
  a < dim -> b < dim -> a <> b ->
  uc_well_typed (list_to_ucom ([@SWAP dim a b])).
Proof.
  intros.
  simpl.
  constructor.
  apply uc_well_typed_SWAP; lia.
  apply uc_well_typed_ID.
  lia.
Qed.

Lemma SWAP_semantics : forall a b,
  dim > 0 -> eval ([@SWAP dim a b]) = uc_eval (SQIR.SWAP a b).
Proof.
  intros.
  unfold eval.
  simpl.
  rewrite denote_SKIP by auto.
  Msimpl.
  reflexivity.
Qed.

Lemma path_to_swaps_sound : forall n1 n2 p m l m',
  dim > 0 ->
  valid_path n1 n2 CG.is_in_graph dim p ->
  layout_well_formed dim m ->
  path_to_swaps p m = (l, m') ->
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
    destruct (path_to_swaps (n :: n0 :: p) (swap_in_map m a n)) eqn:res'.
    inversion res; subst.  
    destruct Hpath as [H1 [H2 [H3 [H4 H5]]]].
    inversion H1; subst.
    inversion H4; subst.
    assert (WFm':=res').
    eapply path_to_swaps_well_formed in WFm'.
    eapply IHp in res'.
    unfold uc_eq_perm in *.
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

Lemma fix_cnots_sound : forall (l : standard_ucom_l dim),
  uc_equiv_l (fix_cnots l CG.is_in_graph) l.
Proof.
  intros.
  induction l; simpl.
  reflexivity.
  destruct a.
  - rewrite IHl. reflexivity.
  - dependent destruction s.
    destruct (CG.is_in_graph n n0) eqn:gr; rewrite IHl.
    reflexivity.
    repeat rewrite (cons_to_app _ l).
    repeat rewrite app_comm_cons.
    apply uc_app_congruence; try reflexivity.
    unfold uc_equiv_l; simpl.
    repeat rewrite <- useq_assoc.
    rewrite H_swaps_CNOT.
    reflexivity.
    rewrite IHl. reflexivity.
    rewrite IHl. reflexivity.
  - rewrite IHl. reflexivity.
Qed.

Lemma decompose_swaps_sound : forall (l : standard_ucom_l dim),
  uc_equiv_l (decompose_swaps CG.is_in_graph l) l.
Proof.
  induction l.
  reflexivity.
  unfold decompose_swaps.
  rewrite change_gate_set_cons.
  rewrite IHl.
  rewrite cons_to_app.
  StdList.apply_app_congruence.
  destruct a; dependent destruction s; try reflexivity.
  simpl.
  destruct (CG.is_in_graph n n0); unfold uc_equiv_l; simpl.
  repeat rewrite <- useq_assoc.
  reflexivity.
  rewrite 2 SKIP_id_r.
  unfold uc_equiv; simpl.
  bdestruct (n <? dim).
  bdestruct (n0 <? dim).
  bdestruct (n =? n0).
  1,3,4: autorewrite with eval_db; gridify. (* ill-typed cases *)
  apply equal_on_basis_states_implies_equal; auto with wf_db.
  intro f.
  repeat rewrite Mmult_assoc.
  repeat rewrite f_to_vec_CNOT by lia.
  rewrite f_to_vec_SWAP by assumption.
  repeat rewrite update_index_eq.
  repeat rewrite update_index_neq by lia.
  repeat rewrite update_index_eq.
  rewrite update_twice_neq by lia.
  rewrite update_twice_eq.
  rewrite update_twice_neq by lia.
  destruct (f n); destruct (f n0); reflexivity.
Qed.

(* These uc_eq_perm_* lemmas are specific to simple_map_sound -- they help
   keep the main proof a little cleaner *)

Lemma uc_eq_perm_cons_cong : forall (g : gate_app Std_Unitary dim) (l1 l2 : standard_ucom_l dim) (m : qmap dim) p,
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

Lemma uc_eq_perm_uc_equiv_l_app : forall (l l1 l1' l2 : gate_list Std_Unitary dim) p_in p_out,
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

Lemma uc_eq_perm_app1 : forall (l1 l1' l2 l2' : standard_ucom_l dim) (m1 m2 m3 : qmap dim),
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

Lemma uc_eq_perm_app2 : forall (l1 l2 : standard_ucom_l dim) (g : gate_app Std_Unitary dim) (m : qmap dim) p,
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

Lemma uc_eq_perm_trans_r : forall (l1 l2 l3 : gate_list Std_Unitary dim) p_in p_out,
  uc_equiv_l l2 l3 ->
  l1 ≡ l2 with p_in and p_out ->
  l1 ≡ l3 with p_in and p_out.
Proof.
  intros l1 l2 l3 p_in p_out H1 H2.
  unfold uc_equiv_l, uc_equiv, uc_eq_perm, eval in *.
  rewrite H2, H1.
  reflexivity.
Qed.

Lemma uc_eq_perm_trans_l : forall (l1 l2 l3 : gate_list Std_Unitary dim) p_in p_out,
  uc_equiv_l l1 l2 ->
  l2 ≡ l3 with p_in and p_out ->
  l1 ≡ l3 with p_in and p_out.
Proof.
  intros l1 l2 l3 p_in p_out H1 H2.
  unfold uc_equiv_l, uc_equiv, uc_eq_perm, eval in *.
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
   uc_eval P1 = p_in × uc_eval P2 × p_out where permutation p_in=(phys2log m)
   is the inverse of the input logical->physical qubit mapping and permutation
   p_out=(log2phys m') is the output logical->physical qubit mapping.
*)
Lemma simple_map_sound : forall (l l' : standard_ucom_l dim) (m m' : qmap dim),
  uc_well_typed_l l ->
  layout_well_formed dim m ->
  simple_map l m CG.get_path CG.is_in_graph = (l', m') -> 
  l ≡ l' with (phys2log m) and (log2phys m').
Proof. 
  intros l l' m m' WT WFm H.
  unfold simple_map in H.
  destruct (insert_swaps (decompose_to_cnot l) m CG.get_path) eqn:res.
  inversion H; subst.
  clear H.
  eapply uc_eq_perm_trans_r.
  symmetry.
  apply fix_cnots_sound.
  eapply uc_eq_perm_trans_r.
  symmetry.
  apply decompose_swaps_sound.
  eapply uc_eq_perm_trans_l.
  symmetry.
  apply decompose_to_cnot_sound.
  apply decompose_to_cnot_WT in WT.
  remember (decompose_to_cnot l) as l'.
  assert (fg : forall_gates only_cnots l').
  subst. 
  apply decompose_to_cnot_gates.
  clear Heql'.
  generalize dependent s.
  generalize dependent m'.
  generalize dependent m.
  induction l'; intros m WFm m' s res; simpl in res.
  - inversion res; subst. 
    apply uc_eq_perm_nil; auto.
    apply uc_well_typed_l_implies_dim_nonzero in WT.
    assumption.
  - destruct a; inversion WT; subst.
    + destruct (insert_swaps l' m CG.get_path) eqn:res'.
      inversion res; subst.
      apply IHl' in res'; auto.
      replace (App1 s0 (log2phys m n)) with (@map_qubits_app _ dim (log2phys m) (App1 s0 n)) by reflexivity.
      apply uc_eq_perm_cons_cong; auto.
      constructor.
      assumption.
      constructor.
      apply uc_well_typed_l_implies_dim_nonzero in WT.
      assumption.
      eapply forall_gates_drop.
      apply fg.
    + dependent destruction s0; try impossible_gate.
      destruct (path_to_swaps (CG.get_path (log2phys m n) (log2phys m n0)) m) eqn:pth.
      destruct (insert_swaps l' q CG.get_path) eqn:res'.
      inversion res; subst.
      assert (pth':=pth).
      eapply path_to_swaps_well_formed in pth'; auto.
      eapply path_to_swaps_sound in pth; auto.
      apply IHl' in res'; auto.
      rewrite (cons_to_app _ l').
      eapply uc_eq_perm_app1. 
      assumption.
      2: apply res'.
      replace (CNOT (log2phys q n) (log2phys q n0)) with (@map_qubits_app _ dim (log2phys q) (CNOT n n0)) by reflexivity.
      rewrite <- (app_nil_l [App2 U_CX _ _]).
      apply uc_eq_perm_app2. 
      assumption.
      constructor; try assumption.
      constructor.
      lia.
      apply pth.
      eapply forall_gates_drop.
      apply fg.
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
    + dependent destruction s0; impossible_gate.
Qed.

Lemma path_to_swaps_respects_undirected : forall n1 n2 p m l m',
  n1 < dim -> n2 < dim ->
  valid_path (log2phys m n1) (log2phys m n2) CG.is_in_graph dim p ->
  layout_well_formed dim m ->
  path_to_swaps p m = (l, m') ->
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
  constructor.
  destruct (path_to_swaps (n :: n0 :: p) (swap_in_map m a n)) eqn:res'.
  inversion res; subst.
  destruct Hpath as [H1 [H2 [H3 [H4 H5]]]].
  inversion H1; subst.
  inversion H3; subst.
  inversion H4; subst.
  rewrite <- app_comm_cons.
  apply res_und_app2; try assumption. 
  eapply IHp; try apply res'.
  assumption.
  replace (log2phys (swap_in_map m (log2phys m n1) n) n1) with n.
  replace (log2phys (swap_in_map m (log2phys m n1) n) n2) with (log2phys m n2).
  repeat split.
  inversion H2; subst. assumption.
  inversion H3; subst. assumption. 
  assumption.
  inversion H5; subst. assumption.  
  unfold swap_in_map. 
  destruct m; simpl.
  bdestruct (n2 =? n4 (n3 n1)).
  subst.
  inversion H5; subst.
  contradict H12.
  destruct (WF (n3 n1)) as [_ [_ [_ ?]]]; auto. 
  bdestruct (n2 =? n4 n).
  subst.
  inversion H5; subst.
  inversion H17; subst.
  contradict H12.
  destruct (WF n) as [_ [_ [_ ?]]]; auto.
  contradict H16.
  destruct (WF n) as [_ [_ [_ ?]]]; auto.
  reflexivity.
  unfold swap_in_map. 
  destruct m; simpl.
  bdestruct (n1 =? n4 (n3 n1)).
  reflexivity.
  contradict H0.
  destruct (WF n1) as [_ [_ [? _]]]; auto.
  apply swap_in_map_well_formed; auto.
Qed.

Definition only_cnots_and_swaps {dim} (g : gate_app Std_Unitary dim) :=
  match g with
  | App2 U_CZ _ _ | App3 U_CCX _ _ _ | App3 U_CCZ _ _ _ => False
  | _ => True
  end.

Lemma path_to_swaps_gates : forall p m (l : standard_ucom_l dim) m',
  path_to_swaps p m = (l, m') ->
  forall_gates only_cnots_and_swaps l.
Proof.
  intros p m l m' res.
  generalize dependent l.
  generalize dependent m.
  induction p; intros m l res; simpl in res.
  - inversion res; subst.
    intros g Hg.
    inversion Hg.
  - destruct p.
    inversion res; subst.
    intros g Hg.
    inversion Hg.
    destruct p.
    inversion res; subst.
    intros g Hg.
    inversion Hg.
    destruct (path_to_swaps (n :: n0 :: p) (swap_in_map m a n)) eqn:pth.
    inversion res; subst.
    apply IHp in pth.
    apply forall_gates_extend.
    simpl; auto.
    apply pth.
Qed.

Lemma insert_swaps_gates : forall (l l' : standard_ucom_l dim) (m m' : qmap dim),
  forall_gates only_cnots l ->
  insert_swaps l m CG.get_path = (l', m') -> 
  forall_gates only_cnots_and_swaps l'.
Proof.
  intros l l' m m' H.
  generalize dependent l'.
  generalize dependent m'.
  generalize dependent m.
  induction l; intros m m' l' res; simpl in res.
  - inversion res; subst.
    intros g Hg.
    inversion Hg.
  - destruct a.
    + destruct (insert_swaps l m CG.get_path) eqn:sw.
      inversion res; subst.
      apply forall_gates_extend.
      simpl; auto.
      eapply IHl; try apply sw.
      eapply forall_gates_drop.
      apply H.
    + dependent destruction s; try impossible_gate.
      destruct (path_to_swaps (CG.get_path (log2phys m n) (log2phys m n0)) m) eqn:pth.
      destruct (insert_swaps l q CG.get_path) eqn:sw.
      inversion res; subst.
      clear res.
      eapply IHl in sw.
      repeat apply forall_gates_append.
      apply path_to_swaps_gates in pth.
      assumption.
      apply forall_gates_extend.
      simpl; auto.
      intros g Hg.
      inversion Hg.
      apply sw.
      eapply forall_gates_drop.
      apply H0.
    + dependent destruction s; impossible_gate.
Qed.

Lemma decompose_swaps_gates : forall (l : standard_ucom_l dim),
  forall_gates only_cnots_and_swaps l ->
  forall_gates only_cnots (decompose_swaps CG.is_in_graph l).
Proof.
  intros l Hl.
  unfold decompose_swaps.
  induction l.
  - rewrite change_gate_set_nil.
    intros g Hg; inversion Hg.
  - rewrite change_gate_set_cons.
    apply forall_gates_append.
    destruct a; simpl.
    + apply forall_gates_extend.
      simpl; auto.
      intros g Hg; inversion Hg.
    + dependent destruction s; try impossible_gate.
      apply forall_gates_extend.
      simpl; auto.
      intros g Hg; inversion Hg.
      destruct (CG.is_in_graph n n0); 
        repeat apply forall_gates_extend; simpl; auto.
      intros g Hg; inversion Hg.
      intros g Hg; inversion Hg.
    + dependent destruction s; impossible_gate.
    + apply IHl.
      eapply forall_gates_drop.
      apply Hl.
Qed.

Lemma fix_cnots_respects_constraints : forall (l : standard_ucom_l dim),
  forall_gates only_cnots l ->
  respects_constraints_undirected CG.is_in_graph l ->
  respects_constraints_directed CG.is_in_graph U_CX (fix_cnots l CG.is_in_graph).
Proof.
  intros l H1 H2.
  induction H2. 
  constructor.
  simpl. constructor.
  apply IHrespects_constraints_undirected.
  eapply forall_gates_drop.
  apply H1.
  simpl.
  dependent destruction u; try impossible_gate.
  apply forall_gates_drop in H1.
  apply IHrespects_constraints_undirected in H1.
  destruct (is_in_graph n1 n2) eqn:H.
  constructor; assumption. 
  destruct (is_in_graph n2 n1) eqn:?.
  repeat constructor; try assumption.
  destruct H0 as [H0 | H0]; try contradict H0; auto.
Qed.

Lemma decompose_swaps_respects_constraints : forall (l : standard_ucom_l dim),
  respects_constraints_undirected CG.is_in_graph l ->
  respects_constraints_undirected CG.is_in_graph (decompose_swaps CG.is_in_graph l).
Proof.
  intros l H.
  unfold decompose_swaps.
  induction H. 
  constructor.
  rewrite change_gate_set_cons.
  apply respects_constraints_undirected_app.
  simpl. repeat constructor.
  apply IHrespects_constraints_undirected.
  rewrite change_gate_set_cons.
  apply respects_constraints_undirected_app.
  simpl. 
  dependent destruction u.
  apply res_und_app2; auto.
  constructor.
  apply res_und_app2; auto.
  constructor.
  destruct (is_in_graph n1 n2) eqn:?; 
    repeat apply res_und_app2; try apply res_und_nil; auto.
  destruct H0 as [H0 | H0]; auto; contradict H0; auto.
  destruct H0 as [H0 | H0]; auto; contradict H0; auto.
  destruct H0 as [H0 | H0]; auto; contradict H0; auto.
  apply IHrespects_constraints_undirected.
Qed.

Lemma simple_map_respects_constraints_directed : forall (l : standard_ucom_l dim) (m : qmap dim) l' m',
  uc_well_typed_l l ->
  layout_well_formed dim m ->
  simple_map l m CG.get_path CG.is_in_graph = (l', m') -> 
  respects_constraints_directed CG.is_in_graph U_CX l'.
Proof. 
  intros l m l' m' WT WF res.
  unfold simple_map in res.
  destruct (insert_swaps (decompose_to_cnot l) m CG.get_path) eqn:sw.
  inversion res; subst.
  clear res.
  apply fix_cnots_respects_constraints.
  apply decompose_swaps_gates.
  eapply insert_swaps_gates; try apply sw.
  apply decompose_to_cnot_gates.
  apply decompose_swaps_respects_constraints.
  apply decompose_to_cnot_WT in WT.
  remember (decompose_to_cnot l) as l'.
  assert (fg : forall_gates only_cnots l').
  subst. 
  apply decompose_to_cnot_gates.
  clear Heql'.
  generalize dependent m'.
  generalize dependent s.
  generalize dependent m.
  induction l'; intros m WF s m' res; simpl in res.
  inversion res; subst.
  constructor.
  destruct a.
  - inversion WT; subst.
    destruct (insert_swaps l' m CG.get_path) eqn:sw.
    inversion res; subst.
    constructor.
    eapply IHl'; try apply sw; auto.
    eapply forall_gates_drop.
    apply fg.
  - inversion WT; subst.
    destruct (path_to_swaps (CG.get_path (log2phys m n) (log2phys m n0)) m) eqn:pth.
    destruct (insert_swaps l' q CG.get_path) eqn:sw.
    dependent destruction s0; try impossible_gate.
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
    apply respects_constraints_undirected_app.
    eapply path_to_swaps_respects_undirected; try apply pth; auto.
    apply CG.get_path_valid; auto.
    eapply IHl'; try apply sw; auto.
    eapply forall_gates_drop.
    apply fg.
    eapply path_to_swaps_well_formed; try apply pth; auto.
    apply CG.get_path_valid; auto.
  - dependent destruction s0; impossible_gate.
Qed.

Lemma simple_map_WT : forall (l : standard_ucom_l dim) (m : qmap dim) l' m',
  uc_well_typed_l l ->
  layout_well_formed dim m ->
  simple_map l m CG.get_path CG.is_in_graph = (l', m') -> 
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

Definition uc_cong_perm (l1 l2 : standard_ucom_l dim) pin pout :=
  eval l1 ∝ perm_to_matrix dim pout × eval l2 × perm_to_matrix dim pin.
Notation "c1 ≅ c2 'with' p1 'and' p2" := (uc_cong_perm c1 c2 p1 p2) (at level 20).

Lemma uc_eq_perm_implies_uc_cong_perm : forall (l1 l2 : standard_ucom_l dim) p1 p2,
  l1 ≡ l2 with p1 and p2 -> l1 ≅ l2 with p1 and p2.
Proof.
  intros l1 l2 p1 p2 H.
  exists 0%R.
  rewrite Cexp_0.
  rewrite Mscale_1_l.
  apply H.
Qed.

Lemma uc_eq_perm_uc_cong_l : forall (l1 l2 l3 : standard_ucom_l dim) p1 p2,
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

Lemma uc_eq_perm_uc_cong_l_alt : forall (l1 l2 l3 : standard_ucom_l dim) p1 p2,
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

(* Some maybe helpful Ltacs for proofs *)
Ltac destruct_matches :=
  
  match goal with
  | H :   match ?Y with _ => _  end = _ |- _ =>
    let h:= fresh in remember Y as h;
                     try destruct h;
                     try dependent destruction h;
                     try discriminate; destruct_pairs; subst
  end.

Ltac assert_next_single_qubit_gate  :=
  
  match reverse goal with
  |[ H :   Some (?l11, ?gat, ?l22) = next_single_qubit_gate ?in_l ?qub 
    |- respects_constraints_directed ?iig _ /\
       respects_constraints_directed ?iig _] =>
    assert (respects_constraints_directed iig l11
            /\ respects_constraints_directed iig l22)
  | H :   Some (?l11, ?gat, ?l22) = next_single_qubit_gate ?in_l ?qub 
     |- respects_constraints_directed ?iig _  =>
   assert (respects_constraints_directed iig l11
           /\ respects_constraints_directed iig l22)
           
end.

Ltac assert_next_two_qubit_gate :=
  match reverse goal with
  |[ H :   Some (?l11, URzQ_CNOT, ?n0, ?n, ?l22) = next_two_qubit_gate ?in_l ?qub 
    |- respects_constraints_directed ?iig _ /\
       respects_constraints_directed ?iig _] =>
    assert (respects_constraints_directed iig l11
            /\ respects_constraints_directed iig l22
            /\ iig n0 n = true)
  |[ H :   Some (?l11, URzQ_CNOT, ?n0, ?n, ?l22) = next_two_qubit_gate ?in_l ?qub 
     |- respects_constraints_directed ?iig _] =>
   assert (respects_constraints_directed iig l11
           /\ respects_constraints_directed iig l22
           /\ iig n0 n = true)
  end. 
Ltac prove_next_gates_assertion  :=
  
  match reverse goal with
  | H :   Some (?l11, ?gat, ?l22) = next_single_qubit_gate ?in_l ?qub 
    |- respects_constraints_directed ?iig ?ll1 /\
       respects_constraints_directed ?iig ?ll2 =>
    
    try (eapply next_single_qubit_gate_respects_constraints
           with (l := in_l) (l1 := l11) (l2 := l22) (g5 := gat) (q0 := qub));
    try (eapply next_single_qubit_gate_respects_constraints
           with (l := in_l) (l1 := l11) (l2 := l22) (g1 := gat) (q0 := qub));
    try assumption
        
  | H :   Some  (?l11, URzQ_CNOT, ?n0, ?n, ?l22) = next_two_qubit_gate ?in_l ?qub 
    |- respects_constraints_directed ?iig ?ll1 /\
       respects_constraints_directed ?iig ?ll2 /\ ?iig ?n0 ?n = true=>
    
    try (eapply next_two_qubit_gate_respects_constraints
           with (l := in_l) (l1 := l11) (l2 := l22) (g5 := URzQ_CNOT) (q0 := qub));
        try (eapply next_two_qubit_gate_respects_constraints
      with (l := in_l) (l1 := l11) (l2 := l22) (g1 := URzQ_CNOT) (q0 := qub));
    try assumption
  end.

Ltac clear_next_gates  :=
  
  match reverse goal with
  | H :   Some (_) = _
    |- _ =>
    clear H

  end.
