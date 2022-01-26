Require Export ConnectivityGraph.
Require Export Layouts2.
Require Export MappingConstraints.
Require Import MappingGateSet.
Require Import UnitaryListRepresentation.

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

Module SimpleMap (CG : ConnectivityGraph).

Definition ucom_l (U : Set) dim := gate_list (Map_Unitary U) dim.

(** Mapping function definition. *)
Definition SWAP {U dim} a b : gate_app (Map_Unitary U) dim := App2 U_SWAP a b.
Definition CNOT {U dim} a b : gate_app (Map_Unitary U) dim := App2 U_CX a b.

Fixpoint path_to_swaps {U dim} p m : (ucom_l U dim * layout) :=
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
Fixpoint simple_map {U dim} (l : ucom_l U dim) (m : layout) : (ucom_l U dim * layout) :=
  match l with
  | [] => ([],m)
  | App2 U_CX n1 n2 :: t =>
      let p := CG.get_path (get_phys m n1) (get_phys m n2) in
      let (swaps, m') := path_to_swaps p m in
      let mapped_cnot := 
        swaps ++ [CNOT (get_phys m' n1) (get_phys m' n2)] in 
      let (t',m'') := simple_map t m' in
      (mapped_cnot ++ t', m'')
  | App1 u n :: t =>
      let (t',m') := simple_map t m in
      (App1 u (get_phys m n) :: t', m')
  | _ => ([], m) (* unreachable due to the gate set *)
  end.

End SimpleMap.












Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

(*********** ignore from here ************)

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
#[export] Hint Resolve perm_mat_WF : wf_db.

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
  rewrite Hinv in H1 by assumption.
  contradiction.
  rewrite Hinv in H1 by assumption.
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
#[export] Hint Resolve perm_to_matrix_WF : wf_db.

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

(*********** to here ************)

















(** * Proofs *)


Definition perm_pair dim p1 p2 :=
  finite_bijection dim p1 /\
  finite_bijection dim p2 /\
  (forall x, x < dim -> p1 (p2 x) = x) /\
  (forall x, x < dim -> p2 (p1 x) = x).


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
    { destruct H0 as [? H0].
      specialize (H0 n H4).
      destruct H0. auto. }
    unfold pad.
    bdestruct_all.
    rewrite (f_to_vec_split 0 dim n) by assumption.
    rewrite (f_to_vec_split 0 dim (p2 n)) by assumption.
    restore_dims.
    replace (dim - 1 - n) with (dim - (n + 1)) by lia.
    replace (dim - 1 - p2 n) with (dim - (p2 n + 1)) by lia. 
    Msimpl.
    rewrite H1; auto. 
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
      rewrite H1 by auto.
      bdestruct_all; trivial.
      bdestruct_all; trivial.
      rewrite <- H8 in H7.
      rewrite H2 in H7 by auto.
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
      rewrite H1 by auto.
      bdestruct_all; trivial.
      bdestruct_all; trivial.
      rewrite <- H8 in H7.
      rewrite H2 in H7 by auto.
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
    { destruct H0 as [? H0].
      specialize (H0 n H6).
      destruct H0. auto. }
    assert (p2 n0 < dim).
    { destruct H0 as [? H0].
      specialize (H0 n0 H7).
      destruct H0. auto. }
    rewrite f_to_vec_CNOT; auto.
    apply f_to_vec_eq.
    intros x Hx.
    unfold update.
    rewrite 2 H1 by auto.
    bdestruct_all; try reflexivity.
    rewrite <- H5 in H9.
    rewrite H2 in H9 by auto.
    contradiction.
    rewrite H9 in H5.
    rewrite H1 in H5 by auto.
    contradiction.
    intro contra.
    assert (p1 (p2 n) = p1 (p2 n0)) by auto.
    rewrite 2 H1 in H5 by auto.
    contradiction.
Qed.


Local Close Scope C_scope.
Local Close Scope R_scope.
Local Close Scope Q_scope.

Module SimpleMappingProofs (G : GateSet) (CG : ConnectivityGraph).

Module SM := SimpleMap CG.
Import SM.

Definition dim := CG.dim.
Definition ucom_l dim := ucom_l (G.U 1) dim.

Module MapG := MappingGateSet G.
Module MapList := UListProofs MapG.
Import MapList.

(** Equivalence up to qubit reordering **)
Definition uc_eq_perm (l1 l2 : ucom_l dim) pin pout :=
  eval l1 = perm_to_matrix dim pout × eval l2 × perm_to_matrix dim pin.
Notation "c1 ≡ c2 'with' p1 'and' p2" := (uc_eq_perm c1 c2 p1 p2) (at level 20).

Lemma uc_eq_perm_nil : forall p1 p2,
  dim > 0 ->
  perm_pair dim p1 p2 ->
  [] ≡ [] with p1 and p2.
Proof.
  intros p1 p2 Hdim [? [? [? ?]]].
  unfold uc_eq_perm.
  unfold eval; simpl.
  rewrite denote_SKIP by assumption.
  Msimpl.
  rewrite perm_to_matrix_Mmult, perm_to_matrix_I; auto.
  apply finite_bijection_compose; auto.
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

Lemma path_to_swaps_bijection : forall n1 n2 p m (l : ucom_l dim) m',
  valid_path n1 n2 CG.is_in_graph dim p ->
  layout_bijection dim m ->
  path_to_swaps p m = (l, m') ->
  layout_bijection dim m'.
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
  apply swap_log_bijection; assumption.
Qed.
Print fswap.
Lemma fswap_swap_log : forall m f a b x,
  fswap f a b (get_phys (swap_log m a b) x) = f (get_phys m x).
Proof.
  intros. unfold fswap.
Admitted.

Lemma path_to_swaps_sound : forall n1 n2 p m l m',
  dim > 0 ->
  valid_path n1 n2 CG.is_in_graph dim p ->
  layout_bijection dim m ->
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
    apply uc_eq_perm_nil; auto.
    repeat split.
    apply get_phys_bij; auto.
    apply get_log_bij; auto.
    intros. apply get_phys_log_inv with (n:=dim); auto.
    intros. apply get_log_phys_inv with (n:=dim); auto.
  - (* inductive case *)
    destruct (path_to_swaps (n :: n0 :: p) (swap_log m a n)) eqn:res'.
    inversion res; subst.  
    destruct Hpath as [H1 [H2 [H3 [H4 H5]]]].
    inversion H1; subst.
    inversion H4; subst.
    assert (WFm':=res').
    eapply path_to_swaps_bijection in WFm'.
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
(*
    rewrite <- (fswap_swap_log m f a n x).
*)

admit.


    apply get_phys_bij; assumption.
    apply get_phys_bij.
    apply swap_log_bijection; assumption.
    eapply valid_path_subpath.
    repeat split; try apply H2; try assumption.
    apply swap_log_bijection; assumption.
    eapply valid_path_subpath.
    repeat split; try apply H1; try apply H2; try assumption.
    apply swap_log_bijection; assumption.
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
   uc_eval P1 = p_in × uc_eval P2 × p_out where permutation p_in=(get_log m)
   is the inverse of the input logical->physical qubit map and permutation
   p_out=(get_phys m') is the output logical->physical qubit map.
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
