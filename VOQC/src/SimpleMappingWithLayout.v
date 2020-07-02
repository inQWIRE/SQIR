Require Import SimpleMapping.
Require Import MappingExamples.

Local Close Scope C_scope.
Local Close Scope R_scope.

(** Simple Mapping Extended with Layouts **)

(* This extends the simple mapping approach with a mapping between
   logical and physical qubits. In SimpleMapping, we moved logical 
   qubits to be adjacent before a CNOT and then moved them back to 
   their original locations before continuing. In practice, this is
   very inefficient. It is better to leave the logical qubits in their 
   new positions, and continue from there. *)

(* We will represent a layout with two functions: one that maps from
   logical qubits to physcial qubits, and one that maps from physical
   qubits to logical qubits. We use two functions instead of one to 
   make lookup in either direction efficient. However, this requires
   some extra machinery to describe well-formed layouts. *)
Definition qmap (dim : nat) : Type := (nat -> nat) * (nat -> nat).

Definition log2phys {dim} (m : qmap dim) q :=
  match m with
  | (m, _) => m q
  end.

Definition phys2log {dim} (m : qmap dim) q :=
  match m with
  | (_, m) => m q
  end.

(* Swap the logical qubits associated with physical qubits phys1 and phys2. *)
Definition swap_in_map {dim} (m : qmap dim) phys1 phys2 : qmap dim :=
  match m with
  | (m1, m2) => 
      let log1 := m2 phys1 in
      let log2 := m2 phys2 in
      let m1' q := if q =? log1 then phys2
                   else if q =? log2 then phys1 
                   else m1 q in
      let m2' q := if q =? phys1 then log2 
                   else if q =? phys2 then log1 
                   else m2 q in
      (m1', m2')
  end.

(* First two conditions necessary? *)
Definition layout_well_formed {dim} (m : qmap dim) := 
  (forall x, x < dim <-> log2phys m x < dim) /\
  (forall x, x < dim <-> phys2log m x < dim) /\
  (forall x y, log2phys m x = y <-> phys2log m y = x).

(* Mapping function definition. *)

Fixpoint path_to_swaps dim p m : (base_ucom dim * qmap dim) :=
  match p with
  | n1 :: n2 :: [] => (SKIP, m)
  | n1 :: ((n2 :: _) as t) => 
      let (c, m') := path_to_swaps dim t (swap_in_map m n1 n2) in
      (SWAP n1 n2 ; c, m')
  | _ => (SKIP, m) (* bad input case - invaid path *)
  end.

(* Note: the input program references *logical* qubits, and the returned program
   references *physical* qubits. get_path and is_in_graph_b also reference physical
   qubits. *) 
Fixpoint simple_map_w_layout {dim} (c : base_ucom dim) (m : qmap dim) (get_path : nat -> nat -> list nat) (is_in_graph_b : nat -> nat -> bool) : (base_ucom dim * qmap dim) :=
  match c with
  | c1; c2 => let (c1', m') := simple_map_w_layout c1 m get_path is_in_graph_b in
             let (c2', m'') := simple_map_w_layout c2 m' get_path is_in_graph_b in
             (c1'; c2', m'')
  | uapp2 U_CNOT n1 n2 => 
      let p := get_path (log2phys m n1) (log2phys m n2) in
      let (c', m') := path_to_swaps dim p m in
      let c'' := fix_cnots (c'; CNOT (log2phys m' n1) (log2phys m' n2)) is_in_graph_b in
      (c'', m')
  | uapp1 u n => (uapp1 u (log2phys m n), m)
  | _ => (c, m)
  end.  

(* Examples *)
Definition trivial_layout : qmap 5 := (fun x => x, fun x => x).
Definition test_layout1 : qmap 5 := 
  let l2p q := if q =? 0 then 4
               else if q =? 1 then 2
                    else if q =? 2 then 3
                         else if q =? 3 then 0
                              else 1 in
  let p2l q := if q =? 0 then 3
               else if q =? 1 then 4
                    else if q =? 2 then 1
                         else if q =? 3 then 2
                              else 0 in
  (l2p, p2l).

Definition map_to_tenerife_w_layout (c : base_ucom 5) (m : qmap 5) :=
  simple_map_w_layout c m Tenerife.tenerife_get_path Tenerife.tenerife_is_in_graph_b.

Compute (map_to_tenerife_w_layout Tenerife.test_tenerife1 trivial_layout).
Compute (map_to_tenerife_w_layout Tenerife.test_tenerife1 test_layout1).
Compute (map_to_tenerife_w_layout Tenerife.test_tenerife2 trivial_layout).
Compute (map_to_tenerife_w_layout Tenerife.test_tenerife2 test_layout1).
Compute (map_to_tenerife_w_layout Tenerife.test_tenerife3 trivial_layout).
Compute (map_to_tenerife_w_layout Tenerife.test_tenerife3 test_layout1).

(* Represent a layout as a list where element x at index i indicates that
   logical qubit x is located at physical qubit i. (Makes printing nicer.)  *)
Fixpoint layout_to_list' {dim} n (m : qmap dim) :=
  match n with 
  | O => []
  | S n' => (layout_to_list' n' m) ++ [phys2log m n'] 
  end.
Definition layout_to_list {dim} (m : qmap dim) := layout_to_list' dim m.

Compute (layout_to_list trivial_layout).
Compute (layout_to_list test_layout1).

(* Proofs *)

Lemma swap_in_map_well_formed : forall {dim} (m : qmap dim) n1 n2,
  n1 < dim -> n2 < dim -> layout_well_formed m -> 
  layout_well_formed (swap_in_map m n1 n2).
Proof.
  unfold layout_well_formed, swap_in_map, log2phys, phys2log.
  intros dim m n1 n2 Hn1 Hn2.
  destruct m as [m1 m2].
  intros [H1 [H2 H3]].
  repeat split; intros H.
  - bdestruct (x =? m2 n1). assumption.
    bdestruct (x =? m2 n2). assumption.
    rewrite <- H1. assumption.
  - bdestruct (x =? m2 n1). subst. rewrite <- H2. assumption.
    bdestruct (x =? m2 n2). subst. rewrite <- H2. assumption.
    rewrite <- H1 in H. assumption.
  - bdestruct (x =? n1). rewrite <- H2. assumption.
    bdestruct (x =? n2). rewrite <- H2. assumption.
    rewrite <- H2. assumption.
  - bdestruct (x =? n1). subst. assumption.
    bdestruct (x =? n2). subst. assumption.
    rewrite <- H2 in H. assumption.
  - bdestruct (x =? m2 n1); subst.
    bdestruct (y =? n1); subst. 
    reflexivity.
    bdestructΩ (y =? y).  
    bdestruct (x =? m2 n2); subst.
    bdestructΩ (n1 =? n1).
    apply not_eq_sym in H0.    
    rewrite <- H3 in H0; try assumption.
    apply not_eq_sym in H.
    rewrite <- H3 in H; try assumption.
    bdestructΩ (m1 x =? n1); bdestructΩ (m1 x =? n2).
    apply H3; auto.
  - bdestruct (y =? n1); subst.
    bdestruct (m2 n2 =? m2 n1); subst.
    symmetry in H; apply H3 in H; try assumption.
    rewrite <- H.
    symmetry; apply H3; auto.
    bdestructΩ (m2 n2 =? m2 n2).
    bdestruct (y =? n2); subst.
    bdestructΩ (m2 n1 =? m2 n1).
    apply not_eq_sym in H0.
    bdestruct (m2 y =? m2 n1); subst.
    symmetry in H1; apply H3 in H4; auto.
    contradict H0.
    rewrite <- H4.
    symmetry.
    apply H3; auto.
    bdestruct (m2 y =? m2 n2); subst.
    symmetry; apply H3 in H5; auto.
    contradict H.
    rewrite <- H5.
    apply H3; auto.
    apply H3; auto.    
Qed.

Lemma swap_in_map_twice : forall {dim} (m : qmap dim) n1 n2,
  layout_well_formed m ->
  swap_in_map (swap_in_map m n1 n2) n1 n2 = m.
Proof.
  intros dim m n1 n2 [_ [_ WF]].
  unfold swap_in_map.
  destruct m.
  simpl in WF.
  bdestructΩ (n1 =? n1).
  bdestructΩ (n2 =? n2).
  apply f_equal2.
  - apply functional_extensionality.
    intros x.
    bdestruct (x =? n0 n2).
    symmetry. apply WF. auto.
    bdestruct (n2 =? n1); subst.
    bdestructΩ (x =? n0 n1).
    bdestruct (x =? n0 n1); auto.
    symmetry. apply WF. auto.
  - apply functional_extensionality.
    intros x.
    bdestruct (x =? n1); subst.
    bdestruct (n2 =? n1); subst; auto.
    bdestruct (x =? n2); subst; auto.
Qed.

Lemma path_to_swaps_well_formed : forall {dim} n1 n2 is_in_graph p m c m',
  valid_graph dim is_in_graph ->
  valid_path n1 n2 is_in_graph p ->
  layout_well_formed m ->
  path_to_swaps dim p m = (c, m') ->
  layout_well_formed m'.
Proof.
  intros.
  generalize dependent c.
  generalize dependent m.
  generalize dependent n1.
  induction p; intros n1 Hpath m WFm c res; simpl in res.
  inversion res; subst. assumption.
  destruct p. inversion res; subst. assumption.
  destruct p. inversion res; subst. assumption.
  destruct (path_to_swaps dim (n :: n0 :: p) (swap_in_map m a n)) eqn:res'.
  inversion res; subst.
  destruct Hpath as [H1 [H2 [H3 H4]]].
  inversion H1; subst.
  eapply IHp; try apply res'.
  repeat split.
  inversion H2; subst. assumption.
  inversion H3; subst. assumption. 
  inversion H4; subst. assumption.
  assert (a < dim).
  { inversion H3; subst.
    destruct H8.
    apply H in H0 as [H0 _].
    assumption. 
    apply H in H0 as [_ [H0 _]]. 
    assumption. }
  assert (n < dim).
  { inversion H3; subst.
    destruct H9.
    apply H in H5 as [_ [H5 _]].
    assumption. 
    apply H in H5 as [H5 _]. 
    assumption. }
  apply swap_in_map_well_formed; assumption.
Qed.

Lemma simple_map_w_layout_well_formed : forall {dim} (c : base_ucom dim) m get_path is_in_graph is_in_graph_b c' m',
  valid_graph dim is_in_graph ->
  get_path_valid dim get_path is_in_graph ->
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  uc_well_typed c ->
  layout_well_formed m ->
  simple_map_w_layout c m get_path is_in_graph_b = (c', m') ->
  layout_well_formed m'.
Proof.
  intros dim c m get_path is_in_graph is_in_graph_b c' m' Hgraph Hpath Href WT WF res.
  generalize dependent m'.
  generalize dependent c'.
  generalize dependent m.
  induction c; intros m WF c' m' res; simpl in res.
  - destruct (simple_map_w_layout c1 m get_path is_in_graph_b) eqn:res1.
    destruct (simple_map_w_layout c2 q get_path is_in_graph_b) eqn:res2.
    inversion res; subst.
    inversion WT; subst.
    eapply IHc2; try apply res2; auto.
    eapply IHc1; try apply res1; auto.
  - inversion res; subst. assumption.
  - dependent destruction u.
    destruct (path_to_swaps dim (get_path (log2phys m n) (log2phys m n0)) m) eqn:res'.
    inversion res; subst.
    eapply path_to_swaps_well_formed; try apply res'; auto.
    apply Hgraph.
    inversion WT; subst.
    destruct WF as [WF1 [WF2 WF3]].
    apply Hpath.
    rewrite <- WF1; auto.
    rewrite <- WF1; auto.
    intros contra.
    contradict H4.
    apply WF3 in contra.
    rewrite <- contra. 
    apply WF3; auto.
  - dependent destruction u.
Qed.

(* Some facts about permutation matrices. *)

(* One thing that's not so great about this definition is that it states the 
   existence of an inverse function, but it doesn't explicitly name this function.
   That's why I end up using the qmap type defined at the top of the file. *)
Definition finite_bijection (n : nat) (f : nat -> nat) :=
  (forall x, x < n <-> f x < n) /\ 
  (exists g, (forall x, g (f x) = x) /\ (forall y, f (g y) = y)).

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
  split. split. reflexivity. 
  exists (fun x : nat => x). split; reflexivity. 
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
  destruct Hp1 as [Hpbnd1 [pinv1 [Hpinvl1 Hpinvr1]]].
  destruct Hp2 as [Hpbnd2 [pinv2 [Hpinvl2 Hpinvr2]]].
  split; [split|].
  intro x.
  rewrite Hpbnd1, Hpbnd2. 
  reflexivity.
  exists (compose pinv1 pinv2).
  unfold compose. 
  split; intro. 
  rewrite Hpinvl2, Hpinvl1. reflexivity.
  rewrite Hpinvr1, Hpinvr2. reflexivity.
  intro f.
  rewrite Mmult_assoc.
  rewrite HP2, HP1.
  reflexivity.
Qed.

Lemma implement_permutation_adjoint : forall n (P : Square (2^n)) (m1 m2 : qmap n),
  layout_well_formed m1 ->
  layout_well_formed m2 ->
  implements_permutation P (log2phys m1 ∘ phys2log m2)%prg -> 
  implements_permutation (P†) (log2phys m2 ∘ phys2log m1)%prg.
Proof.
  intros n P m1 m2 WFm1 WFm2 [WFP [_ HP]].
  split; [split |].
  destruct WFP. auto with wf_db.
  apply transpose_unitary in WFP.
  destruct WFP. auto.
  split. 
  destruct WFm1 as [? [? ?]].
  destruct WFm2 as [? [? ?]].
  unfold compose.
  split. 
  intro x. rewrite <- H2. apply H0.
  exists (fun x : nat => log2phys m1 (phys2log m2 x)).
  split; intro.
  rewrite H1. symmetry. rewrite <- H4. reflexivity.
  rewrite H4. symmetry. rewrite <- H1. reflexivity.
  intro f.
  rewrite <- Mmult_1_l; auto with wf_db.
  destruct WFP.
  rewrite <- H0.
  rewrite Mmult_assoc.
  apply f_equal2; try reflexivity.
  rewrite HP.
  unfold compose.
  replace (fun x : nat => f (log2phys m2 (phys2log m1 (log2phys m1 (phys2log m2 x))))) with f.
  reflexivity.
  apply functional_extensionality; intro.
  apply f_equal.
  symmetry.
  destruct WFm1 as [_ [_ ?]].
  destruct WFm2 as [_ [_ ?]].
  rewrite H2. symmetry. rewrite <- H1. reflexivity.
Qed.

Lemma permute_commutes_with_map_qubits : 
  forall {dim} (P : Square (2 ^ dim)) (m1 m2 : qmap dim) (c : base_ucom dim),
  layout_well_formed m1 ->
  layout_well_formed m2 ->
  implements_permutation P (fun x : nat => log2phys m2 (phys2log m1 x)) ->
  uc_well_typed c ->
  (uc_eval (map_qubits (log2phys m1) c)) × P = 
      P × (uc_eval (map_qubits (log2phys m2) c)).
Proof.
  intros dim P m1 m2 c WFm1 WFm2 [[WF ?] [? HP]] WT.
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
    { subst. destruct WFm1 as [WFm1 _]. rewrite <- WFm1. assumption. }
    assert (y < dim).
    { subst. destruct WFm2 as [WFm2 _]. rewrite <- WFm2. assumption. }
    unfold pad.
    bdestruct_all.
    rewrite (f_to_vec_split 0 dim x) by assumption.
    rewrite (f_to_vec_split 0 dim y) by assumption.
    replace (f' x) with (f y).
    2: { subst. apply f_equal. 
         destruct WFm1 as [_ [_ WFm1]].
         replace (phys2log m1 (log2phys m1 n)) with n.
         reflexivity.
         symmetry. rewrite <- WFm1. reflexivity. }
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
      replace (fun x0 : nat => f0 (log2phys m2 (phys2log m1 x0))) with f0'.
      rewrite (f_to_vec_split 0 dim x) by auto.
      replace (dim - 1 - x) with (dim - (x + 1)) by lia. 
      apply f_equal2; [apply f_equal2 |].
      all: subst. 
      symmetry.
      1,7: apply f_to_vec_update_oob; lia.
      1,5: repeat rewrite update_index_eq; reflexivity.
      symmetry.
      1,3: apply f_to_vec_shift_update_oob; right; lia.
      apply functional_extensionality; intro x.
      bdestruct (x =? log2phys m1 n); subst.
      replace (phys2log m1 (log2phys m1 n)) with n.
      2: { destruct WFm1 as [_ [_ WFm1]].
           symmetry. rewrite <- WFm1. reflexivity. }
      rewrite 2 update_index_eq. reflexivity.
      rewrite 2 update_index_neq; auto.
      intro contra.
      destruct WFm2 as [_ [_ WFm2]]. 
      rewrite WFm2 in contra.
      replace (phys2log m2 (log2phys m2 (phys2log m1 x))) with (phys2log m1 x) in contra.
      destruct WFm1 as [_ [_ WFm1]].
      rewrite <- WFm1 in contra; auto.
      symmetry. rewrite <- WFm2. reflexivity.
    + remember (update f y true) as f1.
      replace (f_to_vec y f) with (f_to_vec y f1).
      replace ∣ 1 ⟩ with  ∣ Nat.b2n (f1 y) ⟩.
      replace (f_to_vec (dim - (y + 1)) (shift f (y + 1))) 
        with (f_to_vec (dim - (y + 1)) (shift f1 (y + 1))).
      replace (dim - (y + 1)) with (dim - 1 - y) by lia.
      rewrite <- f_to_vec_split by auto.
      rewrite HP.
      remember (update (fun x0 : nat => f (log2phys m2 (phys2log m1 x0))) x true) as f1'.
      replace (fun x0 : nat => f1 (log2phys m2 (phys2log m1 x0))) with f1'.
      rewrite (f_to_vec_split 0 dim x) by auto.
      replace (dim - 1 - x) with (dim - (x + 1)) by lia. 
      apply f_equal2; [apply f_equal2 |].
      all: subst. 
      symmetry.
      1,7: apply f_to_vec_update_oob; lia.
      1,5: repeat rewrite update_index_eq; reflexivity.
      symmetry.
      1,3: apply f_to_vec_shift_update_oob; right; lia.
      apply functional_extensionality; intro x.
      bdestruct (x =? log2phys m1 n); subst.
      replace (phys2log m1 (log2phys m1 n)) with n.
      2: { destruct WFm1 as [_ [_ WFm1]].
           symmetry. rewrite <- WFm1. reflexivity. }
      rewrite 2 update_index_eq. reflexivity.
      rewrite 2 update_index_neq; auto.
      intro contra.
      destruct WFm2 as [_ [_ WFm2]]. 
      rewrite WFm2 in contra.
      replace (phys2log m2 (log2phys m2 (phys2log m1 x))) with (phys2log m1 x) in contra.
      destruct WFm1 as [_ [_ WFm1]].
      rewrite <- WFm1 in contra; auto.
      symmetry. rewrite <- WFm2. reflexivity.
  - rewrite HP.
    remember (log2phys m2 n) as x.
    remember (log2phys m2 n0) as y.
    assert (x < dim).
    { subst. destruct WFm2 as [WFm2 _]. rewrite <- WFm2. assumption. }
    assert (y < dim).
    { subst. destruct WFm2 as [WFm2 _]. rewrite <- WFm2. assumption. }
    assert (x <> y).
    { subst. intro contra.
      destruct WFm2 as [_ [_ WFm2]].
      rewrite WFm2 in contra.
      replace (phys2log m2 (log2phys m2 n0)) with n0 in contra; auto.
      symmetry. rewrite <- WFm2. reflexivity. }
    replace (ueval_cnot dim x y) with (uc_eval (@CNOT dim x y)) by reflexivity.
    rewrite f_to_vec_CNOT by assumption.
    rewrite HP.
    remember (log2phys m1 n) as z.
    remember (log2phys m1 n0) as w.
    assert (z < dim).
    { subst. destruct WFm1 as [WFm1 _]. rewrite <- WFm1. assumption. }
    assert (w < dim).
    { subst. destruct WFm1 as [WFm1 _]. rewrite <- WFm1. assumption. }
    assert (z <> w).
    { subst. intro contra.
      destruct WFm1 as [_ [_ WFm1]].
      rewrite WFm1 in contra.
      replace (phys2log m1 (log2phys m1 n0)) with n0 in contra; auto.
      symmetry. rewrite <- WFm1. reflexivity. }
    replace (ueval_cnot dim z w) with (uc_eval (@CNOT dim z w)) by reflexivity.
    rewrite f_to_vec_CNOT by assumption.
    apply f_equal2; try reflexivity.
    subst.
    apply functional_extensionality; intro x.
    bdestruct (x =? log2phys m1 n0); subst.
    replace (phys2log m1 (log2phys m1 n0)) with n0.
    2: { destruct WFm1 as [_ [_ WFm1]].
         symmetry. rewrite <- WFm1. reflexivity. }
    rewrite 2 update_index_eq. 
    replace (phys2log m1 (log2phys m1 n)) with n.
    2: { destruct WFm1 as [_ [_ WFm1]].
         symmetry. rewrite <- WFm1. reflexivity. }
    reflexivity.
    rewrite 2 update_index_neq; auto.
    intro contra.
    destruct WFm2 as [_ [_ WFm2]]. 
    rewrite WFm2 in contra.
    replace (phys2log m2 (log2phys m2 (phys2log m1 x))) with (phys2log m1 x) in contra.
    destruct WFm1 as [_ [_ WFm1]].
    rewrite <- WFm1 in contra; auto.
    symmetry. rewrite <- WFm2. reflexivity.
Qed.

(** Equivalence up to qubit reordering **)

Definition uc_eq_perm {dim : nat} (c1 c2 : base_ucom dim) p :=
  exists P, implements_permutation P p /\ uc_eval c1 = P × uc_eval c2.
Notation "c1 ≡ c2 'with' p" := (uc_eq_perm c1 c2 p) (at level 20).

Lemma uc_eq_perm_refl : forall {dim : nat} (c1 : base_ucom dim), 
  c1 ≡ c1 with (fun x : nat => x).
Proof. 
  intros. 
  exists (I (2 ^ dim)).
  split. 
  apply implements_permutation_I.
  Msimpl. reflexivity.
Qed.

(* We can also prove the following, but it's tricky to state since we don't 
   have a name for p's inverse.

Lemma uc_eq_perm_sym : forall {dim : nat} (c1 c2 : base_ucom dim) P, 
  c1 ≡ c2 with p -> c2 ≡ c1 with p^{-1}. 
*)

Lemma uc_eq_perm_trans : forall {dim : nat} (c1 c2 c3 : base_ucom dim) p12 p23, 
  c1 ≡ c2 with p12 -> c2 ≡ c3 with p23 -> c1 ≡ c3 with (compose p23 p12).
Proof.
  intros dim c1 c2 c3 p12 p23 H12 H23. 
  destruct H12 as [P12 [HP12 H12]].
  destruct H23 as [P23 [HP23 H23]].
  exists (P12 × P23). 
  split. 
  apply implements_permutation_Mmult; assumption.
  rewrite Mmult_assoc.
  rewrite <- H23, <- H12. reflexivity.
Qed.

Lemma path_to_swaps_sound : forall {dim} n1 n2 is_in_graph p m c m',
  valid_graph dim is_in_graph ->
  valid_path n1 n2 is_in_graph p ->
  layout_well_formed m ->
  path_to_swaps dim p m = (c, m') ->
  c ≡ SKIP with (compose (log2phys m) (phys2log m')).
Proof.
  intros dim n1 n2 is_in_graph p m c m' Hgraph.
  generalize dependent c.
  generalize dependent m.
  generalize dependent n1.
  induction p; intros n1 m c Hpath WFm res; simpl in res.
  (* invalid path cases *)
  destruct Hpath as [H _].
  inversion H.
  destruct p.
  destruct Hpath as [_ [_ [H _]]].
  inversion H.
  destruct p.
  - (* base case *)
    inversion res; subst. 
    replace (log2phys m' ∘ phys2log m')%prg with (fun x : nat => x).
    apply uc_eq_perm_refl.
    unfold compose.
    apply functional_extensionality; intro x.
    destruct WFm as [_ [_ WFm]].
    symmetry. rewrite WFm. 
    reflexivity.
  - (* inductive case *)
    destruct (path_to_swaps dim (n :: n0 :: p) (swap_in_map m a n)) eqn:res'.
    inversion res; subst.  
    destruct Hpath as [H1 [H2 [H3 H4]]].
    inversion H1; subst.
    assert (a < dim).
    { inversion H3; subst.
      destruct H7.
      apply Hgraph in H as [H _].
      assumption. 
      apply Hgraph in H as [_ [H _]]. 
      assumption. }
    assert (n < dim).
    { inversion H3; subst.
      destruct H8.
      apply Hgraph in H0 as [_ [H0 _]].
      assumption. 
      apply Hgraph in H0 as [H0 _]. 
      assumption. }
    assert (a <> n).
    { inversion H3; subst.
      destruct H9.
      apply Hgraph in H5 as [_ [_ H5]].
      assumption. 
      apply Hgraph in H5 as [_ [_ H5]]. 
      lia. }
    assert (WFm':=res').
    eapply path_to_swaps_well_formed in WFm'.
    2: apply Hgraph.
    eapply IHp in res'.
    destruct res' as [P [HP res']].
    exists (P × (uc_eval (SWAP a n))).
    destruct HP as [? [? HP]].
    split; [split |].
    apply Mmult_unitary; auto.
    apply uc_eval_unitary.
    apply uc_well_typed_SWAP; auto.
    split.
    destruct WFm as [WFm1 [WFm2 WFm3]].
    destruct WFm' as [WFm'1 [WFm'2 WFm'3]].
    split. unfold compose.
    intro x. rewrite <- WFm1. apply WFm'2.
    exists (log2phys m' ∘ phys2log m)%prg.
    split; unfold compose; intro x.
    rewrite WFm'3.
    symmetry.
    rewrite <- WFm3. 
    reflexivity.
    rewrite WFm3.
    symmetry.
    rewrite <- WFm'3. 
    reflexivity.
    intro f.
    rewrite Mmult_assoc.
    rewrite f_to_vec_SWAP by assumption.
    rewrite HP.
    apply f_equal2; try reflexivity.
    apply functional_extensionality; intro x.
    unfold compose.
    unfold swap_in_map.
    destruct m; simpl.
    destruct WFm as [_ [_ WFm]].
    simpl in WFm.
    bdestruct (phys2log m' x =? n3 a).
    rewrite update_index_neq by assumption.
    rewrite update_index_eq.
    apply f_equal.
    rewrite H8.
    symmetry. rewrite WFm. reflexivity.
    bdestruct (phys2log m' x =? n3 n).
    rewrite update_index_eq.
    apply f_equal.
    rewrite H9.
    symmetry. rewrite WFm. reflexivity.
    rewrite 2 update_index_neq.
    reflexivity.
    intro contra.
    symmetry in contra.
    rewrite WFm in contra.
    contradict H9.
    symmetry. apply contra.
    intro contra.
    symmetry in contra.
    rewrite WFm in contra.
    contradict H8.
    symmetry. apply contra.
    simpl.
    rewrite res'.
    rewrite denote_SKIP by lia.
    destruct H6.
    Msimpl. reflexivity.
    eapply valid_path_subpath.
    repeat split; try apply H2; try assumption.
    apply swap_in_map_well_formed; assumption.
    eapply valid_path_subpath.
    repeat split; try apply H1; try apply H2; try assumption.
    apply swap_in_map_well_formed; assumption.
Qed.

(* Say that mapping program c (with initial layout m) onto the given 
   architecture produces program c' and final layout m'. Then the behavior
   of c using layout m is the same as the behavior of c' followed by 
   a conversion between m and m'. *)
Lemma simple_map_w_layout_sound : forall dim (c : base_ucom dim) (m : qmap dim) get_path is_in_graph is_in_graph_b c' m',
  valid_graph dim is_in_graph ->
  get_path_valid dim get_path is_in_graph ->
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  uc_well_typed c ->
  layout_well_formed m ->
  simple_map_w_layout c m get_path is_in_graph_b = (c', m') -> 
  map_qubits (log2phys m) c ≡ c' with ((log2phys m') ∘ (phys2log m))%prg.
Proof. 
  intros dim c m get_path is_in_graph is_in_graph_b c' m' Hgraph Hpath Href WT.
  generalize dependent m'.
  generalize dependent c'.
  generalize dependent m.
  induction c; intros m c' m' WFm res; try dependent destruction u.
  - simpl in res.
    destruct (simple_map_w_layout c1 m get_path is_in_graph_b) eqn:res1.
    destruct (simple_map_w_layout c2 q get_path is_in_graph_b) eqn:res2.
    inversion res; subst.
    inversion WT; subst.
    assert (WFq:=res1).
    eapply simple_map_w_layout_well_formed in WFq; try apply Href; auto.
    apply IHc1 in res1; try assumption.
    apply IHc2 in res2; try assumption. 
    destruct res1 as [P1 [HP1 res1]].
    destruct res2 as [P2 [HP2 res2]].
    exists (P1 × P2).
    split.
    replace (log2phys m' ∘ phys2log m)%prg with 
        ((log2phys m' ∘ phys2log q) ∘ (log2phys q ∘ phys2log m))%prg.
    apply implements_permutation_Mmult; try assumption.
    unfold compose.
    apply functional_extensionality; intro x.
    apply f_equal.
    destruct WFq as [_ [_ WFq]].
    rewrite <- WFq.
    reflexivity.
    simpl.
    rewrite res1. 
    rewrite <- Mmult_assoc.
    erewrite permute_commutes_with_map_qubits; try apply HP1; auto.
    rewrite res2. 
    repeat rewrite Mmult_assoc.
    reflexivity.
  - simpl in res.
    inversion res; subst.
    replace (log2phys m' ∘ phys2log m')%prg with (fun x : nat => x).
    apply uc_eq_perm_refl.
    unfold compose.
    apply functional_extensionality; intro x.
    destruct WFm as [_ [_ WFm]].
    symmetry. rewrite WFm. 
    reflexivity.
  - simpl in res.
    destruct (path_to_swaps dim (get_path (log2phys m n) (log2phys m n0)) m) eqn:pts.
    inversion res; subst.
    inversion WT; subst.
    assert (WFm':=pts).
    eapply path_to_swaps_well_formed in WFm'; try apply Hgraph; auto.
    eapply path_to_swaps_sound in pts; try apply Hgraph; auto.
    destruct pts as [P [HP pts]].
    exists P†.
    split. 
    apply implement_permutation_adjoint; auto.
    simpl. 
    rewrite 2 fix_cnots_sound.
    rewrite denote_SKIP in pts. 
    rewrite Mmult_1_r in pts.
    rewrite pts.
    replace (@CNOT dim (log2phys m' n) (log2phys m' n0)) with 
        (@map_qubits _ dim (log2phys m') (CNOT n n0)) by reflexivity.
    rewrite permute_commutes_with_map_qubits with (m2:=m); auto.
    rewrite <- Mmult_assoc.
    destruct HP as [[? ?] _].
    rewrite H0. Msimpl.
    reflexivity.
    destruct HP as [[? _] _]; assumption. 
    eapply uc_well_typed_implies_dim_nonzero; apply WT.
    destruct WFm as [? [_ ?]]. 
    apply Hpath.
    rewrite <- i; assumption.
    rewrite <- i; assumption.
    intro contra.
    rewrite i0 in contra.
    contradict H4.
    rewrite <- contra, <- i0.
    reflexivity.
    destruct WFm as [? [_ ?]]. 
    apply Hpath.
    rewrite <- i; assumption.
    rewrite <- i; assumption.
    intro contra.
    rewrite i0 in contra.
    contradict H4.
    rewrite <- contra, <- i0.
    reflexivity.
Qed.

Lemma path_to_swaps_respects_undirected : forall {dim} n1 n2 is_in_graph p m c m',
  valid_graph dim is_in_graph ->
  valid_path (log2phys m n1) (log2phys m n2) is_in_graph p ->
  layout_well_formed m ->
  path_to_swaps dim p m = (c, m') ->
  respects_constraints_undirected is_in_graph (c ; CNOT (log2phys m' n1) (log2phys m' n2)).
Proof.
  intros dim n1 n2 is_in_graph p m c m' Hgraph Hpath WF res.
  generalize dependent c.
  generalize dependent m.
  generalize dependent n1.
  induction p; intros n1 m Hpath WF c res; simpl in res.
  destruct Hpath as [H _].
  inversion H.
  destruct p.
  destruct Hpath as [_ [_ [H _]]].
  inversion H.
  destruct p.
  inversion res; subst. 
  Transparent SKIP ID.
  constructor; constructor.
  destruct Hpath as [H1 [H2 [H3 H4]]].
  inversion H1; subst.
  inversion H2; subst.
  inversion H5; subst.
  inversion H3; subst.
  assumption.
  inversion H9. inversion H6.
  destruct (path_to_swaps dim (n :: n0 :: p) (swap_in_map m a n)) eqn:res'.
  inversion res; subst.
  destruct Hpath as [H1 [H2 [H3 H4]]].
  inversion H1; subst.
  inversion H3; subst.
  assert (log2phys m n1 < dim).
  { destruct H7.
    apply Hgraph in H as [H _].
    assumption. 
    apply Hgraph in H as [_ [H _]]. 
    assumption. }
  assert (n < dim).
  { destruct H7.
    apply Hgraph in H0 as [_ [H0 _]].
    assumption. 
    apply Hgraph in H0 as [H0 _]. 
    assumption. }
  assert (aux: forall (a b c : base_ucom dim), 
    respects_constraints_undirected is_in_graph ((a;b);c) <-> respects_constraints_undirected is_in_graph (a;(b;c))).
  { clear. intros a b c. split; intros H. 
    inversion H; subst. inversion H3; subst.
    repeat constructor; auto.
    inversion H; subst. inversion H4; subst.
    repeat constructor; auto. }
  apply aux.
  constructor.
  Transparent SWAP.
  repeat apply res_und_seq; constructor; auto.
  apply or_comm; assumption.
  eapply IHp; try apply res'.
  replace (log2phys (swap_in_map m (log2phys m n1) n) n1) with n.
  2: { unfold swap_in_map. 
       destruct m; simpl.
       destruct WF as [_ [_ WF]].
       bdestruct (n1 =? n4 (n3 n1)).
       reflexivity.
       contradict H5.
       symmetry. apply WF. reflexivity. }
  replace (log2phys (swap_in_map m (log2phys m n1) n) n2) with (log2phys m n2).
  2: { unfold swap_in_map. 
       destruct m; simpl.
       destruct WF as [_ [_ WF]]. 
       inversion H4; subst.
       bdestruct (n2 =? n4 (n3 n1)).
       symmetry in H5.
       apply WF in H5.
       contradict H10. symmetry. assumption.
       bdestruct (n2 =? n4 n).
       inversion H12; subst.
       contradict H13. symmetry. apply WF. reflexivity.
       contradict H14. symmetry. apply WF. reflexivity.
       reflexivity. }
  repeat split.
  inversion H2; subst. assumption.
  inversion H3; subst. assumption. 
  inversion H4; subst. assumption.  
  apply swap_in_map_well_formed; assumption.
Qed.
  
Lemma simple_map_w_layout_respects_constraints : forall dim (c : base_ucom dim) (m : qmap dim) get_path is_in_graph is_in_graph_b c' m',
  valid_graph dim is_in_graph ->
  get_path_valid dim get_path is_in_graph ->
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  uc_well_typed c ->
  layout_well_formed m ->
  simple_map_w_layout c m get_path is_in_graph_b = (c', m') -> 
  respects_constraints is_in_graph c'.
Proof. 
  intros dim c m get_path is_in_graph is_in_graph_b c' m' Hgraph Hpath Href WT WF res.
  generalize dependent m'.
  generalize dependent c'.
  generalize dependent m.
  induction c; intros m WF c' m' res.
  - inversion WT; subst.
    simpl in res. 
    destruct (simple_map_w_layout c1 m get_path is_in_graph_b) eqn:res1.
    destruct (simple_map_w_layout c2 q get_path is_in_graph_b) eqn:res2.
    inversion res; subst.
    constructor.
    eapply IHc1; try apply res1; auto.
    eapply IHc2; try apply res2; auto.
    eapply simple_map_w_layout_well_formed; try apply res1; auto; assumption.
  - inversion res; subst. constructor.
  - dependent destruction u.
    Opaque fix_cnots. 
    simpl in res.
    destruct (path_to_swaps dim (get_path (log2phys m n) (log2phys m n0)) m) eqn:path.
    inversion res; subst.
    apply fix_cnots_respects_constraints; try assumption. 
    eapply path_to_swaps_respects_undirected; try apply path; auto.
    inversion WT; subst.
    destruct WF as [WF1 [WF2 WF3]].
    apply Hpath.
    rewrite <- WF1; auto.
    rewrite <- WF1; auto.
    intros contra.
    contradict H4.
    apply WF3 in contra.
    rewrite <- contra. 
    apply WF3; auto.
  - dependent destruction u.
Qed.



