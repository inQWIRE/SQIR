Require Import SimpleMapping.
Require Import MappingExamples.
Require Import Utilities.

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
  | n1 :: n2 :: [] => (SKIP, m) (* normal termination *)
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

(* For soundness we will want to prove that the resulting program is equivalent
   to the input program if you 'undo' all the SWAPs. To state this, we need a 
   way to produce a series of SWAPs that converts between layouts. *)

(* The goal is to get from layout m1 to layout m2.
   
   If the m1 has logical qubit A at physical qubit 0 and m2 has A at 3, 
   then convert_between_layouts should produce a program that swaps the
   values at locations 0 and 3. Note that we don't worry about satisfying
   connectivity constraints because the generated program is used in our
   proof - it is not meant to be run on a machine. *)
Fixpoint convert_between_layouts' {dim} n (m1 m2 : qmap dim) : base_ucom dim :=
  match n with 
  | O => SKIP
  | S n' => 
      let x := log2phys m1 (phys2log m2 n') in
      if n' =? x 
      then convert_between_layouts' n' m1 m2
      else SWAP n' x ; convert_between_layouts' n' (swap_in_map m1 n' x) m2
  end.

Definition convert_between_layouts {dim} (m1 m2 : qmap dim) : base_ucom dim :=
  convert_between_layouts' dim m1 m2.

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
Compute (convert_between_layouts trivial_layout test_layout1).
Compute (convert_between_layouts test_layout1 trivial_layout).
Compute (convert_between_layouts test_layout1 test_layout1).

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

Lemma convert_between_layouts'_same : forall {dim} n (m : qmap dim),
  layout_well_formed m -> convert_between_layouts' n m m ≡ SKIP.
Proof.
  intros dim n m [_ [_ WF]].
  induction n.
  reflexivity.
  simpl. 
  bdestruct (n =? log2phys m (phys2log m n)).
  apply IHn.
  contradict H. 
  symmetry. apply WF. reflexivity.
Qed.

Lemma convert_between_layouts_same : forall {dim} (m : qmap dim),
  layout_well_formed m -> convert_between_layouts m m ≡ SKIP.
Proof. intros. apply convert_between_layouts'_same. assumption. Qed.

Lemma convert_between_layouts'_SWAP : forall {dim} n (m1 m2 : qmap dim) n1 n2,
  layout_well_formed m1 ->
  layout_well_formed m2 ->
  n1 < dim -> n2 < dim -> n1 <> n2 -> (* SWAP n1 n2 is well typed *)
  (* some restriction involving n... *)
  SWAP n1 n2 ; convert_between_layouts' n (swap_in_map m1 n1 n2) m2 ≡ convert_between_layouts' n m1 m2.
Proof. Admitted.

Lemma convert_between_layouts_SWAP : forall {dim} (m1 m2 : qmap dim) n1 n2,
  layout_well_formed m1 ->
  layout_well_formed m2 ->
  n1 < dim -> n2 < dim -> n1 <> n2 ->
  SWAP n1 n2 ; convert_between_layouts (swap_in_map m1 n1 n2) m2 ≡ convert_between_layouts m1 m2.
Proof. intros. apply convert_between_layouts'_SWAP; assumption. Qed.

Lemma convert_between_layouts_map_commutes : forall {dim} (m1 m2 : qmap dim) (c : base_ucom dim),
  layout_well_formed m1 ->
  layout_well_formed m2 ->
  uc_well_typed c ->
  convert_between_layouts m1 m2 ; map_qubits (log2phys m2) c ≡ map_qubits (log2phys m1) c ; convert_between_layouts m1 m2.
Proof.
Admitted.

Lemma convert_between_layouts_transitive : forall {dim} (m1 m2 m3 : qmap dim),
  convert_between_layouts m1 m2 ; convert_between_layouts m2 m3 ≡ convert_between_layouts m1 m3.
Proof.
Admitted.

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

Lemma path_to_swaps_sound : forall {dim} n1 n2 is_in_graph p m c m',
  valid_graph dim is_in_graph ->
  valid_path n1 n2 is_in_graph p ->
  layout_well_formed m ->
  path_to_swaps dim p m = (c, m') ->
  c ≡ convert_between_layouts m m'.
Proof.
  intros dim n1 n2 is_in_graph p m c m' Hgraph Hpath WF res.
  generalize dependent c.
  generalize dependent m.
  generalize dependent n1.
  induction p; intros n1 Hpath m WF c res; simpl in res.
  destruct Hpath as [H _].
  inversion H.
  destruct p.
  destruct Hpath as [_ [_ [H _]]].
  inversion H.
  destruct p.
  inversion res; subst. symmetry. 
  apply convert_between_layouts_same; assumption.
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
  rewrite IHp with (c:=b); try apply res'.
  apply convert_between_layouts_SWAP; auto.
  eapply path_to_swaps_well_formed; try apply res'.
  apply Hgraph.
  repeat split.
  inversion H2; subst. apply H8.
  inversion H3; subst. assumption. 
  inversion H4; subst. assumption.  
  apply swap_in_map_well_formed; assumption.
  repeat split.
  inversion H2; subst. apply H8.
  inversion H3; subst. assumption. 
  inversion H4; subst. assumption.  
  apply swap_in_map_well_formed; assumption.
Qed.

Lemma simple_map_w_layout_sound : forall dim (c : base_ucom dim) (m : qmap dim) get_path is_in_graph is_in_graph_b c' m',
  valid_graph dim is_in_graph ->
  get_path_valid dim get_path is_in_graph ->
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  uc_well_typed c ->
  layout_well_formed m ->
  simple_map_w_layout c m get_path is_in_graph_b = (c', m') -> 
  (c' ; convert_between_layouts m' m) ≡ (map_qubits (log2phys m) c).
Proof. 
  intros dim c m get_path is_in_graph is_in_graph_b c' m' Hgraph Hpath Href WT WF res.
  generalize dependent m'.
  generalize dependent c'.
  generalize dependent m.
  induction c; intros m WF c' m' res.
  - simpl in res. 
    destruct (simple_map_w_layout c1 m get_path is_in_graph_b) eqn:res1.
    destruct (simple_map_w_layout c2 q get_path is_in_graph_b) eqn:res2.
    inversion res; subst.
    simpl.
    inversion WT; subst.
    erewrite <- IHc1; try apply res1; auto.
    repeat rewrite useq_assoc.
    rewrite convert_between_layouts_map_commutes; try assumption.
    erewrite <- IHc2; try apply res2; auto.
    repeat rewrite useq_assoc.
    rewrite convert_between_layouts_transitive.
    reflexivity.
    eapply simple_map_w_layout_well_formed; try apply res1; auto; assumption.
    eapply simple_map_w_layout_well_formed; try apply res1; auto; assumption.
  - inversion res; subst.
    dependent destruction u. 
    simpl.
    apply uc_well_typed_implies_dim_nonzero in WT.
    unfold convert_between_layouts.
    rewrite convert_between_layouts'_same; try assumption.
    unfold uc_equiv; simpl.
    rewrite denote_SKIP; try assumption.
    Msimpl_light; reflexivity.
  - dependent destruction u. 
    simpl in res.
    destruct (path_to_swaps dim (get_path (log2phys m n) (log2phys m n0)) m) eqn:path.
    inversion res; subst.
    simpl.
    repeat rewrite fix_cnots_sound.
    Transparent CNOT.
    replace (CNOT (log2phys m' n) (log2phys m' n0)) with (@map_qubits _ dim (log2phys m') (CNOT n n0)) by reflexivity.
    rewrite useq_assoc.
    rewrite <- convert_between_layouts_map_commutes; try assumption.
    rewrite <- useq_assoc.
    rewrite path_to_swaps_sound with (c:=b); try apply path; auto.
    rewrite convert_between_layouts_transitive.
    unfold convert_between_layouts.
    rewrite convert_between_layouts'_same; try assumption.
    unfold uc_equiv; simpl.
    rewrite denote_SKIP.
    Msimpl_light; reflexivity.
    apply uc_well_typed_implies_dim_nonzero in WT. assumption.
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
    eapply path_to_swaps_well_formed; try apply path; auto.
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



