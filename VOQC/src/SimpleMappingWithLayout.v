Require Export UnitaryListRepresentation.

Local Close Scope C_scope.
Local Close Scope R_scope.

(* Simple strategy for mapping a program to a CNOT connectivity graph.
   DAG. When a CNOT occurs between non-adjacent qubits: (1) insert SWAPs to 
   make the qubits adjacent, (2) perform the CNOT, (3) update the 
   correspondence between logical (program) qubits and physical (machine)
   qubits. In cases where a CNOT is between adjacent qubits but in the wrong 
   orientation, insert H gates on the target and control. 
*)

(** Definition of layouts. **)

(* We will represent a layout with two functions: one that maps from
   logical qubits to physcial qubits, and one that maps from physical
   qubits to logical qubits. We use two functions instead of one to 
   make lookup in either direction efficient. However, this requires
   some extra machinery to describe well-formed layouts. 

   Layouts are parameterized by *two* dimensions: one for the logical 
   qubit register (ldim) and one for the physical qubit register (pdim).
   We assume that the physical qubit register is at least as large as the 
   logical qubit register. So every logical qubit must be mapped to a 
   physical qubit (hence the type nat -> nat), but a physical qubit may 
   not be mapped to a logical qubit (hence the type nat -> option nat).
*)
Definition qmap (logdim physdim : nat) : Type := (nat -> nat) * (nat -> option nat).

Definition log2phys {ldim pdim} (m : qmap ldim pdim) q :=
  match m with
  | (m, _) => m q
  end.

Definition phys2log {ldim pdim} (m : qmap ldim pdim) q :=
  match m with
  | (_, m) => m q
  end.

(* Swap the logical qubits associated with physical qubits phys1 and phys2. *)
Definition swap_in_map {ldim pdim} (m : qmap ldim pdim) phys1 phys2 : qmap ldim pdim :=
  match m with
  | (m1, m2) => 
      let olog1 := m2 phys1 in
      let olog2 := m2 phys2 in
      let m1' q := 
        match olog1, olog2 with
        | None, None => m1 q
        | Some log1, None => if q =? log1 then phys2 else m1 q
        | None, Some log2 => if q =? log2 then phys1 else m1 q
        | Some log1, Some log2 => 
            if q =? log1 then phys2
            else if q =? log2 then phys1 
            else m1 q 
        end in
      let m2' q := if q =? phys1 then olog2 
                   else if q =? phys2 then olog1 
                   else m2 q in
      (m1', m2')
  end.

Definition layout_well_formed ldim pdim (m : qmap ldim pdim) := 
  (forall x, x < ldim ->
    (log2phys m x < pdim /\ phys2log m (log2phys m x) = Some x)) /\
  (forall x y, y < pdim -> phys2log m y = Some x ->
    (x < ldim /\ log2phys m x = y)).

(* TODO: Probably tricky to prove, but I think it's true. -KH

Lemma layout_well_formed_implies_ldim_le_pdim : forall ldim pdim (m : qmap ldim pdim),
  layout_well_formed ldim pdim m ->
  ldim <= pdim. *)

Fixpoint check_log2phys ldim pdim x (m : qmap ldim pdim) :=
  match x with
  | O => true
  | S x' => 
      let y := log2phys m x' in
      (y <? pdim) && 
      (match phys2log m y with None => false | Some x0 => x0 =? x' end) &&
      (check_log2phys ldim pdim x' m)
  end. 
Fixpoint check_phys2log ldim pdim y (m : qmap ldim pdim) :=
  match y with
  | O => true
  | S y' => 
      let ox := phys2log m y' in
      (match ox with
       | None => true
       | Some x => (x <? ldim) && (log2phys m x =? y')
       end) &&
      (check_phys2log ldim pdim y' m)
  end. 
Definition layout_well_formed_b ldim pdim (m : qmap ldim pdim) :=
  check_log2phys ldim pdim ldim m &&
  check_phys2log ldim pdim pdim m.

Lemma layout_well_formed_b_equiv : forall ldim pdim (m : qmap ldim pdim),
  layout_well_formed_b ldim pdim m = true -> layout_well_formed ldim pdim m.
Proof.
  intros.
  assert (forall x, check_log2phys ldim pdim x m = true ->
          forall x0, x0 < x -> (log2phys m x0 < pdim /\ phys2log m (log2phys m x0) = Some x0)).
  { intros x Hx x0 Hx0.
    induction x.
    lia.
    simpl in Hx.
    apply andb_prop in Hx as [Hx Hx3].
    apply andb_prop in Hx as [Hx1 Hx2].
    apply Nat.ltb_lt in Hx1.
    destruct (phys2log m (log2phys m x)) eqn:?.
    2: inversion Hx2.
    apply beq_nat_true in Hx2; subst.
    specialize (IHx Hx3).
    bdestruct (x0 =? x).    
    subst. 
    split; assumption.
    apply IHx.
    lia. }
  assert (forall y, check_phys2log ldim pdim y m = true ->
          forall x0 y0, y0 < y -> phys2log m y0 = Some x0 ->
            (x0 < ldim /\ log2phys m x0 = y0)).
  { intros y Hy x0 y0 Hy01 Hy02.
    induction y.
    lia.
    simpl in Hy.
    apply andb_prop in Hy as [Hy Hy3].
    specialize (IHy Hy3).
    bdestruct (y0 =? y).
    subst.
    rewrite Hy02 in Hy.
    apply andb_prop in Hy as [Hy1 Hy2].
    apply Nat.ltb_lt in Hy1.
    apply beq_nat_true in Hy2.
    split; assumption.
    apply IHy.
    lia. }
  apply andb_prop in H as [Hl2p Hp2l].
  specialize (H0 ldim Hl2p).
  specialize (H1 pdim Hp2l).
  split; assumption.
Qed.

Lemma swap_in_map_well_formed : forall {ldim pdim} (m : qmap ldim pdim) n1 n2,
  n1 < pdim -> n2 < pdim -> layout_well_formed ldim pdim m -> 
  layout_well_formed ldim pdim (swap_in_map m n1 n2).
Proof.
  unfold layout_well_formed, swap_in_map, log2phys, phys2log.
  intros ldim pdim m n1 n2 Hn1 Hn2.
  destruct m as [m1 m2].
  intros [H1 H2].
  split.
  - intros x Hx.
    specialize (H1 x Hx) as [? H].
    destruct (m2 n1) eqn:m2n1; destruct (m2 n2) eqn:m2n2.
    all: bdestruct_all; subst; split; auto.
    rewrite <- m2n1, m2n2; auto.
    all: try rewrite m2n1 in H; try rewrite m2n2 in H.
    all: try inversion H; subst; try contradiction.
    rewrite m2n2 in m2n1. 
    inversion m2n1.
  - intros x y Hy H.
    bdestruct (y =? n1); bdestruct (y =? n2); subst.
    + destruct (H2 x n2 Hn2 H) as [? ?].
      split; auto.
      rewrite H.
      bdestructΩ (x =? x).
    + destruct (H2 x n2 Hn2 H) as [? ?].
      split; auto.
      rewrite H.
      bdestructΩ (x =? x).
      destruct (m2 n1) eqn:m2n1; auto.
      bdestruct_all; subst; auto.
      destruct (H2 n n1 Hn1 m2n1) as [? Heq].
      symmetry in Heq.
      contradiction.
    + destruct (H2 x n1 Hn1 H) as [? ?].
      split; auto.
      rewrite H.
      bdestructΩ (x =? x).
      destruct (m2 n2); auto.
    + destruct (H2 x y Hy H) as [? ?].
      split; auto.
      destruct (m2 n1) eqn:m2n1; destruct (m2 n2) eqn:m2n2.
      all: bdestruct_all; subst; auto.
      destruct (H2 n n1 Hn1 m2n1) as [? ?].
      contradiction.
      destruct (H2 n0 n2 Hn2 m2n2) as [? ?].
      contradiction.
      destruct (H2 n n1 Hn1 m2n1) as [? ?].
      contradiction.
      destruct (H2 n n2 Hn2 m2n2) as [? ?].
      contradiction.
Qed.

(* Represent a layout as a list where element l at index p indicates that
   logical qubit l is stored at physcial qubit p. (Makes printing nicer.)  *)
Fixpoint layout_to_list' {ldim pdim} x (m : qmap ldim pdim) :=
  match x with 
  | O => []
  | S x' => (layout_to_list' x' m) ++ [phys2log m x'] 
  end.
Definition layout_to_list {ldim} pdim (m : qmap ldim pdim) := 
  layout_to_list' pdim m.

(* Produce a layout from its list representation. *)
Fixpoint list_to_layout' {ldim pdim} l acc : qmap ldim pdim :=
  match l with
  | [] => (fun x => x, fun x => None) (* default mapping *)
  | h :: t =>
      let m' := @list_to_layout' ldim pdim t (S acc) in
      match h with
      | None => (fst m', fun x => if x =? acc then None else snd m' x)
      | Some h =>
      (fun x => if x =? h then acc else fst m' x, fun x => if x =? acc then Some h else snd m' x)
      end
  end.
Definition list_to_layout {ldim pdim} l : qmap ldim pdim := 
  list_to_layout' l 0.

(* TODO: May be useful to prove that layout_to_list and list_to_layout are inverses. *)

(* Examples *)
Definition trivial_layout ldim pdim : qmap ldim pdim :=
  (fun x => x, fun x => if x <? ldim then Some x else None).
Definition test_layout1 : qmap 5 6 := 
  let l2p q := if q =? 0 then 4
               else if q =? 1 then 2
                    else if q =? 2 then 3
                         else if q =? 3 then 0
                              else 1 in
  let p2l q := if q =? 0 then Some 3
               else if q =? 1 then Some 4
                    else if q =? 2 then Some 1
                         else if q =? 3 then Some 2
                              else if q =? 5 then Some 0
                              else None in
  (l2p, p2l).

Compute (layout_to_list 6 (trivial_layout 5 6)).
Compute (layout_to_list 6 test_layout1).
Compute (layout_to_list 6 (@list_to_layout 5 6 
    (Some 0 :: Some 1 :: Some 2 :: Some 3 :: Some 4 :: None :: []))).
Compute (layout_to_list 6 (@list_to_layout 5 6 
    (Some 3 :: Some 4 :: Some 1 :: Some 2 :: None :: Some 0 :: []))).

(** Specification of CNOT connectivity graphs. **)

(* We've chosen to leave the implementation of the CNOT connectivity graph 
   unspecified. Instead, the mapping algorithm requires two functions:

   - get_path, which returns an undirected path between two nodes in the
     graph; this function must satisfy 
         forall n1 n2, valid_path (get_path n1 n2)

   - is_in_graph(_b), which indicates whether there is a directed edge between 
     two nodes; this function must satisfy
         valid_graph dim is_in_graph
   
   Examples of get_path and is_in_graph for particular graphs can be found
   in MappingExamples. 

   We use a loose formalism for describing paths in a graph -- a proper graph 
   library would have more precise definitions. We represent a path between n1 
   and n2 as a list of nodes with the following properties:
   1. The path must begin with n1.
   2. The path must end with n2.
   3. For every n1' and n2' adjacent in the path, there must exist an 
      undirected edge between n1' and n2'.  
   4. The path does not go through n2 twice.
   Restriction #4 is really just to make the proof easier, we could
   probably remove it. However, if we were defining proper graph-theoretic 
   paths then this restriction would be implied because a path cannot
   go through a vertex multiple times.
*)

(* Restrictions on the structure of the graph to ensure that the chain
   of SWAPs constructed from a path form a well-typed program. *)
Definition valid_graph dim (is_in_graph : nat -> nat -> Prop) := 
  forall n1 n2, is_in_graph n1 n2 -> (n1 < dim /\ n2 < dim /\ n1 <> n2).

(* For extraction, we'll need a Boolean function that mirrors is_in_graph. *)
Definition is_in_graph_refl (is_in_graph : nat -> nat -> Prop) (is_in_graph_b : nat -> nat -> bool) := 
  forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2).

Inductive begins_with : nat -> list nat -> Prop :=
  | begins_with_cons : forall h t, begins_with h (h :: t).

Inductive ends_with : nat -> list nat -> Prop :=
  | end_with_single_elmt : forall x, ends_with x [x]
  | ends_with_cons : forall x h t, ends_with x t -> ends_with x (h :: t).

Inductive path_is_in_graph : list nat -> (nat -> nat -> Prop) -> Prop :=
  | path_in_graph_two_elmts : forall n1 n2 is_in_graph, 
      (is_in_graph n1 n2) \/ (is_in_graph n2 n1) -> 
      path_is_in_graph (n1 :: n2 :: []) is_in_graph
  | path_in_graph_cons : forall n1 n2 t is_in_graph, 
      (is_in_graph n1 n2) \/ (is_in_graph n2 n1) -> 
      path_is_in_graph (n2 :: t) is_in_graph -> 
      path_is_in_graph (n1 :: n2 :: t) is_in_graph.

Inductive not_in_interior : nat -> list nat -> Prop :=
  | not_in_interior_two_elmts : forall n n1 n2,
      n1 <> n -> not_in_interior n (n1 :: n2 :: [])
  | not_in_interior_cons : forall n n1 n2 t,
      n1 <> n -> 
      not_in_interior n (n2 :: t) ->
      not_in_interior n (n1 :: n2 :: t).

Definition valid_path n1 n2 is_in_graph p :=
  (begins_with n1 p) /\ (ends_with n2 p) 
    /\ (path_is_in_graph p is_in_graph) /\ (not_in_interior n2 p).

Definition get_path_valid dim get_path is_in_graph :=
  forall n1 n2, n1 < dim -> n2 < dim -> n1 <> n2 -> 
           valid_path n1 n2 is_in_graph (get_path n1 n2).

Lemma valid_path_subpath : forall n1 n2 a b is_in_graph p,
  valid_path n1 n2 is_in_graph (n1 :: a :: b :: p) ->
  valid_path a n2 is_in_graph (a :: b :: p).
Proof.
  intros.
  destruct H as [_ [H1 [H2 H3]]].
  split; split; try split. 
  - inversion H1; assumption.
  - inversion H2; assumption.
  - inversion H3; assumption.
Qed.

(** Mapping function definition. **)

Fixpoint path_to_swaps {U ldim pdim} p m (SWAP : nat -> nat -> gate_list U pdim)
  : (gate_list U pdim * qmap ldim pdim) :=
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
      (is_in_graph_b : nat -> nat -> bool) 
      (CNOT : nat -> nat -> gate_app U dim) 
      (H : nat -> gate_app U dim)
  : gate_list U dim :=
  match l with
  | [] => l
  | App2 _ n1 n2 :: t => 
      if is_in_graph_b n1 n2
      then CNOT n1 n2 :: fix_cnots t is_in_graph_b CNOT H
      else H n1 :: H n2 :: CNOT n2 n1 :: H n1 :: H n2 :: fix_cnots t is_in_graph_b CNOT H
  | h :: t => h :: fix_cnots t is_in_graph_b CNOT H
  end.

(* The input program references *logical* qubits, and the returned program
   references *physical* qubits. get_path and is_in_graph_b also reference 
   physical qubits. *) 
Fixpoint simple_map {U ldim pdim} (l : gate_list U ldim) (m : qmap ldim pdim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph_b : nat -> nat -> bool) 
      (CNOT : nat -> nat -> gate_app U pdim) 
      (SWAP : nat -> nat -> gate_list U pdim)
      (H : nat -> gate_app U pdim)
  : (gate_list U pdim * qmap ldim pdim) :=
  match l with
  | [] => ([],m)
  | App2 _ n1 n2 :: t =>
      let p := get_path (log2phys m n1) (log2phys m n2) in
      let (swaps, m') := path_to_swaps p m SWAP in
      let mapped_cnot := 
        fix_cnots (swaps ++ [CNOT (log2phys m' n1) (log2phys m' n2)]) 
                  is_in_graph_b CNOT H in 
      let (t',m'') := simple_map t m' get_path is_in_graph_b CNOT SWAP H in
      (mapped_cnot ++ t', m'')
  | App1 u n :: t =>
      let (t',m') := simple_map t m get_path is_in_graph_b CNOT SWAP H in
      (App1 u (log2phys m n) :: t', m')
  | _ => ([], m) (* unreachable *)
  end.

(** Gate set for mapping. **)

Lemma one_elem_list : forall (m : nat), List.length (m :: []) = 1. 
Proof. easy. Qed.
Lemma two_elem_list : forall (m n : nat), List.length (m :: n :: []) = 2. 
Proof. easy. Qed.

(* Our mapping routine is defined for any gate set that consists of (1) the CNOT
   gate, (2) the H gate, and (3) any other 1-qubit gates. The H gate is used to 
   "reverse" the direction of a CNOT (see fix_cnots). *)
Module Type MappableGateSet (G :GateSet).

  Parameter had : G.U 1.
  Parameter cnot : G.U 2.
  Axiom had_semantics : forall (dim q : nat), 
    @G.to_base dim 1 had (q :: []) (one_elem_list q) = SQIR.H q.
  Axiom cnot_sem : forall (dim q1 q2 : nat),
    @G.to_base dim 2 cnot (q1 :: q2 :: []) (two_elem_list q1 q2) = SQIR.CNOT q1 q2.
  Axiom no_other_2_q_gates : forall (u : G.U 2), u = cnot.
  Axiom no_3_q_gates : forall (u : G.U 3), False.

End MappableGateSet.

(** Proofs **)

Module SimpleMappingProofs (G: GateSet) (MG : MappableGateSet G).

Definition CNOT dim q1 q2 := @App2 _ dim MG.cnot q1 q2.
Definition H dim q := @App1 _ dim MG.had q.
Definition SWAP dim q1 q2 := CNOT dim q1 q2 :: CNOT dim q2 q1 :: CNOT dim q1 q2 :: [].

Lemma path_to_swaps_well_formed : forall {ldim pdim} n1 n2 is_in_graph p m c m',
  valid_graph pdim is_in_graph ->
  valid_path n1 n2 is_in_graph p ->
  layout_well_formed ldim pdim m ->
  path_to_swaps p m (SWAP pdim) = (c, m') ->
  layout_well_formed ldim pdim m'.
Proof.
  intros.
  generalize dependent c.
  generalize dependent m.
  generalize dependent n1.
  induction p; intros n1 Hpath m WFm c res; simpl in res.
  inversion res; subst. assumption.
  destruct p. inversion res; subst. assumption.
  destruct p. inversion res; subst. assumption.
  destruct (path_to_swaps (n :: n0 :: p) (swap_in_map m a n) (SWAP pdim)) eqn:res'.
  inversion res; subst.
  destruct Hpath as [H1 [H2 [H3 H4]]].
  inversion H1; subst.
  eapply IHp; try apply res'.
  repeat split.
  inversion H2; subst. assumption.
  inversion H3; subst. assumption. 
  inversion H4; subst. assumption.
  assert (a < pdim).
  { inversion H3; subst.
    destruct H9.
    apply H0 in H5 as [H5 _].
    assumption. 
    apply H0 in H5 as [_ [H5 _]]. 
    assumption. }
  assert (n < pdim).
  { inversion H3; subst.
    destruct H10.
    apply H0 in H6 as [_ [H6 _]].
    assumption. 
    apply H0 in H6 as [H6 _]. 
    assumption. }
  apply swap_in_map_well_formed; assumption.
Qed.

Lemma simple_map_w_layout_well_formed : forall {ldim pdim} (c : gate_list G.U ldim) m get_path is_in_graph is_in_graph_b (c' : gate_list G.U pdim) m',
  valid_graph pdim is_in_graph ->
  get_path_valid pdim get_path is_in_graph ->
  is_in_graph_refl is_in_graph is_in_graph_b ->
  uc_well_typed_l c ->
  layout_well_formed ldim pdim m ->
  simple_map c m get_path is_in_graph_b (CNOT pdim) (SWAP pdim) (H pdim) = (c', m') ->
  layout_well_formed ldim pdim m'.
Proof.
  intros ldim pdim c m get_path is_in_graph is_in_graph_b c' m'
      Hgraph Hpath Href WT WF res.
  generalize dependent m'.
  generalize dependent c'.
  generalize dependent m.
  induction c; intros m WF c' m' res; simpl in res.
  inversion res; subst. assumption.
  destruct a.
  - destruct (simple_map c m get_path is_in_graph_b (CNOT pdim) (SWAP pdim) (H pdim)) eqn:res1. 
    inversion res; subst.
    eapply IHc.
    inversion WT; auto.
    apply WF.
    apply res1.
  - destruct (path_to_swaps (get_path (log2phys m n) (log2phys m n0)) m (SWAP pdim)) eqn:res1. 
    destruct (simple_map c q get_path is_in_graph_b (CNOT pdim) (SWAP pdim) (H pdim)) eqn:res2. 
    inversion res; subst.
    inversion WT; subst.
    eapply IHc; auto.
    eapply path_to_swaps_well_formed in res1.
    apply res1.
    apply Hgraph.
    destruct WF as [WF _].
    apply Hpath.
    specialize (WF n H4) as [WF _].
    apply WF.
    specialize (WF n0 H5) as [WF _].
    apply WF.
    intro contra.
    contradict H6.
    destruct (WF n H4) as [_ neqn].
    destruct (WF n0 H5) as [_ neqn0].
    rewrite contra, neqn0 in neqn.
    inversion neqn; auto.
    assumption.
    apply res2.
  - assert False. 
    apply MG.no_3_q_gates.
    assumption.
    contradiction.
Qed.

(* Formalisms for describing correct mappings. *)

Inductive respects_constraints_undirected {dim} : (nat -> nat -> Prop) -> gate_list G.U dim -> Prop :=
  | res_und_nil : forall f, respects_constraints_undirected f []
  | res_und_app1 : forall f u n t, 
      respects_constraints_undirected f t ->
      respects_constraints_undirected f (App1 u n :: t)
  | res_und_app2 : forall f u n1 n2 t, 
      f n1 n2 \/ f n2 n1 -> (* undirected *)
      respects_constraints_undirected f t ->
      respects_constraints_undirected f (App2 u n1 n2 :: t).

Inductive respects_constraints_directed {dim} : (nat -> nat -> Prop) -> gate_list G.U dim -> Prop :=
  | res_dir_nil : forall f, respects_constraints_directed f []
  | res_dir_app1 : forall f u n t, 
      respects_constraints_directed f t ->
      respects_constraints_directed f (App1 u n :: t)
  | res_dir_app2 : forall (f : nat -> nat -> Prop) u n1 n2 t, 
      f n1 n2 -> (* directed *) 
      respects_constraints_directed f t ->
      respects_constraints_directed f (App2 u n1 n2 :: t).

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

(* Construct a finite bijection between physical qubits, transforming layout
   m1 into layout m2. We can map physical qubit p with phys2log m p = None 
   to any other p' with phys2log m p' = None. These are the physcial qubits 
   that are not associated with a logical qubit and hence not modified by our 
   program. *)

(*
Definition build_bij {ldim pdim} (m1 m2 : layout ldim pdim) :=
  fun p =>
    match phys2log m1 p with
    | Some l => log2phys m2 l
    | None => get_next_available 

Given an initial mapping m1 and resulting mapping m2

for physical qubit p

if p2l m1 p = Some l
    p <-> to l2p m1 l
if p2l m1 p = None
    p maps to next available empty spot


1 2 X1 X2 3 X3
X1 X2 1 3 2 X3

1<->3
2>->5
3<->  1
4<->  2
5<->4
6<->  6

need a function for an "arbitrary" permutation, given that it respects the fixed values


log2phys m2 (phys2log m1 x)*)

(*Lemma implement_permutation_adjoint : forall ldim pdim (P : Square (2^pdim)) (m1 m2 : qmap ldim pdim),
  layout_well_formed ldim pdim m1 ->
  layout_well_formed ldim pdim m2 ->
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
  forall {ldim pdim} (P : Square (2 ^ pdim)) (m1 m2 : qmap ldim pdim) (c : gate_list G.U pdim),
  layout_well_formed ldim pdim m1 ->
  layout_well_formed ldim pdim m2 ->
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
Qed.*)

Lemma simple_map_w_layout_respects_constraints : forall {ldim pdim} (l : gate_list G.U ldim) (m : qmap ldim pdim) get_path is_in_graph is_in_graph_b l' m',
  valid_graph pdim is_in_graph ->
  get_path_valid pdim get_path is_in_graph ->
  is_in_graph_refl is_in_graph is_in_graph_b ->
  uc_well_typed_l l ->
  layout_well_formed ldim pdim m ->
  simple_map l m get_path is_in_graph_b (CNOT pdim) (SWAP pdim) (H pdim) = (l', m') -> 
  respects_constraints_directed is_in_graph l'.
Proof. Admitted.

End SimpleMappingProofs.

(* For example, we can define mapping over the RzQ gate set. *)
Require Import RzQGateSet.
Module MappableRzQ <: MappableGateSet RzQGateSet.

  Definition had := URzQ_H.
  Definition cnot := URzQ_CNOT.
  Lemma had_semantics : forall (dim q : nat), 
    @to_base dim 1 had (q :: []) (one_elem_list q) = SQIR.H q.
  Proof. intros. reflexivity. Qed.
  Lemma cnot_sem : forall (dim q1 q2 : nat),
    @to_base dim 2 cnot (q1 :: q2 :: []) (two_elem_list q1 q2) = SQIR.CNOT q1 q2.
  Proof. intros. reflexivity. Qed.  
  Lemma no_other_2_q_gates : forall (u : U 2), u = cnot.
  Proof. intros. dependent destruction u. reflexivity. Qed.
  Lemma no_3_q_gates : forall (u : U 3), False.
  Proof. intros. dependent destruction u. Qed.

End MappableRzQ.
Import MappableRzQ.

(* For the RzQ gate set, the specialized versions of the mapping functions is: *)
Definition simple_map_rzq {ldim pdim} 
      (l : RzQ_ucom_l ldim)
      (m : qmap ldim pdim) 
      (get_path : nat -> nat -> list nat) 
      (is_in_graph_b : nat -> nat -> bool)
  : RzQ_ucom_l pdim * qmap ldim pdim
  := simple_map l m get_path is_in_graph_b RzQGateSet.CNOT RzQGateSet.SWAP RzQGateSet.H.

Module SMP := SimpleMappingProofs RzQGateSet MappableRzQ.
Import SMP.

Lemma simple_map_w_layout_respects_constraints : forall {ldim pdim} (l : RzQ_ucom_l ldim) (m : qmap ldim pdim) get_path is_in_graph is_in_graph_b l' m',
  valid_graph pdim is_in_graph ->
  get_path_valid pdim get_path is_in_graph ->
  is_in_graph_refl is_in_graph is_in_graph_b ->
  uc_well_typed_l l ->
  layout_well_formed ldim pdim m ->
  simple_map_rzq l m get_path is_in_graph_b = (l', m') -> 
  respects_constraints_directed is_in_graph l'.
Proof. 
  intros.
  eapply SMP.simple_map_w_layout_respects_constraints; try apply H5; auto.
Qed.
