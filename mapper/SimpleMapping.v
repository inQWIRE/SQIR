Require Import Compose.
Require Import Equivalences.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.

(* Simplest possible strategy for mapping a program to a CNOT connectivity 
   DAG. When a CNOT occurs between non-adjacent qubits: (1) insert SWAPs to 
   make the qubits adjacent, (2) perform the CNOT, (3) move the qubits back
   to their original locations. In cases where a CNOT is between adjacent
   qubits but in the wrong orientation, insert H gates on the target and
   control. 

   We've chosen to leave the implemnetation of the CNOT connectivity DAG 
   unspecified. Instead, the mapping algorithm requires two functions:

   - get_path, which returns an undirected path between two nodes in the
     graph; this function must satisfy 
         forall n1 n2, valid_path (get_path n1 n2)

   - is_in_graph, which indicates whether there is a directed edge between 
     two nodes; this function must satisfy
         valid_graph dim is_in_graph
   
   Examples of get_path and is_in_graph for particular graphs can be found in 
   the LNN and Tenerife sections below. *)

(****************************)
(** General Simple Mapping **)
(****************************)

(** Definition **)

(* NOTE: This assumes that paths are oriented from control --> target. *)

Fixpoint do_cnot_along_path dim p : ucom dim :=
  match p with
  | n1 :: n2 :: [] => CNOT n1 n2
  | n1 :: ((n2 :: _) as t) => SWAP n1 n2 ; do_cnot_along_path dim t ; SWAP n1 n2
  | _ => uskip (* bad input case *)
  end.

(* At this point all CNOTs should be between adjacent qubits, but
   they may not respect the direction of the edges in the connectivity
   graph. We can fix this by insert Hadamard gates before and after
   each offending CNOT. *)
Fixpoint fix_cnots {dim} (c : ucom dim) (is_in_graph_b : nat -> nat -> bool) :=
  match c with
  | c1; c2 => fix_cnots c1 is_in_graph_b ; fix_cnots c2 is_in_graph_b
  | uapp2 U_CNOT n1 n2 => 
      if is_in_graph_b n1 n2
      then CNOT n1 n2
      else H n1; H n2; CNOT n2 n1; H n1; H n2
  | _ => c
  end.

Fixpoint simple_map {dim} (c : ucom dim) (get_path : nat -> nat -> list nat) (is_in_graph_b : nat -> nat -> bool) :=
  match c with
  | c1; c2 => simple_map c1 get_path is_in_graph_b ; 
             simple_map c2 get_path is_in_graph_b
  | uapp2 U_CNOT n1 n2 => let p := do_cnot_along_path dim (get_path n1 n2) in
                         fix_cnots p is_in_graph_b
  | uapp1 u n => uapp1 u n
  | _ => c
  end.

(** Proofs **)

(* Loose formalism for describing paths in a graph - a proper graph 
   library would have more precise definitions. We will represent
   a path between n1 and n2 as a list of nodes with the following 
   properties:
   1. The path must begin with n1.
   2. The path must end with n2.
   3. For every n1' and n2' adjacent in the path, there must exist an 
      undirected edge between n1' and n2'.  
   4. The path does not go through n2 twice.

   Restriction #4 is really just to make the proof easier, we could
   probably remove it. However, if we were defining proper graph-theoretic 
   paths then this restriction would be implied because a path cannot
   go through a vertex multiple times. *)

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

(* Restrictions on the structure of the graph to ensure that the chain
   of SWAPs constructed from a path form a well-typed program. If we 
   had defined proper paths (above), then only the n1 < dim and n2 < dim
   constraints would be required. *)
Definition valid_graph dim (is_in_graph : nat -> nat -> Prop) := 
  forall n1 n2, is_in_graph n1 n2 -> (n1 < dim /\ n2 < dim /\ n1 <> n2).

(* Formalisms for describing correct mappings. *)

Inductive respects_constraints_undirected {dim} : (nat -> nat -> Prop) -> ucom dim -> Prop :=
  | res_und_skip : forall f, respects_constraints_undirected f uskip
  | res_und_seq : forall f c1 c2, 
      respects_constraints_undirected f c1 -> 
      respects_constraints_undirected f c2 -> 
      respects_constraints_undirected f (c1; c2)
  | res_und_app_u : forall f (u : Unitary 1) n, 
      respects_constraints_undirected f (uapp1 u n)
  | res_und_app_cnot : forall (f : nat -> nat -> Prop) n1 n2, 
      f n1 n2 \/ f n2 n1 -> (* undirected *)
      respects_constraints_undirected f (CNOT n1 n2).

Inductive respects_constraints {dim} : (nat -> nat -> Prop) -> ucom dim -> Prop :=
  | res_skip : forall f, respects_constraints f uskip
  | res_seq : forall f c1 c2, 
      respects_constraints f c1 -> 
      respects_constraints f c2 -> 
      respects_constraints f (c1; c2)
  | res_app_u : forall f (u : Unitary 1) n, 
      respects_constraints f (uapp1 u n)
  | res_app_cnot : forall (f : nat -> nat -> Prop) n1 n2, 
      f n1 n2 -> (* directed *)
      respects_constraints f (CNOT n1 n2).

(* Correctness of do_cnot_along_path *)

Lemma swap_cnot : forall {dim} a b c,
  (* well-typedness constraints *)
  a < dim -> b < dim -> c < dim ->
  a <> b -> b <> c -> a <> c ->
  (* main equivalence *)
  @uc_equiv dim (SWAP a b; CNOT b c; SWAP a b) (CNOT a c).
Proof. Admitted. (* TODO *)

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

Lemma do_cnot_along_path_sound : forall dim n1 n2 is_in_graph p,
  valid_graph dim is_in_graph ->
  valid_path n1 n2 is_in_graph p ->
  @uc_well_typed dim (CNOT n1 n2) ->
  do_cnot_along_path dim p ≡ CNOT n1 n2.
Proof.
  intros dim n1 n2 is_in_graph p Hgraph Hpath WT.
  generalize dependent n1.
  induction p; intros.
  - (* invalid case: path can't be empty *)
    destruct Hpath as [H1 _].
    inversion H1.
  - destruct p. 
    + (* invalid case: path can't have only one element *)
      destruct Hpath as [_ [_ [H1 _]]].
      inversion H1.
    + simpl; destruct p.
      * (* base case: exactly two elements in the path *)
        destruct Hpath as [H1 [H2 [_ _]]]. 
        inversion H1; subst.
        inversion H2; subst. 
        inversion H3; subst.
        reflexivity. 
        inversion H4.
      * (* inductive case *) 
        inversion Hpath as [H1 Hpath']. 
        destruct Hpath' as [_ [H2 H3]].
        inversion H1; subst.
        inversion WT; subst.
        assert (n < dim).
        { inversion H2; subst.
          destruct H9; apply Hgraph in H; easy. }
        assert (a <> n).
        { inversion H2; subst.
          destruct H10; apply Hgraph in H0; try easy.
          apply not_eq_sym; easy. }
        assert (n <> n2).
        { inversion H3; subst.
          inversion H12; subst; easy. }
        rewrite IHp with (n1:=n).
        apply swap_cnot; assumption.    
        apply (valid_path_subpath _ _ _ _ _ _ Hpath).
        constructor; assumption.
Qed.

(* This has roughly the same structure as the soundness proof, but it's
   shorter and relies on fewer assumptions because we don't need to
   worry about well-typedness. *)
Lemma do_cnot_along_path_respects_undirected : forall dim n1 n2 is_in_graph p,
  valid_path n1 n2 is_in_graph p ->
  respects_constraints_undirected is_in_graph (do_cnot_along_path dim p).
Proof.
  intros dim n1 n2 is_in_graph p Hpath.
  generalize dependent n1.
  induction p; intros; try constructor.
  destruct p; try constructor. 
  destruct p.
  - destruct Hpath as [_ [_ [H1 _]]]. 
    inversion H1; subst.
    constructor; assumption.
    inversion H5.
  - inversion Hpath as [H1 Hpath']. 
    inversion H1; subst.
    destruct Hpath' as [_ [H2 _]].
    inversion H2; subst.
    repeat apply res_und_seq; try apply res_und_app_cnot;
      try assumption;
      try (destruct H5; [right | left]; assumption).
    apply IHp with (n1:=n). 
    apply (valid_path_subpath _ _ _ _ _ _ Hpath).
Qed.

(* Correctness of fix_cnots *)

Lemma H_swaps_CNOT : forall {dim} m n,
  @uc_equiv dim (H m; H n; CNOT n m; H m; H n) (CNOT m n).
Proof. Admitted. (* TODO *)

Lemma fix_cnots_sound : forall dim (c : ucom dim) is_in_graph_b,
  fix_cnots c is_in_graph_b ≡ c.
Proof.
  intros.
  induction c; try reflexivity; simpl.
  - rewrite IHc1, IHc2. reflexivity.
  - dependent destruction u.
    destruct (is_in_graph_b n n0).
    reflexivity.
    apply H_swaps_CNOT.
Qed.

Lemma fix_cnots_respects_constraints : forall dim (c : ucom dim) is_in_graph is_in_graph_b,
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  respects_constraints_undirected is_in_graph c ->
  respects_constraints is_in_graph (fix_cnots c is_in_graph_b).
Proof.
  intros.
  induction H0; try constructor.
  apply IHrespects_constraints_undirected1; assumption.
  apply IHrespects_constraints_undirected2; assumption.
  destruct H0; simpl.
  - assert (is_in_graph_b n1 n2 = true).
    { rewrite <- reflect_iff. apply H0. apply H. }
    rewrite H1; simpl.  
    constructor; assumption.
  - bdestruct (is_in_graph_b n1 n2). 
    constructor; assumption. 
    repeat constructor; assumption.
Qed.

(* Correctness of simple_map *)

Lemma simple_map_sound : forall dim (c : ucom dim) get_path is_in_graph is_in_graph_b,
  valid_graph dim is_in_graph ->
  get_path_valid dim get_path is_in_graph ->
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  uc_well_typed c ->
  simple_map c get_path is_in_graph_b ≡ c.
Proof.
  intros.
  induction c; try reflexivity; simpl.
  - inversion H2.
    rewrite IHc1, IHc2; try assumption.
    reflexivity.
  - dependent destruction u.
    rewrite fix_cnots_sound.
    inversion H2; subst.
    eapply do_cnot_along_path_sound.
    apply H.
    apply H0; assumption.
    constructor; assumption.
Qed.

Lemma simple_map_respect_constraints : forall dim (c : ucom dim) get_path is_in_graph is_in_graph_b,
  valid_graph dim is_in_graph ->
  get_path_valid dim get_path is_in_graph ->
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  uc_well_typed c ->
  respects_constraints is_in_graph (simple_map c get_path is_in_graph_b).
Proof.
  intros.
  induction c; try constructor; inversion H2; subst.  
  apply IHc1; assumption. 
  apply IHc2; assumption.
  simpl.
  dependent destruction u.
  apply fix_cnots_respects_constraints; try assumption.
  eapply do_cnot_along_path_respects_undirected.
  apply H0; assumption.
Qed.


(*************************)
(** LNN Mapping Example **)
(*************************)

(* Creates a DAG of size dim where element i is connected to (i-1) and (i+1). *)

Inductive LNN_is_in_graph dim : nat -> nat -> Prop := 
  | LNN_in_graph1 : forall n, n + 1 < dim -> LNN_is_in_graph dim n (n + 1)
  | LNN_in_graph2 : forall n, n + 1 < dim -> LNN_is_in_graph dim (n + 1) n.

Definition LNN_is_in_graph_b dim n1 n2 :=
  ((n1 + 1 <? dim) && (n2 =? n1 + 1)) || ((n2 + 1 <? dim) && (n1 =? n2 + 1)).

Fixpoint move_left base dist :=
  match dist with 
  | O => (base + 1) :: base :: []
  | S n' => (base + dist + 1) :: move_left base n'
  end.

Fixpoint move_right base dist :=
  match dist with 
  | O => base :: (base + 1) :: []
  | S n' => (base - dist) :: move_right base n'
  end.

Definition LNN_get_path n1 n2 :=
  if n1 <? n2
  then move_right (n2 - 1) (n2 - n1 - 1)
  else if n2 <? n1
       then move_left n2 (n1 - n2 - 1)
       else [] (* badly-typed case, n1=n2 *).

(* Examples *)
Compute (LNN_get_path 2 5).
Compute (LNN_get_path 6 1).

Definition map_to_lnn {dim} (c : ucom dim) : ucom dim :=
  simple_map c LNN_get_path (LNN_is_in_graph_b dim).

(* Examples *)
Definition test_lnn1 : ucom 3 := CNOT 2 1.
Compute (map_to_lnn test_lnn1).
Definition test_lnn2 : ucom 5 := CNOT 0 3; CNOT 4 1.
Compute (map_to_lnn test_lnn2).

(* Correctness *)

Lemma LNN_is_in_graph_valid : forall dim, 
  valid_graph dim (LNN_is_in_graph dim).
Proof.
  intros.
  split; try split; inversion H; try lia.
Qed.

Lemma LNN_get_path_valid : forall dim, 
  get_path_valid dim LNN_get_path (LNN_is_in_graph dim).
Proof.
  intros dim n1 n2 Hn1 Hn2 Hn1n2.
  unfold LNN_get_path.
  remember (LNN_is_in_graph dim) as f.
  bdestruct (n1 <? n2).
  - (* move_right case *)
    assert (forall base dist, 
      dist <= base -> base + 1 < dim -> 
      valid_path (base - dist) (base + 1) f (move_right base dist)).
    { intros. 
      induction dist; simpl.
      - replace (base - 0) with base by lia.
        split; [|split; [|split]]; repeat constructor; try lia.
        subst f; constructor; assumption.
      - destruct IHdist as [H2 [H3 [H4 H5]]]; try lia.
        split; [|split; [|split]]; try constructor; try assumption.
        + destruct (move_right base dist); try easy.
          constructor; try assumption.
          inversion H2; subst. left. 
          replace (base - dist) with (base - S dist + 1) by lia. 
          constructor; lia.
        + destruct (move_right base dist); try easy. 
          constructor; try assumption; lia. }
    remember (n2 - 1) as base.
    remember (n2 - n1 - 1) as dist.
    replace n1 with (base - dist) by lia.
    replace n2 with (base + 1) by lia.
    apply H0; lia. 
  - (* move_left case *)
    bdestructΩ (n2 <? n1).
    assert (forall base dist, 
      base + dist + 1 < dim ->
      valid_path (base + dist + 1) base f (move_left base dist)).
    { intros. 
      induction dist; simpl.
      - replace (base + 0 + 1) with (base + 1) by lia.
        split; [|split; [|split]]; repeat constructor; try lia.
        subst f; constructor; lia.
      - destruct IHdist as [H2 [H3 [H4 H5]]]; try lia.
        split; [|split; [|split]]; try constructor; try assumption.
        + destruct (move_left base dist); try easy.
          constructor; try assumption.
          inversion H2; subst. left. 
          replace (base + S dist + 1) with (base + dist + 1 + 1) by lia. 
          constructor; lia.
        + destruct (move_left base dist); try easy. 
          constructor; try assumption; lia. }
    remember n2 as base.
    remember (n1 - base - 1) as dist.
    replace n1 with (base + dist + 1) by lia.
    apply H1; lia. 
Qed.

Lemma LNN_is_in_graph_reflects : forall dim n1 n2,
  reflect (LNN_is_in_graph dim n1 n2) (LNN_is_in_graph_b dim n1 n2).
Proof.
  intros.
  unfold LNN_is_in_graph_b.
  bdestruct (n1 + 1 <? dim); bdestruct (n2 =? n1 + 1); 
  bdestruct (n2 + 1 <? dim); bdestruct (n1 =? n2 + 1);
  simpl; subst; constructor. 
  all: try (constructor; assumption). 
  all: try (intros contra; inversion contra; subst). 
  all: try (contradict H0; lia).
  contradict H2; lia. 
Qed.

Lemma map_to_lnn_sound : forall dim (c : ucom dim),
  uc_well_typed c -> map_to_lnn c ≡ c.
Proof.
  intros.
  unfold map_to_lnn.
  eapply simple_map_sound.
  apply LNN_is_in_graph_valid.
  apply LNN_get_path_valid.
  apply LNN_is_in_graph_reflects.
  assumption.
Qed.

Lemma map_to_lnn_respects_constraints : forall dim (c : ucom dim),
  uc_well_typed c -> respects_constraints (LNN_is_in_graph dim) (map_to_lnn c).
Proof.
  intros.
  unfold map_to_lnn.
  eapply simple_map_respect_constraints.
  apply LNN_is_in_graph_valid.
  apply LNN_get_path_valid.
  apply LNN_is_in_graph_reflects.
  assumption.
Qed.


(******************************)
(** Tenerife Mapping Example **)
(******************************)

(* Map to IBM's 5-qubit Tenerife machine. The connectivity graph for the 
   Tenerife machine is depicted here: https://github.com/Qiskit/ibmq-device-information/blob/master/backends/tenerife/V1/version_log.md 

   We'll be using a hardcoded graph because we haven't found an easy-to-use 
   (and easy-to-extract) graph library for Coq. *)

Definition tenerife_graph : list (nat * nat) := 
  (1, 0) :: (2, 0) :: (2, 1) :: (3, 2) :: (3, 4) :: (4, 2) :: [].

Definition tenerife_is_in_graph n1 n2 := 
  In (n1, n2) tenerife_graph.

Definition beq_tup t t' := 
  match t, t' with
  | (n1, n2), (n1', n2') => (n1 =? n1') && (n2 =? n2')
  end.

Definition tenerife_is_in_graph_b n1 n2 := 
  existsb (beq_tup (n1, n2)) tenerife_graph.

Definition tenerife_get_path n1 n2 :=
  match n1, n2 with 
  | 0, 1 => 0 :: 1 :: []
  | 0, 2 => 0 :: 2 :: []
  | 0, 3 => 0 :: 2 :: 3 :: []
  | 0, 4 => 0 :: 2 :: 4 :: []
  | 1, 0 => 1 :: 0 :: []
  | 1, 2 => 1 :: 2 :: []
  | 1, 3 => 1 :: 2 :: 3 :: []
  | 1, 4 => 1 :: 2 :: 4 :: []
  | 2, 0 => 2 :: 0 :: []
  | 2, 1 => 2 :: 1 :: []
  | 2, 3 => 2 :: 3 :: []
  | 2, 4 => 2 :: 4 :: []
  | 3, 0 => 3 :: 2 :: 0 :: []
  | 3, 1 => 3 :: 2 :: 1 :: []
  | 3, 2 => 3 :: 2 :: []
  | 3, 4 => 3 :: 4 :: []
  | 4, 0 => 4 :: 2 :: 0 :: []
  | 4, 1 => 4 :: 2 :: 1 :: []
  | 4, 2 => 4 :: 2 :: []
  | 4, 3 => 4 :: 3 :: []
  | _, _ => [] (* bad input case *)
  end.

Definition map_to_tenerife (c : ucom 5) : ucom 5 :=
  simple_map c tenerife_get_path tenerife_is_in_graph_b.

(* Examples *)
Definition test_tenerife1 : ucom 5 := CNOT 1 2.
Compute (map_to_tenerife test_tenerife1).
Definition test_tenerife2 : ucom 5 := CNOT 3 0.
Compute (map_to_tenerife test_tenerife2).
Definition test_tenerife3 : ucom 5 := CNOT 0 2; X 3; CNOT 4 1; X 2; CNOT 3 2.
Compute (map_to_tenerife test_tenerife3).

(* Correctness *)

Lemma tenerife_is_in_graph_valid : 
  valid_graph 5 tenerife_is_in_graph.
Proof.
  unfold tenerife_is_in_graph; simpl.
  split; try split;
  repeat (destruct H; try (inversion H; subst; lia)).
Qed.

Lemma tenerife_get_path_valid : 
  get_path_valid 5 tenerife_get_path tenerife_is_in_graph.
Proof.
  split; [| split; [| split]].
  - do 5 try destruct n1; do 5 try destruct n2;
    try contradiction;
    try (contradict H1; lia);
    constructor.
  - do 5 try destruct n1; do 5 try destruct n2;
    try contradiction;
    try (contradict H1; lia);
    repeat constructor.
  - do 5 try destruct n1; do 5 try destruct n2;
    try contradiction;
    try (contradict H1; lia);
    try constructor;
    unfold tenerife_is_in_graph; simpl;
    auto 8.
    all: try constructor; auto 8.
  - do 5 try destruct n1; do 5 try destruct n2;
    try contradiction;
    try (contradict H1; lia);
    try constructor; try constructor; lia.
Qed.    


Lemma beq_tup_refl : forall t t',
  reflect (t = t') (beq_tup t t').
Proof.
  intros; unfold beq_tup.
  destruct t; destruct t'.
  bdestruct (n =? n1); bdestruct (n0 =? n2); simpl; 
  constructor;
  try (rewrite H, H0; reflexivity);
  try (intros contra; inversion contra; subst; contradiction).
Qed.

Lemma tenerife_is_in_graph_reflects : forall n1 n2,
  reflect (tenerife_is_in_graph n1 n2) (tenerife_is_in_graph_b n1 n2).
Proof.
  intros.
  unfold tenerife_is_in_graph, tenerife_is_in_graph_b.
  remember (existsb (beq_tup (n1, n2)) tenerife_graph); symmetry in Heqb.
  destruct b; constructor.
  - apply existsb_exists in Heqb.
    destruct Heqb. destruct H as [H1 H2].
    eapply reflect_iff in H2.
    2: { apply beq_tup_refl. }
    subst; assumption.
  - intros contra.
    apply not_true_iff_false in Heqb.
    rewrite existsb_exists in Heqb. 
    destruct Heqb.
    exists (n1, n2).
    split; try assumption. 
    erewrite <- (reflect_iff _ _ (beq_tup_refl (n1,n2) (n1,n2))). 
    reflexivity.
Qed.  

Lemma map_to_tenerife_sound : forall (c : ucom 5),
  uc_well_typed c -> map_to_tenerife c ≡ c.
Proof.
  intros.
  unfold map_to_tenerife.
  eapply simple_map_sound.
  apply tenerife_is_in_graph_valid.
  apply tenerife_get_path_valid.
  apply tenerife_is_in_graph_reflects.
  assumption.
Qed.

Lemma map_to_tenerife_respects_constraints : forall (c : ucom 5),
  uc_well_typed c -> respects_constraints tenerife_is_in_graph (map_to_tenerife c).
Proof.
  intros.
  unfold map_to_tenerife.
  eapply simple_map_respect_constraints.
  apply tenerife_is_in_graph_valid.
  apply tenerife_get_path_valid.
  apply tenerife_is_in_graph_reflects.
  assumption.
Qed.
