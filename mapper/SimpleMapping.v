Require Export Compose.
Require Export Equivalences.
Require Import Tactics.
Require Export List.
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
   
   Examples of get_path and is_in_graph for particular graphs can be found
   at the end of the file. *)

(****************************)
(** General Simple Mapping **)
(****************************)

(** Definition **)

(* NOTE: This assumes that paths are oriented from control --> target. *)

Fixpoint do_cnot_along_path dim p : base_ucom dim :=
  match p with
  | n1 :: n2 :: [] => CNOT n1 n2
  | n1 :: ((n2 :: _) as t) => SWAP n1 n2 ; do_cnot_along_path dim t ; SWAP n1 n2
  | _ => SKIP (* bad input case *)
  end.

(* At this point all CNOTs should be between adjacent qubits, but
   they may not respect the direction of the edges in the connectivity
   graph. We can fix this by insert Hadamard gates before and after
   each offending CNOT. *)
Fixpoint fix_cnots {dim} (c : base_ucom dim) (is_in_graph_b : nat -> nat -> bool) :=
  match c with
  | c1; c2 => fix_cnots c1 is_in_graph_b ; fix_cnots c2 is_in_graph_b
  | uapp2 U_CNOT n1 n2 => 
      if is_in_graph_b n1 n2
      then CNOT n1 n2
      else H n1; H n2; CNOT n2 n1; H n1; H n2
  | _ => c
  end.

Fixpoint simple_map {dim} (c : base_ucom dim) (get_path : nat -> nat -> list nat) (is_in_graph_b : nat -> nat -> bool) :=
  match c with
  | c1; c2 => simple_map c1 get_path is_in_graph_b ; 
             simple_map c2 get_path is_in_graph_b
  | uapp2 U_CNOT n1 n2 => let p := do_cnot_along_path dim (get_path n1 n2) in
                         fix_cnots p is_in_graph_b
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

Fixpoint merge_path (p1 : list nat) p2 :=
  match p1 with
  | [] | [_] => p2
  | h :: t => h :: (merge_path t p2)
  end.

Lemma valid_path_extend_path : forall a n1 n2 (is_in_graph : nat -> nat -> Prop) p,
  n1 <> n2 ->
  is_in_graph n1 a \/ is_in_graph a n1 ->
  valid_path a n2 is_in_graph p ->
  valid_path n1 n2 is_in_graph (n1 :: p).
Proof.
  intros.
  destruct p.
  destruct H1 as [H2 _]; inversion H2.
  destruct p.
  destruct H1 as [_ [_ [_ H2]]]; inversion H2.
  destruct H1 as [H2 [H3 [H4 H5]]].
  inversion H2; subst.
  repeat split; constructor; assumption.
Qed.  

Lemma valid_path_merge_path : forall a b c is_in_graph p1 p2, 
  valid_path a b is_in_graph p1 -> 
  valid_path b c is_in_graph p2 -> 
  not_in_interior c p1 ->
  valid_path a c is_in_graph (merge_path p1 p2).
Proof.
  intros a b c f p1 p2 Hp1 Hp2 NIp1.
  (* Because p1 and p2 are valid paths, we know something about their
     structure. Invert some hypotheses here for use later. *)
  destruct p1; [| destruct p1].
  1, 2: inversion NIp1.
  destruct Hp1 as [H1 [H2 [H3 H4]]].
  inversion H1; subst; clear H1.
  destruct p2.
  destruct Hp2 as [H _]; inversion H.
  destruct Hp2 as [H [H1 [H5 H6]]].
  inversion H; subst; clear H.
  (* now a standard proof by induction *)
  generalize dependent n0.
  generalize dependent n.
  induction p1.
  - intros.
    inversion H2; subst. inversion H7; subst.
    2: inversion H8.
    inversion H3; subst.
    2: inversion H11.
    simpl. 
    repeat split; constructor; try assumption.
    inversion NIp1; assumption.
  - intros.
    replace (merge_path (n :: n0 :: a :: p1) (n1 :: p2)) with (n :: (merge_path (n0 :: a :: p1) (n1 :: p2))) by reflexivity.
    apply valid_path_extend_path with (a:=n0).
    inversion NIp1; assumption.
    inversion H3; assumption.
    apply IHp1.
    inversion H2; assumption.
    inversion H3; assumption.
    inversion H4; assumption.
    inversion NIp1; assumption.
Qed.

(* Restrictions on the structure of the graph to ensure that the chain
   of SWAPs constructed from a path form a well-typed program. If we 
   had defined proper paths (above), then only the n1 < dim and n2 < dim
   constraints would be required. *)
Definition valid_graph dim (is_in_graph : nat -> nat -> Prop) := 
  forall n1 n2, is_in_graph n1 n2 -> (n1 < dim /\ n2 < dim /\ n1 <> n2).

(* Formalisms for describing correct mappings. *)

Inductive respects_constraints_undirected {dim} : (nat -> nat -> Prop) -> base_ucom dim -> Prop :=
  | res_und_seq : forall f c1 c2, 
      respects_constraints_undirected f c1 -> 
      respects_constraints_undirected f c2 -> 
      respects_constraints_undirected f (c1; c2)
  | res_und_app_u : forall f u n, 
      respects_constraints_undirected f (uapp1 u n)
  | res_und_app_cnot : forall (f : nat -> nat -> Prop) n1 n2, 
      f n1 n2 \/ f n2 n1 -> (* undirected *)
      respects_constraints_undirected f (CNOT n1 n2).

Inductive respects_constraints {dim} : (nat -> nat -> Prop) -> base_ucom dim -> Prop :=
  | res_seq : forall f c1 c2, 
      respects_constraints f c1 -> 
      respects_constraints f c2 -> 
      respects_constraints f (c1; c2)
  | res_app_u : forall f u n, 
      respects_constraints f (uapp1 u n)
  | res_app_cnot : forall (f : nat -> nat -> Prop) n1 n2, 
      f n1 n2 -> (* directed *)
      respects_constraints f (CNOT n1 n2).

(* Proof about the relationship between CNOT & SWAP (move elsewhere?) *)

(* The proof below does the same thing as 'gridify' but only partially distributes
   matrices. This keeps the terms a little smaller and seems to be faster than
   directly using gridify. It's still slow though. *)
Lemma swap_cnot_control : forall {dim} a b c,
  (* well-typedness constraints *)
  a < dim -> b < dim -> c < dim ->
  a <> b -> b <> c -> a <> c ->
  (* main equivalence *)
  @uc_equiv dim (SWAP a b; CNOT b c; SWAP a b) (CNOT a c).
Proof. 
  intros.
  unfold uc_equiv; simpl.
  autorewrite with eval_db. 
  repad.
  (* rewrite with id_kron *)
  all: repeat rewrite Nat.pow_add_r; 
       repeat rewrite <- id_kron.
  (* distribute (I c) and (I d) right *)
  all: repeat rewrite <- kron_assoc;
       match goal with 
      | |- context [(?a ⊗ ?b) ⊗ (I ?c) ⊗ (I ?d) ⊗ (I ?e) ] => 
            rewrite (kron_assoc a b);
            repeat rewrite (kron_plus_distr_r _ _ _ _ _ _ (I c)); 
            restore_dims_fast;
            rewrite (kron_assoc a _ (I d));
            repeat rewrite (kron_plus_distr_r _ _ _ _ _ _ (I d))
      end;
  (* distribute (I b) and (I c) left *)
     restore_dims_fast; repeat rewrite kron_assoc;
      match goal with 
      | |- context [(I ?a) ⊗ ((I ?b) ⊗ ((I ?c) ⊗ (?d ⊗ ?e))) ] => 
            rewrite <- (kron_assoc (I c) _ e);
            repeat rewrite (kron_plus_distr_l _ _ _ _ (I c));
            restore_dims_fast;
            rewrite <- (kron_assoc (I b) _ e);
            repeat rewrite (kron_plus_distr_l _ _ _ _ (I b))
      end.
  (* simplify to remove extra id's *)
  all: restore_dims_fast;
       repeat rewrite <- kron_assoc;
       restore_dims_fast; 
       repeat rewrite kron_mixed_product;
       Msimpl_light;
       do 2 (apply f_equal2; trivial).
  (* the rest of gridify... *)
  all: simpl; restore_dims_fast;
       distribute_plus;
       restore_dims_fast; repeat rewrite <- kron_assoc;
       restore_dims_fast; repeat rewrite kron_mixed_product;
       Msimpl_light.
  (* rewrite w/ cnot_db *)
  all: autorewrite with cnot_db; Msimpl_light.
  1, 2, 3: rewrite Mplus_swap_mid.
  all: match goal with 
    | [|- ?A .+ ?B .+ ?C .+ ?D = _] => rewrite 2 Mplus_assoc;
                                     rewrite <- (Mplus_assoc _ _ A)
    end;
    repeat (try rewrite <- (kron_plus_distr_l);
            try rewrite <- (kron_plus_distr_r));
    rewrite Mplus_comm;
    replace (∣0⟩⟨0∣ .+ ∣1⟩⟨1∣) with (I 2) by solve_matrix;
    reflexivity.
Qed. 

(* Alternative proof that uses gridify. From (not rigorous) testing on
   Kesha's local machine, it seems to take about 2.5x longer than the 
   proof above.
   
Lemma swap_cnot_control : forall {dim} a b c,
  a < dim -> b < dim -> c < dim ->
  a <> b -> b <> c -> a <> c ->
  @uc_equiv dim (SWAP a b; CNOT b c; SWAP a b) (CNOT a c).
Proof. 
  intros.
  unfold uc_equiv; simpl.
  autorewrite with eval_db.
  gridify.
  all: autorewrite with cnot_db; Msimpl_light.
  1, 2, 3: rewrite Mplus_swap_mid.
  all: match goal with 
       | [|- ?A .+ ?B .+ ?C .+ ?D = _] => rewrite 2 Mplus_assoc;
                                        rewrite <- (Mplus_assoc _ _ A)
       end;
       repeat (try rewrite <- (kron_plus_distr_l);
               try rewrite <- (kron_plus_distr_r));
       rewrite Mplus_comm;
       replace (∣0⟩⟨0∣ .+ ∣1⟩⟨1∣) with (I 2) by solve_matrix;
       reflexivity.
Qed.
*)

(* Correctness of do_cnot_along_path *)

Local Transparent SWAP CNOT H ID.
Lemma do_cnot_along_path_sound : forall dim n1 n2 is_in_graph p,
  valid_graph dim is_in_graph ->
  valid_path n1 n2 is_in_graph p ->
  @uc_well_typed _ dim (CNOT n1 n2) ->
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
        apply swap_cnot_control; assumption.    
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
  induction p; intro; try constructor.
  destruct p; try constructor. 
  destruct p; intros Hpath.
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

Lemma fix_cnots_sound : forall dim (c : base_ucom dim) is_in_graph_b,
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

Lemma fix_cnots_respects_constraints : forall dim (c : base_ucom dim) is_in_graph is_in_graph_b,
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

Lemma simple_map_sound : forall dim (c : base_ucom dim) get_path is_in_graph is_in_graph_b,
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

Lemma simple_map_respect_constraints : forall dim (c : base_ucom dim) get_path is_in_graph is_in_graph_b,
  valid_graph dim is_in_graph ->
  get_path_valid dim get_path is_in_graph ->
  (forall n1 n2, reflect (is_in_graph n1 n2) (is_in_graph_b n1 n2)) ->
  uc_well_typed c ->
  respects_constraints is_in_graph (simple_map c get_path is_in_graph_b).
Proof.
  intros.
  induction c; try dependent destruction u; simpl;
  try constructor; inversion H2; subst.  
  apply IHc1; assumption. 
  apply IHc2; assumption.
  apply fix_cnots_respects_constraints; try assumption.
  eapply do_cnot_along_path_respects_undirected.
  apply H0; assumption.
Qed.

(*************************)
(** LNN Mapping Example **)
(*************************)

Module LNN.

(* Creates a DAG of size dim where element i is connected to (i-1) and (i+1),
   but element 0 is not connected to element (dim-1). *)

Inductive LNN_is_in_graph dim : nat -> nat -> Prop := 
  | LNN_in_graph1 : forall n, n + 1 < dim -> LNN_is_in_graph dim n (n + 1)
  | LNN_in_graph2 : forall n, n + 1 < dim -> LNN_is_in_graph dim (n + 1) n.

Definition LNN_is_in_graph_b dim n1 n2 :=
  ((n1 + 1 <? dim) && (n2 =? n1 + 1)) || ((n2 + 1 <? dim) && (n1 =? n2 + 1)).

Fixpoint move_left n dist :=
  match dist with 
  | O => [n]
  | S n' => n :: move_left (n - 1) n'
  end.

Fixpoint move_right n dist :=
  match dist with 
  | O => [n]
  | S n' => n :: move_right (n + 1) n'
  end.

Definition LNN_get_path n1 n2 :=
  if n1 <? n2
  then move_right n1 (n2 - n1)
  else if n2 <? n1
       then move_left n1 (n1 - n2)
       else [] (* badly-typed case, n1=n2 *).

(* Examples *)
Compute (LNN_get_path 2 5).
Compute (LNN_get_path 6 1).

Definition map_to_lnn {dim} (c : base_ucom dim) : base_ucom dim :=
  simple_map c LNN_get_path (LNN_is_in_graph_b dim).

(* Examples *)
Definition test_lnn1 : base_ucom 3 := CNOT 2 1.
Compute (map_to_lnn test_lnn1).
Definition test_lnn2 : base_ucom 5 := CNOT 0 3; CNOT 4 1.
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
  bdestruct_all. 
  - assert (move_right_valid_path : forall n dist, 
      dist > 0 -> n + dist < dim -> 
      valid_path n (n + dist) (LNN_is_in_graph dim) (move_right n dist)).
    { intros. 
      destruct dist; try lia. 
      generalize dependent n.
      induction dist; simpl in *.
      - intros. repeat split; repeat constructor; lia.
      - intros. 
        apply valid_path_extend_path with (a:=n + 1); try lia.
        left; constructor; lia.
        replace (n + S (S dist)) with (n + 1 + (S dist)) by lia.
        apply IHdist; lia. }
    replace n2 with (n1 + (n2 - n1)) at 1 by lia.
    apply move_right_valid_path; lia.
  - assert (move_left_valid_path : forall n dist, 
      dist > 0 -> dist <= n -> n < dim ->
      valid_path n (n - dist) (LNN_is_in_graph dim) (move_left n dist)).
    { intros. 
      destruct dist; try lia. 
      generalize dependent n.
      induction dist; simpl in *.
      - intros. repeat split; repeat constructor; try lia.
        remember (n - 1) as n'.
        replace n with (n' + 1) by lia.
        constructor; lia.
      - intros. 
        apply valid_path_extend_path with (a:=n - 1); try lia.
        left. remember (n - 1) as n'.
        replace n with (n' + 1) by lia.
        constructor; lia. 
        replace (n - S (S dist)) with (n - 1 - (S dist)) by lia.
        apply IHdist; lia. }
    replace n2 with (n1 - (n1 - n2)) at 1 by lia.
    apply move_left_valid_path; lia.
Qed.

Lemma LNN_is_in_graph_reflects : forall dim n1 n2,
  reflect (LNN_is_in_graph dim n1 n2) (LNN_is_in_graph_b dim n1 n2).
Proof.
  intros.
  unfold LNN_is_in_graph_b.
  bdestruct_all; simpl; subst; constructor.
  all: try (constructor; assumption). 
  all: try (intros contra; inversion contra; subst). 
  all: try (contradict H0; lia).
Qed.

Lemma map_to_lnn_sound : forall dim (c : base_ucom dim),
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

Lemma map_to_lnn_respects_constraints : forall dim (c : base_ucom dim),
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

End LNN.

(******************************)
(** LNN Ring Mapping Example **)
(******************************)

Module LNNRing.

(* Creates a DAG of size dim where element i is connected to ((i-1) mod dim) and 
   ((i+1) mod dim). *)

Inductive LNN_ring_is_in_graph dim : nat -> nat -> Prop := 
  | LNNR_in_graph1 : forall n, dim > 1 -> n < dim -> 
      LNN_ring_is_in_graph dim n ((n + 1) mod dim)
  | LNNR_in_graph2 : forall n, dim > 1 -> n < dim -> 
      LNN_ring_is_in_graph dim ((n + 1) mod dim) n.

Definition LNN_ring_is_in_graph_b dim n1 n2 :=
  (1 <? dim) && (((n1 <? dim) && (n2 =? (n1 + 1) mod dim)) || ((n2 <? dim) && (n1 =? (n2 + 1) mod dim))).

Fixpoint move_cw dim n dist :=
  match dist with 
  | O => [n]
  | S dist' => n :: move_cw dim ((n + 1) mod dim) dist'
  end.

Fixpoint move_ccw dim n dist :=
  match dist with 
  | O => [n]
  | S dist' => n :: move_ccw dim ((dim + n - 1) mod dim) dist'
  end.

Definition LNN_ring_get_path dim n1 n2 :=
  if n1 <? n2
  then let dist_cw := n2 - n1 in
       let dist_ccw := dim + n1 - n2 in
         if dist_cw <? dist_ccw 
         then move_cw dim n1 dist_cw
         else move_ccw dim n1 dist_ccw 
  else if n2 <? n1
       then let dist_cw := dim + n2 - n1 in
            let dist_ccw := n1 - n2 in
              if dist_cw <? dist_ccw 
              then move_cw dim n1 dist_cw
              else move_ccw dim n1 dist_ccw
       else [] (* badly-typed case, n1=n2 *).

(* Examples *)
Compute (LNN_ring_get_path 8 2 5).
Compute (LNN_ring_get_path 8 6 1).
Compute (LNN_ring_get_path 8 6 3).
Compute (LNN_ring_get_path 8 2 7).

Definition map_to_lnn_ring {dim} (c : base_ucom dim) : base_ucom dim :=
  simple_map c (LNN_ring_get_path dim) (LNN_ring_is_in_graph_b dim).

(* Examples *)
Definition test_lnn_ring1 : base_ucom 3 := CNOT 2 1.
Compute (map_to_lnn_ring test_lnn_ring1).
Definition test_lnn_ring2 : base_ucom 5 := CNOT 0 3; CNOT 4 1.
Compute (map_to_lnn_ring test_lnn_ring2).

(* Correctness *)

Lemma LNN_ring_is_in_graph_valid : forall dim, 
  valid_graph dim (LNN_ring_is_in_graph dim).
Proof.
  intros.
  split; try split; inversion H; try assumption.
  1, 2: apply Nat.mod_upper_bound; lia.
  - bdestruct (n1 + 1 <? dim).
    rewrite Nat.mod_small; lia.
    assert (n1 + 1 = dim) by lia. 
    subst; rewrite Nat.mod_same; lia.
  - bdestruct (n2 + 1 <? dim).
    rewrite Nat.mod_small; lia.
    assert (n2 + 1 = dim) by lia. 
    subst; rewrite Nat.mod_same; lia.  
Qed.

(* TODO: Proof is a little gross because of mod. Is there an 'lia' for expressions
   involving mod? If not, we should try to make something. *)

Lemma move_cw_valid_path : forall dim n dist,
  0 < dist -> dist < dim -> n < dim ->
  valid_path n ((n + dist) mod dim) (LNN_ring_is_in_graph dim) (move_cw dim n dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent n.
  induction dist; simpl in *.
  - intros.
    split; [|split; [|split]]; repeat constructor; try lia.
    bdestruct (n + 1 <? dim).
    rewrite Nat.mod_small; lia.
    assert (n + 1 = dim) by lia. 
    subst; rewrite Nat.mod_same; lia.
  - intros. 
    apply valid_path_extend_path with (a:=(n + 1) mod dim).
    bdestruct (n + S (S dist) <? dim).
    rewrite Nat.mod_small; try assumption; lia.
    rewrite Nat.mod_eq; try lia.
    assert ((n + S (S dist)) / dim = 1).
    { assert ((n + S (S dist)) / dim < 2).
      apply Nat.div_lt_upper_bound; lia.
      assert ((n + S (S dist)) / dim > 0).
      apply Nat.div_str_pos; lia.
      lia. }
    rewrite H3. lia.
    left; constructor; lia.
    replace ((n + S (S dist)) mod dim) with (((n + 1) mod dim + S dist) mod dim).
    2: { replace (n + S (S dist)) with (n + 1 + S dist) by lia.
         rewrite Nat.add_mod_idemp_l. 
         reflexivity. lia. }
    apply IHdist; try lia.
    apply Nat.mod_upper_bound; lia.
Qed.

Ltac rewrite_mod_sub e :=
  match e with 
  | (?a + ?b - ?c) mod ?n =>
        bdestruct (c <=? b);
        [ rewrite <- (Nat.add_sub_assoc a b); try lia;
          rewrite <- (Nat.add_mod_idemp_l a); try lia;
          rewrite Nat.mod_same; try lia;
          rewrite Nat.add_0_l;
          rewrite (Nat.mod_small (b - c)); try lia
        | rewrite (Nat.mod_small (a + b - c)); try lia ]
  end.

Lemma move_ccw_valid_path : forall dim n dist,
  0 < dist -> dist < dim -> n < dim ->
  valid_path n ((dim + n - dist) mod dim) (LNN_ring_is_in_graph dim) (move_ccw dim n dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent n.
  induction dist; simpl in *.
  - intros.
    remember ((dim + n - 1) mod dim) as x.
    replace n with ((x + 1) mod dim).
    2: { subst. rewrite Nat.add_mod_idemp_l; try lia.
         replace (dim + n - 1 + 1) with (dim + n) by lia.
         rewrite <- Nat.add_mod_idemp_l; try lia.
         rewrite Nat.mod_same; try lia.
         rewrite Nat.add_0_l.
         apply Nat.mod_small; assumption. }
    assert (x < dim).
    { subst. apply Nat.mod_upper_bound; lia. }
    split; [|split; [|split]]; repeat constructor; try lia.
    bdestruct (x + 1 <? dim).
    rewrite Nat.mod_small; lia.
    assert (x + 1 = dim) by lia. 
    subst dim. rewrite Nat.mod_same; lia.
  - intros.
    apply valid_path_extend_path with (a:=(dim + n - 1) mod dim).
    rewrite_mod_sub ((dim + n - S (S dist)) mod dim).
    left. remember ((dim + n - 1) mod dim) as x.
    replace n with ((x + 1) mod dim).
    2: { subst. rewrite Nat.add_mod_idemp_l; try lia.
         replace (dim + n - 1 + 1) with (dim + n) by lia.
         rewrite <- Nat.add_mod_idemp_l; try lia.
         rewrite Nat.mod_same; try lia.
         rewrite Nat.add_0_l.
         apply Nat.mod_small; assumption. }
    assert (x < dim).
    { subst. apply Nat.mod_upper_bound; lia. }
    constructor; lia.
    replace ((dim + n - S (S dist)) mod dim) with ((dim + (dim + n - 1) mod dim - S dist) mod dim).
    2: { rewrite_mod_sub ((dim + n - 1) mod dim).
         apply f_equal2; lia.
         rewrite <- Nat.add_sub_assoc; try lia.
         rewrite <- Nat.add_mod_idemp_l; try lia.
         rewrite Nat.mod_same; try lia.
         rewrite Nat.add_0_l. 
         apply f_equal2; lia. }
    apply IHdist; try lia.
    apply Nat.mod_upper_bound; lia.
Qed.

Lemma LNN_ring_get_path_valid : forall dim, 
  get_path_valid dim (LNN_ring_get_path dim) (LNN_ring_is_in_graph dim).
Proof.
  intros dim n1 n2 Hn1 Hn2 Hn1n2.
  unfold LNN_ring_get_path.
  bdestruct_all. 
  - replace n2 with ((n1 + (n2 - n1)) mod dim) at 1.
    2: { rewrite Nat.mod_small; lia. }
    apply move_cw_valid_path; lia.
  - replace n2 with ((dim + n1 - (dim + n1 - n2)) mod dim) at 1.
    2: { rewrite Nat.mod_small; lia. }
    apply move_ccw_valid_path; lia.
  - replace n2 with ((n1 + (dim + n2 - n1)) mod dim) at 1.
    2: { rewrite Nat.add_sub_assoc; try lia. 
         rewrite Nat.add_comm. 
         rewrite <- Nat.add_sub_assoc; try lia. 
         rewrite Nat.sub_diag. 
         rewrite Nat.add_0_r. 
         rewrite <- Nat.add_mod_idemp_l; try lia. 
         rewrite Nat.mod_same; try lia.
         rewrite Nat.add_0_l.  
         rewrite Nat.mod_small; lia. }
    apply move_cw_valid_path; lia.
  - replace n2 with ((dim + n1 - (n1 - n2)) mod dim) at 1.
    2: { rewrite <- Nat.add_sub_assoc; try lia. 
         rewrite <- Nat.add_mod_idemp_l; try lia. 
         rewrite Nat.mod_same; try lia.
         rewrite Nat.add_0_l.  
         rewrite Nat.mod_small; lia. }
    apply move_ccw_valid_path; lia.
Qed.

Lemma LNN_ring_is_in_graph_reflects : forall dim n1 n2,
  reflect (LNN_ring_is_in_graph dim n1 n2) (LNN_ring_is_in_graph_b dim n1 n2).
Proof.
  intros.
  unfold LNN_ring_is_in_graph_b.
  bdestruct_all; simpl; subst; constructor.
  all: try (constructor; assumption). 
  all: try (intros contra; inversion contra; subst). 
  all: try (contradict H2; lia).
  assert (n1 < dim). { rewrite H3. apply Nat.mod_upper_bound; lia. }
  contradict H2; lia.
  assert ((n + 1) mod dim < dim) by (apply Nat.mod_upper_bound; lia).
  contradict H5; lia. 
Qed.

Lemma map_to_lnn_ring_sound : forall dim (c : base_ucom dim),
  uc_well_typed c -> map_to_lnn_ring c ≡ c.
Proof.
  intros.
  unfold map_to_lnn_ring.
  eapply simple_map_sound.
  apply LNN_ring_is_in_graph_valid.
  apply LNN_ring_get_path_valid.
  apply LNN_ring_is_in_graph_reflects.
  assumption.
Qed.

Lemma map_to_lnn_ring_respects_constraints : forall dim (c : base_ucom dim),
  uc_well_typed c -> respects_constraints (LNN_ring_is_in_graph dim) (map_to_lnn_ring c).
Proof.
  intros.
  unfold map_to_lnn_ring.
  eapply simple_map_respect_constraints.
  apply LNN_ring_is_in_graph_valid.
  apply LNN_ring_get_path_valid.
  apply LNN_ring_is_in_graph_reflects.
  assumption.
Qed.

End LNNRing.

(*****************************)
(** 2D Grid Mapping Example **)
(*****************************)

Module Grid.

(* Creates a grid of size numRows by numCols. We will use the following mapping
   between qubit i and grid position (r,c):
       r := i / numCols
       c := i % numCols
   Then qubit i, at position (r,c), is connected to the following:
       i' = i - dimX  <->  (r-1, c)
       i' = i + dimX  <->  (r+1, c)
       i' = i - 1     <->  (r, c-1)
       i' = i + 1     <->  (r, c+1)
   (With some restrictions on valid indices.)
*)

Inductive grid_is_in_graph numRows numCols : nat -> nat -> Prop := 
  | grid_up : forall i, i + numCols < numRows * numCols -> 
      grid_is_in_graph numRows numCols (i + numCols) i
  | grid_down : forall i, i + numCols < numRows * numCols -> 
      grid_is_in_graph numRows numCols i (i + numCols)
  | grid_left : forall i, i + 1 < numRows * numCols -> 
      grid_is_in_graph numRows numCols (i + 1) i
  | grid_right : forall i, i + 1 < numRows * numCols -> 
      grid_is_in_graph numRows numCols i (i + 1).

Definition grid_is_in_graph_b numRows numCols i i' :=
  ((i  + numCols <? numRows * numCols) && (i' =? i  + numCols)) ||
  ((i' + numCols <? numRows * numCols) && (i  =? i' + numCols)) ||
  ((i  + 1 <? numRows * numCols) && (i' =? i + 1)) ||
  ((i' + 1 <? numRows * numCols) && (i =? i' + 1)).
 
(* Running example:
  
   numRows = 3
   numCols = 5
   
   0  1  2  3  4
   5  6  7  8  9
   10 11 12 13 14
*)
Definition test_nr := 3.
Definition test_nc := 5.
Compute (grid_is_in_graph_b test_nr test_nc 2 0). (* -> false *)
Compute (grid_is_in_graph_b test_nr test_nc 2 9). (* -> false *)
Compute (grid_is_in_graph_b test_nr test_nc 2 7). (* -> true *)
Compute (grid_is_in_graph_b test_nr test_nc 2 3). (* -> true *)
Compute (grid_is_in_graph_b test_nr test_nc 8 3). (* -> true *)
Compute (grid_is_in_graph_b test_nr test_nc 8 7). (* -> true *)
Compute (grid_is_in_graph_b test_nr test_nc 15 0). (* -> false *)
Compute (grid_is_in_graph_b test_nr test_nc 14 8). (* -> false *)

Definition row numCols i := i / numCols.
Definition col numCols i := i mod numCols.

Definition move_up numCols i := i - numCols.
Definition move_down numCols i := i + numCols.
Definition move_left i := i - 1.
Definition move_right i := i + 1.

Fixpoint repeat_move f (i : nat) dist :=
  match dist with 
  | O => [i]
  | S dist' => i :: repeat_move f (f i) dist'
  end.

Definition grid_get_path numCols i1 i2 :=
  let r1 := row numCols i1 in
  let c1 := col numCols i1 in
  let r2 := row numCols i2 in
  let c2 := col numCols i2 in
  if ((r1 <? r2) && (c1 <? c2))
  then (* move down, right *)
       let p1 := repeat_move (move_down numCols) i1 (r2 - r1) in
       let p2 := repeat_move move_right (i1 + (r2 - r1) * numCols) (c2 - c1) in
       merge_path p1 p2
  else if ((r1 <? r2) && (c1 =? c2))
  then (* move down *)
       repeat_move (move_down numCols) i1 (r2 - r1)
  else if ((r1 <? r2) && (c2 <? c1))
  then (* move down, left *)
       let p1 := repeat_move (move_down numCols) i1 (r2 - r1) in
       let p2 := repeat_move move_left (i1 + (r2 - r1) * numCols) (c1 - c2) in
       merge_path p1 p2
  else if ((r1 =? r2) && (c1 <? c2))
  then (* move right *)
       repeat_move move_right i1 (c2 - c1)
  else if ((r1 =? r2) && (c1 =? c2))
  then (* badly-typed case, i1=i2 *)
       [] 
  else if ((r1 =? r2) && (c2 <? c1))
  then (* move left *)
       repeat_move move_left i1 (c1 - c2)
  else if ((r2 <? r1) && (c1 <? c2))
  then (* move up, right *)
       let p1 := repeat_move (move_up numCols) i1 (r1 - r2) in
       let p2 := repeat_move move_right (i1 - (r1 - r2) * numCols) (c2 - c1) in
       merge_path p1 p2
  else if ((r2 <? r1) && (c1 =? c2))
  then (* move up *)
       repeat_move (move_up numCols) i1 (r1 - r2)
  else if ((r2 <? r1) && (c2 <? c1))
  then (* move up, left *)
       let p1 := repeat_move (move_up numCols) i1 (r1 - r2) in
       let p2 := repeat_move move_left (i1 - (r1 - r2) * numCols) (c1 - c2) in
       merge_path p1 p2
  else (* impossible case - conditionals are exhaustive *)
       [].

(* Running example:
  
   numRows = 3
   numCols = 5
   
   0  1  2  3  4
   5  6  7  8  9
   10 11 12 13 14
*)
Compute (grid_get_path test_nc 2 5).
Compute (grid_get_path test_nc 6 14).
Compute (grid_get_path test_nc 4 14).
Compute (grid_get_path test_nc 13 1).
Compute (grid_get_path test_nc 10 2).
Compute (grid_get_path test_nc 11 1).
Compute (grid_get_path test_nc 6 9).
Compute (grid_get_path test_nc 13 10).

Definition map_to_grid numRows numCols (c : base_ucom (numRows * numCols)) : base_ucom (numRows * numCols) :=
  simple_map c (grid_get_path numCols) (grid_is_in_graph_b numRows numCols).

(* Examples *)
Definition test_grid1 : base_ucom (test_nr * test_nc) := CNOT 2 1.
Compute (map_to_grid test_nr test_nc test_grid1).
Definition test_grid2 : base_ucom (test_nr * test_nc) := CNOT 0 3; CNOT 4 8; CNOT 12 6.
Compute (map_to_grid test_nr test_nc test_grid2).

(* Correctness *)

Lemma grid_is_in_graph_implies_numCols_nonzero : forall numRows numCols i i',
  grid_is_in_graph numRows numCols i i' -> numCols > 0.
Proof.
  intros.
  inversion H; subst.
  all: assert (Hz : 0 < numRows * numCols) by lia.
  all: apply Nat.lt_0_mul' in Hz as [_ ?];
       assumption.
Qed.

Lemma grid_is_in_graph_valid : forall numRows numCols, 
  valid_graph (numRows * numCols) (grid_is_in_graph numRows numCols).
Proof.
  intros.
  repeat split; inversion H; subst; try assumption; try lia.
  all: apply grid_is_in_graph_implies_numCols_nonzero in H;
       lia.
Qed.

Lemma move_up_valid_path : forall i dist numRows numCols,
  numCols > 0 -> dist > 0 ->
  i < numRows * numCols ->
  dist * numCols <= i ->
  valid_path i (i - dist * numCols)
    (grid_is_in_graph numRows numCols)
    (repeat_move (move_up numCols) i dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent i.
  induction dist.
  - intros.
    rewrite Nat.mul_1_l.
    simpl. unfold move_up.
    repeat split; repeat constructor; try lia.
    remember (i - numCols) as x.
    replace i with (x + numCols) by lia.
    constructor; lia.
  - intros.
    simpl in *; unfold move_up in *.
    apply valid_path_extend_path with (a:=i - numCols). 
    lia.
    left. 
    remember (i - numCols) as x.
    replace i with (x + numCols) by lia.
    constructor; lia. 
    rewrite Nat.sub_add_distr.
    apply IHdist; lia.
Qed.

Lemma move_down_valid_path : forall i dist numRows numCols,
  numCols > 0 -> dist > 0 ->
  i + dist * numCols < numRows * numCols ->
  valid_path i (i + dist * numCols)
    (grid_is_in_graph numRows numCols)
    (repeat_move (move_down numCols) i dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent i.
  induction dist.
  - intros.
    rewrite Nat.mul_1_l.
    simpl. unfold move_down.
    repeat split; repeat constructor; lia.
  - intros.
    simpl in *; unfold move_down in *.
    apply valid_path_extend_path with (a:=i + numCols).
    lia.
    left; constructor; lia.
    rewrite plus_assoc.
    apply IHdist; lia.
Qed.

Lemma move_left_valid_path : forall i dist numRows numCols,
  numCols > 0 -> dist > 0 ->
  i < numRows * numCols ->
  dist <= i ->
  valid_path i (i - dist)
    (grid_is_in_graph numRows numCols)
    (repeat_move move_left i dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent i.
  induction dist.
  - intros.
    simpl. unfold move_left.
    repeat split; repeat constructor; try lia.
    remember (i - 1) as x.
    replace i with (x + 1) by lia.
    constructor; lia.
  - intros.
    simpl in *; unfold move_left in *.
    apply valid_path_extend_path with (a:=i - 1). 
    lia.
    left.
    remember (i - 1) as x.
    replace i with (x + 1) by lia.
    constructor; lia. 
    replace (i - S (S dist)) with (i - 1 - S dist) by lia.
    apply IHdist; lia.
Qed.

Lemma move_right_valid_path : forall i dist numRows numCols,
  numCols > 0 -> dist > 0 ->
  i + dist < numRows * numCols ->
  valid_path i (i + dist)
    (grid_is_in_graph numRows numCols)
    (repeat_move move_right i dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent i.
  induction dist.
  - intros.
    simpl. unfold move_right.
    repeat split; repeat constructor; lia.
  - intros.
    simpl in *; unfold move_right in *.
    apply valid_path_extend_path with (a:=i + 1). 
    lia. 
    left; constructor; lia.
    replace (i + S (S dist)) with (i + 1 + S dist) by lia.
    apply IHdist; lia.
Qed.

Lemma not_in_interior_move_up : forall n1 n2 dist numCols,
  numCols <> 0 -> dist > 0 ->
  dist * numCols <= n1 ->
  col numCols n1 <> col numCols n2 ->
  not_in_interior n2 (repeat_move (move_up numCols) n1 dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent n1.
  induction dist; unfold col, move_up in *; simpl in *.
  - intros. constructor. 
    do 2 rewrite Nat.mod_eq in H2; try assumption.
    intros F. 
    contradict H2; subst; reflexivity.
  - intros. constructor.
    do 2 rewrite Nat.mod_eq in H2; try assumption.
    intros F. 
    contradict H2; subst; reflexivity.
    apply IHdist; try lia.
    rewrite <- (Nat.add_0_r (n1 - numCols)).
    rewrite <- (Nat.mod_same numCols); try assumption.
    rewrite Nat.add_mod_idemp_r; try assumption.
    replace (n1 - numCols + numCols) with n1 by lia.
    assumption.
Qed.

Lemma not_in_interior_move_down : forall n1 n2 dist numCols,
  numCols <> 0 -> dist > 0 ->
  col numCols n1 <> col numCols n2 ->
  not_in_interior n2 (repeat_move (move_down numCols) n1 dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent n1.
  induction dist; unfold col, move_down in *; simpl in *.
  - intros. constructor. 
    do 2 rewrite Nat.mod_eq in H1; try assumption.
    intros F. 
    contradict H1; subst; reflexivity.
  - intros. constructor.
    do 2 rewrite Nat.mod_eq in H1; try assumption.
    intros F. 
    contradict H1; subst; reflexivity.
    apply IHdist; try lia.
    rewrite <- Nat.add_mod_idemp_r; try assumption.
    rewrite Nat.mod_same; try assumption.
    rewrite Nat.add_0_r; assumption.
Qed.

(* TODO: fill in admitted facts about mod/divide *)
Lemma grid_get_path_valid : forall numRows numCols, 
  get_path_valid (numRows * numCols) 
                 (grid_get_path numCols) 
                 (grid_is_in_graph numRows numCols).
Proof.
  intros numRows numCols n1 n2 Hn1 Hn2 Hn1n2.
  assert (0 < numRows * numCols) by lia.
  apply Nat.lt_0_mul' in H as [_ H].
  unfold grid_get_path.
  (* some aux. lemmas *)
  assert (Haux1 : (row numCols n1 - row numCols n2) * numCols <= n1).
  { unfold row.
    rewrite Nat.mul_sub_distr_r.
    rewrite Nat.mul_comm. 
    assert (numCols * (n1 / numCols) <= n1) by (apply Nat.mul_div_le; lia). 
    lia. }
  bdestruct_all; simpl.
  - (* move down, right *)
    remember (row numCols n2 - row numCols n1) as distR.
    remember (col numCols n2 - col numCols n1) as distC.
    eapply valid_path_merge_path.
    apply move_down_valid_path; try assumption; try lia.
    admit. (* n1 + distR * numCols < numRows * numCols *)
    replace n2 with (n1 + distR * numCols + distC).
    apply move_right_valid_path; try assumption; try lia.
    admit. (* n1 + distR * numCols + distC < numRows * numCols *)
    admit. (* n1 + distR * numCols + distC = n2 *)
    apply not_in_interior_move_down; try lia.
  - (* move down, left *)
    remember (row numCols n2 - row numCols n1) as distR.
    remember (col numCols n1 - col numCols n2) as distC.
    eapply valid_path_merge_path.
    apply move_down_valid_path; try assumption; try lia.
    admit. (* n1 + distR * numCols < numRows * numCols *)
    replace n2 with (n1 + distR * numCols - distC).
    apply move_left_valid_path; try assumption; try lia.   
    admit. (* n1 + distR * numCols < numRows * numCols *)
    admit. (* distC <= n1 + distR * numCols *)
    admit. (* n1 + distR * numCols - distC = n2 *)
    apply not_in_interior_move_down; try lia.
  - (* move down *)
    remember (row numCols n2 - row numCols n1) as distR.
    replace n2 with (n1 + distR * numCols).
    apply move_down_valid_path; try assumption; try lia.
    admit. (* n1 + distR * numCols < numRows * numCols *)
    { (* n1 + distR * numCols = n2 *)
      subst distR; unfold row, col in *.
      do 2 rewrite Nat.mod_eq in H4; try lia.
      rewrite Nat.mul_sub_distr_r.
      rewrite Nat.add_sub_assoc.
      rewrite Nat.add_comm.
      rewrite <- Nat.add_sub_assoc.
      rewrite (Nat.mul_comm _ (n1 / numCols)) in H4.
      rewrite (Nat.mul_comm _ (n2 / numCols)) in H4.
      rewrite H4.
      rewrite Nat.add_sub_assoc.
      rewrite minus_plus.
      reflexivity.
      rewrite Nat.mul_comm; apply Nat.mul_div_le; lia.
      rewrite Nat.mul_comm; apply Nat.mul_div_le; lia.
      rewrite (Nat.mul_comm (n1 / numCols)).
      rewrite (Nat.mul_comm (n2 / numCols)).
      apply Nat.mul_le_mono_l; assumption. }
  - (* move up, right *)
    remember (row numCols n1 - row numCols n2) as distR.
    remember (col numCols n2 - col numCols n1) as distC.
    eapply valid_path_merge_path.
    apply move_up_valid_path; try assumption; try lia.
    replace n2 with (n1 - distR * numCols + distC).
    apply move_right_valid_path; try assumption; try lia.   
    admit. (* n1 - distR * numCols + distC < numRows * numCols *)
    admit. (* n1 - distR * numCols + distC = n2 *)
    apply not_in_interior_move_up; try assumption; try lia.
  - (* move right *)
    remember (col numCols n2 - col numCols n1) as distC.
    replace n2 with (n1 + distC).
    apply move_right_valid_path; try assumption; try lia.
    admit. (* n1 + distC < numRows * numCols *)
    { (* n1 + distC = n2 *)
      subst distC; unfold row, col in *. 
      rewrite Nat.add_sub_assoc; try assumption.
      rewrite Nat.add_comm.
      rewrite <- Nat.add_sub_assoc.
      2: { rewrite Nat.mod_eq; lia. }
      rewrite Nat.mod_eq; try lia.
      rewrite Nat.mod_eq; try lia.
      rewrite H5.
      remember (numCols * (n2 / numCols)) as x.
      assert (x <= n1).
      { subst x. rewrite <- H5. apply Nat.mul_div_le. lia. }
      assert (x <= n2).
      { subst x. apply Nat.mul_div_le. lia. }
      lia. }
  - (* move up, left *)
    remember (row numCols n1 - row numCols n2) as distR.
    remember (col numCols n1 - col numCols n2) as distC.
    eapply valid_path_merge_path.
    apply move_up_valid_path; try assumption; try lia.
    replace n2 with (n1 - distR * numCols - distC).
    apply move_left_valid_path; try assumption; try lia.   
    admit. (* distC <= n1 - distR * numCols *)
    admit. (* n1 - distR * numCols - distC = n2 *)
    apply not_in_interior_move_up; try assumption; try lia. 
  - (* move left *)
    remember (col numCols n1 - col numCols n2) as distC.
    replace n2 with (n1 - distC).
    apply move_left_valid_path; try assumption; try lia.
    subst. unfold col. rewrite Nat.mod_eq; lia.
    { (* n1 - distC = n2 *)
      subst distC; unfold row, col in *. 
      rewrite Nat.mod_eq; try lia.
      rewrite Nat.mod_eq; try lia.
      rewrite H5.
      remember (numCols * (n2 / numCols)) as x.
      assert (x <= n2).
      { subst x. apply Nat.mul_div_le. lia. }
      assert (n2 <= n1).
      { do 2 rewrite Nat.mod_eq in H1; try lia.
        rewrite H5 in H1.
        rewrite <- Heqx in H1.
        assert (x <= n1).
        subst. rewrite <- H5. apply Nat.mul_div_le. lia.
        lia. }
      lia. }
  - (* move up *)
    remember (row numCols n1 - row numCols n2) as distR.
    replace n2 with (n1 - distR * numCols).
    apply move_up_valid_path; try assumption; try lia.
    { (* n1 - distR * numCols = n2 *)
      subst distR; unfold row, col in *.
      do 2 rewrite Nat.mod_eq in H4; try lia.
      rewrite Nat.mul_sub_distr_r.
      rewrite (Nat.mul_comm (n1 / numCols)).
      rewrite (Nat.mul_comm (n2 / numCols)).
      assert (numCols * (n1 / numCols) <=  n1).
      apply Nat.mul_div_le. lia.
      replace (numCols * (n1 / numCols)) with (n1 - (n1 - numCols * (n1 / numCols))) by lia.
      rewrite H4.
      assert (numCols * (n2 / numCols) <=  n2).
      apply Nat.mul_div_le. lia.
      assert (n2 <= n1).
      assert (numCols * (n2 / numCols) <= numCols * (n1 / numCols)). 
      apply Nat.mul_le_mono_l; assumption.
      lia.
      lia. }
  - (* badly-typed case *)
    contradict Hn1n2.
    unfold col, row in *.
    do 2 rewrite Nat.mod_eq in H4; try lia.
    rewrite H5 in H4. 
    rewrite <- (Nat.sub_add (numCols * (n2 / numCols)) n1).
    rewrite H4.
    rewrite Nat.sub_add.
    reflexivity.
    rewrite Nat.mul_div_le; lia.
    rewrite <- H5.
    rewrite Nat.mul_div_le; lia.
Admitted.

Lemma grid_is_in_graph_reflects : forall numRows numCols n1 n2,
  reflect (grid_is_in_graph numRows numCols n1 n2) (grid_is_in_graph_b numRows numCols n1 n2).
Proof.
  intros.
  unfold grid_is_in_graph_b.
  bdestruct_all; simpl; subst; constructor. 
  all: try (constructor; assumption). 
  all: try (intros contra; inversion contra; subst). 
  all: try (contradict H0; lia).
Qed.

Lemma map_to_grid_sound : forall numRows numCols (c : base_ucom (numRows * numCols)),
  uc_well_typed c -> map_to_grid numRows numCols c ≡ c.
Proof.
  intros.
  unfold map_to_grid.
  eapply simple_map_sound.
  apply grid_is_in_graph_valid.
  apply grid_get_path_valid.
  apply grid_is_in_graph_reflects.
  assumption.
Qed.

Lemma map_to_grid_respects_constraints : forall numRows numCols (c : base_ucom (numRows * numCols)),
  uc_well_typed c -> respects_constraints (grid_is_in_graph numRows numCols) (map_to_grid numRows numCols c).
Proof.
  intros.
  unfold map_to_grid.
  eapply simple_map_respect_constraints.
  apply grid_is_in_graph_valid.
  apply grid_get_path_valid.
  apply grid_is_in_graph_reflects.
  assumption.
Qed.

End Grid.

(******************************)
(** Tenerife Mapping Example **)
(******************************)

Module Tenerife.

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

Definition map_to_tenerife (c : base_ucom 5) : base_ucom 5 :=
  simple_map c tenerife_get_path tenerife_is_in_graph_b.

(* Examples *)
Definition test_tenerife1 : base_ucom 5 := CNOT 1 2.
Compute (map_to_tenerife test_tenerife1).
Definition test_tenerife2 : base_ucom 5 := CNOT 3 0.
Compute (map_to_tenerife test_tenerife2).
Definition test_tenerife3 : base_ucom 5 := CNOT 0 2; X 3; CNOT 4 1; X 2; CNOT 3 2.
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

Lemma map_to_tenerife_sound : forall (c : base_ucom 5),
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

Lemma map_to_tenerife_respects_constraints : forall (c : base_ucom 5),
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

End Tenerife.