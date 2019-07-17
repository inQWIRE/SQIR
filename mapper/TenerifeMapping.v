Require Import Compose.
Require Import Equivalences.
Require Import List.
Open Scope ucom.

Local Close Scope C_scope.
Local Close Scope R_scope.


(******************************)
(** Tenerife Mapping Example **)
(******************************)

(* Map to IBM's 5-qubit Tenerife machine. The connectivity graph for the 
   Tenerife machine is depicted here: https://github.com/Qiskit/ibmq-device-information/blob/master/backends/tenerife/V1/version_log.md 

   Ideally we would consider mapping to an arbitrary connectivity graph.
   But for now we'll be using a hardcoded graph because we haven't found an
   easy-to-use (and easy-to-extract) graph library for Coq. We've tried to
   keep the structure of the code general so we can use it as a guideline
   for future development. *)

(* CNOT connectivity between qubits. *)
Definition cnot_graph : list (nat * nat) := (1, 0) :: (2, 0) :: (2, 1) :: (3, 2) :: (3, 4) :: (4, 2) :: [].

(* Find a path to put the control adjacent to the target. This function 
   is (disgustingly) hardcoded for our harcoded graph, but should in general
   be a shortest path algorithm. *)
Definition find_path n1 n2 :=
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

(* Loose formalism for describing paths (or rather walks) in a graph.
   A proper graph library would have more precise definitions. *)

Inductive begins_with : nat -> list nat -> Prop :=
  | begins_with_cons : forall h t, begins_with h (h :: t).

Inductive ends_with : nat -> list nat -> Prop :=
  | end_with_single_elmt : forall x, ends_with x [x]
  | ends_with_cons : forall x h t, ends_with x t -> ends_with x (h :: t).

Inductive valid_walk : list nat -> list (nat * nat) -> Prop :=
  | valid_walk_two_elmts : forall n1 n2 g, 
      In (n1, n2) g \/ In (n2, n1) g -> valid_walk (n1 :: n2 :: []) g
  | valid_walk_two_cons : forall n1 n2 t g, 
      In (n1, n2) g \/ In (n2, n1) g -> valid_walk (n2 :: t) g -> valid_walk (n1 :: n2 :: t) g.

Definition is_path p n1 n2 := 
  (begins_with n1 p) /\ (ends_with n2 p) /\ (valid_walk p cnot_graph).

(* This proof is ugly because of our hardcoded definition of find_path. *)
Lemma find_path_returns_path : forall n1 n2, 
  n1 <> n2 -> n1 < 5 -> n2 < 5 -> 
  is_path (find_path n1 n2) n1 n2.
Proof.
  intros.
  destruct n1.
  destruct n2; [| destruct n2; [| destruct n2 ; [| destruct n2; [| destruct n2]]]];
  try contradiction;
  try (contradict H1; lia);
  simpl; repeat split;
  try (left; repeat constructor; reflexivity);
  try (right; repeat constructor; reflexivity).
  destruct n1.
  destruct n2; [| destruct n2; [| destruct n2 ; [| destruct n2; [| destruct n2]]]];
  try contradiction;
  try (contradict H1; lia);
  simpl; repeat split;
  try (left; repeat constructor; reflexivity);
  try (right; repeat constructor; reflexivity).
  destruct n1.
  destruct n2; [| destruct n2; [| destruct n2 ; [| destruct n2; [| destruct n2]]]];
  try contradiction;
  try (contradict H1; lia);
  simpl; repeat split;
  try (left; repeat constructor; reflexivity);
  try (right; repeat constructor; reflexivity).
  destruct n1.
  destruct n2; [| destruct n2; [| destruct n2 ; [| destruct n2; [| destruct n2]]]];
  try contradiction;
  try (contradict H1; lia);
  simpl; repeat split;
  try (left; repeat constructor; reflexivity);
  try (right; repeat constructor; reflexivity).
  destruct n1.
  destruct n2; [| destruct n2; [| destruct n2 ; [| destruct n2; [| destruct n2]]]];
  try contradiction;
  try (contradict H1; lia);
  simpl; repeat split;
  try (left; repeat constructor; reflexivity);
  try (right; repeat constructor; reflexivity).
  contradict H0; lia.
Qed.

Definition beq_tup t t' := 
  match t, t' with
  | (n1, n2), (n1', n2') => (n1 =? n1') && (n2 =? n2')
  end.

Lemma beq_tup_refl : forall t t',
  beq_tup t t' = true <-> t = t'.
Proof.
  intros; unfold beq_tup.
  destruct t; destruct t'.
  split; intros.
  - apply andb_true_iff in H as [H1 H2].
    apply Nat.eqb_eq in H1; inversion H1; subst.
    apply Nat.eqb_eq in H2; inversion H2; subst.
    reflexivity.
  - apply andb_true_iff. 
    split; inversion H; subst; apply Nat.eqb_refl.
Qed.

Lemma tup_in_cnot_graph : forall n1 n2,
  existsb (beq_tup (n1, n2)) cnot_graph = true <-> In (n1, n2) cnot_graph.
Proof.
  intros.
  split; intros.
  - apply existsb_exists in H.
    destruct H; destruct x; destruct H as [H1 H2].
    apply beq_tup_refl in H2.
    inversion H2; subst.
    assumption.
  - apply existsb_exists.
    exists (n1, n2).
    split.
    assumption.
    apply beq_tup_refl; reflexivity.
Qed.

Inductive respects_tenerife_undirected : ucom 5 -> Prop :=
  | uTen_skip : respects_tenerife_undirected uskip
  | uTen_seq : forall c1 c2, 
      respects_tenerife_undirected c1 -> 
      respects_tenerife_undirected c2 -> 
      respects_tenerife_undirected (c1; c2)
  | uTen_app_u : forall (u : Unitary 1) n, respects_tenerife_undirected (uapp1 u n)
  | uTen_app_cnot : forall n1 n2, 
      (In (n1, n2) cnot_graph) \/ (In (n2, n1) cnot_graph) -> 
      respects_tenerife_undirected (CNOT n1 n2).

Inductive respects_tenerife : ucom 5 -> Prop :=
  | Ten_skip : respects_tenerife uskip
  | Ten_seq : forall c1 c2, 
      respects_tenerife c1 -> 
      respects_tenerife c2 -> 
      respects_tenerife (c1; c2)
  | Ten_app_u : forall (u : Unitary 1) n, respects_tenerife (uapp1 u n)
  | Ten_app_cnot : forall n1 n2, 
      In (n1, n2) cnot_graph -> respects_tenerife (CNOT n1 n2).


(** Version 1: Without logical <-> physical qubit mapping **)

Fixpoint do_cnot_along_path p : ucom 5 :=
  match p with
  | [] => uskip (* bad input case *)
  | n1 :: t => match t with 
             | [] => uskip (* bad input case *)
             | [n2] => CNOT n1 n2
             | n2 :: _ => SWAP n1 n2 ; do_cnot_along_path t ; SWAP n1 n2
             end
  end.

(* At this point all CNOTs should be between adjacent qubits, but
   they may not respect the direction of the edges in the connectivity
   graph. We can fix this by insert Hadamard gates before and after
   each offending CNOT. *)
Fixpoint fix_cnots (c : ucom 5) :=
  match c with
  | c1; c2 => fix_cnots c1; fix_cnots c2
  | uapp2 U_CNOT n1 n2 => 
      if existsb (beq_tup (n1, n2)) cnot_graph
      then CNOT n1 n2
      else H n1; H n2; CNOT n2 n1; H n1; H n2
  | _ => c
  end.

Fixpoint map_to_tenerife (c : ucom 5) :=
  match c with
  | c1; c2 => map_to_tenerife c1 ; map_to_tenerife c2
  | uapp2 U_CNOT n1 n2 => 
      let p := find_path n1 n2 in
      let c := do_cnot_along_path p in
      fix_cnots c
  | uapp1 u n => uapp1 u n
  | _ => c
  end.

(* Small examples *)
Definition test1 : ucom 5 := CNOT 0 2; X 3; CNOT 4 1; X 2; CNOT 3 2.
Definition test2 : ucom 5 := CNOT 4 1; CNOT 3 0; CNOT 3 2; CNOT 3 0; CNOT 2 1.
Compute (map_to_tenerife test1).
Compute (map_to_tenerife test2).
 
Lemma swap_cnot_general : forall {dim} a b c,
  (* well-typedness constraints *)
  a < dim -> b < dim -> c < dim ->
  a <> b -> b <> c -> a <> c ->
  (* main equivalence *)
  @uc_equiv dim (SWAP a b; CNOT b c; SWAP a b) (CNOT a c).
Proof. Admitted.

Lemma do_cnot_along_path_sound : forall n1 n2,
  n1 <> n2 -> n1 < 5 -> n2 < 5 ->
  CNOT n1 n2 ≡ do_cnot_along_path (find_path n1 n2).
Proof.
  intros.
  specialize (find_path_returns_path n1 n2 H H0 H1) as [H_l_begins [H_l_ends H_l_valid]].
  induction (find_path n1 n2); inversion H_l_begins; subst.
  clear H_l_begins.  
  destruct l.
  - inversion H_l_ends; subst. 
    contradict H; reflexivity.
    inversion H4.
  - simpl.
    destruct l.
    + inversion H_l_ends; subst.
      inversion H4; subst.
      reflexivity.
      inversion H5.
    +
 Admitted.

Lemma do_cnot_along_path_respects_undirected : forall n1 n2,
  respects_tenerife_undirected (do_cnot_along_path (find_path n1 n2)).
Proof.
Admitted.

Lemma H_swaps_CNOT : forall {dim} m n,
  @uc_equiv dim (CNOT m n) (H m; H n; CNOT n m; H m; H n).
Proof. Admitted.

Lemma fix_cnots_sound : forall c,
  c ≡ fix_cnots c.
Proof.
  intros.
  induction c; try reflexivity.
  - simpl. apply useq_congruence; assumption. 
  - unfold fix_cnots.
    destruct (existsb (beq_tup (n, n0)) cnot_graph);
    dependent destruction u.
    + reflexivity.
    + apply H_swaps_CNOT.
Qed.

Lemma fix_cnots_mapped : forall c,
  respects_tenerife_undirected c -> respects_tenerife (fix_cnots c).
Proof.
  intros.
  induction H.
  - constructor.
  - constructor. 
    apply IHrespects_tenerife_undirected1.
    apply IHrespects_tenerife_undirected2.
  - constructor.
  - destruct H. 
    + assert (existsb (beq_tup (n1, n2)) cnot_graph = true). 
      { apply tup_in_cnot_graph; assumption. }
      simpl; simpl in H0.
      rewrite H0.
      constructor; assumption.
    + remember (existsb (beq_tup (n1, n2)) cnot_graph) as e.
      symmetry in Heqe; destruct e. 
      assert (In (n1, n2) cnot_graph).
      { apply tup_in_cnot_graph; assumption. }
      simpl; simpl in Heqe.
      rewrite Heqe.
      constructor; assumption.
      simpl; simpl in Heqe.
      rewrite Heqe.
      repeat apply Ten_seq; try apply Ten_app_u.
      constructor.
      assumption.
Qed.

Lemma map_to_tenerife_sound : forall c, 
  uc_well_typed c -> c ≡ map_to_tenerife c.
Proof.
  intros.
  induction c; try reflexivity.
  - inversion H; subst. 
    simpl; apply useq_congruence. 
    apply IHc1; assumption.
    apply IHc2; assumption.
  - inversion H; subst. 
    dependent destruction u; simpl.
    rewrite <- fix_cnots_sound.
    rewrite <- do_cnot_along_path_sound; try assumption.
    reflexivity.
Qed.

Lemma map_to_tenerife_correct : forall c,
  respects_tenerife (map_to_tenerife c).
Proof.
  intros.
  induction c; try constructor; try assumption.
  dependent destruction u; simpl.
  apply fix_cnots_mapped.
  apply do_cnot_along_path_respects_undirected.
Qed.


(** Version 2: With logical <-> physical qubit mapping **)

(* Type for representing a logical <-> physical qubit mapping with dim 
   physical qubits. *)
Definition qmap (dim : nat) : Type := (nat -> nat) * (nat -> nat).

Definition l2p {dim} (m : qmap dim) q :=
  match m with
  | (m, _) => m q
  end.

Definition p2l {dim} (m : qmap dim) q :=
  match m with
  | (_, m) => m q
  end.

(* swap the logical qubits associated with physical qubits qphys1 and qphys2 *)
Definition swap_in_map {dim} (m : qmap dim) qphys1 qphys2 : qmap dim :=
  match m with
  | (m1, m2) => 
      let qlog1 := m2 qphys1 in
      let qlog2 := m2 qphys2 in
      let m1' q := if q =? qlog1 then qphys2
                   else if q =? qlog2 then qphys1 
                   else m1 q in
      let m2' q := if q =? qphys1 then qlog2 
                   else if q =? qphys2 then qlog1 
                   else m2 q in
      (m1', m2')
  end.

(* There may be a more elegant way to write this *)
Definition qmap_well_formed {dim} (m : qmap dim) := forall x y, 
  (x < dim /\ l2p m x = y) <-> (y < dim /\ p2l m y = x).

Lemma l2p_p2l_inverse : forall {dim} (m : qmap dim) q,
  qmap_well_formed m -> q < dim -> l2p m (p2l m q) = q.
Proof.
  unfold qmap_well_formed; intros.
  destruct m; simpl in *.
  specialize (H (n0 q) q) as [H1 H2].
  apply H2.
  split; try assumption; reflexivity.
Qed.

Lemma p2l_l2p_inverse : forall {dim} (m : qmap dim) q,
  qmap_well_formed m -> q < dim -> p2l m (l2p m q) = q.
Proof.
  unfold qmap_well_formed; intros.
  destruct m; simpl in *.
  specialize (H q (n q)) as [H1 H2].
  apply H1.
  split; try assumption; reflexivity.
Qed.    

Fixpoint path_to_swaps l (m : qmap 5) : (ucom 5 * qmap 5) :=
  match l with
  | [] => (uskip, m) (* bad input case *)
  | n1 :: t => match t with
             | [] => (uskip, m) (* bad input case *)
             | [n2] => (uskip, m) (* normal termination *)
             | n2 :: _ => let (c, m') := path_to_swaps t (swap_in_map m n1 n2) in
                        (SWAP n1 n2 ; c, m')
             end
  end.

(* Input:  program c and mapping m between logical and physical qubits
   Output: program c' that respects the Tenerife topology and resulting
           mapping m' between logical and physical qubits. 

   NOTE: The input program references logical qubits, and the output
   program references physical qubits. The soundness property says that
   the denotation of c is equivalent to the denotation of c', given 
   the reordering described by m' *)
Fixpoint map_to_tenerife_v2 (c : ucom 5) (m : qmap 5) :=
  match c with
  | c1; c2 => let (c1', m') := map_to_tenerife_v2 c1 m in
             let (c2', m'') := map_to_tenerife_v2 c2 m' in
             (c1'; c2', m'')
  | uapp2 U_CNOT n1 n2 => 
      let p := find_path (l2p m n1) (l2p m n2) in
      let (c, m') := path_to_swaps p m in
      let c' := fix_cnots (c; CNOT (l2p m' n1) (l2p m' n2)) in
      (c', m')
  | uapp1 u n => (uapp1 u (l2p m n), m)
  | _ => (c, m)
  end.

(* Small examples *)
Definition trivial_map : qmap 5 := (fun x => x, fun x => x).
Compute (map_to_tenerife_v2 test1 trivial_map).
Compute (map_to_tenerife_v2 test2 trivial_map).
Definition test_map : qmap 5 := 
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
Compute (map_to_tenerife_v2 test1 test_map).
