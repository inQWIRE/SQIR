Require Import QWIRE.Prelim.

(** Specification of CNOT connectivity graph. **)

(* For circuit mapping (SimpleMapping.v) we describe the input architecture
   connectivity graph using two functions:
   - get_path, which returns an undirected path between two nodes in the graph
   - is_in_graph, which indicates whether there is a directed edge between 
     two nodes
   
   Examples of get_path and is_in_graph for particular graphs can be found
   at the end of this file. 

   We use a loose formalism for describing paths in a graph -- a proper graph 
   library would have more precise definitions. We represent a path between n1 
   and n2 as a list of nodes with the following properties:
   1. The path must begin with n1.
   2. The path must end with n2.
   3. For every x and y adjacent in the path, either is_in_graph x y = true
      or is_in_graph y x = true.
   4. For every x and y adjacent in the path, x and y are within bounds
      of the global register and x <> y.
   5. The path does not go through n2 twice.
   Restriction #5 is really just to make the proof easier, we might be
   able to remove it.
*)

(** General defns and proofs, parameterized by is_in_graph **)

Inductive begins_with : nat -> list nat -> Prop :=
  | begins_with_cons : forall h t, begins_with h (h :: t).

Inductive ends_with : nat -> list nat -> Prop :=
  | end_with_single_elmt : forall x, ends_with x [x]
  | ends_with_cons : forall x h t, ends_with x t -> ends_with x (h :: t).

Inductive path_is_in_graph : list nat -> (nat -> nat -> bool) -> Prop :=
  | path_in_graph_two_elmts : forall n1 n2 is_in_graph, 
      (is_in_graph n1 n2 = true) \/ (is_in_graph n2 n1 = true) -> 
      path_is_in_graph (n1 :: n2 :: []) is_in_graph
  | path_in_graph_cons : forall n1 n2 t is_in_graph, 
      (is_in_graph n1 n2 = true) \/ (is_in_graph n2 n1 = true) -> 
      path_is_in_graph (n2 :: t) is_in_graph -> 
      path_is_in_graph (n1 :: n2 :: t) is_in_graph.

Inductive path_well_typed : list nat -> nat -> Prop :=
  | path_well_typed_two_elmts : forall n1 n2 dim, 
      n1 < dim -> n2 < dim -> n1 <> n2 -> 
      path_well_typed (n1 :: n2 :: []) dim
  | path_well_typed_cons : forall n1 n2 t dim, 
      n1 < dim -> n2 < dim -> n1 <> n2 -> 
      path_well_typed (n2 :: t) dim -> 
      path_well_typed (n1 :: n2 :: t) dim.

Inductive not_in_interior : nat -> list nat -> Prop :=
  | not_in_interior_two_elmts : forall n n1 n2,
      n1 <> n -> not_in_interior n (n1 :: n2 :: [])
  | not_in_interior_cons : forall n n1 n2 t,
      n1 <> n -> 
      not_in_interior n (n2 :: t) ->
      not_in_interior n (n1 :: n2 :: t).

Definition valid_path n1 n2 is_in_graph dim p :=
  (begins_with n1 p) 
    /\ (ends_with n2 p) 
    /\ (path_is_in_graph p is_in_graph)
    /\ (path_well_typed p dim)
    /\ (not_in_interior n2 p).

Lemma valid_path_subpath : forall n1 n2 is_in_graph a b p dim,
  valid_path n1 n2 is_in_graph dim (n1 :: a :: b :: p) ->
  valid_path a n2 is_in_graph dim (a :: b :: p).
Proof.
  intros n1 n2 is_in_graph a b p dim H.
  destruct H as [_ [H1 [H2 [H3 H4]]]] .
  repeat split. 
  - inversion H1; assumption.
  - inversion H2; assumption.
  - inversion H3; assumption.
  - inversion H4; assumption.
Qed.

Fixpoint merge_path (p1 : list nat) p2 :=
  match p1 with
  | [] | [_] => p2
  | h :: t => h :: (merge_path t p2)
  end.

Lemma valid_path_extend_path : forall a n1 n2 (is_in_graph : nat -> nat -> bool) dim p,
  n1 <> n2 -> n1 < dim -> n1 <> a ->
  is_in_graph n1 a = true \/ is_in_graph a n1 = true ->
  valid_path a n2 is_in_graph dim p ->
  valid_path n1 n2 is_in_graph dim (n1 :: p).
Proof.
  intros a n1 n2 is_in_graph dim p Hneq Hn1 Hn1a H [H1 [H2 [H3 [H4 H5]]]].
  destruct p.
  inversion H1.
  destruct p.
  inversion H3.
  inversion H1; subst.
  repeat split; constructor; try assumption.
  inversion H4; assumption.
Qed.  

Lemma valid_path_merge_path : forall a b c is_in_graph dim p1 p2, 
  valid_path a b is_in_graph dim p1 -> 
  valid_path b c is_in_graph dim p2 -> 
  not_in_interior c p1 ->
  valid_path a c is_in_graph dim (merge_path p1 p2).
Proof.
  intros a b c f dim p1 p2 Hp1 Hp2 NIp1.
  (* Because p1 and p2 are valid paths, we know something about their
     structure. Invert some hypotheses here for use later. *)
  destruct p1; [| destruct p1].
  1, 2: inversion NIp1.
  destruct Hp1 as [H1 [H2 [H3 [H4 H5]]]].
  inversion H1; subst; clear H1.
  destruct p2.
  destruct Hp2 as [H _]; inversion H.
  destruct Hp2 as [H [H1 [H6 [H7 H8]]]].
  inversion H; subst; clear H.
  (* now a standard proof by induction *)
  generalize dependent n0.
  generalize dependent n.
  induction p1.
  - intros.
    inversion H2; subst. inversion H9; subst.
    2: inversion H10.
    inversion H3; subst.
    2: inversion H13.
    inversion H4; subst.
    2: inversion H16.
    simpl.
    repeat split; constructor; try assumption.
    inversion NIp1; assumption.
  - intros.
    replace (merge_path (n :: n0 :: a :: p1) (n1 :: p2)) with (n :: (merge_path (n0 :: a :: p1) (n1 :: p2))) by reflexivity.
    apply valid_path_extend_path with (a:=n0).
    inversion NIp1; assumption.
    inversion H4; assumption.
    inversion H4; assumption.
    inversion H3; assumption.
    apply IHp1.
    inversion H2; assumption.
    inversion H3; assumption.
    inversion H4; assumption.
    inversion H5; assumption.
    inversion NIp1; assumption.
Qed.

Fixpoint check_path p n2 is_in_graph dim :=
  match p with
  | _ :: [] | [] => false
  | x :: y :: [] => 
      (is_in_graph x y || is_in_graph y x) (* path_is_in_graph *)
      && (x <? dim) && (y <? dim) && negb (x =? y) (* path_well_typed *)
      && (y =? n2) (* ends_with *)
  | x :: ((y :: _) as t) =>
      (is_in_graph x y || is_in_graph y x) (* path_is_in_graph *)
      && (x <? dim) && (y <? dim) && negb (x =? y) (* path_well_typed *)
      && negb (x =? n2) && negb (y =? n2) (* not_in_interior *)
      && check_path t n2 is_in_graph dim
  end.

Fixpoint foralln (f : nat -> bool) n :=
  match n with
  | 0 => true
  | S n' => f n' && foralln f n'
  end.

Lemma foralln_correct : forall f n, foralln f n = true -> (forall x, x < n -> f x = true).
Proof. 
  intros f n H x Hx.
  induction n; try lia.
  simpl in H.
  apply andb_prop in H as [H1 H2].
  bdestruct (x =? n).
  subst. assumption.
  apply IHn.
  assumption.
  lia.
Qed.

Definition check_graph (dim : nat) (get_path : nat -> nat -> list nat) (is_in_graph : nat -> nat -> bool) :=
  let f n1 n2 := if n1 =? n2 then true 
                 else match get_path n1 n2 with
                      | (x :: _) as p => (x =? n1) (* starts_with *)
                            && check_path (get_path n1 n2) n2 is_in_graph dim 
                      | _ => false end in
  foralln (fun n1 => foralln (fun n2 => f n1 n2) dim) dim.

Ltac destruct_bool_goals :=
  repeat match goal with
  | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
  | H : _ || _ = true |- _ => apply orb_prop in H
  | H : _ <? _ = true |- _ => apply Nat.ltb_lt in H
  | H : _ =? _ = false |- _ => apply beq_nat_false in H 
  | H : _ =? _ = true |- _ => apply beq_nat_true in H 
  | H : negb _ = true |- _ => apply negb_true_iff in H
  end.

Lemma check_path_correct : forall n1 n2 is_in_graph dim p,
  check_path (n1 :: p) n2 is_in_graph dim = true ->
  valid_path n1 n2 is_in_graph dim (n1 :: p).
Proof.
  intros n1 n2 is_in_graph dim p H.
  destruct p.
  inversion H.
  generalize dependent n.
  generalize dependent n1.
  induction p; intros n n1 H.
  simpl in H; destruct_bool_goals; subst.
  repeat split; constructor; try assumption.
  constructor.
  replace (check_path (n :: n1 :: a :: p) n2 is_in_graph dim = true) 
    with (((is_in_graph n n1 || is_in_graph n1 n)
           && (n <? dim) && (n1 <? dim) && negb (n =? n1)
           && negb (n =? n2) && negb (n1 =? n2)
           && check_path (n1 :: a :: p) n2 is_in_graph dim) = true) 
    in H by reflexivity.
  destruct_bool_goals.
  apply valid_path_extend_path with (a:=n1); try assumption.
  apply IHp.
  assumption.
Qed.

Lemma check_graph_correct : forall (dim : nat) (get_path : nat -> nat -> list nat) (is_in_graph : nat -> nat -> bool),
  check_graph dim get_path is_in_graph = true ->
  (forall n1 n2, n1 < dim -> n2 < dim -> n1 <> n2 ->
            valid_path n1 n2 is_in_graph dim (get_path n1 n2)).
Proof.
  intros dim get_path is_in_graph H n1 n2 Hn1 Hn2 Hneq.
  unfold check_graph in H.
  apply foralln_correct with (x:=n1) in H; try assumption.
  apply foralln_correct with (x:=n2) in H; try assumption.
  bdestructΩ (n1 =? n2).
  remember (get_path n1 n2) as p; clear Heqp.
  destruct p.
  inversion H.
  bdestruct (n =? n1). 
  2: inversion H.
  rewrite andb_true_l in H.
  subst.
  apply check_path_correct.
  assumption.
Qed.

(** Graph type for mapping; contains defns for get_path and is_in_graph. **)

Module Type ConnectivityGraph.

(* number of nodes (qubits) *)
Parameter dim : nat.

Parameter get_path : nat -> nat -> list nat.

Parameter is_in_graph : nat -> nat -> bool.

Axiom get_path_valid : forall n1 n2, 
  n1 < dim -> n2 < dim -> n1 <> n2 -> valid_path n1 n2 is_in_graph dim (get_path n1 n2).

End ConnectivityGraph.


(*************************)
(**     LNN Example     **)
(*************************)

Module LNN.

(* Creates a graph of size dim where element i is connected to (i-1) and (i+1),
   but element 0 is not connected to element (dim-1). *)

Definition is_in_graph dim n1 n2 :=
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

Definition get_path n1 n2 :=
  if n1 <? n2
  then move_right n1 (n2 - n1)
  else if n2 <? n1
       then move_left n1 (n1 - n2)
       else [] (* badly-typed case, n1=n2 *).

(* Examples *)
Compute (get_path 2 5).
Compute (get_path 6 1).

Lemma get_path_valid : forall dim n1 n2, 
  n1 < dim -> n2 < dim -> n1 <> n2 -> valid_path n1 n2 (is_in_graph dim) dim (get_path n1 n2).
Proof.
  intros dim n1 n2 Hn1 Hn2 Hn1n2.
  unfold get_path, LNN.get_path.
  bdestruct_all. 
  - assert (move_right_valid_path : forall n dist, 
      dist > 0 -> n + dist < dim -> 
      valid_path n (n + dist) (is_in_graph dim) dim (move_right n dist)).
    { intros. 
      destruct dist; try lia. 
      generalize dependent n.
      induction dist; simpl in *.
      - intros. 
        repeat split; repeat constructor; try lia.
        unfold is_in_graph, LNN.is_in_graph. 
        bdestruct_all; reflexivity.
      - intros. 
        apply valid_path_extend_path with (a:=n + 1); try lia.
        left.
        unfold is_in_graph, LNN.is_in_graph. 
        bdestruct_all; reflexivity.
        replace (n + S (S dist)) with (n + 1 + (S dist)) by lia.
        apply IHdist; lia. }
    replace n2 with (n1 + (n2 - n1)) at 1 by lia.
    apply move_right_valid_path; lia.
  - assert (move_left_valid_path : forall n dist, 
      dist > 0 -> dist <= n -> n < dim ->
      valid_path n (n - dist) (is_in_graph dim) dim (move_left n dist)).
    { intros. 
      destruct dist; try lia. 
      generalize dependent n.
      induction dist; simpl in *.
      - intros. 
        repeat split; repeat constructor; try lia.
        unfold is_in_graph, LNN.is_in_graph. 
        bdestruct_all; reflexivity.
      - intros. 
        apply valid_path_extend_path with (a:=n - 1); try lia.
        left. 
        unfold is_in_graph, LNN.is_in_graph.
        bdestruct_all; reflexivity.
        replace (n - S (S dist)) with (n - 1 - (S dist)) by lia.
        apply IHdist; lia. }
    replace n2 with (n1 - (n1 - n2)) at 1 by lia.
    apply move_left_valid_path; lia.
Qed.

End LNN.

(*************************)
(**   LNN Ring Example  **)
(*************************)

Module LNNRing.

(* Creates a DAG of size dim where element i is connected to ((i-1) mod dim) and 
   ((i+1) mod dim). *)

Definition is_in_graph dim n1 n2 :=
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

Definition get_path dim n1 n2 :=
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
Compute (get_path 8 2 5).
Compute (get_path 8 6 1).
Compute (get_path 8 6 3).
Compute (get_path 8 2 7).

(* TODO: Proof is a little gross because of mod. Is there an 'lia' for expressions
   involving mod? If not, we should try to make something. *)

Lemma move_cw_valid_path : forall dim n dist,
  0 < dist -> dist < dim -> n < dim ->
  valid_path n ((n + dist) mod dim) (is_in_graph dim) dim (move_cw dim n dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent n.
  induction dist; simpl in *.
  - intros n Hn.
    assert (n <> (n + 1) mod dim).
    { bdestruct (n + 1 <? dim).
      rewrite Nat.mod_small; lia.
      assert (Hdim : n + 1 = dim) by lia. 
      rewrite <- Hdim; rewrite Nat.mod_same; lia. }
    repeat split; repeat constructor; try assumption.
    unfold is_in_graph.
    bdestruct_all; reflexivity.
    apply Nat.mod_upper_bound; lia.
  - intros n Hn. 
    assert (n <> (n + 1) mod dim).
    { bdestruct (n + 1 <? dim).
      rewrite Nat.mod_small; lia.
      assert (Hdim : n + 1 = dim) by lia. 
      rewrite <- Hdim; rewrite Nat.mod_same; lia. }
    apply valid_path_extend_path with (a:=(n + 1) mod dim); try assumption.
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
    left.
    unfold is_in_graph.
    bdestruct_all; reflexivity.
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
  valid_path n ((dim + n - dist) mod dim) (is_in_graph dim) dim (move_ccw dim n dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent n.
  induction dist; simpl in *.
  - intros n Hn.
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
    assert (x <> (x + 1) mod dim).
    { bdestruct (x + 1 <? dim).
      rewrite Nat.mod_small; lia.
      assert (Hdim : x + 1 = dim) by lia. 
      rewrite <- Hdim; rewrite Nat.mod_same; lia. }
    assert ((x + 1) mod dim <> x) by lia.
    repeat split; repeat constructor; try assumption.
    unfold is_in_graph.
    bdestruct_all; reflexivity.
    apply Nat.mod_upper_bound; lia.
  - intros n Hn.
    assert (n <> (dim + n - 1) mod dim).
    { rewrite_mod_sub ((dim + n - 1) mod dim). }
    apply valid_path_extend_path with (a:=(dim + n - 1) mod dim); try assumption.
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
    unfold is_in_graph.
    bdestruct_all; reflexivity.
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

Lemma get_path_valid : forall dim n1 n2, 
  n1 < dim -> n2 < dim -> n1 <> n2 -> valid_path n1 n2 (is_in_graph dim) dim (get_path dim n1 n2).
Proof.
  intros dim n1 n2 Hn1 Hn2 Hn1n2.
  unfold get_path.
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

End LNNRing.

(*************************)
(**   2D Grid Example   **)
(*************************)

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

Definition is_in_graph numRows numCols i i' :=
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
Compute (is_in_graph test_nr test_nc 2 0). (* -> false *)
Compute (is_in_graph test_nr test_nc 2 9). (* -> false *)
Compute (is_in_graph test_nr test_nc 2 7). (* -> true *)
Compute (is_in_graph test_nr test_nc 2 3). (* -> true *)
Compute (is_in_graph test_nr test_nc 8 3). (* -> true *)
Compute (is_in_graph test_nr test_nc 8 7). (* -> true *)
Compute (is_in_graph test_nr test_nc 15 0). (* -> false *)
Compute (is_in_graph test_nr test_nc 14 8). (* -> false *)

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

Definition get_path numCols i1 i2 :=
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
  then (* move left, down *)
       (* Note: It makes the proof easier to move left -> down rather than 
          down -> left. So this case is a little different from the others. *)
       let p1 := repeat_move move_left i1 (c1 - c2) in
       let p2 := repeat_move (move_down numCols) (i1 - (c1 - c2)) (r2 - r1) in
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
Compute (get_path test_nc 2 5).
Compute (get_path test_nc 6 14).
Compute (get_path test_nc 4 14).
Compute (get_path test_nc 13 1).
Compute (get_path test_nc 10 2).
Compute (get_path test_nc 11 1).
Compute (get_path test_nc 6 9).
Compute (get_path test_nc 13 10).

Lemma grid_is_in_graph_implies_numCols_nonzero : forall numRows numCols i i',
  is_in_graph numRows numCols i i' = true -> numCols > 0.
Proof.
  intros numRows numCols i i' H.
  unfold is_in_graph in H.
  bdestruct(i + numCols <? numRows * numCols); try lia.
  simpl in H.
  bdestruct(i' + numCols <? numRows * numCols); try lia.
  simpl in H.
  bdestruct(i + 1 <? numRows * numCols); try lia.
  simpl in H.
  bdestruct(i' + 1 <? numRows * numCols); try lia.
  simpl in H.
  inversion H.
Qed.

Lemma move_up_valid_path : forall numRows numCols i dist,
  numCols > 0 -> dist > 0 ->
  i < numRows * numCols ->
  dist * numCols <= i ->
  valid_path i (i - dist * numCols) (is_in_graph numRows numCols) (numRows * numCols) (repeat_move (move_up numCols) i dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent i.
  induction dist.
  - intros.
    rewrite Nat.mul_1_l.
    simpl. unfold move_up.
    repeat split; repeat constructor; try lia.
    unfold is_in_graph.
    bdestruct_all; reflexivity.
  - intros.
    simpl in *; unfold move_up in *.
    apply valid_path_extend_path with (a:=i - numCols); try lia. 
    left. 
    unfold is_in_graph.
    bdestruct_all; reflexivity.
    rewrite Nat.sub_add_distr.
    apply IHdist; lia.
Qed.

Lemma move_down_valid_path : forall numRows numCols i dist,
  numCols > 0 -> dist > 0 ->
  i + dist * numCols < numRows * numCols ->
  valid_path i (i + dist * numCols) (is_in_graph numRows numCols) (numRows * numCols) (repeat_move (move_down numCols) i dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent i.
  induction dist.
  - intros.
    rewrite Nat.mul_1_l.
    simpl. unfold move_down.
    repeat split; repeat constructor; try lia.
    unfold is_in_graph.
    bdestruct_all; reflexivity.
  - intros.
    simpl in *; unfold move_down in *.
    apply valid_path_extend_path with (a:=i + numCols); try lia.
    left.
    unfold is_in_graph.
    bdestruct_all; reflexivity.
    rewrite plus_assoc.
    apply IHdist; lia.
Qed.

Lemma move_left_valid_path : forall numRows numCols i dist,
  numCols > 0 -> dist > 0 ->
  i < numRows * numCols ->
  dist <= i ->
  valid_path i (i - dist) (is_in_graph numRows numCols) (numRows * numCols) (repeat_move move_left i dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent i.
  induction dist.
  - intros.
    simpl. unfold move_left.
    repeat split; repeat constructor; try lia.
    unfold is_in_graph.
    bdestruct_all; reflexivity.
  - intros.
    simpl in *; unfold move_left in *.
    apply valid_path_extend_path with (a:=i - 1); try lia.
    left.
    unfold is_in_graph.
    bdestruct_all; reflexivity.
    replace (i - S (S dist)) with (i - 1 - S dist) by lia.
    apply IHdist; lia.
Qed.

Lemma move_right_valid_path : forall numRows numCols i dist,
  numCols > 0 -> dist > 0 ->
  i + dist < numRows * numCols ->
  valid_path i (i + dist) (is_in_graph numRows numCols) (numRows * numCols) (repeat_move move_right i dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent i.
  induction dist.
  - intros.
    simpl. unfold move_right.
    repeat split; repeat constructor; try lia.
    unfold is_in_graph.
    bdestruct_all; reflexivity.
  - intros.
    simpl in *; unfold move_right in *.
    apply valid_path_extend_path with (a:=i + 1); try lia.
    left.
    unfold is_in_graph.
    bdestruct_all; reflexivity.
    replace (i + S (S dist)) with (i + 1 + S dist) by lia.
    apply IHdist; lia.
Qed.

Lemma not_in_interior_move_up : forall numCols n1 n2 dist,
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

Lemma not_in_interior_move_down : forall numCols n1 n2 dist,
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

Lemma not_in_interior_move_left : forall numCols n1 n2 dist,
  numCols <> 0 -> dist > 0 ->
  dist <= n1 ->
  row numCols n1 < row numCols n2 ->
  not_in_interior n2 (repeat_move move_left n1 dist).
Proof.
  intros.
  destruct dist; try lia.
  generalize dependent n1.
  induction dist; unfold row, move_left in *; simpl in *.
  - intros. constructor. 
    intros F. 
    contradict H2; subst; lia.
  - intros. constructor.
    intros F. 
    contradict H2; subst; lia.
    apply IHdist; try lia. 
    assert ((n1 - 1) / numCols <= n1 / numCols).
    { apply Nat.div_le_mono; lia. }
    lia.
Qed.

Lemma get_path_valid : forall numRows numCols n1 n2, 
  n1 < (numRows * numCols) -> n2 < (numRows * numCols) -> n1 <> n2 -> valid_path n1 n2 (is_in_graph numRows numCols) (numRows * numCols) (get_path numCols n1 n2).
Proof.
  intros numRows numCols n1 n2 Hn1 Hn2 Hn1n2.
  assert (0 < numRows * numCols) by lia.
  apply Nat.lt_0_mul' in H as [_ H].
  unfold get_path.
  (* some aux. lemmas *)
  assert (Haux0 : numCols <> 0) by lia.
  assert (Haux1 : numCols * (n1 / numCols) <= n1).
  { apply Nat.mul_div_le. lia. }
  assert (Haux2 : numCols * (n2 / numCols) <= n2).
  { apply Nat.mul_div_le. lia. }
  assert (Haux3 : (row numCols n1 - row numCols n2) * numCols <= n1).
  { unfold row.
    rewrite Nat.mul_sub_distr_r.
    rewrite Nat.mul_comm. lia. }
  bdestruct_all; simpl.
  (* get rid of some clutter *)
  all: repeat match goal with
       | H : row _ _ <> row _ _ |- _ => clear H
       | H : col _ _ <> col _ _ |- _ => clear H
       | H : row _ _ >= row _ _ |- _ => clear H
       | H : col _ _ >= col _ _ |- _ => clear H
       end.
  - (* move down, right *)
    remember (row numCols n2 - row numCols n1) as distR.
    remember (col numCols n2 - col numCols n1) as distC.
    assert (n1 + distR * numCols + distC = n2).
    { unfold row, col in *; subst.
      do 2 rewrite Nat.mod_eq in H1; try assumption.
      do 2 (rewrite Nat.mod_eq; try assumption).
      rewrite Nat.mul_sub_distr_r.
      rewrite (Nat.mul_comm (n1 / numCols)).
      rewrite (Nat.mul_comm (n2 / numCols)).
      assert (numCols * (n1 / numCols) < numCols * (n2 / numCols)).
      { apply mult_lt_compat_l; assumption. }
      remember (numCols * (n1 / numCols)) as x.
      remember (numCols * (n2 / numCols)) as y.
      clear - Haux1 Haux2 H1 H2.
      lia. }
    eapply valid_path_merge_path.
    apply move_down_valid_path; try assumption; try lia.
    replace n2 with (n1 + distR * numCols + distC); try assumption.
    apply move_right_valid_path; try assumption; try lia.    
    apply not_in_interior_move_down; try lia.
  - (* move down, left *)
    remember (row numCols n2 - row numCols n1) as distR.
    remember (col numCols n1 - col numCols n2) as distC.
    assert (distC <= n1).
    { unfold row, col in *; subst.
      do 2 (rewrite Nat.mod_eq; try assumption).
      lia. }
    assert (n1 - distC + distR * numCols = n2). 
    { unfold row, col in *; subst.
      do 2 (rewrite Nat.mod_eq; try assumption).
      do 2 rewrite Nat.mod_eq in H2; try assumption.
      rewrite Nat.mul_sub_distr_r.
      rewrite (Nat.mul_comm (n1 / numCols)).
      rewrite (Nat.mul_comm (n2 / numCols)).
      assert (numCols * (n1 / numCols) <= numCols * (n2 / numCols)).
      { apply mult_le_compat_l; lia. }
      remember (numCols * (n1 / numCols)) as x.
      remember (numCols * (n2 / numCols)) as y.
      clear - Haux1 Haux2 H2 H3.
      lia. }
    eapply valid_path_merge_path.
    apply move_left_valid_path; try assumption; try lia.
    replace n2 with (n1 - distC + distR * numCols); try assumption.
    apply move_down_valid_path; try assumption; try lia.   
    apply not_in_interior_move_left with (numCols:=numCols); try lia.
  - (* move down *)
    remember (row numCols n2 - row numCols n1) as distR.
    assert (n1 + distR * numCols = n2).
    { unfold row, col in *; subst.
      do 2 rewrite Nat.mod_eq in H4; try assumption.
      rewrite Nat.mul_sub_distr_r.
      rewrite (Nat.mul_comm (n1 / numCols)).
      rewrite (Nat.mul_comm (n2 / numCols)).
      assert (numCols * (n1 / numCols) < numCols * (n2 / numCols)).
      { apply mult_lt_compat_l; assumption. }
      remember (numCols * (n1 / numCols)) as x.
      remember (numCols * (n2 / numCols)) as y.
      clear - Haux1 Haux2 H1 H4.
      lia. }
    replace n2 with (n1 + distR * numCols); try assumption.
    apply move_down_valid_path; try assumption; try lia.
  - (* move up, right *)
    remember (row numCols n1 - row numCols n2) as distR.
    remember (col numCols n2 - col numCols n1) as distC.
    assert (n1 - distR * numCols + distC = n2).
    { unfold row, col in *; subst.
      do 2 (rewrite Nat.mod_eq; try assumption).
      do 2 rewrite Nat.mod_eq in H1; try assumption.
      rewrite Nat.mul_sub_distr_r.
      rewrite (Nat.mul_comm (n1 / numCols)).
      rewrite (Nat.mul_comm (n2 / numCols)).
      rewrite Nat.add_sub_assoc; try lia; 
      (* In Coq v8.10, the goal is solved by the previous line. *)
      try (rewrite Nat.add_sub_assoc; try assumption; 
           assert (numCols * (n2 / numCols) < numCols * (n1 / numCols));
           [ apply mult_lt_compat_l; assumption 
           |  remember (numCols * (n1 / numCols)) as x;
              remember (numCols * (n2 / numCols)) as y;
              clear - Haux1 Haux2 H0 H1;
              lia]).
    }
    eapply valid_path_merge_path.
    apply move_up_valid_path; try assumption; try lia.
    replace n2 with (n1 - distR * numCols + distC); try assumption.
    apply move_right_valid_path; try assumption; try lia.   
    apply not_in_interior_move_up; try assumption; try lia.
  - (* move right *)
    remember (col numCols n2 - col numCols n1) as distC.
    assert (n1 + distC = n2).
    { unfold row, col in *; subst.
      do 2 (rewrite Nat.mod_eq; try assumption). 
      assert (n1 - numCols * (n2 / numCols) <= n2 - numCols * (n2 / numCols)).
      { rewrite <- H5 at 1.
        do 2 rewrite Nat.mod_eq in H1; try assumption. 
        lia. }    
      assert (numCols * (n2 / numCols) <= n1).
      { rewrite <- H5. apply Nat.mul_div_le. assumption. }
      rewrite H5.
      remember (numCols * (n1 / numCols)) as x.
      remember (numCols * (n2 / numCols)) as y.
      clear - Haux1 Haux2 H0 H2.
      lia. }
    replace n2 with (n1 + distC); try assumption.
    apply move_right_valid_path; try assumption; try lia.
  - (* move up, left *)
    remember (row numCols n1 - row numCols n2) as distR.
    remember (col numCols n1 - col numCols n2) as distC.
    assert (distC <= n1 - distR * numCols).
    { unfold row, col in *; subst.
      do 2 (rewrite Nat.mod_eq; try assumption).
      rewrite Nat.mul_sub_distr_r.
      rewrite (Nat.mul_comm (n1 / numCols)).
      rewrite (Nat.mul_comm (n2 / numCols)).
      lia. }
    assert (n1 - distR * numCols - distC = n2).
    { unfold row, col in *; subst.
      do 2 (rewrite Nat.mod_eq; try assumption).
      do 2 rewrite Nat.mod_eq in H2; try assumption.
      rewrite Nat.mul_sub_distr_r.
      rewrite (Nat.mul_comm (n1 / numCols)).
      rewrite (Nat.mul_comm (n2 / numCols)).
      assert (numCols * (n2 / numCols) <= numCols * (n1 / numCols)).
      { apply mult_le_compat_l; lia. }
      remember (numCols * (n1 / numCols)) as x.
      remember (numCols * (n2 / numCols)) as y.
      clear - Haux1 Haux2 H1 H2.
      lia. }
    eapply valid_path_merge_path.
    apply move_up_valid_path; try assumption; try lia.
    replace n2 with (n1 - distR * numCols - distC).
    apply move_left_valid_path; try assumption; try lia.
    apply not_in_interior_move_up; try assumption; try lia. 
  - (* move left *)
    remember (col numCols n1 - col numCols n2) as distC.
    assert (n1 - distC = n2).
    { unfold row, col in *; subst.
      do 2 (rewrite Nat.mod_eq; try assumption).
      rewrite H5.
      assert (n2 <= n1).
      { do 2 rewrite Nat.mod_eq in H2; try assumption.
        rewrite H5 in H2. lia. }
      remember (numCols * (n1 / numCols)) as x.
      remember (numCols * (n2 / numCols)) as y.
      clear - Haux1 Haux2 H0.
      lia. }
    replace n2 with (n1 - distC); try assumption.
    apply move_left_valid_path; try assumption; try lia.
    subst. unfold col. rewrite Nat.mod_eq; lia.
  - (* move up *)
    remember (row numCols n1 - row numCols n2) as distR.
    assert (n1 - distR * numCols = n2).
    { unfold row, col in *; subst.
      do 2 rewrite Nat.mod_eq in H4; try assumption.
      rewrite Nat.mul_sub_distr_r.
      rewrite (Nat.mul_comm (n1 / numCols)).
      rewrite (Nat.mul_comm (n2 / numCols)).
      assert (numCols * (n2 / numCols) <= numCols * (n1 / numCols)). 
      { apply Nat.mul_le_mono_l. lia. } 
      remember (numCols * (n1 / numCols)) as x.
      remember (numCols * (n2 / numCols)) as y.
      clear - Haux1 Haux2 H0 H4.
      lia. }
    replace n2 with (n1 - distR * numCols); try assumption.
    apply move_up_valid_path; try assumption; try lia.
  - (* badly-typed case *)
    contradict Hn1n2.
    unfold col, row in *.
    do 2 rewrite Nat.mod_eq in H4; try lia;
    (* Coq v8.10 solves early again... *)
    try (rewrite H5 in H4;
         rewrite <- (Nat.sub_add (numCols * (n2 / numCols)) n1);
         [ rewrite H4; rewrite Nat.sub_add; 
           [ reflexivity | rewrite Nat.mul_div_le; lia]
         | rewrite <- H5; rewrite Nat.mul_div_le; lia ]). 
Qed.

End Grid.

(*************************)
(**   Tenerife Example  **)
(*************************)

Module Tenerife.

(* Map to IBM's 5-qubit Tenerife machine. The connectivity graph for the 
   Tenerife machine is depicted here: https://github.com/Qiskit/ibmq-device-information/blob/master/backends/tenerife/V1/version_log.md 

   We'll be using a hardcoded graph because we haven't found an easy-to-use 
   (and easy-to-extract) graph library for Coq. *)

Definition tenerife_graph : list (nat * nat) := 
  (1, 0) :: (2, 0) :: (2, 1) :: (3, 2) :: (3, 4) :: (4, 2) :: [].

Definition beq_tup t t' := 
  match t, t' with
  | (n1, n2), (n1', n2') => (n1 =? n1') && (n2 =? n2')
  end.

Definition is_in_graph n1 n2 :=
  existsb (beq_tup (n1, n2)) tenerife_graph.

Definition get_path n1 n2 :=
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

Lemma get_path_valid : forall n1 n2, 
  n1 < 5 -> n2 < 5 -> n1 <> n2 -> valid_path n1 n2 is_in_graph 5 (get_path n1 n2).
Proof.
  intros n1 n2 Hn1 Hn2 Hneq.
  repeat split.
  - do 5 try destruct n1; do 5 try destruct n2;
      try contradiction; try lia;
      try constructor.
  - do 5 try destruct n1; do 5 try destruct n2;
      try contradiction; try lia;
      repeat constructor.
  - do 5 try destruct n1; do 5 try destruct n2;
      try contradiction; try lia;
      try constructor.
    all: unfold is_in_graph; simpl; auto; try constructor; auto. 
  - do 5 try destruct n1; do 5 try destruct n2;
      try contradiction; try lia;
      repeat constructor; lia.
  - do 5 try destruct n1; do 5 try destruct n2;
    try contradiction; try lia.
    all: repeat constructor; lia.
Qed.

End Tenerife.

