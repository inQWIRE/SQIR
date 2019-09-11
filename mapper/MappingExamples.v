Require Import SimpleMapping.

Local Close Scope C_scope.
Local Close Scope R_scope.


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

Lemma not_in_interior_move_left : forall n1 n2 dist numCols,
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
