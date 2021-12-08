Require Import QWIRE.Prelim.
Require Import VectorStates.
Require Export ConnectivityGraph.
Require Export StandardGateSet.
From Coq Require Import Lists.List.


Local Close Scope R_scope.
Local Close Scope Q_scope.

(** Definition of layouts for mapping. **)

(* We will represent a layout with two functions: one that maps from
   logical qubits to physcial qubits, and one that maps from physical
   qubits to logical qubits. We use two functions instead of one to 
   make lookup in either direction efficient. However, this requires
   some extra machinery to describe well-formed layouts.

   In general, the logical qubit register may be smaller than the physical
   qubit register, so it could also make sense to have the type of phys2log
   be (nat -> option nat). However, it makes the proof easier to use a pair
   of (nat -> nat) functions. This just means that we need to associate 
   every "unused" physical qubit with a fresh logical qubit.
 *)
Definition qmap (dim : nat) : Type := (nat -> nat) * (nat -> nat).

Definition log2phys {dim} (m : qmap dim) q :=
  match m with
  | (m, _) => m q
  end.

Definition phys2log {dim} (m : qmap dim) q :=
  match m with
  | (_, m) => m q
  end.


(*********** begin mapper via matching *************)
Definition matching : Type := list (nat*nat).
Definition layer : Type := list (nat*nat).

Definition fst_tuple (l : layer) : list nat := map fst l.
Definition snd_tuple (l : layer) : list nat := map snd l.
Fixpoint elem_in (a : nat)(l : list nat) : bool :=
  match l with
  | [] => false
  | h :: t => if a =? h then true else elem_in a t
  end.

Fixpoint first_layer {dim} (l : standard_ucom_l dim) (la : layer): layer :=
  match l with
  | [] => la
  | App2 U_CX n1 n2 :: t => if (orb (elem_in n1 (fst_tuple la)) (elem_in n2 (snd_tuple la))) then la
                          else (first_layer t ((n1, n2)::la))
  | _ :: t => first_layer t la
  end.

Fixpoint qmapper dim (mat : matching) (la : layer) : qmap dim :=
  match la with
  | [] =>
    let m1 q := 0 in
    let m2 q := 0 in
    (m1, m2)
  | [(q1, q2)] =>
    match (hd (0,0) mat) with
    | (v1, v2) =>
      let m1 q := if q =? q1 then v1 else v2 in
      let m2 q := if q =? v1 then q1 else q2 in
      (m1, m2)
    end
  | ((q1, q2) :: t) =>
    match (qmapper dim (tl mat) t) with
    | (m1, m2) =>
      match (hd (0,0) mat) with
      | (v1, v2) =>
        let m1' q := if q =? q1 then v1
                     else if q =? q2 then v2
                          else m1 q in
        let m2' q := if q =? v1 then q1
                     else if q =? v2 then q2
                          else m2 q in
        (m1', m2')
      end
    end
  end.

Definition initial_qmap {dim} (l : standard_ucom_l dim) (mat : matching) : qmap dim :=
  qmapper dim mat (first_layer l []).

(****************end of mapper via matching******************)




























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

Definition layout_well_formed dim (m : qmap dim) := 
  forall x, x < dim ->
    log2phys m x < dim /\ 
    phys2log m x < dim /\ 
    phys2log m (log2phys m x) = x /\
    log2phys m (phys2log m x) = x.

Fixpoint layout_well_formed_b' dim n (m : qmap dim) :=
  match n with
  | O => true
  | S n' => 
      (log2phys m n' <? dim) &&
      (phys2log m n' <? dim) &&
      (phys2log m (log2phys m n') =? n') &&
      (log2phys m (phys2log m n') =? n') &&
      (layout_well_formed_b' dim n' m)
  end. 
Definition layout_well_formed_b dim (m : qmap dim) :=
  layout_well_formed_b' dim dim m.

Lemma layout_well_formed_b_equiv : forall dim (m : qmap dim),
  layout_well_formed_b dim m = true -> layout_well_formed dim m.
Proof.
  intros.
  assert (forall x, layout_well_formed_b' dim x m = true ->
          forall x0, x0 < x -> log2phys m x0 < dim /\ 
                         phys2log m x0 < dim /\ 
                         phys2log m (log2phys m x0) = x0 /\
                         log2phys m (phys2log m x0) = x0).
  { intros x Hx x0 Hx0.
    induction x.
    lia.
    simpl in Hx.
    apply andb_prop in Hx as [Hx Hx5].
    apply andb_prop in Hx as [Hx Hx4].
    apply andb_prop in Hx as [Hx Hx3].
    apply andb_prop in Hx as [Hx1 Hx2].
    apply Nat.ltb_lt in Hx1.
    apply Nat.ltb_lt in Hx2.
    apply beq_nat_true in Hx3.
    apply beq_nat_true in Hx4.
    specialize (IHx Hx5).
    bdestruct (x0 =? x).    
    subst. 
    repeat split; assumption.
    apply IHx.
    lia. }
  specialize (H0 dim H).
  assumption.
Qed.

Lemma well_formed_log2phys_bij : forall {dim} (m : qmap dim),
  layout_well_formed dim m ->
  finite_bijection dim (log2phys m).
Proof.
  intros dim m WF.
  exists (phys2log m).
  apply WF.
Qed.  

Lemma well_formed_phys2log_bij : forall {dim} (m : qmap dim),
  layout_well_formed dim m ->
  finite_bijection dim (phys2log m).
Proof.
  intros dim m WF.
  exists (log2phys m).
  intros x Hx.
  specialize (WF x Hx) as [? [? [? ?]]].
  auto.
Qed.  

Lemma swap_in_map_well_formed : forall {dim} (m : qmap dim) n1 n2,
  n1 < dim -> n2 < dim -> layout_well_formed dim m -> 
  layout_well_formed dim (swap_in_map m n1 n2).
Proof.
  unfold layout_well_formed, swap_in_map, log2phys, phys2log.
  intros dim m n1 n2 Hn1 Hn2.
  destruct m as [m1 m2].
  intros H x Hx.
  destruct (H x Hx) as [? [? [? ?]]].
  destruct (H n1 Hn1) as [? [? [? ?]]].
  destruct (H n2 Hn2) as [? [? [? ?]]].
  repeat split.
  - bdestruct_all; auto.
  - bdestruct_all; auto.
  - bdestruct (x =? m2 n1); bdestruct (x =? m2 n2); subst; auto.
    all: bdestruct_all; subst; auto.
    symmetry in H2. contradiction.
    symmetry in H2. contradiction.
  - bdestruct (x =? n1); bdestruct (x =? n2); bdestruct_all; subst; auto. 
    assert (m1 (m2 n2) = m1 (m2 n1)) by auto.
    rewrite H3, H11 in H12.
    symmetry in H12. contradiction.
    assert (m1 (m2 x) = m1 (m2 n1)) by auto.
    rewrite H3, H7 in H15.
    contradiction.
    assert (m1 (m2 x) = m1 (m2 n2)) by auto.
    rewrite H3, H11 in H16.
    contradiction.
Qed.

(* Represent a layout as a list where element l at index p indicates that
   logical qubit l is stored at physcial qubit p. (Makes printing nicer.)  *)
Fixpoint layout_to_list' {dim} x (m : qmap dim) :=
  match x with 
  | O => []
  | S x' => (layout_to_list' x' m) ++ [phys2log m x'] 
  end.
Definition layout_to_list dim (m : qmap dim) := 
  layout_to_list' dim m.

(* Produce a layout from its list representation. *)
Fixpoint list_to_layout' {dim} l acc : qmap dim :=
  match l with
  | [] => (fun x => x, fun x => x) (* default mapping *)
  | h :: t =>
      let m' := @list_to_layout' dim t (S acc) in
      (fun x => if x =? h then acc else fst m' x, 
       fun x => if x =? acc then h else snd m' x)
  end.
Definition list_to_layout l : qmap (length l) := 
  list_to_layout' l 0.

(* TODO: May be useful to prove that layout_to_list and list_to_layout are inverses. *)

(* Examples *)
Definition trivial_layout dim : qmap dim :=
  (fun x => x, fun x => x).
Definition test_layout : qmap 5 := 
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

Compute (layout_to_list 5 (trivial_layout 5)).
Compute (layout_to_list 5 test_layout).
Compute (layout_to_list 5 (list_to_layout (0 :: 1 :: 2 :: 3 :: 4 :: []))).
Compute (layout_to_list 5 (list_to_layout (3 :: 4 :: 1 :: 2 :: 0 :: []))).

(* The trivial layout is always well formed. *)
Lemma trivial_layout_well_formed : forall dim,
  layout_well_formed dim (trivial_layout dim).
Proof.
  intros dim.
  unfold layout_well_formed, trivial_layout, log2phys, phys2log.
  intros x Hx.
  auto.
Qed.

(* Most things that are true of log2phys will be true of phys2log too -- 
   there is not an important conceptual difference between the two functions
   (except in the swap_in_map function). The qmap construct is largely just 
   a way to store a function with its inverse. So it's typically fine to 
   switch the order of log2phys and phys2log. *)
Definition invert_layout {dim} (m : qmap dim) : qmap dim := (snd m, fst m).

Lemma invert_layout_well_formed : forall {dim} (m : qmap dim),
  layout_well_formed dim m ->
  layout_well_formed dim (invert_layout m).
Proof.
  intros dim m H.
  intros x Hx.
  specialize (H x Hx) as [? [? [? ?]]].
  unfold invert_layout.
  destruct m; simpl in *.
  repeat split; auto.
Qed.
