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
Definition layer : Type := list nat.

Definition fst_tuple (l : list (nat*nat)) : list nat := map fst l.
Definition snd_tuple (l : list (nat*nat)) : list nat := map snd l.

Fixpoint elem_in (a : nat)(l : list nat) : bool :=
  match l with
  | [] => false
  | h :: t => if a =? h then true else elem_in a t
  end.

Fixpoint first_layer {dim} (l : standard_ucom_l dim) (la : layer): layer :=
  match l with
  | [] => la
  | App2 U_CX n1 n2 :: t => if (orb (elem_in n1 la) (elem_in n2 la)) then la
                          else (first_layer t (n1::n2::la))
  | _ :: t => first_layer t la
  end.

Fixpoint rest_log_qubits {dim} (l : standard_ucom_l dim) (la : layer) (ls : list nat) : list nat :=
  match l with
  | [] => ls
  | App1 _ n1 :: t =>
    if (orb (elem_in n1 la) (elem_in n1 ls))
    then rest_log_qubits t la ls
    else rest_log_qubits t la (n1::ls)
  | App2 _ n1 n2 :: t =>
    let new_ls := if (orb (elem_in n1 la) (elem_in n1 ls))
                  then if (orb (elem_in n2 la) (elem_in n2 ls))
                       then ls
                       else n2 :: ls
                  else if (orb (elem_in n2 la) (elem_in n2 ls))
                      then n1 ::ls
                      else n1 :: n2 :: ls
    in
    rest_log_qubits t la ls
  | _ :: t => rest_log_qubits t la ls
  end.

Fixpoint qmapper dim (m : qmap dim) (mat : matching) (la : layer) : qmap dim :=
  match la with
  | [] => m
  | q1 :: [] =>
    match mat with
    | [] => m
    | h :: t =>
        let m1 q := if q =? q1 then (fst h) else (fst m) q in
        let m2 q := if q =? (fst h) then q1 else (snd m) q in
        (m1, m2)
        end
  | q1 :: q2 :: t =>
    match mat with
    | [] => m
    | h :: t =>
      let m1' q := if q =? q1 then (fst h)
                   else if q =? q2 then (snd h)
                        else (fst (qmapper dim m t la)) q in
      let m2' q := if q =? (fst h) then q1
                   else if q =? (snd h) then q2
                        else (snd ( qmapper dim m t la)) q in
        (m1', m2')
      end
    end.


Definition initial_qmap {dim} (l : standard_ucom_l dim) (mat : matching) (m : qmap dim): qmap dim :=
  let fst_l := first_layer l [] in
  let full_layer := fst_l ++ (rest_log_qubits l fst_l []) in 
  qmapper dim m mat full_layer.

(****************end of mapper via matching******************)

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

(**************** Proof qmapper well formed ************************)
Inductive matching_well_typed : nat -> matching -> Prop :=
| mat_nil dim : matching_well_typed dim nil
| mat_ind dim : forall p l, (fst p) < dim -> (snd p) < dim -> (fst p) <> (snd p) -> not (In (fst p) (fst_tuple l)) -> not (In (fst p) (snd_tuple l)) -> not (In (snd p) (fst_tuple l)) -> not (In (snd p) (snd_tuple l)) -> matching_well_typed dim l -> matching_well_typed dim (p::l).

Inductive layer_well_typed : nat -> layer -> Prop :=
| la_nil dim : layer_well_typed dim []
| la_inductive dim : forall n l, n < dim -> not (In n l) -> layer_well_typed dim l -> layer_well_typed dim (n :: l).


Lemma qmapper_well_formed : forall dim (m : qmap dim) (mat : matching) (la : layer),
    matching_well_typed dim mat ->
    layer_well_typed dim la ->
    layout_well_formed dim m ->
    layout_well_formed dim (qmapper dim m mat la).
Proof.
  unfold layout_well_formed, log2phys, phys2log.
  intros dim m mat la Hmat Hla. 
  destruct m as [m1 m2].
  intros H x Hx. 
  destruct (H x Hx) as [? [? [? ?]]].
  induction mat. 
  - (* first base case *)
    repeat split.
    do 2 (destruct la; simpl; auto).
    do 2 (destruct la; simpl; auto).
    do 2 (destruct la; simpl; auto).
    do 2 (destruct la; simpl; auto).
  - destruct la.
    simpl. apply H. auto.
    destruct la; simpl.
    + (* second base case *)
      inversion Hmat; subst.
      (* you should have everything you need here, it just requires a bunch of destructs *)
      bdestruct (x =? n).
      split. auto.
      (* hint: try looking at what the tactic bdestruct_all does *)
      admit.
      admit.
   + destruct IHmat as [? [? [? ?]]].
     inversion Hmat. auto.
     (* you should have everything you need here, it's just a little annoying :) *)
Admitted.
    

(**************** Proof End  ************************)

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


Compute (layout_to_list 6 (qmapper 6 ((1,2)::(3,4)::(5,6)::[]) ((1,2)::(3,4)::(5,6)::[]))).


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
