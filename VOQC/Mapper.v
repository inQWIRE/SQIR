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

Definition fst_tuple (l : list (nat*nat)) : list nat := map fst l.
Definition snd_tuple (l : list (nat*nat)) : list nat := map snd l.

Fixpoint elem_in (a : nat)(l : list nat) : bool :=
  match l with
  | [] => false
  | h :: t => if a =? h then true else elem_in a t
  end.

Fixpoint listNN2N (l : list (nat * nat)) : list nat :=
  match l with
  | [] => []
  | (a, b) :: t => a :: b :: (listNN2N t)
  end.

Fixpoint first_layer {dim} (l : standard_ucom_l dim) (la : layer): layer :=
  match l with
  | [] => la
  | App2 U_CX n1 n2 :: t => if (orb (elem_in n1 (listNN2N la)) (elem_in n2 (listNN2N la))) then la
                          else (first_layer t ((n1,n2)::la))
  | _ :: t => first_layer t la
  end.

Fixpoint rest_log_qubits {dim} (l : standard_ucom_l dim) (la : layer) (ls : list nat) : list nat :=
  match l with
  | [] => ls
  | App1 _ n1 :: t =>
    if (orb (elem_in n1 (listNN2N la)) (elem_in n1 ls))
    then rest_log_qubits t la ls
    else rest_log_qubits t la (n1::ls)
  | App2 _ n1 n2 :: t =>
    let new_ls := if (orb (elem_in n1 (listNN2N la)) (elem_in n1 ls))
                  then if (orb (elem_in n2 (listNN2N la)) (elem_in n2 ls))
                       then ls
                       else n2 :: ls
                  else if (orb (elem_in n2 (listNN2N la)) (elem_in n2 ls))
                      then n1 ::ls
                      else n1 :: n2 :: ls
    in
    rest_log_qubits t la ls
  | _ :: t => rest_log_qubits t la ls
  end.

Fixpoint qmapper dim (m : qmap dim) (mat : matching) (la : layer) : qmap dim :=
  match la with
  | [] => m
  | q1 :: tla =>
    match mat with
    | [] => m
    | h :: tmat =>
      let m1' q := if q =? (fst q1) then (fst h)
                   else if q =? (snd q1) then (snd h)
                        else (fst (qmapper dim m tmat tla)) q in
      let m2' q := if q =? (fst h) then (fst q1)
                   else if q =? (snd h) then (snd q1)
                        else (snd ( qmapper dim m tmat tla)) q in
        (m1', m2')
      end
    end.


Definition initial_qmap {dim} (l : standard_ucom_l dim) (mat : matching) (m : qmap dim): qmap dim :=
  let fst_l := first_layer l [] in
  let full_layer := fst_l in 
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
| mat_ind dim : forall p l, (fst p) < dim -> (snd p) < dim -> (fst p) <> (snd p) -> not (In p l) -> matching_well_typed dim l -> matching_well_typed dim (p::l).

Inductive layer_well_typed : nat -> layer -> Prop :=
| la_nil dim : layer_well_typed dim []
| la_inductive dim : forall n l, (fst n) < dim -> (snd n) < dim -> (fst n) <> (snd n) -> not (In n l) -> layer_well_typed dim l -> layer_well_typed dim (n :: l).


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
    destruct la. simpl.
    destruct IHmat as [? [? [? ?]]].
    inversion Hmat. auto.
    bdestruct_all.
    split. subst. rewrite <- H9. auto. 
    split. subst. auto.
    split. auto. auto.
    split. inversion Hmat. auto.
    split. subst. rewrite H12. auto.
    split. auto. inversion Hmat. auto. symmetry. admit.
    split. auto. inversion Hmat. auto.
    split. inversion Hla. auto.
    split. auto. auto.
    split. inversion Hmat. auto.
    split. rewrite H12. inversion Hla. auto.
    split. auto. admit.
    split. inversion Hmat. auto.
    split. rewrite H13. inversion Hla. auto.
    split. auto. admit.
    split. inversion Hmat. auto.
    split. destruct mat. simpl. auto. simpl. auto.
    split. auto. destruct mat. simpl. auto. simpl. auto.
    split. inversion Hmat. auto.
    split. inversion Hla. auto.
    split. admit. auto.
    split. inversion Hmat. auto.
    split. inversion Hla. auto.
    split. auto. auto.
    split. inversion Hmat. auto.
    split. inversion Hla. auto.
    split. auto. auto.
    split. inversion Hmat. auto.
    split. rewrite H13. inversion Hla. auto.
    split. inversion Hmat. symmetry in H12. contradiction.
    inversion Hmat. symmetry in H12. contradiction.
    split. inversion Hmat. auto.
    split. rewrite H14. inversion Hla. auto.
    split. inversion Hmat. symmetry in H12. contradiction.
    inversion Hmat. symmetry in H12. contradiction.
    split. inversion Hmat. auto.
    split. inversion Hmat. symmetry in H12. contradiction.
    split. inversion Hmat; symmetry in H12; contradiction.
    inversion Hmat; symmetry in H12; contradiction.
    split. inversion Hmat. auto.
    split. rewrite H14. inversion Hla. auto.
    split. auto. admit.
    split. inversion Hmat. auto.
    split. rewrite H15. inversion Hla. auto.
    split. auto. admit.
    split.  inversion Hmat. auto.
    split. destruct mat. simpl. auto. simpl. auto.
    split. auto. destruct mat. simpl. auto. simpl. auto.
    split. rewrite H11. inversion Hmat. auto.
    split. inversion Hla. auto.
    split. admit. auto.
    split. rewrite H12. inversion Hmat. auto.
    split. inversion Hla. auto.
    split. admit. auto.
    split. destruct mat. simpl. auto. simpl. auto.
    split. inversion Hla. auto.
    split. destruct mat. simpl. auto. simpl. auto. auto.
    split. destruct mat. simpl. auto. simpl. auto.
    split. inversion Hla. auto.
    split. inversion Hla. symmetry in H13. contradiction.
    inversion Hla. symmetry in H13. contradiction.
    split. destruct mat. simpl. auto. simpl. auto.
    split. inversion Hla. auto.
    split. admit. auto.
    split. rewrite H13. inversion Hmat. auto.
    split. inversion Hla. auto.
    split. admit. admit.
    split. rewrite H13. inversion Hmat. auto.
    split. inversion Hla. auto.
    split. admit. auto.
    split. destruct mat. simpl. auto. simpl. auto.
    split. inversion Hla. auto.
    split. destruct mat. simpl. auto. simpl. auto.
    admit.
    split. destruct mat. simpl. auto. simpl. auto.
    split. inversion Hla. auto.
    split. destruct mat. simpl. auto. simpl. auto. auto.
    split. rewrite H12. inversion Hmat. auto.
    split. rewrite H13. inversion Hla. auto.
    admit.
    split. rewrite H12. inversion Hmat. auto.
    split. rewrite H14. inversion Hla. auto.
    admit.
    split. rewrite H12. inversion Hmat. auto.
    split. destruct mat. simpl. auto. simpl. auto.
    split. admit.
    destruct mat. simpl. auto. simpl. auto.
    split. rewrite H13. inversion Hmat. auto.
    split. rewrite H14. inversion Hla. auto.
    admit.
    split. rewrite H13. inversion Hmat. auto.
    split. rewrite H15. inversion Hla. auto.
    admit.
    split. rewrite H13. inversion Hmat. auto.
    split. destruct mat. inversion Hmat. auto. inversion Hmat. auto.
    split. admit.
    destruct mat. simpl. auto. simpl. auto.
    destruct mat. repeat split. auto. auto. auto. admit.
    repeat split. auto. auto. auto. admit.
    destruct mat. repeat split. auto. auto. auto. admit.
    repeat split. auto. auto. auto. admit.
    destruct mat. repeat auto. auto.
    destruct IHmat as [? [? [? ?]]]. inversion Hmat. auto.
    repeat split.
    simpl. bdestruct_all. inversion Hmat. auto. inversion Hmat. auto.
    destruct mat. simpl. auto.
    simpl. bdestruct_all. inversion Hmat. inversion H18. auto.
    inversion Hmat. inversion H19. auto. admit.
    simpl. bdestruct_all. inversion Hla. auto. inversion Hla. auto.
    destruct mat. simpl. auto.
    simpl. bdestruct_all. inversion Hla. inversion H18. auto.
    inversion Hla. inversion H19. auto. admit.
    simpl. admit.
    simpl. admit.
    Admitted.     
    

(**************** Proof End  ************************)
