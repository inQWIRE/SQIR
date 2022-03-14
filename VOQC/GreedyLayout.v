Require Import QuantumLib.VectorStates.
Require Import SimpleMapping2.
Require Import FullGateSet MappingGateSet.


(* some function for choosing a good pair of qubits *)

(** Given a set of currently allocated qubits, choose two new qubits to 
    allocate. In our OCaml implementation, we will choose qubits from
    a maximal matching of the connectivity graph. It could also make 
    sense to allocate qubits based on error rate. **)

(*
Function to split a circuit into layers
(parameter) Based on next layer(s) and current layout, build a swap circuit to 
            permute and update the layout 
Reassemble the layers with SWAPs in between

# of layers = CNOT depth of the circuit
*)

(** A layer is a set of gates that can use the same layout. It includes
single-qubit gates and two-qubit gates that can be performed in parallel. **)

Fixpoint get_layer {U dim} (l : gate_list (Map_Unitary U) dim) (la : layer): layer :=

(* get as many single-qubit gates as possible *)

(* get the next two-qubit gate that doesn't conflict with the current set of qubits in use *)

  match l with
  | [] => la
  | App2 U_CX n1 n2 :: t => if (orb (elem_in n1 (listNN2N la)) (elem_in n2 (listNN2N la))) then la
                          else (first_layer t ((n1,n2)::la))
  | _ :: t => first_layer t la
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


(* Map the logical qubits in the first layer to matching *)
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


(********************************************
(* These part is my original design.
It is tested by the test case written by Kesha. 
However, it is really hard to prove. Therefore I changed it to the upper version.
To test it, uncomment this part and comment qmapper function above.  *)

(* Becasue we want all logic qubits can be matched with physical qubits, and
first_layer function can only find logic qubits that are used by two-qubit gate
in the first layer, we need this rest_log_qubits to find other qubits
that are not in the first layer. *)
Fixpoint rest_log_qubits {dim} (l : full_ucom_l dim) (la : layer) (ls : list nat) : list nat :=
  match l with
  | [] => ls
  | App1 _ n1 :: t =>
    if (orb (orb (elem_in n1 (fst_tuple la)) (elem_in n1 (snd_tuple la))) (elem_in n1 ls))
    then rest_log_qubits t la ls
    else rest_log_qubits t la (n1::ls)
  | App2 _ n1 n2 :: t =>
    let new_ls := if (orb (orb (elem_in n1 (fst_tuple la)) (elem_in n1 (snd_tuple la))) (elem_in n1 ls))
                 then if (orb (orb (elem_in n2 (fst_tuple la)) (elem_in n2 (snd_tuple la))) (elem_in n2 ls))
                      then ls
                      else n2 :: ls
                 else if (orb (orb (elem_in n2 (fst_tuple la)) (elem_in n2 (snd_tuple la))) (elem_in n2 ls))
                      then n1 ::ls
                      else n1 :: n2 :: ls
    in
    rest_log_qubits t la ls
  | _ :: t => rest_log_qubits t la ls
  end.

Fixpoint lst_N2lst_NN (l : list nat) : layer :=
  match l with
  | [] => []
  | x :: [] => (x,x) :: []
  |x :: y :: t => (x, y) :: lst_N2lst_NN t
  end.

(* Original design of qmapper.*)
Fixpoint qmapper dim (mat : matching) (la : layer) : qmap dim :=
  match la with
  | [] =>
    let m1 q := 0 in
    let m2 q := 0 in
    (m1, m2)
  | [(q1, q2)] =>
    match (hd (0,0) mat) with
    | (v1, v2) =>
      if q1 =? q2 then
        let m1 q := v1 in
        let m2 q := q1 in
        (m1, m2)
      else
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

(* This function takes a circuit program, l, and a matching and return the 
initial mapping function of logic qubits and physiacal qubits. *)
Definition initial_qmap {dim} (l : full_ucom_l dim) (mat : matching) : qmap dim :=
  let fst_l := first_layer l [] in
  let full_layer := fst_l ++ (lst_N2lst_NN (rest_log_qubits l fst_l [])) in 
  qmapper dim mat full_layer.

********end of original code****************)

(****************end of mapper via matching******************)


(**************** Proof qmapper well formed ************************)
Inductive matching_well_typed : nat -> matching -> Prop :=
| mat_nil dim : matching_well_typed dim nil
| mat_ind dim : forall p l, (fst p) < dim -> (snd p) < dim ->
                       (fst p) <> (snd p) ->
                       not (In (fst p) (listNN2N l)) ->
                       not (In (snd p) (listNN2N l)) ->
                       matching_well_typed dim l ->
                       matching_well_typed dim (p::l).

Inductive layer_well_typed : nat -> layer -> Prop :=
| la_nil dim : layer_well_typed dim []
| la_inductive dim : forall n l, (fst n) < dim -> (snd n) < dim ->
                            (fst n) <> (snd n) ->
                            not (In (fst n) (listNN2N l)) ->
                            not (In (snd n) (listNN2N l)) ->
                            layer_well_typed dim l ->
                            layer_well_typed dim (n :: l).

Lemma matching_layer_no_dup : forall (n : nat) (a : nat) (l : list (nat * nat)),
    not (In n (listNN2N l)) -> In a (listNN2N l) -> n <> a.
Proof.
  unfold not. intros. apply H. subst. auto. Qed.

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
  - repeat split.
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
    repeat split.
    subst. rewrite <- H9. auto. 
    subst. auto. auto. auto.
    repeat split.
    inversion Hmat. auto.
    subst. rewrite H12. auto. auto. admit.
    repeat split.
    auto. inversion Hmat. auto.
    inversion Hla. auto. auto. auto.
    repeat split.
    inversion Hmat. auto.
    rewrite H12. inversion Hla. auto. auto. admit.
    repeat split.
    inversion Hmat. auto.
    rewrite H13. inversion Hla. auto. auto. admit.
    repeat split.
    inversion Hmat. auto.
    destruct mat. simpl. auto. simpl. auto.
    auto. destruct mat. simpl. auto. simpl. auto.
    repeat split.
    inversion Hmat. auto. inversion Hla. auto. admit. auto.
    repeat split.
    inversion Hmat. auto. inversion Hla. auto. auto. auto.
    repeat split.
    inversion Hmat. auto. inversion Hla. auto. auto. auto.
    repeat split.
    inversion Hmat. auto.
    rewrite H13. inversion Hla. auto.
    inversion Hmat. symmetry in H12. contradiction.
    inversion Hmat. symmetry in H12. contradiction.
    repeat split.
    inversion Hmat. auto.
    rewrite H14. inversion Hla. auto.
    inversion Hmat. symmetry in H12. contradiction.
    inversion Hmat. symmetry in H12. contradiction.
    repeat split.
    inversion Hmat. auto.
    inversion Hmat. symmetry in H12. contradiction.
    inversion Hmat. symmetry in H12. contradiction.
    inversion Hmat. symmetry in H12. contradiction.
    repeat split.
    inversion Hmat. auto.
    rewrite H14. inversion Hla. auto. auto. admit.
    repeat split.
    inversion Hmat. auto.
    rewrite H15. inversion Hla. auto. auto. admit.
    repeat split.
    inversion Hmat. auto.
    destruct mat. simpl. auto. simpl. auto.
    auto. destruct mat. simpl. auto. simpl. auto.
    repeat split.
    rewrite H11. inversion Hmat. auto.
    inversion Hla. auto. admit. auto.
    repeat split.
    rewrite H12. inversion Hmat. auto.
    inversion Hla. auto. admit. auto.
    repeat split.
    destruct mat. simpl. auto. simpl. auto.
    inversion Hla. auto.
    destruct mat. simpl. auto. simpl. auto. auto.
    destruct mat. simpl. auto. simpl. auto.
    repeat split.
    inversion Hla. auto.
    inversion Hla. symmetry in H13. contradiction.
    inversion Hla. symmetry in H13. contradiction. admit.
    repeat split.
    destruct mat. simpl. auto. simpl. auto.
    inversion Hla. auto. admit. admit.
    repeat split.
    rewrite H12. inversion Hmat. auto.
    inversion Hla. auto. admit. auto.
    repeat split.
    rewrite H13. inversion Hmat. auto.
    inversion Hla. auto. admit. admit.
    repeat split.
    destruct mat. simpl. auto. simpl. auto.
    inversion Hla. auto. admit. auto.
    repeat split.
    destruct mat. simpl. auto. simpl. auto.
    inversion Hla. auto. 
    destruct mat. simpl. auto. simpl. auto. admit.
    repeat split.
    destruct mat. simpl. auto. auto.
    inversion Hla. auto.
    destruct mat. simpl. auto. simpl. auto. auto.
    repeat split.
    rewrite H12. inversion Hmat. auto.
    rewrite H13. inversion Hla. auto. admit. admit.
    repeat split.
    rewrite H12. inversion Hmat. auto.
    rewrite H14. inversion Hla. auto. admit. admit.
    repeat split.
    rewrite H12. inversion Hmat. auto.
    destruct mat. simpl. auto. simpl. auto. admit.
    destruct mat. simpl. auto. simpl. auto.
    repeat split.
    rewrite H13. inversion Hmat. auto.
    rewrite H14. inversion Hla. auto. admit. admit. 
    repeat split.
    rewrite H13. inversion Hmat. auto.
    rewrite H15. inversion Hla. auto. admit. admit.
    repeat split.
    rewrite H13. inversion Hmat. auto.
    destruct mat. inversion Hmat. auto.
    inversion Hmat. auto. admit.
    destruct mat. simpl. auto. simpl. auto.
    repeat split.
    destruct mat; auto; auto.
    destruct mat. auto. auto.
    destruct mat. auto. auto. admit.
    repeat split.
    destruct mat. auto. auto.
    destruct mat. auto. auto.
    destruct mat. auto. auto. admit.
    repeat split.
    destruct mat. auto. auto.
    destruct mat. auto. auto.
    destruct mat. auto. auto.
    destruct mat. auto. auto. 
    destruct IHmat as [? [? [? ?]]].
    inversion Hmat. auto.
    simpl. inversion Hmat. inversion Hla.
    bdestruct_all.
    repeat split.
    auto. auto. auto. auto.
    repeat split.
    auto. auto. auto. auto.
    repeat split.
    auto. rewrite H30. auto. auto. admit.
    repeat split.
    auto. rewrite H31. auto. auto. admit.
    repeat split.
    auto. admit. auto. admit.
    repeat split.
    auto. auto. auto. auto.
    repeat split.
    auto. auto. auto. auto.
    repeat split.
    auto. rewrite H32. auto. auto. admit.
    repeat split.
    auto. rewrite H33. auto. auto. admit.
    repeat split.
    auto. admit. auto. admit.
    repeat split.
    rewrite H29. auto. auto. admit. auto.
    repeat split.
    rewrite H30. auto. auto. admit. auto.
    repeat split.
    admit. auto. admit. auto.
    repeat split.
    rewrite H30. auto. auto. admit. auto.
    repeat split.
    subst. rewrite H31. auto. auto. admit. auto.
    repeat split.
    admit. auto. admit. auto.
    repeat split.
    rewrite H30. auto. rewrite H31. auto. admit. admit.
    repeat split.
    rewrite H30. auto. rewrite H32. auto. admit. admit.
    repeat split.
    rewrite H30. auto. admit. admit. admit.
    repeat split.
    rewrite H31. auto. rewrite H32. auto. admit. admit.
    repeat split.
    rewrite H31. auto. rewrite H33. auto. admit. admit.
    repeat split.
    rewrite H31. auto. admit. admit. admit.
    repeat split.
    admit. rewrite H32. auto. admit. admit.
    repeat split.
    admit. rewrite H33. auto. admit. admit.
    admit.

Admitted.     
    
(**************** Proof End  ************************)
