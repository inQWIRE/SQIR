Require Import QuantumLib.VectorStates.
Require Import MappingGateSet.
Require Import Layouts.

Require Import FSets.FSetAVL.
Require Import FSets.FSetFacts.
Require Import FSets.FSetProperties.

Module FSet := FSetAVL.Make(Coq.Structures.OrderedTypeEx.Nat_as_OT).
Module FSetFacts := FSetFacts.Facts FSet.
Module FSetProps := FSetProperties.Properties FSet.

Local Open Scope nat_scope.

(** Choose an initial logical->physical qubit mapping (i.e., layout) for a
    program that puts qubits close together on the architecture if they are 
    used together in a two-qubit gate. *)

(** Choose an unused qubit based on the given preferences. *)
Fixpoint get_fresh_qubit (prefs : list nat) (alloc : FSet.t) :=
  match prefs with
  | [] => O (* unreachable, per conditions in the proof *)
  | p :: prefs => 
      if FSet.mem p alloc 
      then get_fresh_qubit prefs alloc 
      else p
  end.

(** Build a layout based on the structure of the input program.
   - l: input program
   - alloc: current allocated physical qubits
   - lay: current layout
 
   For every gate (CNOT m n), if logical qubits m or n are not already mapped 
   to physical qubits, we choose physical qubits m_phys and n_phys to be nearby
   in the returned layout. Note that the layout may change during mapping 
   (due to inserted swaps) so this strategy will not always choose the best 
   placement. *)
Fixpoint build_layout {U dim} (l : gate_list (Map_Unitary U) dim) (alloc : FSet.t) (lay : layout) (q_ordering : option nat -> list nat) : FSet.t * layout:=
  match l with
  | [] => (alloc, lay)
  | App2 UMap_CNOT m n :: t => 
      match find_phys lay m, find_phys lay n with
      | Some _, Some _ => build_layout t alloc lay q_ordering
      | Some m_phys, None =>
          let n_phys := get_fresh_qubit (q_ordering (Some m_phys)) alloc in
          let alloc' := FSet.add n_phys alloc in
          let lay' := add lay n n_phys in
          build_layout t alloc' lay' q_ordering
      | None, Some n_phys =>
          let m_phys := get_fresh_qubit (q_ordering (Some n_phys)) alloc in
          let alloc' := FSet.add m_phys alloc in
          let lay' := add lay m m_phys in
          build_layout t alloc' lay' q_ordering
      | None, None =>
          let m_phys := get_fresh_qubit (q_ordering None) alloc in
          let n_phys := get_fresh_qubit (q_ordering (Some m_phys)) alloc in
          let alloc' := FSet.add n_phys (FSet.add m_phys alloc) in
          let lay' := add (add lay m m_phys) n n_phys in
          build_layout t alloc' lay' q_ordering
      end
  | _ :: t => build_layout t alloc lay q_ordering
  end.

(** Choose a physical qubit for any unallocated logical qubits. n is the number
    of physical qubits available. *)
Fixpoint extend_layout (n : nat) (alloc : FSet.t) (lay : layout) (q_ordering : option nat -> list nat)  :=
  match n with
  | O => lay
  | S n' => 
      match find_phys lay n' with 
      | Some _ => extend_layout n' alloc lay q_ordering
      | None => let m := get_fresh_qubit (q_ordering None) alloc in
               extend_layout n' (FSet.add m alloc) (add lay n' m) q_ordering
      end
  end.

(** dim is the number of qubits used in the program l and n is the number of
   qubits available on the machine *)
Definition greedy_layout {U dim} (l : gate_list (Map_Unitary U) dim) (n : nat) (q_ordering : option nat -> list nat) : layout :=
  let (alloc, lay) := build_layout l FSet.empty empty q_ordering in
  extend_layout n alloc lay q_ordering.

(** Proofs *)

Lemma get_fresh_qubit_lt : forall prefs alloc n,
  (forall x, In x prefs -> x < n) -> 
  (exists x, In x prefs /\ ~ FSet.In x alloc) ->
  get_fresh_qubit prefs alloc < n.
Proof.
  intros prefs alloc n Hn H.
  induction prefs; simpl.
  destruct H as [? [H ?]].
  inversion H.
  destruct H as [x [Hx1 Hx2]].
  bdestruct (x =? a). subst.
  destruct (FSet.mem a alloc) eqn:fmem.
  apply FSetFacts.mem_iff in fmem.
  contradiction.
  apply Hn. left. auto.
  destruct (FSet.mem a alloc).
  apply IHprefs.
  intros. apply Hn. right. auto.
  exists x. split; auto. 
  inversion Hx1. subst. contradiction. auto.
  apply Hn. left. auto.
Qed.

Lemma get_fresh_qubit_not_In_alloc : forall prefs alloc,
  (exists x, In x prefs /\ ~ FSet.In x alloc) ->
  ~ FSet.In (get_fresh_qubit prefs alloc) alloc.
Proof.
  intros prefs alloc H.
  induction prefs; simpl.
  destruct H as [? [H ?]].
  inversion H.
  destruct H as [x [Hx1 Hx2]].
  bdestruct (x =? a). subst.
  destruct (FSet.mem a alloc) eqn:fmem.
  apply FSetFacts.mem_iff in fmem.
  contradiction. auto.
  destruct (FSet.mem a alloc) eqn:fmem.
  apply IHprefs.
  exists x. split; auto. 
  inversion Hx1. subst. contradiction. auto.
  apply FSetFacts.not_mem_iff.
  assumption.
Qed.

Definition alloc_records_allocated_phys_qubits lay alloc :=
  forall p, FSet.In p alloc <-> exists l, find_phys lay l = Some p.

Definition find_log_bounded lay n := 
 forall p l, find_log lay p = Some l -> l < n.

Definition find_phys_bounded lay n := 
 forall l p, find_phys lay l = Some p -> p < n.

Lemma alloc_records_allocated_phys_qubits_add : forall lay alloc l p,
  find_phys lay l = None ->
  alloc_records_allocated_phys_qubits lay alloc ->
  alloc_records_allocated_phys_qubits (add lay l p) (FSet.add p alloc).
Proof.
  intros lay alloc l p Hl H.
  unfold alloc_records_allocated_phys_qubits in *.
  intro p0.
  bdestruct (p0 =? p). subst.
  split; intro.
  exists l.
  apply find_phys_add_eq.
  apply FSet.add_1; auto.
  split; intro.
  apply FSet.add_3 in H1; auto.
  apply H in H1.
  destruct H1 as [l0 H1].
  exists l0.
  rewrite find_phys_add_neq; auto.
  intro contra. subst.
  rewrite Hl in H1.
  inversion H1.
  destruct H1 as [l0 H1].
  apply FSet.add_2.
  apply H.
  exists l0.
  rewrite find_phys_add_neq in H1; auto.
  intro contra. subst.
  rewrite find_phys_add_eq in H1.
  inversion H1; subst.
  contradiction.
Qed.

Definition find_log_bounded_add : forall lay n l p,
  find_log_bounded lay n -> l < n -> find_log_bounded (add lay l p) n.
Proof.
  intros lay n l p H Hl.
  unfold find_log_bounded in *.
  intros p0 l0 Hadd.
  bdestruct (p =? p0); subst.
  rewrite find_log_add_eq in Hadd.
  inversion Hadd; subst. auto.
  rewrite find_log_add_neq in Hadd by auto.
  apply H in Hadd. auto.
Qed.

Definition find_phys_bounded_add : forall lay n l p,
  find_phys_bounded lay n -> p < n -> find_phys_bounded (add lay l p) n.
Proof.
  intros lay n l p H Hp.
  unfold find_phys_bounded in *.
  intros l0 p0 Hadd.
  bdestruct (l =? l0); subst.
  rewrite find_phys_add_eq in Hadd.
  inversion Hadd; subst. auto.
  rewrite find_phys_add_neq in Hadd by auto.
  apply H in Hadd. auto.
Qed.

(* TODO: move to CG *)
Definition valid_q_ordering (q_ordering : option nat -> list nat) n :=
  forall o x, x < n <-> List.In x (q_ordering o).

(* Easy definition that satisfies the spec *)
Fixpoint list_nats n := match n with O => [] | S n' => n' :: list_nats n' end.

Lemma list_nats_is_valid_q_ordering : forall n, valid_q_ordering (fun _ => list_nats n) n.
Proof.
  intros n o x.
  induction n; simpl.
  lia.
  bdestruct (x =? n).
  subst.
  split; intro H; auto.
  split; intro H0.
  right. apply IHn. lia.
  destruct H0 as [H0 | H0]; subst; try contradiction.
  apply IHn in H0. lia.
Qed.

Lemma find_phys_None_implies_alloc_incomplete : forall lay alloc q_ord n o,
  valid_q_ordering q_ord n ->
  well_formed lay ->
  alloc_records_allocated_phys_qubits lay alloc ->
  find_log_bounded lay n ->
  find_phys_bounded lay n ->
  (exists x, x < n /\ find_phys lay x = None) ->
  exists x : FSet.elt, In x (q_ord o) /\ ~ FSet.In x alloc.
Proof.
  intros lay alloc q_ord n o Hqor WF Halloc Hlog Hphys [x [Hx1 Hx2]].


(* stuck -- we probably need some kind of counting argument *)

Admitted.

Lemma build_layout_well_formed : forall U dim (l : gate_list (Map_Unitary U) dim) alloc lay q_ordering lay' alloc',
  well_formed lay ->
  uc_well_typed_l l ->
  alloc_records_allocated_phys_qubits lay alloc ->
  find_log_bounded lay dim ->
  find_phys_bounded lay dim ->
  valid_q_ordering q_ordering dim ->
  build_layout l alloc lay q_ordering = (alloc', lay') ->
  well_formed lay' /\
  alloc_records_allocated_phys_qubits lay' alloc' /\
  find_log_bounded lay' dim /\
  find_phys_bounded lay' dim.
Proof.
  intros U dim l alloc lay q_ordering lay' alloc' WF WT Halloc Hlog Hphys Hqor H.
  gen alloc lay.
  induction l; intros alloc lay WF Halloc Hlog Hphys H.
  simpl in *.
  inversion H; subst.
  auto.
  simpl in H.
  destruct a; dependent destruction m; inversion WT; subst; try apply IHl in H; auto.
  destruct (find_phys lay n) eqn:fpn; destruct (find_phys lay n0) eqn:fpn0.
  - apply IHl in H; auto.
  - remember (get_fresh_qubit (q_ordering (Some n1)) alloc) as x.
    apply IHl in H; auto; clear IHl.
    apply add_well_formed; auto.
    intros [contra | contra].
    apply Halloc in contra.
    contradict contra.
    subst. apply get_fresh_qubit_not_In_alloc.
    eapply find_phys_None_implies_alloc_incomplete.
    apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
    exists n0. split; auto.
    destruct contra as [p contra].
    apply WF in contra.
    rewrite fpn0 in contra.
    inversion contra.
    apply alloc_records_allocated_phys_qubits_add; auto.
    apply find_log_bounded_add; auto.
    apply find_phys_bounded_add; auto.
    subst. apply get_fresh_qubit_lt.
    intros. apply Hqor in H0. auto.
    eapply find_phys_None_implies_alloc_incomplete.
    apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
    exists n0. split; auto.
  - remember (get_fresh_qubit (q_ordering (Some n)) alloc) as x.
    apply IHl in H; auto; clear IHl.
    apply add_well_formed; auto.
    intros [contra | contra].
    apply Halloc in contra.
    contradict contra.
    subst. apply get_fresh_qubit_not_In_alloc.
    eapply find_phys_None_implies_alloc_incomplete.
    apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
    exists n. split; auto.
    destruct contra as [p contra].
    apply WF in contra.
    rewrite fpn in contra.
    inversion contra.
    apply alloc_records_allocated_phys_qubits_add; auto.
    apply find_log_bounded_add; auto.
    apply find_phys_bounded_add; auto.
    subst. apply get_fresh_qubit_lt.
    intros. apply Hqor in H0. auto.
    eapply find_phys_None_implies_alloc_incomplete.
    apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
    exists n. split; auto.
  - remember (get_fresh_qubit (q_ordering None) alloc) as x.
    remember (get_fresh_qubit (q_ordering (Some x)) (FSet.add x alloc)) as y.
    apply IHl in H; auto; clear IHl.
    apply add_well_formed; auto.
    apply add_well_formed; auto.
    intros [contra | contra].
    apply Halloc in contra.
    contradict contra.
    subst. apply get_fresh_qubit_not_In_alloc.
    eapply find_phys_None_implies_alloc_incomplete.
    apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
    exists n. split; auto.
    destruct contra as [p contra].
    apply WF in contra.
    rewrite fpn in contra.
    inversion contra. 
    apply not_In_add; auto.
     admit. (* y <> x ; y is not in (FSet.add x alloc) *)
    intros [contra | contra].
    apply Halloc in contra.
    contradict contra.
    subst. apply get_fresh_qubit_not_In_alloc.
    eapply find_phys_None_implies_alloc_incomplete.
    apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
    exists n. split; auto.
    destruct contra as [p contra].
    apply WF in contra.
    rewrite fpn0 in contra.
    inversion contra.
    apply alloc_records_allocated_phys_qubits_add; auto.
    rewrite find_phys_add_neq; auto.
    apply alloc_records_allocated_phys_qubits_add; auto.
    apply find_log_bounded_add; auto.
    apply find_log_bounded_add; auto.
    apply find_phys_bounded_add; auto.
    apply find_phys_bounded_add; auto.
    subst. apply get_fresh_qubit_lt.
    intros. apply Hqor in H0. auto.
    eapply find_phys_None_implies_alloc_incomplete.
    apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
    exists n. split; auto.
    subst. apply get_fresh_qubit_lt.
    intros. apply Hqor in H0. auto.
    eapply find_phys_None_implies_alloc_incomplete.
    apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
    exists n. split; auto.
Admitted.

Lemma find_log_extend_layout1 : forall n alloc lay q_ordering p l,
  alloc_records_allocated_phys_qubits lay alloc ->
  find_log lay p = Some l ->
  find_log (extend_layout n alloc lay q_ordering) p = Some l.
Proof.
  intros n alloc lay q_ordering p l.
  gen alloc lay.
  induction n; intros alloc lay H1 H2; simpl; auto.
  destruct (find_phys lay n) eqn:fp.
  auto.
  apply IHn.
  apply alloc_records_allocated_phys_qubits_add; auto.
  rewrite find_log_add_neq; auto.
  (* "get_default q_ordering alloc" is not in alloc, but p is *)
Admitted.

Lemma find_log_extend_layout2 : forall m n alloc lay q_ordering p,
  (p < n)%nat ->
  well_formed lay ->
  alloc_records_allocated_phys_qubits lay alloc ->
  find_log lay p = None ->
  exists l, find_log (extend_layout n alloc lay q_ordering) p = Some l /\ (l < m)%nat.
Proof.
  intros m n alloc lay q_ordering p Hp.
  gen alloc lay.
  induction n; intros alloc lay H1 H2 H3; simpl; auto.
lia.

(*
bdestruct (p =? n).
subst. clear IHn.

destruct (find_phys lay n) eqn:fp.

  exists (get_default q_ordering alloc).
  split.
  erewrite find_phys_extend_layout1.
  reflexivity.
  apply alloc_records_allocated_phys_qubits_add; auto.
  apply find_phys_add_eq.


admit.


destruct (find_phys lay n) eqn:fp.

apply IHn; auto. lia.

apply IHn. lia.
  apply alloc_records_allocated_phys_qubits_add; auto.
  rewrite find_log_add_neq; auto.
*)

 Admitted.

Lemma find_phys_extend_layout1 : forall n alloc lay q_ordering l p,
  alloc_records_allocated_phys_qubits lay alloc ->
  find_phys lay l = Some p ->
  find_phys (extend_layout n alloc lay q_ordering) l = Some p.
Proof.
  intros n alloc lay q_ordering l p.
  gen alloc lay.
  induction n; intros alloc lay H1 H2; simpl; auto.
  destruct (find_phys lay n) eqn:fp.
  auto.
  apply IHn.
  apply alloc_records_allocated_phys_qubits_add; auto.
  rewrite find_phys_add_neq; auto.
  intro contra. subst.
  rewrite H2 in fp. inversion fp.
Qed.

Lemma find_phys_extend_layout2 : forall m n alloc lay q_ordering l,
  (l < n)%nat ->
  well_formed lay ->
  alloc_records_allocated_phys_qubits lay alloc ->
  valid_q_ordering q_ordering m ->
  find_phys lay l = None ->
  exists p, find_phys (extend_layout n alloc lay q_ordering) l = Some p /\ (p < m)%nat.
Proof.
  intros m n alloc lay q_ordering l Hl ? ? Hqor.
  gen alloc lay.
  induction n; intros alloc lay WF Halloc H; simpl; auto.
  lia.
  bdestruct (l =? n).
  subst. clear IHn.
  rewrite H.
  exists (get_fresh_qubit (q_ordering None) alloc).
  split.
  erewrite find_phys_extend_layout1.
  reflexivity.
  apply alloc_records_allocated_phys_qubits_add; auto.
  apply find_phys_add_eq.
  apply get_fresh_qubit_lt.
  intros. apply Hqor in H0. auto.
  eapply find_phys_None_implies_alloc_incomplete.
  apply Hqor. apply WF. apply Halloc. (*apply Hlog. apply Hphys.
  exists n. split; auto.
  admit. (*  (get_default q_ordering alloc < m)%nat *)
  destruct (find_phys lay n) eqn:fp.
  apply IHn; auto. lia.
  apply IHn. lia.
  apply alloc_records_allocated_phys_qubits_add; auto.
  rewrite find_phys_add_neq; auto.*)
Admitted.

Lemma extend_layout_well_formed : forall n alloc lay q_ordering,
  well_formed lay ->
  alloc_records_allocated_phys_qubits lay alloc ->
  well_formed (extend_layout n alloc lay q_ordering).
Proof.
  intros n alloc lay q_ordering.
  gen alloc lay.
  induction n; intros alloc lay H1 H2; simpl; auto.
  destruct (find_phys lay n) eqn:fp.
  apply IHn; auto.
  apply IHn.
  apply add_well_formed; auto.
  apply Classical_Prop.and_not_or.
  split.
  intro contra.
  apply H2 in contra.
  assert (~ (FSet.In (get_fresh_qubit (q_ordering None) alloc) alloc)).
  admit.
  contradiction.
  intros [p contra].
  apply H1 in contra.
  rewrite fp in contra.
  inversion contra.
  apply alloc_records_allocated_phys_qubits_add; auto.
Admitted.

Lemma extend_layout_bijective : forall n alloc lay q_ordering,
  well_formed lay ->
  alloc_records_allocated_phys_qubits lay alloc ->
  find_log_bounded lay n ->
  find_phys_bounded lay n ->
  valid_q_ordering q_ordering n ->
  layout_bijective n (extend_layout n alloc lay q_ordering).
Proof.
  intros n alloc lay q_ordering WF H1 H2 H3 H4.
  split; [|split].
  - apply extend_layout_well_formed; auto.
  - intros l Hl.
    destruct (find_phys lay l) eqn:fp.
    exists n0.
    split.
    apply find_phys_extend_layout1; auto.
    apply H3 in fp. auto.
    apply find_phys_extend_layout2; auto.
  - intros p Hp.
    destruct (find_log lay p) eqn:fl.
    exists n0.
    split.
    apply find_log_extend_layout1; auto.
    apply H2 in fl. auto.
    apply find_log_extend_layout2; auto.
Qed.

(** dim is the number of qubits used in the program l and n is the number of
   qubits available on the machine *)
Lemma greedy_layout_bijective : forall U dim (l : gate_list (Map_Unitary U) dim) q_ordering,
  uc_well_typed_l l ->
  valid_q_ordering q_ordering dim ->
  layout_bijective dim (greedy_layout l dim q_ordering).
Proof.
  intros U dim l qubit_ordering WT Hqor.
  unfold greedy_layout.
  destruct (build_layout l FSet.empty empty qubit_ordering) eqn:bl.
  apply build_layout_well_formed with (dim:=dim) in bl as [? [? [? ?]]]; auto.
  apply extend_layout_bijective; auto.
  apply empty_well_formed.
  split; intro H.
  apply FSetFacts.empty_iff in H. easy.
  destruct H as [? H].
  rewrite find_phys_empty in H.
  inversion H.
  intros ? ? H.
  rewrite find_log_empty in H.
  inversion H.
  intros ? ? H.
  rewrite find_phys_empty in H.
  inversion H.
Qed.
