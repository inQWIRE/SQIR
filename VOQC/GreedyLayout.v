Require Import QuantumLib.VectorStates.
Require Import MappingGateSet.
Require Import Layouts.
Require Import ConnectivityGraph.

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
Fixpoint build_layout {U dim} (l : gate_list (Map_Unitary U) dim) (alloc : FSet.t) (lay : layout) (q_ordering : option nat -> list nat) : FSet.t * layout :=
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
          let n_phys := get_fresh_qubit (q_ordering (Some m_phys)) 
                                        (FSet.add m_phys alloc) in
          let alloc' := FSet.add n_phys (FSet.add m_phys alloc) in
          let lay' := add (add lay m m_phys) n n_phys in
          build_layout t alloc' lay' q_ordering
      end
  | _ :: t => build_layout t alloc lay q_ordering
  end.

(** Choose a physical qubit for any unallocated logical qubits. n is the number
    of physical qubits available. *)
Fixpoint extend_layout (n : nat) (alloc : FSet.t) (lay : layout) (prefs: list nat) :=
  match n with
  | O => lay
  | S n' => 
      match find_phys lay n' with 
      | Some _ => extend_layout n' alloc lay prefs
      | None => let m := get_fresh_qubit prefs alloc in
               extend_layout n' (FSet.add m alloc) (add lay n' m) prefs
      end
  end.

(** dim is the number of qubits used in the program l and n is the number of
   qubits available on the machine *)
Definition greedy_layout {U dim} (l : gate_list (Map_Unitary U) dim) (n : nat) (q_ordering : option nat -> list nat) : layout :=
  let (alloc, lay) := build_layout l FSet.empty empty q_ordering in
  extend_layout n alloc lay (q_ordering None).

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

Lemma bounded_set_incomplete : forall (s : FSet.t) n,
  FSet.cardinal s < n ->
  (forall x, FSet.In x s -> x < n) ->
  exists y, y < n /\ ~ FSet.In y s.
Proof.
  intros s n.
  gen s.
  induction n; intros s Hs1 Hs2.
  lia.
  remember (FSet.max_elt s) as o.
  symmetry in Heqo.
  destruct o.
  - (* max_elt is Some *)
    remember (FSet.remove e s) as s'.
    assert (FSet.cardinal s' < n).
    { rewrite <- FSetProps.remove_cardinal_1 with (x:=e) in Hs1.
      subst. lia.
      apply FSet.max_elt_1. auto. }
    assert (forall x, FSet.In x s' -> x < n).
    { intros x Hx.
      subst s'.
      assert (x <> e).
      intro contra.
      contradict Hx.
      apply FSet.remove_1. auto.
      bdestruct (x =? n).
      subst.
      apply FSet.remove_3 in Hx.
      assert (Heqo':=Heqo).
      eapply FSet.max_elt_2 in Heqo.
      2: apply Hx.
      apply FSet.max_elt_1 in Heqo'.
      apply Hs2 in Heqo'.
      lia.
      apply FSet.remove_3 in Hx.
      apply Hs2 in Hx. lia. }
    specialize (IHn s' H H0). 
    destruct IHn as [y [Hy1 Hy2]].
    bdestruct (y =? e).
    + (* y = e *)
      subst.
      exists n.
      split; auto.
      intro contra.
      apply FSet.max_elt_2 with (x:=e) in contra; auto.
    + (* y <> e *)
      exists y.
      split; auto.
      intro contra.
      contradict Hy2.
      subst s'.
      apply FSetProps.FM.remove_iff.
      split; auto.
  - (* max_elt is None *)
    apply FSet.max_elt_3 in Heqo.
    exists 0. split. lia.
    apply FSetProps.empty_is_empty_1 in Heqo.
    rewrite Heqo.
    intro contra.
    apply FSetFacts.empty_iff in contra.
    auto.
Qed.

Fixpoint record_Somes (f : nat -> option nat) (n : nat) : FSet.t :=
  match n with
  | O => FSet.empty
  | S n' => match f n' with
           | None => record_Somes f n'
           | Some x => FSet.add x (record_Somes f n')
           end
  end.

Lemma record_Somes_size : forall f n x,
  x < n -> f x = None ->
  FSet.cardinal (record_Somes f n) < n.
Proof.
  assert (Haux: forall f n, FSet.cardinal (record_Somes f n) < S n).
  { intros f n.
    induction n; simpl.
    rewrite FSetProps.empty_cardinal. lia.
    destruct (f n).
    destruct (FSetProps.In_dec n0 (record_Somes f n)).
    rewrite FSetProps.add_cardinal_1 by assumption. lia.
    rewrite FSetProps.add_cardinal_2 by assumption. lia.
    lia. }
  intros f n x H1 H2.
  induction n; simpl in *.
  lia.
  bdestruct (x =? n).
  subst.
  rewrite H2.
  apply Haux.
  destruct (f n).
  destruct (FSetProps.In_dec n0 (record_Somes f n)).
  rewrite FSetProps.add_cardinal_1 by assumption. lia.
  rewrite FSetProps.add_cardinal_2 by assumption. lia.
  lia.
Qed.

Lemma record_Somes_find_phys_bounded : forall lay m n,
  find_phys_bounded lay m -> 
  forall x, FSet.In x (record_Somes (find_phys lay) n) -> x < m.
Proof.
  intros lay m n Hbnd x Hx.
  induction n; simpl in *.
  apply FSetFacts.empty_iff in Hx.
  contradiction.
  destruct (find_phys lay n) eqn:fl; auto.
  apply Hbnd in fl.
  apply FSetFacts.add_iff in Hx.
  destruct Hx as [Hx | Hx]; auto.
  lia.
Qed.

Lemma record_Somes_find_log_bounded : forall lay m n,
  find_log_bounded lay m -> 
  forall x, FSet.In x (record_Somes (find_log lay) n) -> x < m.
Proof.
  intros lay m n Hbnd x Hx.
  induction n; simpl in *.
  apply FSetFacts.empty_iff in Hx.
  contradiction.
  destruct (find_log lay n) eqn:fl; auto.
  apply Hbnd in fl.
  apply FSetFacts.add_iff in Hx.
  destruct Hx as [Hx | Hx]; auto.
  lia.
Qed.

Lemma record_Somes_correct : forall f n x,
  FSet.In x (record_Somes f n) <-> exists y, y < n /\ f y = Some x.
Proof.
  intros f n x.  
  induction n; simpl.
  rewrite FSetFacts.empty_iff.
  split; intro H; try easy.
  destruct H as [? [? ?]]. lia.
  split; intro H.
  destruct (f n) eqn:fn.
  apply FSetFacts.add_iff in H.
  destruct H.
  subst.
  exists n. split; auto.
  apply IHn in H as [y [? ?]].
  exists y. split; auto.
  apply IHn in H as [y [? ?]].
  exists y. split; auto.
  destruct H as [y [? ?]].
  bdestruct (y =? n).
  subst.
  rewrite H0.
  apply FSetFacts.add_iff.
  left. auto.
  destruct (f n) eqn:fn.
  apply FSetFacts.add_iff.
  right. apply IHn.
  exists y. split. lia. auto.
  apply IHn.
  exists y. split. lia. auto.
Qed.

Lemma not_Some_implies_None : forall A (o : option A), ~ (exists x, o = Some x) -> o = None.
Proof.
  intros A o H.
  destruct o; auto.
  contradict H.
  exists a. auto.
Qed.

Lemma find_phys_None_implies_find_log_None : forall lay n,
  well_formed lay ->
  find_log_bounded lay n ->
  find_phys_bounded lay n ->
  (exists x, x < n /\ find_phys lay x = None) ->
  exists y, y < n /\ find_log lay y = None.
Proof.
  intros lay n WF Hlog Hphys [x [Hx1 Hx2]].
  remember (record_Somes (find_phys lay) n) as s.
  assert (FSet.cardinal s < n).
  { subst s. eapply record_Somes_size. apply Hx1. auto. }
  assert (forall x, FSet.In x s -> x < n).
  { subst s. apply record_Somes_find_phys_bounded. auto. }
  assert (exists y, y < n /\ ~ FSet.In y s).
  { apply bounded_set_incomplete; auto. }
  destruct H1 as [y [Hy1 Hy2]].
  exists y.
  split; auto.
  subst s.
  rewrite record_Somes_correct in Hy2.
  apply not_Some_implies_None.
  intro contra.
  contradict Hy2.
  destruct contra as [z Hz].
  assert (z < n).
  eapply Hlog. apply Hz.
  apply WF in Hz.
  exists z.
  split; auto.
Qed.

Lemma find_log_None_implies_find_phys_None : forall lay n,
  well_formed lay ->
  find_log_bounded lay n ->
  find_phys_bounded lay n ->
  (exists x, x < n /\ find_log lay x = None) ->
  exists y, y < n /\ find_phys lay y = None.
Proof.
  intros lay n WF Hlog Hphys [x [Hx1 Hx2]].
  remember (record_Somes (find_log lay) n) as s.
  assert (FSet.cardinal s < n).
  { subst s. eapply record_Somes_size. apply Hx1. auto. }
  assert (forall x, FSet.In x s -> x < n).
  { subst s. apply record_Somes_find_log_bounded. auto. }
  assert (exists y, y < n /\ ~ FSet.In y s).
  { apply bounded_set_incomplete; auto. }
  destruct H1 as [y [Hy1 Hy2]].
  exists y.
  split; auto.
  subst s.
  rewrite record_Somes_correct in Hy2.
  apply not_Some_implies_None.
  intro contra.
  contradict Hy2.
  destruct contra as [z Hz].
  assert (z < n).
  eapply Hphys. apply Hz.
  apply WF in Hz.
  exists z.
  split; auto.
Qed.

Lemma find_phys_None_implies_alloc_incomplete : forall lay alloc q_ord n o,
  valid_q_ordering q_ord n ->
  well_formed lay ->
  alloc_records_allocated_phys_qubits lay alloc ->
  find_log_bounded lay n ->
  find_phys_bounded lay n ->
  (exists x, x < n /\ find_phys lay x = None) ->
  (match o with Some y => find_log lay y <> None | _ => True end) ->
  exists x : FSet.elt, In x (q_ord o) /\ ~ FSet.In x alloc.
Proof.
  intros lay alloc q_ord n o Hqor WF Halloc Hlog Hphys [x [Hx1 Hx2]] Ho.
  apply Classical_Pred_Type.not_all_not_ex.
  intro contra.
  assert (exists y, y < n /\ find_log lay y = None).
  { eapply find_phys_None_implies_find_log_None; auto.
    exists x. auto. }
  destruct H as [y [Hy1 Hy2]].
  specialize (contra y).
  apply Classical_Prop.not_and_or in contra as [contra | contra].
  contradict contra.                                                             
  apply Hqor.
  destruct o; auto.
  split; auto.
  intro contra.
  subst. easy.
  apply Classical_Prop.NNPP in contra.
  apply Halloc in contra.
  destruct contra as [z contra].
  apply WF in contra.
  rewrite contra in Hy2.
  discriminate.
Qed.

Lemma valid_q_ordering_lt : forall q_ordering dim o,
  valid_q_ordering q_ordering dim ->
  forall x : nat, In x (q_ordering o) -> 
  x < dim.
Proof.
  intros q_ordering dim o H1 x H2.
  apply H1 in H2.
  destruct o; auto.
  destruct H2 as [? ?]; auto.
Qed.

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
    apply WF in fpn. rewrite fpn. easy.
    destruct contra as [p contra].
    apply WF in contra.
    rewrite fpn0 in contra.
    inversion contra.
    apply alloc_records_allocated_phys_qubits_add; auto.
    apply find_log_bounded_add; auto.
    apply find_phys_bounded_add; auto.
    subst. apply get_fresh_qubit_lt.
    apply valid_q_ordering_lt. auto.
    eapply find_phys_None_implies_alloc_incomplete.
    apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
    exists n0. split; auto.
    apply WF in fpn. rewrite fpn. easy.
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
    apply WF in fpn0. rewrite fpn0. easy.
    destruct contra as [p contra].
    apply WF in contra.
    rewrite fpn in contra.
    inversion contra.
    apply alloc_records_allocated_phys_qubits_add; auto.
    apply find_log_bounded_add; auto.
    apply find_phys_bounded_add; auto.
    subst. apply get_fresh_qubit_lt.
    apply valid_q_ordering_lt. auto.
    eapply find_phys_None_implies_alloc_incomplete.
    apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
    exists n. split; auto.
    apply WF in fpn0. rewrite fpn0. easy.
  - remember (get_fresh_qubit (q_ordering None) alloc) as x.
    remember (get_fresh_qubit (q_ordering (Some x)) (FSet.add x alloc)) as y.
    assert (WF' : well_formed (add lay n x)).
    { apply add_well_formed; auto.
      intros [contra | contra].
      apply Halloc in contra.
      contradict contra.
      subst x. apply get_fresh_qubit_not_In_alloc.
      eapply find_phys_None_implies_alloc_incomplete.
      apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
      exists n. split; auto. easy.
      destruct contra as [p contra].
      apply WF in contra.
      rewrite fpn in contra.
      inversion contra. }
    assert (Halloc' : alloc_records_allocated_phys_qubits (add lay n x) (FSet.add x alloc)).
    { apply alloc_records_allocated_phys_qubits_add; auto. }
    assert (x < dim).
    { subst x. apply get_fresh_qubit_lt.
      intros. apply Hqor in H0. auto.
      eapply find_phys_None_implies_alloc_incomplete.
      apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
      exists n. split; auto. easy. }
    assert (y < dim).
    { subst y.  apply get_fresh_qubit_lt.
      apply valid_q_ordering_lt. auto.
      eapply find_phys_None_implies_alloc_incomplete.
      apply Hqor. apply WF'. apply Halloc'.
      apply find_log_bounded_add; auto.
      apply find_phys_bounded_add; auto.
      exists n0. split; auto.
      rewrite find_phys_add_neq; auto.
      rewrite find_log_add_eq. easy. }
    apply IHl in H; auto; clear IHl.
    apply add_well_formed; auto.
    intros [contra | contra].
    apply Halloc' in contra.
    contradict contra.
    subst y. apply get_fresh_qubit_not_In_alloc.
    eapply find_phys_None_implies_alloc_incomplete.
    apply Hqor. 
    apply WF'.
    apply Halloc'.
    apply find_log_bounded_add; auto.
    apply find_phys_bounded_add; auto.
    exists n0. split; auto.
    rewrite find_phys_add_neq; auto.
    rewrite find_log_add_eq. easy.
    destruct contra as [p contra].
    apply WF' in contra.
    rewrite find_phys_add_neq in contra; auto.
    rewrite fpn0 in contra.
    inversion contra.
    apply alloc_records_allocated_phys_qubits_add; auto.
    rewrite find_phys_add_neq; auto.
    apply find_log_bounded_add; auto.
    apply find_log_bounded_add; auto.
    apply find_phys_bounded_add; auto.
    apply find_phys_bounded_add; auto.
Qed.

Lemma extend_layout_well_formed : forall dim n alloc lay q_ordering,
  well_formed lay ->
  alloc_records_allocated_phys_qubits lay alloc ->
  find_log_bounded lay dim ->
  find_phys_bounded lay dim ->
  valid_q_ordering q_ordering dim ->
  n <= dim ->
  well_formed (extend_layout n alloc lay (q_ordering None)).
Proof.
  intros dim n alloc lay q_ordering ? ? ? ? Hqor.
  gen alloc lay.
  induction n; intros alloc lay WF Halloc  Hlog Hphys Hn; simpl; auto.
  destruct (find_phys lay n) eqn:fp.
  apply IHn; auto. lia.
  apply IHn.
  apply add_well_formed; auto.
  apply Classical_Prop.and_not_or.
  split.
  intro contra.
  apply Halloc in contra.
  contradict contra.
  apply get_fresh_qubit_not_In_alloc.
  eapply find_phys_None_implies_alloc_incomplete.
  apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
  exists n. split; auto. easy.
  intros [p contra].
  apply WF in contra.
  rewrite fp in contra.
  inversion contra.
  apply alloc_records_allocated_phys_qubits_add; auto.
  apply find_log_bounded_add; auto.
  apply find_phys_bounded_add; auto.
  apply get_fresh_qubit_lt.
  apply Hqor.
  eapply find_phys_None_implies_alloc_incomplete.
  apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
  exists n. split; auto. easy.
  lia.
Qed.

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

Lemma find_phys_extend_layout2 : forall dim n alloc lay q_ordering l,
  (l < n)%nat ->
  well_formed lay ->
  alloc_records_allocated_phys_qubits lay alloc ->
  find_log_bounded lay dim ->
  find_phys_bounded lay dim ->
  valid_q_ordering q_ordering dim ->
  n <= dim ->
  find_phys lay l = None ->
  exists p, find_phys (extend_layout n alloc lay (q_ordering None)) l = Some p /\ (p < dim)%nat.
Proof.
  intros dim n alloc lay q_ordering l Hl ? ? ? ? Hqor.
  gen alloc lay.
  induction n; intros alloc lay WF Halloc Hlog Hphys Hn H; simpl; auto.
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
  apply get_fresh_qubit_lt. apply Hqor.
  eapply find_phys_None_implies_alloc_incomplete.
  apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
  exists n. split; auto. easy.
  destruct (find_phys lay n) eqn:fp.
  apply IHn; auto. lia. lia.
  apply IHn. lia.
  apply add_well_formed; auto.
  intros [contra | contra].
  apply Halloc in contra.
  contradict contra.
  apply get_fresh_qubit_not_In_alloc.
  eapply find_phys_None_implies_alloc_incomplete.
  apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
  exists n. split; auto. easy. 
  destruct contra as [? contra].
  apply WF in contra. rewrite fp in contra. inversion contra.
  apply alloc_records_allocated_phys_qubits_add; auto.
  apply find_log_bounded_add; auto.
  apply find_phys_bounded_add; auto.
  apply get_fresh_qubit_lt.
  apply Hqor.
  eapply find_phys_None_implies_alloc_incomplete.
  apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
  exists n. split; auto. easy.
  lia.
  rewrite find_phys_add_neq; auto.
Qed.

Lemma find_log_extend_layout_bounded : forall dim n alloc lay prefs,
  n <= dim ->
  find_log_bounded lay dim ->
  find_log_bounded (extend_layout n alloc lay prefs) dim.
Proof.
  intros dim n alloc lay prefs Hn.
  gen alloc lay.
  induction n; intros alloc lay Hlog; simpl; auto.
  destruct (find_phys lay n) eqn:fp.
  apply IHn; auto. lia.
  apply IHn. lia.
  apply find_log_bounded_add; auto.
Qed.

Lemma find_phys_extend_layout_bounded : forall dim n alloc lay q_ordering,
  well_formed lay ->
  alloc_records_allocated_phys_qubits lay alloc ->
  find_log_bounded lay dim ->
  find_phys_bounded lay dim ->
  valid_q_ordering q_ordering dim ->
  n <= dim ->
  find_phys_bounded (extend_layout n alloc lay (q_ordering None)) dim.
Proof.
  intros dim n alloc lay q_ordering ? ? ? ? Hqor Hn.
  gen alloc lay.
  induction n; intros alloc lay WF Halloc Hlog Hphys; simpl; auto.
  destruct (find_phys lay n) eqn:fp.
  apply IHn; auto. lia.
  apply IHn. lia.
  apply add_well_formed; auto.
  intros [contra | contra].
  apply Halloc in contra.
  contradict contra.
  apply get_fresh_qubit_not_In_alloc.
  eapply find_phys_None_implies_alloc_incomplete.
  apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
  exists n. split; auto. easy. 
  destruct contra as [? contra].
  apply WF in contra. rewrite fp in contra. inversion contra.
  apply alloc_records_allocated_phys_qubits_add; auto.
  apply find_log_bounded_add; auto.
  apply find_phys_bounded_add; auto.
  apply get_fresh_qubit_lt.
  apply Hqor.
  eapply find_phys_None_implies_alloc_incomplete.
  apply Hqor. apply WF. apply Halloc. apply Hlog. apply Hphys.
  exists n. split; auto. easy.
Qed.

Lemma find_log_extend_layout : forall dim alloc lay q_ordering p,
  (p < dim)%nat ->
  well_formed lay ->
  alloc_records_allocated_phys_qubits lay alloc ->
  find_log_bounded lay dim ->
  find_phys_bounded lay dim ->
  valid_q_ordering q_ordering dim ->
  exists l, find_log (extend_layout dim alloc lay (q_ordering None)) p = Some l /\ (l < dim)%nat.
Proof.
  intros dim alloc lay q_ordering p Hp WF Halloc Hlog Hphys Hqor.
  remember (extend_layout dim alloc lay (q_ordering None)) as elay.
  apply Classical_Pred_Type.not_all_not_ex.
  intro Hcontra.
  assert (contra: find_log elay p = None).
  { apply not_Some_implies_None.
    intros [? contra].
    assert (x < dim).
    eapply find_log_extend_layout_bounded with (n:=dim). 
    lia. apply Hlog. subst elay. apply contra.
    specialize (Hcontra x).
    apply Classical_Prop.not_and_or in Hcontra as [? | ?]; auto. }
  clear Hcontra.
  assert (H: exists p, p < dim /\ find_log elay p = None).
  { exists p. auto. }
  clear contra.
  apply find_log_None_implies_find_phys_None in H.
  destruct H as [? [? H]].
  destruct (find_phys lay x) eqn:fp.
  eapply find_phys_extend_layout1 with (n:=dim) (q_ordering:=q_ordering None) in fp; auto.
  2: apply Halloc.
  rewrite <- Heqelay in fp.
  rewrite H in fp. inversion fp.
  eapply find_phys_extend_layout2 with (n:=dim) (dim:=dim) in fp; auto.
  2: apply Halloc.
  2: apply Hqor.
  destruct fp as [? [fp ?]].
  rewrite <- Heqelay in fp.
  rewrite H in fp. inversion fp.
  subst. apply extend_layout_well_formed with (dim:=dim); auto.
  subst. apply find_log_extend_layout_bounded; auto.
  subst. apply find_phys_extend_layout_bounded; auto.
Qed.

Lemma extend_layout_bijective : forall n alloc lay q_ordering,
  well_formed lay ->
  alloc_records_allocated_phys_qubits lay alloc ->
  find_log_bounded lay n ->
  find_phys_bounded lay n ->
  valid_q_ordering q_ordering n ->
  layout_bijective n (extend_layout n alloc lay (q_ordering None)).
Proof.
  intros n alloc lay q_ordering WF H1 H2 H3 H4.
  split; [|split].
  - apply extend_layout_well_formed with (dim:=n); auto.
  - intros l Hl.
    destruct (find_phys lay l) eqn:fp.
    exists n0.
    split.
    apply find_phys_extend_layout1; auto.
    apply H3 in fp. auto.
    apply find_phys_extend_layout2; auto.
  - intros p Hp.
    apply find_log_extend_layout; auto.
Qed.

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
