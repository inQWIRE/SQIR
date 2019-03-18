Require Export Denote_Ctrls.

Open Scope ucom_scope.

(** Denotation of ucoms **)

Fixpoint uc_eval (dim : nat) (c : ucom) : Matrix (2^dim) (2^dim) :=
  match c with
  | uskip   => I (2^dim)
  | l *= u  => apply_unitary dim u l
  | c1 ; c2 => uc_eval dim c2 × uc_eval dim c1 
  end.

Lemma WF_uc_eval : forall dim c, uc_well_typed dim c -> WF_Matrix _ _ (uc_eval dim c).
Proof.
  intros dim c H.
  induction H; simpl; auto with wf_db.
  apply apply_unitary_unitary; trivial.
  Search forallb.
  unfold SQIMP.bounded in H0.
  destruct (forallb_forall (fun x : nat => x <? dim) l) as [H2 _].
  specialize (H2 H0).
  intros x H3.
  specialize (H2 _ H3).
  Search (_ <? _).
  apply Nat.ltb_lt; easy.
Qed.
  
(* Basic Lemmas *)

Lemma uskip_id_l : forall (dim : nat) (c : ucom), uc_well_typed dim c -> uc_eval dim (uskip ; c) = uc_eval dim c.
Proof.
  intros WT dim c.
  simpl.
  rewrite Mmult_1_r. reflexivity.
  apply WF_uc_eval. easy.
Qed.

(* Minor optimizations *)

Fixpoint rm_uskips (c : ucom) : ucom :=
  match c with
  | c1 ; c2 => match rm_uskips c1, rm_uskips c2 with
              | uskip, c2' => c2'
              | c1', uskip => c1'
              | c1', c2'   => c1'; c2'
              end
  | c'      => c'
  end.

Hint Resolve WF_uc_eval : wf_db.

Lemma rm_uskips_sound : forall c dim,
  uc_well_typed dim c ->
  uc_eval dim c = uc_eval dim (rm_uskips c).
Proof.
  intros c dim WT.
  induction WT; trivial.
  simpl.
  destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; trivial.
  - rewrite IHWT1, IHWT2.
    simpl. Msimpl. reflexivity.
  - rewrite IHWT1, IHWT2 in *.
    
(* Need to show that rm_uskips preserves WT *)
    simpl. Msimpl.
    rewrite Mmult_1_r.
    reflexivity.
    apply WF_mult.
    apply WF_uc_eval; auto.
Abort.

Open Scope ucom.
Close Scope C_scope.
Close Scope R_scope.

(* Note: Make singleton coercions work! *)
Lemma reorder1 : forall (m n dim : nat) (U V : Unitary 1),
  m <> n ->
  (m < dim) ->
  (n < dim) -> 
  uc_eval dim ([m] *= U ; [n] *= V) = uc_eval dim ([n] *= V ; [m] *= U). 
Proof.
  intros m n dim U V NE Lm Ln.
  simpl.
  destruct (unitary_gate_unitary U) as [WFU _].
  destruct (unitary_gate_unitary V) as [WFV _].
  simpl in *.
  remember (denote_unitary U) as DU.
  remember (denote_unitary V) as DV.
  clear HeqDU HeqDV.
  bdestruct (m <? n).
  - remember (n - m - 1) as k.
    replace n with (m + 1 + k) by omega.
    replace (2 ^ (m+1+k)) with (2^m * 2 * 2^k) by unify_pows_two.
    repeat rewrite <- id_kron.
    remember (dim - (m + 1 + k) - 1) as j.
    replace (dim - m - 1) with (k + 1 + j) by omega.
    replace (2 ^ (k + 1 + j)) with (2^k * 2 * 2^ j) by unify_pows_two.
    repeat rewrite <- id_kron.
    simpl in *.
    repeat rewrite kron_assoc.
    repeat rewrite Nat.mul_assoc.
    Msimpl'.
    reflexivity.
  - rename m into n, n into m.
    remember (n - m - 1) as k.
    replace n with (m + 1 + k) by omega.
    replace (2 ^ (m+1+k)) with (2^m * 2 * 2^k) by unify_pows_two.
    repeat rewrite <- id_kron.
    remember (dim - (m + 1 + k) - 1) as j.
    replace (dim - m - 1) with (k + 1 + j) by omega.
    replace (2 ^ (k + 1 + j)) with (2^k * 2 * 2^ j) by unify_pows_two.
    repeat rewrite <- id_kron.
    simpl in *.
    repeat rewrite kron_assoc.
    repeat rewrite Nat.mul_assoc.
    Msimpl'.
    reflexivity.
Qed.
    
