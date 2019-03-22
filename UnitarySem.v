Require Export Denote_Ctrls.

Open Scope ucom_scope.

(** Denotation of ucoms **)

Fixpoint uc_eval (dim : nat) (c : ucom) : Matrix (2^dim) (2^dim) :=
  match c with
  | uskip   => I (2^dim)
  | l *= u  => apply_unitary dim u l
  | c1 ; c2 => uc_eval dim c2 × uc_eval dim c1 
  end.

Lemma WF_uc_eval_uapp : forall dim n (u : Unitary n) l, uc_well_typed dim (l *= u) -> WF_Matrix _ _ (apply_unitary dim u l).
Proof.
  intros dim n u l H.
  inversion H; subst.
  apply apply_unitary_unitary; trivial.
  unfold SQIMP.bounded in H5.
  destruct (forallb_forall (fun x : nat => x <? dim) l) as [H2 _].
  specialize (H2 H5).
  intros x H3.
  specialize (H2 _ H3).
  apply Nat.ltb_lt; easy.
Qed.  
  
Lemma WF_uc_eval : forall dim c, uc_well_typed dim c -> WF_Matrix _ _ (uc_eval dim c).
Proof.
  intros dim c H.
  induction H; simpl; auto with wf_db.
  apply WF_uc_eval_uapp.
  constructor; easy.
Qed.

Hint Resolve WF_uc_eval_uapp WF_uc_eval : wf_db.

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

Hint Constructors uc_well_typed : type_db.

Lemma WT_rm_uskips : forall c dim, uc_well_typed dim c <-> uc_well_typed dim (rm_uskips c).
Proof.
  intros c dim.
  split; intros H.
  - induction H.
    + constructor.
    + simpl.
      destruct (rm_uskips c1), (rm_uskips c2); auto with type_db.
    + simpl. auto with type_db.
  - induction c.
    + constructor.
    + destruct (rm_uskips (c1; c2)) eqn:E.
      * simpl in E.
        destruct (rm_uskips c1), (rm_uskips c2); auto with type_db; discriminate.
      * simpl in E.
        destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; auto with type_db;
        rewrite <- E in H; inversion H; auto with type_db.
      * simpl in E.
        destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; auto with type_db;
        rewrite <- E in H; inversion H; auto with type_db.
    + simpl in H; easy.
Qed.
      

Lemma rm_uskips_sound : forall c dim,
  uc_well_typed dim c ->
  uc_eval dim c = uc_eval dim (rm_uskips c).
Proof.
  intros c dim WT.
  induction WT; trivial.
  simpl.
  apply WT_rm_uskips in WT1.
  apply WT_rm_uskips in WT2.
  destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; trivial;
    rewrite IHWT1, IHWT2; simpl; Msimpl; trivial.
  - inversion WT2; simpl; Msimpl; easy.
  - inversion WT1; simpl; Msimpl; easy.
Qed.    

Close Scope C_scope.
Close Scope R_scope.

Inductive skip_free : ucom -> Prop :=
  | SF_seq : forall c1 c2, skip_free c1 -> skip_free c2 -> skip_free (c1; c2)
  | SF_app : forall n l (u : Unitary n), skip_free (l *= u).

Lemma rm_uskips_correct : forall c,
  (rm_uskips c) = uskip \/ skip_free (rm_uskips c).
Proof.
  intro c.
  induction c.
  - left; easy.
  - destruct IHc1; destruct IHc2.
    + left. simpl. rewrite H. rewrite H0. reflexivity.
    + right. simpl. rewrite H. assumption.
    + right. simpl. rewrite H0. 
      (* I'm sure there's a better way to do this... *)
      assert (rm_uskips c1 = match rm_uskips c1 with
                             | uskip => uskip
                             | u; u0 => u; u0
                             | @uapp n u v => v *= u
                             end).
      destruct (rm_uskips c1); try easy.
      rewrite <- H1. assumption.
    + right. simpl. 
      destruct (rm_uskips c1); try assumption;
      destruct (rm_uskips c2); try (apply SF_seq); easy. 
  - right; simpl. apply SF_app.
Qed.

Fixpoint count_ops (c : ucom) : nat :=
  match c with
  | c1; c2 => (count_ops c1) + (count_ops c2)
  | _ => 1
  end.

Lemma rm_uskips_reduces_count : forall c,
  count_ops (rm_uskips c) <= count_ops c.
Proof.
  intro c.
  induction c.
  - simpl. omega.
  - simpl. destruct (rm_uskips c1); try omega; 
    destruct (rm_uskips c2); 
    simpl; simpl in IHc1; simpl in IHc2;
    omega.
  - simpl. omega.
Qed.

Open Scope ucom.

(* Note: Make singleton coercions work! *)
Lemma slide1 : forall (m n dim : nat) (U V : Unitary 1),
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

Fixpoint flat_append (c1 c2 : ucom) : ucom := 
  match c1 with
  | c1'; c2' => c1' ; (flat_append c2' c2)
  | _ => c1 ; c2
  end.

Fixpoint flatten (c: ucom) : ucom :=
  match c with
  | c1; c2 => flat_append (flatten c1) (flatten c2)
  | _ => c
  end.

Lemma flatten_sound : forall c dim,  
  uc_well_typed dim c ->
  uc_eval dim c = uc_eval dim (flatten c).
Proof.
  intros c dim WT.
  induction WT; try easy.
  simpl.
  rewrite IHWT1. rewrite IHWT2.
Admitted.

(* Cancel a single X gate on qubit q, if possible. This will either 
   return None or (Some c') where c' is the result of removing the 
   appropriate X gate from c.
   
   This function will insert an extra uskip instruction if the cancelled
   gate is at the end of the circuit... I should probably fix that. *)
Fixpoint cancel_X (c : ucom) (q : Var) : ucom option :=
  match c with
  | [q'] *= X => 
      if q =? q' then Some uskip else None
  | [q'] *= X; c' => 
      if q =? q' then Some c' else None
  | [q1, q2] *= CNOT; c' => 
      if q =? q2 
      then match cancel_not c' q with
           | None => None
           | Some c'' => Some ([q1, q2] *= CNOT; c'')
           end
      else if q =? q1 then None
           else match cancel_not c' q with
                | None => None
                | Some c'' => Some ([q1, q2] *= CNOT; c'')
                end
  | l *= U; c' => 
      if (inb q l)
      then None
      else match cancel_X c' q with
           | None => None
           | Some c'' => Some (l *= U; c'')
           end
  end

let (c', b) = cancel_not c q in
              (other gate; c', b)

  | _ => None

(* Call cancel_X on all X gates in the circuit. *)
Fixpoint rm_nots (c : ucom) : ucom :=
  match c with
  | [q] *= X; c' => 
      match cancel_not c' q with
      | None => [q] *= X; (rm_nots c')
      | Some c'' => rm_nots c''
      end
  | c1'; c2' => c1'; (rm_nots c2')
  | _ => c

Definition rm_nots (c : ucom) : ucom := rm_nots' (flatten c)

Definition q1 : Var := 0.
Definition q2 : Var := 1.
Definition q3 : Var := 2.
Definition example1 : ucom := ((q1 *= _X; q2 *= _H); ((q1 *= _X; q2 *= _X); ([q3,q2] *= CNOT; q2 *= _X))).
Compute (flatten example1).