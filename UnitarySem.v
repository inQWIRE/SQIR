Require Export SQIMP.
Require Export Quantum.

Open Scope ucom_scope.

(** Denotation of Unitaries *)

Definition pad {n} (start dim : nat) (A : Square (2^n)) : Square (2^dim) :=
  if start + n <=? dim then I (2^start) ⊗ A ⊗ I (2^(dim - n - start)) else I _.

Lemma WF_pad : forall n start dim (A : Square (2^n)),
  WF_Matrix _ _ A ->
  WF_Matrix _ _ (pad start dim A).
Proof.
  intros n start dim A. unfold pad.
  bdestruct (start + n <=? dim); auto with wf_db.
Qed.  

(* k must be 1, but dependent types... *)
Definition ueval1 {k} (dim n : nat) (u : Unitary k) : Square (2^dim) :=
  @pad 1 n dim
  match u with  
  | U_H         => hadamard 
  | U_X         => σx
  | U_Y         => σy
  | U_Z         => σz
  | U_R ϕ       => phase_shift ϕ
  | _           => I (2^1)
  end.

(* Restriction: m <> n and m, n < dim *)
Definition ueval_cnot (dim m n: nat) : Square (2^dim) :=
  if (m <? n) then
    @pad (1+(n-m-1)+1) m dim (∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I (2^(n-m)))
  else if (n <? m) then
    @pad (1+(m-n-1)+1) n dim (σx ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ .+ I (2^(m-n)) ⊗ ∣0⟩⟨0∣)
  else
    I (2^dim).

Definition ueval {n} (dim : nat) (u : Unitary n) (l : list nat) : Square (2^dim) :=
  match n, l with
  | 1, [i]   => ueval1 dim i u
  | 2, i::[j] => ueval_cnot dim i j
  | _, _     => I _
  end.

(** Denotation of ucoms **)

Fixpoint uc_eval (dim : nat) (c : ucom) : Matrix (2^dim) (2^dim) :=
  match c with
  | uskip    => I (2^dim)
  | uapp u l => ueval dim u l
  | c1 ; c2  => uc_eval dim c2 × uc_eval dim c1 
  end.

(** Well-formedness **)

Lemma WF_ueval1 : forall dim n (u : Unitary 1), WF_Matrix _ _ (ueval1 dim n u).
Proof.
  intros dim n u.
  apply WF_pad.
  destruct u; auto with wf_db.
Qed.  
  
Lemma WF_ueval_cnot : forall dim m n, WF_Matrix _ _ (ueval_cnot dim m n). 
Proof.
  intros dim m n.
  unfold ueval_cnot.
  bdestruct (m <? n); [|bdestruct (n <? m)];
    try apply WF_pad; unify_pows_two; auto 10 with wf_db.    
Qed.  

Lemma WF_ueval : forall n dim (u : Unitary n) l, WF_Matrix _ _ (ueval dim u l).
Proof.
  intros n dim u l.
  destruct n as [|[|[|n']]]; simpl; auto with wf_db.
  - destruct l as [|i [| j l]]; simpl; auto with wf_db.
    apply WF_ueval1.
  - destruct l as [|i [| j [| k l]]]; simpl; auto with wf_db.
    apply WF_ueval_cnot.
Qed.  

Lemma WF_uc_eval : forall dim c, WF_Matrix _ _ (uc_eval dim c).
Proof.
  intros dim c.
  induction c; simpl; auto with wf_db.
  apply WF_ueval.
Qed.

Hint Resolve WF_ueval WF_uc_eval : wf_db.


(* Some unit tests *)

Lemma eval_H : uc_eval 1 (H 0) = hadamard.
Proof.
  simpl. unfold ueval1, pad. (* have these automatically simplify *)
  simpl. Msimpl. reflexivity.
Qed.

Lemma eval_HHpar : uc_eval 2 (H 0; H 1) = hadamard ⊗ hadamard.
Proof.
  simpl. unfold ueval1, pad. (* have these automatically simplify *)
  simpl. Msimpl. reflexivity.
Qed.

Lemma eval_HHseq : uc_eval 2 (H 0; H 0) = I 4.
Proof.
  simpl. unfold ueval1, pad. (* have these automatically simplify *)
  simpl. Msimpl. solve_matrix.
Qed.

Lemma eval_CNOT : uc_eval 2 (CNOT 0 1) = cnot.
Proof.
  unfold uc_eval. simpl.
  simpl. unfold ueval_cnot, pad. (* have these automatically simplify *)
  simpl. Msimpl. solve_matrix.
Qed.


(** Equivalence and Structural Rules **)

(* Precondition about typing? *)
Definition uc_equiv (c1 c2 : ucom) := forall dim, uc_eval dim c1 = uc_eval dim c2.

Infix "≡" := uc_equiv : ucom_scope.

Lemma useq_assoc : forall c1 c2 c3, ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros c1 c2 c3 dim. simpl.
  rewrite Mmult_assoc. easy.
Qed.

Lemma useq_congruence : forall c1 c1' c2 c2',
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros c1 c1' c2 c2' Ec1 Ec2 dim.
  simpl.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

(* Optimization: Remove skips *)

Lemma uskip_id_l : forall (c : ucom),
   (uskip ; c) ≡ c.
Proof.
  intros c dim.
  simpl; Msimpl; reflexivity.
Qed.

Lemma uskip_id_r : forall (c : ucom),
   (c ; uskip) ≡ c.
Proof.
  intros c dim.
  simpl; Msimpl; reflexivity.
Qed.

Fixpoint rm_uskips (c : ucom) : ucom :=
  match c with
  | c1 ; c2 => match rm_uskips c1, rm_uskips c2 with
              | uskip, c2' => c2'
              | c1', uskip => c1'
              | c1', c2'   => c1'; c2'
              end
  | c'      => c'
  end.

(* We don't really need this anymore *)
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
      

Lemma rm_uskips_sound : forall c,
  c ≡ (rm_uskips c).
Proof.
  induction c; intros dim; trivial.
  simpl.
  destruct (rm_uskips c1) eqn:E1, (rm_uskips c2) eqn:E2; trivial;
    rewrite IHc1, IHc2; simpl; Msimpl; trivial.
Qed.

Inductive skip_free : ucom -> Prop :=
  | SF_seq : forall c1 c2, skip_free c1 -> skip_free c2 -> skip_free (c1; c2)
  | SF_app : forall n l (u : Unitary n), skip_free (uapp u l).

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
      destruct (rm_uskips c1); try easy.
    + right. simpl. 
      destruct (rm_uskips c1); try assumption;
      destruct (rm_uskips c2); try (apply SF_seq); easy. 
  - right; simpl. apply SF_app.
Qed.

Close Scope C_scope.
Close Scope R_scope.

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

Local Notation "a *= U" := (uapp U [a]) (at level 0) : ucom_scope.

Lemma slide1 : forall (m n : nat) (U V : Unitary 1),
  m <> n ->
  (m *= U ; n *= V) ≡ (n *= V ; m *= U). 
Proof.
  intros m n U V NE dim.
  simpl.
  simpl in *.
  unfold ueval1. 
  repeat match goal with
  | [|- context [pad m _ ?U ]] => remember U as U'
  | [|- context [pad n _ ?V ]] => remember V as V'
  end.
  assert (WFU : WF_Matrix _ _ U') by 
      (destruct U; subst; auto with wf_db).
  assert (WFV : WF_Matrix _ _ V') by 
      (destruct V; subst; auto with wf_db).
  clear HeqU' HeqV' U V.
  unfold pad.
  bdestruct (n + 1 <=? dim); bdestruct (m + 1 <=? dim);
    try Msimpl; trivial.
  bdestruct (m <? n).
  - remember (n - m - 1) as k.
    replace n with (m + 1 + k) by omega.
    replace (2 ^ (m+1+k)) with (2^m * 2 * 2^k) by unify_pows_two.
    remember (dim - 1 - (m + 1 + k)) as j.
    replace (dim - 1 - m) with (k + 1 + j) by omega.
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
    remember (dim - 1 - (m + 1 + k)) as j.
    replace (dim - 1 - m) with (k + 1 + j) by omega.
    replace (2 ^ (k + 1 + j)) with (2^k * 2 * 2^ j) by unify_pows_two.
    repeat rewrite <- id_kron.
    simpl in *.
    repeat rewrite kron_assoc.
    repeat rewrite Nat.mul_assoc.
    Msimpl'.
    reflexivity.
Qed.

(* help deal with the cases where a circuit is not well-typed *)
Ltac solve_non_WT_cases :=
  try (rewrite Mmult_1_l); 
  try (rewrite Mmult_1_r);
  try (apply WF_ueval1);
  easy.

(* more general version of slide *)
Lemma slide : forall (m q : nat) (l : list nat) (dim : nat) (U : Unitary 1) (V : Unitary m),
  (inb q l) = false ->
  uc_eval dim (uapp U [q] ; uapp V l) = uc_eval dim (uapp V l ; uapp U [q]). 
Proof.
  intros m q l dim U V NE.
  destruct V;
  (* use slide1 to prove all single-qubit gate cases *)
  try (
    destruct l; try (destruct l); simpl;
    try solve_non_WT_cases;
    simpl in NE;
    rewrite orb_false_r in NE;
    apply beq_nat_false in NE;
    apply not_eq_sym in NE;
    apply slide1;

    easy
  ).
  (* all that's left is the cnot case *)
  destruct l; try (destruct l); try (destruct l); simpl; try solve_non_WT_cases.
  unfold ueval1, ueval_cnot. 
  match goal with
  | [|- context [pad q _ ?U ]] => remember U as U'
  end.
  assert (WFU : WF_Matrix _ _ U') by 
      (destruct U; subst; auto with wf_db).
  clear HeqU' U.
  simpl in NE;
  rewrite orb_false_r in NE;
  apply orb_false_elim in NE;
  destruct NE as [NE1 NE2];
  apply beq_nat_false in NE1;
  apply beq_nat_false in NE2.
  bdestruct (n <? n0).
  - unfold pad.
    bdestruct (q + 1 <=? dim); bdestruct (n + (1 + (n0 - n - 1) + 1) <=? dim).
    + bdestruct (n0 <? q).
      (* n < n0 < q *)
      * remember (1 + (n0 - n - 1) + 1) as k.
        replace (dim - k - n) with ((q - k - n) + 1 + (dim - 1 - q)) by omega.
        replace (2 ^ ((q - k - n) + 1 + (dim - 1 - q))) with (2^(q - k - n) * 2 * 2^(dim - 1 - q)) by (repeat rewrite Nat.pow_add_r; easy).
        repeat rewrite <- id_kron.
        repeat rewrite <- kron_assoc.
        show_dimensions.
        admit.   
      * apply le_lt_eq_dec in H2.
        (* get rid of the q = n0 case *) 
        destruct H2; try (contradict e; apply not_eq_sym; easy).
        bdestruct (n <? q).
        (* n < q < n0 *)
        admit.
        (* q < n < n0 *)
        admit.
    (* the next 3 cases handle the behavior when the circuit is not well typed *)
    + rewrite Mmult_1_l;
      try rewrite Mmult_1_r;
      try reflexivity;
      try (apply WF_kron;
              try (repeat rewrite <- Nat.pow_add_r;
                   replace (q + 1 + (dim - 1 - q)) with dim by omega;
                   easy);
              try apply WF_kron;
              try apply WF_I;
              try easy).
    + admit.
    + Msimpl; reflexivity.
  - admit.
Admitted.

(** Flattening sequences **)
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

Lemma denote_flat_append : forall c1 c2 dim,
  uc_eval dim (flat_append c1 c2) = uc_eval dim c2 × uc_eval dim c1.
Proof.
  intros c1 c2 dim.
  induction c1; try easy.
  simpl.
  rewrite IHc1_2.
  apply Mmult_assoc.
Qed.

Lemma flatten_sound : forall c,  
  c ≡ flatten c.
Proof.
  intros c dim.
  induction c; try easy.
  simpl.
  rewrite IHc1, IHc2.
  rewrite denote_flat_append.
  reflexivity.
Qed.

Require Export List. (* Why do I need this here? *)

(* Cancel a single X gate on qubit q, if possible. This will either 
   return None or (Some c') where c' is the result of removing the 
   appropriate X gate from c.
   
   This function will insert an extra uskip instruction if the cancelled
   gate is at the end of the circuit... I should probably fix that. *)
Fixpoint cancel_X (c : ucom) (q : nat) : option ucom :=
  match c with
  | uapp U_X [q'] => 
      if q =? q' then Some uskip else None
  | uapp U_X [q']; c' => 
      if q =? q' then Some c' else None
  | uapp U_CNOT (q1::q2::nil); c' => 
      if q =? q1 then None 
      else match cancel_X c' q with
           | None => None
           | Some c'' => Some (uapp U_CNOT (q1::q2::nil); c'')
           end
  | uapp U l; c' => 
      if (inb q l)
      then None
      else match cancel_X c' q with
           | None => None
           | Some c'' => Some (uapp U l; c'')
           end
  | _ => None
  end.

(* Call cancel_X on all X gates in the circuit. The extra n argument
   is to help Coq recognize termination. *)
Fixpoint cancel_all_X (c : ucom) (n: nat) : ucom :=
  match n with
  | 0 => c (* impossible case *)
  | S n' => match c with
           | uapp U_X [q]; c2 => 
               match cancel_X c2 q with
               | None => uapp U_X [q]; (cancel_all_X c2 n')
               | Some c2' => cancel_all_X c2' n'
               end
           | c1; c2 => c1; (cancel_all_X c2 n')
           | _ => c
           end
  end.

Definition rm_X (c : ucom) : ucom := cancel_all_X (flatten c) (count_ops c).

Lemma XX_I : σx × σx = I (2 ^ 1).
Proof. solve_matrix. Qed.

(*Lemma X_CNOT_CNOT_X : σx × σx = I (2 ^ 1).
Proof. solve_matrix. Qed.*)

Lemma cancel_X_sound : forall c q dim,
  match cancel_X c q with
  | None => True
  | Some c' => uc_eval dim c' = uc_eval dim (uapp U_X [q]; c)
  end.
Proof.
  intros c q dim.
  induction c.
  - (* The skip case is trivial. *)
    easy.
  - (*clear IHWT1.
    destruct WT1; try easy.
    destruct u.
    + 
   admit.
    + destruct l. 
      contradict H; easy.
      assert (l = []) by (inversion H; apply length_zero_iff_nil; easy); subst.
      simpl. bdestruct (q =? n); try easy; subst.
      simpl; unfold ueval1, pad.
      unfold SQIMP.bounded in H0; simpl in H0; destruct H0 as [H0 _].
      assert (n + 1 <=? dim = true) by (apply Nat.leb_le; omega). 
      rewrite H0.
      admit.
    + admit.
    + admit.
    + admit.
    + destruct l.
      contradict H; easy.
      destruct l.
      contradict H; easy.
      assert (l = []) by (inversion H; apply length_zero_iff_nil; easy); subst.
      admit.
  - (* All unitary applications, except the "uapp U_X [q]" case, are trivial. *)
    destruct u; try easy.
    destruct l; try easy.
    assert (l = []) by (inversion H; apply length_zero_iff_nil; easy); subst.
    simpl. bdestruct (q =? n); try easy; subst.
    (* At this point, we have to prove that adjacent X gates will cancel:
        
         uc_eval dim uskip = ueval1 dim n U_X × ueval1 dim n U_X
    *)
    simpl; unfold ueval1, pad.
    unfold SQIMP.bounded in H0; simpl in H0; destruct H0 as [H0 _].
    assert (n + 1 <=? dim = true) by (apply Nat.leb_le; omega). 
    rewrite H0.
    Msimpl'.
    simpl; rewrite XX_I.
    rewrite id_kron.
    replace (2 ^ n * 2 ^ 1) with (2 ^ (n + 1)) by unify_pows_two.
    rewrite id_kron.
    replace (2 ^ (n + 1) * 2 ^ (dim - 1 - n)) with (2 ^ dim) by unify_pows_two.
    reflexivity.*)
Admitted.    
    
Lemma cancel_all_X_sound : forall c n dim,
  uc_eval dim c = uc_eval dim (cancel_all_X c n).
Proof.
  intros c n dim.
  generalize dependent c.
  induction n; try easy.
  intros c.
  induction c; try easy.
  induction c1; 
  try destruct u; 
  try destruct l; try destruct l; 
  try (simpl; rewrite <- IHn; easy).
  simpl.
  specialize (cancel_X_sound c2 n0 dim) as H.
  destruct (cancel_X c2 n0).
  - simpl in H.
    rewrite <- H.
    apply IHn.
  - simpl; rewrite <- IHn; easy.
Qed.
 
Lemma rm_X_sound : forall c dim, 
  uc_eval dim c = uc_eval dim (rm_X c).
Proof.
  intros c dim.
  unfold rm_X.
  rewrite <- cancel_all_X_sound.
  apply flatten_sound.
Qed.

Definition q1 : nat := 0.
Definition q2 : nat := 1.
Definition q3 : nat := 2.
Definition example1 : ucom := ((X q1; H q2); ((X q1; X q2); (CNOT q3 q2; X q2))).
Compute (flatten example1).
Compute (rm_X example1).
Definition example2 : ucom := ((X q1; X q2); X q3).
Compute (flatten example2).
Compute (rm_X example2).



