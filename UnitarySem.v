Require Export SQIMP.
Require Export Quantum.

Open Scope ucom_scope.

(** Denotation of Unitaries *)

Definition pad {n} (start dim : nat) (A : Square (2^n)) : Square (2^dim) :=
  if start + n <=? dim then I (2^start) ⊗ A ⊗ I (2^(dim - n - start)) else I (2^dim).

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

Hint Resolve WF_pad WF_ueval1 WF_ueval_cnot WF_ueval WF_uc_eval : wf_db.


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

Lemma uc_equiv_sym : forall c1 c2, c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

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
    rewrite IHc1, IHc2; simpl; Msimpl; easy.
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

Lemma pad_dims : forall c n k,
  uc_well_typed n c ->
  (uc_eval n c) ⊗ I (2^k) = uc_eval (n + k) c.  
Proof.
  intros c n k H.
  induction c.
  - simpl. rewrite id_kron. unify_pows_two. reflexivity.
  - inversion H; subst.
    simpl. rewrite <- IHc1, <- IHc2; trivial.
    Msimpl'; reflexivity.
  - simpl.
    unfold ueval.
    destruct n0 as [|[|[|]]]; simpl; try (rewrite id_kron; unify_pows_two; reflexivity).
    + destruct l as [| a []]; try (rewrite id_kron; unify_pows_two; reflexivity).
      unfold ueval1.
      repeat match goal with
      | [|- context [pad _ _ ?U ]] => remember U as U'
      end.
      unfold pad.
      assert(L : a + 1 <= n).
      { inversion H; subst.
        specialize (H5 a (or_introl eq_refl)).
        omega.
      }
      bdestruct (a + 1 <=? n); bdestructΩ (a + 1 <=? n+k).
      setoid_rewrite (kron_assoc _ _ _ _ _ _ (I (2^a) ⊗ U')).
      rewrite id_kron. unify_pows_two.
      replace (n - 1 - a + k) with (n + k - 1 - a) by omega.
      reflexivity.
    + destruct l as [| a [|b[|]]]; try (rewrite id_kron; unify_pows_two; reflexivity).
      unfold ueval_cnot.
      inversion H; subst.
      assert (La : a < n) by (apply H5; simpl; auto).
      assert (Lb : b < n) by (apply H5; simpl; auto).
      clear -La Lb.
      unfold pad.
      bdestruct (a <? b); bdestructΩ (b <? a); try (rewrite id_kron; unify_pows_two; reflexivity).
      * bdestructΩ (a + S (b - a - 1 + 1) <=? n).
        bdestructΩ (a + S (b - a - 1 + 1) <=? n + k).
        setoid_rewrite (kron_assoc _ _ _ _ _ _ _ _  (I (2^k))).
        rewrite id_kron.
        unify_pows_two.
        rewrite Nat.sub_add by omega.
        rewrite Nat.add_sub_swap by omega.
        rewrite Nat.add_sub_swap by omega.
        reflexivity.
      * bdestructΩ (b + S (a - b - 1 + 1) <=? n).
        bdestructΩ (b + S (a - b - 1 + 1) <=? n + k).
        setoid_rewrite (kron_assoc _ _ _ _ _ _ _ _  (I (2^k))).
        rewrite id_kron.
        unify_pows_two.
        rewrite Nat.sub_add by omega.
        rewrite Nat.add_sub_swap by omega.
        rewrite Nat.add_sub_swap by omega.
        reflexivity.
Qed.
  
Open Scope ucom_scope.

(* Shouldn't need this here? *)
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

(* This just tries to get rid of extra identity matrices (faster than Msimpl).
   It is mainly intended to be used in solve_non_WT_cases, but I also use it
   in a few places to simplify the goal. *)
Ltac remove_id_gates :=
  repeat rewrite Mmult_1_l;
  repeat rewrite Mmult_1_r;
  auto with wf_db.

(* When circuits are not well-typed, the semantics functions will add
   extra identity matrices. This tactic is intended to handle these cases
   by removing the identity matrices and proving equality. *)
Ltac solve_non_WT_cases :=
  remove_id_gates;
  try unify_pows_two;
  easy.

(* Several of the type rewrites are just associativity issues, and omega
   is a little slow solving these. *)
Ltac rewrite_assoc :=
  repeat rewrite mult_assoc;
  easy.

(* More general version of slide1. *)
Lemma slide12 : forall (m q : nat) (l : list nat) (U : Unitary 1) (V : Unitary m),
  (inb q l) = false ->
  (uapp U [q] ; uapp V l) ≡ (uapp V l ; uapp U [q]). 
Proof.
  intros m q l U V NE dim.
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
  (* all that's left is the CNOT case *)
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
    remember (n0 - n - 1) as i.
    replace (2 ^ (n0 - n)) with (2 ^ i * 2) by unify_pows_two.
    repeat rewrite <- id_kron.
    rewrite <- (kron_assoc _ _ _ _ _ _ _ _ (I 2)).
    bdestruct (q + 1 <=? dim); bdestruct (n + (1 + i + 1) <=? dim); 
    try solve_non_WT_cases;
    (* a couple well-formedness proofs need a little extra help *)
    try (remove_id_gates; apply WF_kron; try unify_pows_two; auto with wf_db).
    bdestruct (n0 <? q).
    (* Case 1/6: n < n0 < q *)
    + remember (q - (1 + i + 1) - n) as j.
      remember (dim - 1 - q) as k.
      replace (2 ^ q) with (2 ^ n * (2 * 2 ^ i * 2) * 2 ^ j) by unify_pows_two.
      replace (2 ^ (dim - (1 + i + 1) - n)) with (2 ^ j * 2 * 2 ^ k) by unify_pows_two.
      repeat rewrite <- id_kron.
      rewrite <- (kron_assoc _ _ _ _ _ _ _ _ (I (2 ^ k))).
      rewrite <- (kron_assoc _ _ _ _ _ _ _ _ (I 2)).  
      (* * *) replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two.
      (* * *) replace (2 ^ dim) with (2 ^ n * (2 * 2 ^ i * 2) * 2 ^ j * 2 * 2 ^ k) by unify_pows_two.
      (* * *) replace (2 ^ n * (2 * 2 ^ i * 2) * (2 ^ j * 2)) with (2 ^ n * (2 * 2 ^ i * 2) * 2 ^ j * 2) by rewrite_assoc.
      (* * *) replace (2 ^ 1) with 2 by easy.
      repeat rewrite kron_mixed_product; remove_id_gates.
      rewrite Mmult_plus_distr_l.
      rewrite Mmult_plus_distr_r.
      repeat rewrite kron_mixed_product; remove_id_gates.
    + apply le_lt_eq_dec in H2; destruct H2; 
        try (contradict e; apply not_eq_sym; easy).
      bdestruct (n <? q).
      (* Case 2/6: n < q < n0 *)
      * remember (q - n - 1) as j.
        remember (i - j - 1) as k.
        remember (dim - (1 + i + 1) - n) as m.
        (* * *) replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two.
        (* TODO: You can use unify_pows_two here, but it's super slow! 
                 How can we help Coq solve these faster? *)
        replace (2 ^ q) with (2 ^ n * 2 * 2 ^ j) by admit. 
        replace (2 ^ i) with (2 ^ j * 2 * 2 ^ k) by admit.    
        replace (2 ^ (dim - 1 - q)) with (2 ^ k * 2 * 2 ^ m) by admit.
        repeat rewrite <- id_kron.
        repeat rewrite <- kron_assoc.
        rewrite (kron_assoc _ _ _ _ _ _ (I (2 ^ n)) _ (I (2 ^ j))).
        (* * *) replace (2 ^ n * 2 * 2 ^ j) with (2 ^ n * (2 * 2 ^ j)) by rewrite_assoc.
        rewrite (kron_assoc _ _ _ _ _ _ (I (2 ^ n)) _ U').
        (* * *) replace (2 ^ 1) with 2 by easy.
        (* * *) replace (2 ^ n * (2 * 2 ^ j) * 2) with (2 ^ n * (2 * 2 ^ j * 2)) by rewrite_assoc.
        rewrite (kron_assoc _ _ _ _ _ _ (I (2 ^ n)) _ (I (2 ^ k))).
        (* * *) replace (2 ^ n * (2 * 2 ^ j * 2) * 2 ^ k) with (2 ^ n * (2 * 2 ^ j * 2 * 2 ^ k)) by rewrite_assoc.
        rewrite (kron_assoc _ _ _ _ _ _ (I (2 ^ n)) _ (I 2)).
        (* * *) replace (2 ^ dim) with (2 ^ n * (2 * 2 ^ j * 2 * 2 ^ k * 2) * 2 ^ m) by unify_pows_two.
        (* * *) replace (2 * (2 ^ j * 2 * 2 ^ k) * 2) with (2 * 2 ^ j * 2 * 2 ^ k * 2) by rewrite_assoc.
        (* * *) replace (2 ^ n * (2 * 2 ^ j * 2) * (2 ^ k * 2)) with (2 ^ n * (2 * 2 ^ j * 2 * 2 ^ k * 2)) by rewrite_assoc.
        rewrite kron_mixed_product.
        repeat rewrite kron_mixed_product; remove_id_gates.
        rewrite Mmult_plus_distr_l.
        rewrite Mmult_plus_distr_r.
        (* * *) replace (2 * (2 ^ j * 2 * 2 ^ k)) with (2 * 2 ^ j * 2 ^ 1 * 2 ^ k) by rewrite_assoc.
        repeat rewrite kron_mixed_product. 
        (* * *) replace (2 * (2 ^ j * 2)) with (2 * 2 ^ j * 2) by rewrite_assoc.
        repeat rewrite kron_mixed_product; remove_id_gates.
      (* Case 3/6: q < n < n0 *)
      * admit.
  - bdestruct (n0 <? n); try solve_non_WT_cases.
    unfold pad.
    remember (n - n0 - 1) as i.
    (* * *) replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two.
    bdestruct (q + 1 <=? dim); bdestruct (n0 + (1 + i + 1) <=? dim); 
    try solve_non_WT_cases;
    (* a couple well-formedness proofs need a little extra help *)
    try (remove_id_gates; apply WF_kron; try unify_pows_two; auto with wf_db).
    bdestruct (n <? q).
    (* Case 4/6: n0 < n < q *)
    + admit.
    + apply le_lt_eq_dec in H3; destruct H3; 
        try (contradict e; apply not_eq_sym; easy).
      bdestruct (n0 <? q).
      (* Case 5/6: n0 < q < n *)
      * admit.
      * apply le_lt_eq_dec in H3; destruct H3; 
        try (contradict e; apply not_eq_sym; easy).
        (* Case 6/6: q < n0 < n *)
        admit.
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

(** Optimization: 'not propagation' **)

Require Export List.

(* Propagate an X gate on qubit q as far right as possible, cancelling
   the gate if possible.
   
   This will return None if no cancellation is possible or (Some c') 
   where c' is the result of removing the appropriate X gate from c.
   
   This function will insert an extra uskip instruction if the cancelled
   gate is at the end of the circuit... I should probably fix that. *)
Fixpoint propagate_not (c : ucom) (q : nat) : option ucom :=
  match c with
  | q' *= U_X => 
      if q =? q' then Some uskip else None
  | q' *= U_X ; c2 => 
      if q =? q' then Some c2 
      else match propagate_not c2 q with
           | None => None
           | Some c2' => Some (q' *= U_X ; c2')
           end
  | uapp U_CNOT (q1::q2::nil) ; c2 => 
      if q =? q1 then None 
      else match propagate_not c2 q with
           | None => None
           | Some c2' => Some (uapp U_CNOT (q1::q2::nil) ; c2')
           end
  | uapp U l ; c2 => 
      if (inb q l)
      then None
      else match propagate_not c2 q with
           | None => None
           | Some c2' => Some (uapp U l ; c2')
           end
  | _ => None
  end.

(* Call propagate_not on all X gates in the circuit. 
   
   The extra n argument is to help Coq recognize termination.
   We start with n = (count_ops c), which is the maximum
   number of times that propagate_nots can be called. *)
Fixpoint propagate_nots (c : ucom) (n: nat) : ucom :=
  match n with
  | 0 => c
  | S n' => match c with
           | q *= U_X ; c2 => 
               match propagate_not c2 q with
               | None => q *= U_X ; (propagate_nots c2 n')
               | Some c2' => propagate_nots c2' n'
               end
           | c1; c2 => c1; (propagate_nots c2 n')
           | _ => c
           end
  end.

Definition rm_nots (c : ucom) : ucom := propagate_nots (flatten c) (count_ops c).

Lemma XX_id : forall q, uskip ≡ q *= U_X; q *= U_X.
Proof. 
  intros q dim. 
  simpl; unfold ueval1, pad. 
  bdestruct (q + 1 <=? dim); Msimpl'; try easy.
  simpl; replace (σx × σx) with (I (2 ^ 1)) by solve_matrix.
  rewrite id_kron.
  replace (2 ^ q * 2 ^ 1) with (2 ^ (q + 1)) by unify_pows_two.
  rewrite id_kron.
  replace (2 ^ (q + 1) * 2 ^ (dim - 1 - q)) with (2 ^ (q + 1 + dim - 1 - q)) by unify_pows_two.
  replace (q + 1 + dim - 1 - q) with dim by omega.
  reflexivity.
Qed.

(* I did my best to keep this proof clean, but I struggled with 
   getting matrix dimension types to line up. Below is the result
   after a couple hours of trying to minimize calls to 'replace'.

   I've marked every location that I manipulate types behind the
   scenes with (* * *).

   This might be an interesting point of comparison for the F* code.
*)
Lemma X_CNOT_comm : forall c t, t *= U_X; uapp U_CNOT (c::t::[]) ≡ uapp U_CNOT (c::t::[]); t *= U_X.
Proof.
  intros c t dim.
  simpl; unfold ueval1, pad. 
  bdestruct (t + 1 <=? dim); try solve_non_WT_cases. 
  unfold ueval_cnot, pad. 
  bdestruct (c <? t).
  - bdestruct (c + (1 + (t - c - 1) + 1) <=? dim); try solve_non_WT_cases.
    (* c < t *)
    remember (t - c - 1) as i.
    replace (dim - (1 + i + 1) - c) with (dim - 1 - t) by omega.
    remember (dim - 1 - t) as j.
    replace (2 ^ t) with (2 ^ c * 2 * 2 ^ i) by unify_pows_two.
    replace (2 ^ (t - c)) with (2 ^ i * 2) by unify_pows_two.
    repeat rewrite <- id_kron.
    rewrite (kron_assoc _ _ _ _ _ _ (I (2 ^ c)) _ (I (2 ^ i))).
    (* * *) replace (2 ^ c * 2 * 2 ^ i) with (2 ^ c * (2 * 2 ^ i)) by rewrite_assoc.
    rewrite (kron_assoc _ _ _ _ _ _ (I (2 ^ c)) _ σx).
    (* * *) replace (2 ^ dim) with (2 ^ c * 2 ^ (1 + i + 1) * 2 ^ j) by unify_pows_two.
    (* * *) replace (2 ^ 1) with 2 by easy.
    (* * *) replace (2 ^ (1 + i + 1)) with (2 * 2 ^ i * 2) by unify_pows_two.
    (* * *) replace (2 ^ c * (2 * 2 ^ i) * 2) with (2 ^ c * (2 * 2 ^ i * 2)) by rewrite_assoc.
    repeat rewrite kron_mixed_product; remove_id_gates.
    rewrite <- (kron_assoc _ _ _ _ _ _ (∣0⟩⟨0∣) (I (2 ^ i)) (I 2)).
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    repeat rewrite kron_mixed_product; remove_id_gates.
  - bdestruct (t <? c); try solve_non_WT_cases.
    bdestruct (t + (1 + (c - t - 1) + 1) <=? dim); try solve_non_WT_cases.
    (* t < c *)
    remember (c - t - 1) as i.
    replace (dim - (1 + i + 1) - t) with (dim - 1 - c) by omega.
    remember (dim - 1 - c) as j.
    replace (2 ^ (dim - 1 - t)) with (2 ^ i * 2 * 2 ^ j) by unify_pows_two.
    replace (2 ^ (c - t)) with (2 * 2 ^ i) by unify_pows_two.
    repeat rewrite <- id_kron.
    rewrite (kron_assoc _ _ _ _ _ _ (I (2 ^ t)) σx _).
    rewrite <- (kron_assoc _ _ _ _ _ _ σx _ (I (2 ^ j))).
    rewrite <- (kron_assoc _ _ _ _ _ _ σx (I (2 ^ i)) (I 2)).
    (* * *) replace (2 * (2 ^ i * 2 * 2 ^ j)) with (2 * (2 ^ i * 2) * 2 ^ j) by rewrite_assoc.
    rewrite <- (kron_assoc _ _ _ _ _ _ (I (2 ^ t)) _ (I (2 ^ j))).
    (* * *) replace (2 ^ dim) with (2 ^ t * 2 ^ (1 + i + 1) * 2 ^ j) by unify_pows_two.
    (* * *) replace (2 ^ (1 + i + 1)) with (2 * (2 ^ i * 2)) by unify_pows_two.
    repeat rewrite kron_mixed_product; remove_id_gates.
    (* * *) replace (2 * (2 ^ i * 2)) with (2 * 2 ^ i * 2) by rewrite_assoc.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    repeat rewrite kron_mixed_product; remove_id_gates.
Qed.

(* Is there a more natural way to write this property? *)
Lemma propagate_not_sound : forall c q,
  match propagate_not c q with
  | None => True
  | Some c' => c' ≡ (q *= U_X; c)
  end.
Proof.
  intros c q.
  induction c.
  - easy.
  - clear IHc1.
    destruct c1; try easy.
    remember u as U.
    destruct u;
    (* U = H, Y, Z, R *)
    try (rewrite HeqU; simpl; rewrite <- HeqU;
         remember (inb q l) as b; 
         destruct b; try easy;
         destruct (propagate_not c2 q); try easy;
         intros dim;
         rewrite <- useq_assoc;
         rewrite (useq_congruence _ (uapp U l; q *= U_X) c2 c2);
         try apply slide12; try easy;
         rewrite useq_assoc;
         rewrite (useq_congruence (uapp U l) (uapp U l) _ (q *= U_X; c2)); 
         easy);
    subst.
    (* U = X *)
    + (* solve the cases where l is empty, or l has >1 element *)
      destruct l; simpl; try destruct l;
      try destruct ((n =? q) || inb q (n0 :: l)); try easy;
      try (destruct (propagate_not c2 q); easy);
      try (destruct (propagate_not c2 q); try easy;
           intros dim; simpl; remove_id_gates;
           unfold uc_equiv in IHc2; simpl in IHc2;
           easy).
      (* solve the case where l has exactly 1 element *)
      bdestruct (q =? n).
      * subst. 
        intros dim.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ uskip _ c2); try easy.
        rewrite uskip_id_l; easy.
        apply uc_equiv_sym.
        apply XX_id.
      * destruct (propagate_not c2 q); try easy.
        intros dim.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ (n *= U_X; q *= U_X) c2 c2); try easy.
        rewrite useq_assoc.
        rewrite (useq_congruence (n *= U_X) (n *= U_X) _ (q *= U_X; c2)); try easy.
        apply slide1; easy.
    (* U = CNOT *)
    + (* solve the cases where l has <2 or >2 elements *)
      destruct l; simpl; try destruct l; simpl; try destruct l;
      [ | destruct ((n =? q) || false) | | destruct ((n =? q) || ((n0 =? q) || (inb q (n1::l)))) ];
      try easy;
      try (destruct (propagate_not c2 q); easy);
      try (destruct (propagate_not c2 q); try easy;
           intros dim; simpl; remove_id_gates;
           unfold uc_equiv in IHc2; simpl in IHc2;
           easy).
      (* solve the case where l has exactly 2 elements *)
      bdestruct (q =? n); try easy.
      bdestruct (q =? n0).
      * subst.
        destruct (propagate_not c2 n0); try easy.
        intros dim.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ (uapp U_CNOT (n::n0::[]); n0 *= U_X) c2 c2); try easy.
        rewrite useq_assoc.
        rewrite (useq_congruence _ (uapp U_CNOT (n::n0::[])) u (n0 *= U_X; c2)); try easy.
        apply X_CNOT_comm.
      * assert (forall n m : nat, (n =? m) = (m =? n)).
        { induction n1; destruct m; auto. apply IHn1. }
        assert (inb q (n::n0::[]) = false). 
        { simpl. 
          apply beq_nat_false_iff in H.
          apply beq_nat_false_iff in H0.
          repeat apply orb_false_intro;
          try rewrite H1;
          easy. }
        destruct (propagate_not c2 q); try easy.
        intros dim.
        rewrite <- useq_assoc.
        rewrite (useq_congruence _ (uapp U_CNOT (n::n0::[]); q *= U_X) c2 c2); try easy.
        rewrite useq_assoc.
        rewrite (useq_congruence _ (uapp U_CNOT (n::n0::[])) u (q *= U_X; c2)); try easy.
        apply slide12; easy.
  - destruct u; try easy. 
    destruct l; try destruct l; try easy.
    simpl. bdestruct (q =? n); try easy; subst.
    apply XX_id.
Qed.   
    
Lemma propagate_nots_sound : forall c n, c ≡ propagate_nots c n.
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
  specialize (propagate_not_sound c2 n0 ) as H.
  destruct (propagate_not c2 n0).
  - unfold uc_equiv in H. simpl in H.
    rewrite <- H.
    apply IHn.
  - simpl; rewrite <- IHn; easy.
Qed.
 
Lemma rm_nots_sound : forall c, c ≡ rm_nots c.
Proof.
  intros c dim.
  unfold rm_nots.
  rewrite <- propagate_nots_sound.
  apply flatten_sound.
Qed.

Definition q1 : nat := 0.
Definition q2 : nat := 1.
Definition q3 : nat := 2.
Definition example1 : ucom := ((X q1; H q2); ((X q1; X q2); (CNOT q3 q2; X q2))).
Compute (flatten example1).
Compute (rm_nots example1).
Definition example2 : ucom := ((X q1; X q2); X q3).
Compute (flatten example2).
Compute (rm_nots example2).


Ltac prove_wt :=
  repeat match goal with
         | |- context [ uc_well_typed ?d uskip ] => apply WT_uskip
         | |- context [ uc_well_typed ?d (useq ?c1 ?c2) ] => apply WT_seq
         | |- context [ uc_well_typed ?d (uapp ?u ?l) ] => try unfold CNOT; apply WT_app
         end.


Lemma typed_pad : forall (n k : nat)(c : ucom), uc_well_typed n c -> uc_well_typed (k + n) c.
Proof.
  intros. generalize dependent n.
  induction c; intros; prove_wt; induction k;
  [| apply IHc1 | apply IHc2 | apply IHc2 | | | | apply (in_bounds_pad _ _ 1%nat) | | ]; 
  inversion H; assumption.
Qed.
