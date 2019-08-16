Require Import Setoid.
Require Export QWIRE.Quantum.
Require Export core.SQIRE.
Require Export core.Tactics.

Local Open Scope matrix_scope.
Local Open Scope ucom_scope.

(** Denotation of Unitaries **)

(* Padding and lemmas *)
Definition pad {n} (start dim : nat) (A : Square (2^n)) : Square (2^dim) :=
  if start + n <=? dim then I (2^start) ⊗ A ⊗ I (2^(dim - (start + n))) else Zero.

Lemma WF_pad : forall n start dim (A : Square (2^n)),
  WF_Matrix A ->
  WF_Matrix (pad start dim A).
Proof.
  intros n start dim A WFA. unfold pad.
  bdestruct (start + n <=? dim); auto with wf_db.
Qed.  

Lemma pad_mult : forall n dim start (A B : Square (2^n)),
  pad start dim A × pad start dim B = pad start dim (A × B).
Proof.
  intros.
  unfold pad.
  gridify.
  reflexivity.
Qed.

(* TODO: move the following to QWIRE's Quantum.v *)

(* Standard(?) definition, but it makes equivalence-checking a little annoying 
   because of a global phase.

Definition rotation (θ ϕ λ : R) : Matrix 2 2 :=
  fun x y => match x, y with
             | 0, 0 => (Cexp (-(ϕ + λ)/2)) * (cos (θ/2))
             | 0, 1 => - (Cexp (-(ϕ - λ)/2)) * (sin (θ/2))
             | 1, 0 => (Cexp ((ϕ - λ)/2)) * (sin (θ/2))
             | 1, 1 => (Cexp ((ϕ + λ)/2)) * (cos (θ/2))
             | _, _ => C0
             end.
*)
Definition rotation (θ ϕ λ : R) : Matrix 2 2 :=
  fun x y => match x, y with
             | 0, 0 => (cos (θ/2))
             | 0, 1 => - (Cexp λ) * (sin (θ/2))
             | 1, 0 => (Cexp ϕ) * (sin (θ/2))
             | 1, 1 => (Cexp (ϕ + λ)) * (cos (θ/2))
             | _, _ => C0
             end.

Lemma WF_rotation : forall θ ϕ λ, WF_Matrix (rotation θ ϕ λ).
Proof. intros. show_wf. Qed.
Hint Resolve WF_rotation : wf_db.

Hint Rewrite sin_0 sin_PI4 sin_PI2 sin_PI cos_0 cos_PI4 cos_PI2 cos_PI sin_neg cos_neg : trig_db.

Lemma rotation_adjoint : forall θ ϕ λ, (rotation θ ϕ λ)† = rotation (-θ) (-λ) (-ϕ).
Proof.
  intros.
  unfold rotation, adjoint.
  prep_matrix_equality.
  destruct_m_eq; try lca;
  unfold Cexp, Cconj;
  apply injective_projections; simpl;
  try rewrite <- Ropp_plus_distr;
  autorewrite with R_db;
  autorewrite with trig_db;
  try rewrite (Rplus_comm λ ϕ);
  autorewrite with R_db;
  reflexivity.
Qed.
Hint Rewrite rotation_adjoint : M_db.

Lemma rotation_unitary : forall θ ϕ λ, @WF_Unitary 2 (rotation θ ϕ λ).
Proof.
  intros.
  split; [show_wf|].
  unfold Mmult, I, rotation, adjoint, Cexp.
  prep_matrix_equality.
  destruct_m_eq; try lca;
  unfold Cexp, Cconj;
  apply injective_projections; simpl;
  autorewrite with R_db;
  try lra.
  (* some general rewriting *)
  all: (repeat rewrite <- Rmult_assoc;
        repeat rewrite Ropp_mult_distr_l;
        repeat rewrite <- Rmult_plus_distr_r;
        repeat rewrite Rmult_assoc;
        repeat rewrite (Rmult_comm (cos (θ * / 2)));
        repeat rewrite (Rmult_comm (sin (θ * / 2)));
        repeat rewrite <- Rmult_assoc;
        repeat rewrite <- Rmult_plus_distr_r).
  (* all the cases are about the same; just setting up applications of
     cos_minus/sin_minus and simplifying *)
  all: repeat rewrite <- cos_minus.
  3: (rewrite (Rmult_comm (cos ϕ));
      rewrite <- (Ropp_mult_distr_l (sin ϕ));
      rewrite (Rmult_comm (sin ϕ));
      rewrite <- Rminus_unfold).
  5: (rewrite (Rmult_comm _ (cos ϕ));
      rewrite (Rmult_comm _ (sin ϕ));
      rewrite <- Ropp_mult_distr_r;
      rewrite <- Rminus_unfold).
  all: try rewrite <- sin_minus.
  all: autorewrite with R_db.
  all: repeat rewrite Rplus_opp_r.
  all: try (rewrite Ropp_plus_distr;
            repeat rewrite <- Rplus_assoc;
            rewrite Rplus_opp_r).
  all: try (rewrite (Rplus_comm ϕ λ);
            rewrite Rplus_assoc;
            rewrite Rplus_opp_r).
  all: (autorewrite with R_db;
        autorewrite with trig_db;
        autorewrite with R_db).
  all: try lra.
  all: try (replace (cos (θ * / 2) * cos (θ * / 2))%R with ((cos (θ * / 2))²) by easy;
            replace (sin (θ * / 2) * sin (θ * / 2))%R with ((sin (θ * / 2))²) by easy).
  1: rewrite Rplus_comm.
  all: try (rewrite sin2_cos2; reflexivity).
  (* two weird left-over cases *)
  all: (destruct ((x =? y) && (S (S x) <? 2)) eqn:E;
        try reflexivity).
  apply andb_prop in E as [_ E].
  apply Nat.ltb_lt in E; lia.
Qed.

Lemma sqrt2_div2 : (√ 2 / 2)%R = (1 / √ 2)%R.
Proof.
   rewrite <- Rmult_1_l.
   assert (√ 2 <> 0) by (apply sqrt_neq_0_compat; lra).
   replace 1 with (√ 2 / √ 2)%R by (autorewrite with R_db; reflexivity).
   rewrite Rmult_div; try assumption. 
   autorewrite with R_db.
   reflexivity.
Qed.

Lemma hadamard_rotation : hadamard = rotation (PI/2) 0 PI.
Proof.
  unfold hadamard, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity; 
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with R_db;
  autorewrite with trig_db;
  autorewrite with R_db;
  try reflexivity.
  all: rewrite Rmult_assoc;
       replace (/2 * /2)%R with (/4)%R by lra;
       repeat rewrite <- Rdiv_unfold;
       autorewrite with trig_db;
       rewrite sqrt2_div2;
       lra.
Qed.

Lemma pauli_x_rotation : σx = rotation PI 0 PI.
Proof.
  unfold σx, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with trig_db;
  lra.
Qed.

Lemma pauli_y_rotation : σy = rotation PI (PI/2) (PI/2).
Proof. 
  unfold σy, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with trig_db;
  lra.
Qed.

Lemma pauli_z_rotation : σz = rotation 0 0 PI.
Proof. 
  unfold σz, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with R_db;
  autorewrite with trig_db;
  lra.
Qed.

Lemma phase_shift_rotation : forall λ, phase_shift λ = rotation 0 0 λ.
Proof. 
  intros.
  unfold phase_shift, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with R_db;
  autorewrite with trig_db;
  lra.
Qed.

Definition ueval_r (dim n : nat) θ ϕ λ : Square (2^dim) :=
  @pad 1 n dim (rotation θ ϕ λ).

(* Restriction: m <> n and m, n < dim *)

Definition ueval_cnot (dim m n: nat) : Square (2^dim) :=
  if (m <? n) then
    @pad (1+(n-m-1)+1) m dim (∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ I 2)
  else if (n <? m) then
    @pad (1+(m-n-1)+1) n dim (σx ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ .+ I 2 ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨0∣)
  else
    Zero.

(* Alt formulation for consistency with pad.
   (Can also simplify first arg of pad, at the cost of complicating WF proofs.)
Definition ueval_cnot (dim m n: nat) : Square (2^dim) :=
  if (m + 1 <=? n ) then
    @pad (1+(n-(m+1))+1) m dim
         (∣1⟩⟨1∣ ⊗ I (2^(n-(m+1))) ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I (2^(n-(m+1))) ⊗ I 2)
  else if (n + 1 <=? m) then
    @pad (1+(m-(n+1))+1) n dim
         (σx ⊗ I (2^(m-(n+1))) ⊗ ∣1⟩⟨1∣ .+ I 2 ⊗ I (2^(m-(n+1))) ⊗ ∣0⟩⟨0∣)
  else
    Zero.
*)

(** Denotation of ucoms **)

Fixpoint uc_eval {dim} (c : ucom dim) : Matrix (2^dim) (2^dim) :=
  match c with
  | uskip           => I (2^dim)
  | c1 ; c2         => uc_eval c2 × uc_eval c1 
  | uapp_R θ ϕ λ n  => ueval_r dim n θ ϕ λ
  | uapp_CNOT m n   => ueval_cnot dim m n
  end.

(** Well-formedness **)

Lemma WF_ueval_r : forall dim n θ ϕ λ, WF_Matrix (ueval_r dim n θ ϕ λ).
Proof.
  intros. apply WF_pad. apply WF_rotation.
Qed.  
  
Lemma WF_ueval_cnot : forall dim m n, WF_Matrix (ueval_cnot dim m n). 
Proof.
  intros dim m n.
  unfold ueval_cnot.
  bdestruct (m <? n); [|bdestruct (n <? m)]; 
    try apply WF_pad;
    unify_pows_two; auto with wf_db.
Qed.  

Lemma WF_uc_eval : forall {dim} (c : ucom dim), WF_Matrix (uc_eval c).
Proof.
  intros dim c.
  induction c; simpl; auto with wf_db.
  apply WF_ueval_r.
  apply WF_ueval_cnot.
Qed.

Hint Resolve WF_pad WF_ueval_r WF_ueval_cnot WF_uc_eval : wf_db.

(* Some lemmas about the denotation of gates. In general, we won't want to 
   interact directly with the 'rotation' matrix. *)

Lemma denote_H : forall dim n, uc_eval (H n) = @pad 1 n dim hadamard.
Proof.
  intros. unfold uc_eval; simpl.
  rewrite hadamard_rotation.
  reflexivity.
Qed.

Lemma denote_X : forall dim n, uc_eval (X n) = @pad 1 n dim σx.
Proof.
  intros. unfold uc_eval; simpl.
  rewrite pauli_x_rotation.
  reflexivity.
Qed.

Lemma denote_Y : forall dim n, uc_eval (Y n) = @pad 1 n dim σy.
Proof.
  intros. unfold uc_eval; simpl.
  rewrite pauli_y_rotation.
  reflexivity.
Qed.

Lemma denote_Z : forall dim n, uc_eval (Z n) = @pad 1 n dim σz.
Proof.
  intros. unfold uc_eval; simpl.
  rewrite pauli_z_rotation.
  reflexivity.
Qed.

Lemma denote_Rz : forall dim λ n, uc_eval (Rz λ n) = @pad 1 n dim (phase_shift λ).
Proof.
  intros. unfold uc_eval; simpl.
  rewrite phase_shift_rotation.
  reflexivity.
Qed.

Lemma denote_cnot : forall dim m n, 
  uc_eval (CNOT m n) = ueval_cnot dim m n.
Proof. easy. Qed.

Definition ueval_swap (dim m n: nat) : Square (2^dim) :=
  if (m <? n) then
      @pad (1+(n-m-1)+1) m dim 
             ( ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨0∣ .+
               ∣0⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨0∣ .+
               ∣1⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨1∣ .+
               ∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨1∣ )
  else if (n <? m) then
      @pad (1+(m-n-1)+1) n dim 
             ( ∣0⟩⟨0∣ ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨0∣ .+
               ∣0⟩⟨1∣ ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨0∣ .+
               ∣1⟩⟨0∣ ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨1∣ .+
               ∣1⟩⟨1∣ ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ )
  else
      Zero.

(* auxiliary lemmas for denote_swap *)
Lemma Mplus_swap_first_and_last : forall {m n} (A B C D : Matrix m n), 
  A .+ B .+ (C .+ D) = D .+ B .+ C .+ A.
Proof.
  intros. 
  rewrite <- Mplus_assoc.
  rewrite Mplus_comm.
  rewrite (Mplus_comm _ _ A).
  repeat rewrite Mplus_assoc.
  rewrite (Mplus_comm _ _ A).
  reflexivity.
Qed.

Lemma Mplus_swap_mid : forall {m n} (A B C D : Matrix m n), 
  A .+ B .+ C .+ D = A .+ C .+ B .+ D.
Proof.
  intros. 
  rewrite 2 Mplus_assoc.
  rewrite <- (Mplus_assoc _ _ B).
  rewrite (Mplus_comm _ _ B).                       
  rewrite <- 2 Mplus_assoc.
  reflexivity.
Qed.

Lemma denote_swap : forall dim m n,
  @uc_eval dim (SWAP m n) = ueval_swap dim m n.
Proof.
  intros.
  simpl; unfold ueval_swap. 
  repeat rewrite denote_cnot.
  unfold ueval_cnot, pad.
  gridify.
  - autorewrite with cnot_db.
    Msimpl_light.
    rewrite Mplus_swap_first_and_last.
    reflexivity. 
  - autorewrite with cnot_db.
    Msimpl_light.
    rewrite Mplus_swap_first_and_last.
    rewrite Mplus_swap_mid.
    reflexivity.
Qed.
Global Opaque SWAP.

Lemma unfold_ueval_cnot : forall dim m n, 
  ueval_cnot dim m n = 
    if (m <? n) then
      @pad (1+(n-m-1)+1) m dim (∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ I 2)
    else if (n <? m) then
      @pad (1+(m-n-1)+1) n dim (σx ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ .+ I 2 ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨0∣)
    else
      Zero.
Proof. easy. Qed.

Lemma unfold_ueval_r : forall dim n θ ϕ λ, 
  ueval_r dim n θ ϕ λ = @pad 1 n dim (rotation θ ϕ λ).
Proof. easy. Qed.

Lemma unfold_pad : forall n start dim A, 
  @pad n start dim A = 
  if start + n <=? dim then I (2^start) ⊗ A ⊗ I (2^(dim - (start + n))) else Zero.
Proof. easy. Qed.

Lemma unfold_ueval_swap : forall dim m n, 
  ueval_swap dim m n = 
    if (m <? n) then
      @pad (1+(n-m-1)+1) m dim 
             ( ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨0∣ .+
               ∣0⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨0∣ .+
               ∣1⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ ∣0⟩⟨1∣ .+
               ∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ ∣1⟩⟨1∣ )
    else if (n <? m) then
      @pad (1+(m-n-1)+1) n dim 
             ( ∣0⟩⟨0∣ ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨0∣ .+
               ∣0⟩⟨1∣ ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨0∣ .+
               ∣1⟩⟨0∣ ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨1∣ .+
               ∣1⟩⟨1∣ ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ )
    else
      Zero.
Proof. easy. Qed.

Hint Rewrite denote_H denote_X denote_Y denote_Z denote_Rz denote_cnot denote_swap unfold_ueval_r : eval_db.
Hint Rewrite unfold_ueval_cnot unfold_pad unfold_ueval_swap : eval_db.

(* Some unit tests *)

Lemma eval_H : uc_eval ((H 0) : ucom 1) = hadamard.
Proof.
  simpl. autorewrite with eval_db.
  simpl. Msimpl. reflexivity.
Qed.

Lemma eval_HHpar : uc_eval ((H 0; H 1) : ucom 2) = hadamard ⊗ hadamard.
Proof.
  simpl. autorewrite with eval_db.
  simpl. restore_dims. Msimpl. 
  restore_dims. Msimpl. 
  reflexivity.
Qed.

Lemma eval_HHseq : uc_eval ((H 0; H 0) : ucom 2) = I 4.
Proof.
  simpl. autorewrite with eval_db.
  simpl. Msimpl. solve_matrix.
Qed.

Lemma eval_CNOT : uc_eval ((CNOT 0 1) : ucom 2) = cnot.
Proof.
  simpl. autorewrite with eval_db.
  simpl. Msimpl. solve_matrix.
Qed.

(** Equivalence and Structural Rules **)

(* Precondition about typing? *)
Definition uc_equiv {dim} (c1 c2 : ucom dim) := uc_eval c1 = uc_eval c2.

Infix "≡" := uc_equiv : ucom_scope.

Lemma uc_equiv_refl : forall {dim} (c1 : ucom dim), c1 ≡ c1. 
Proof. easy. Qed.

Lemma uc_equiv_sym : forall {dim} (c1 c2 : ucom dim), c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

Lemma uc_equiv_trans : forall {dim} (c1 c2 c3 : ucom dim), c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. intros dim c1 c2 c3 H12 H23. unfold uc_equiv. rewrite H12. easy. Qed.

Lemma useq_assoc : forall {dim} (c1 c2 c3 : ucom dim), ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros dim c1 c2 c3. 
  unfold uc_equiv; simpl.
  rewrite Mmult_assoc. 
  reflexivity.
Qed.

Lemma useq_congruence : forall {dim} (c1 c1' c2 c2' : ucom dim),
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros dim c1 c1' c2 c2' Ec1 Ec2.
  unfold uc_equiv; simpl.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (ucom dim) (@uc_equiv dim)
  reflexivity proved by uc_equiv_refl
  symmetry proved by uc_equiv_sym
  transitivity proved by uc_equiv_trans
  as uc_equiv_rel.

Add Parametric Morphism (dim : nat) : (@useq dim)
  with signature (@uc_equiv dim) ==> (@uc_equiv dim) ==> (@uc_equiv dim) as useq_mor.
Proof. intros x y H x0 y0 H0. apply useq_congruence; easy. Qed.

Lemma test_rel : forall (dim : nat) (c1 c2 : ucom dim), c1 ≡ c2 -> c2 ≡ c1.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma test_mor : forall (dim : nat) (c1 c2 : ucom dim), c1 ≡ c2 -> c2 ; c1 ≡ c1 ; c1.
Proof. intros. rewrite H. reflexivity. Qed.

(** Equivalence up to a phase. **)

Require Import Proportional.

Definition uc_cong {dim : nat} (c1 c2 : ucom dim) :=
  uc_eval c1 ∝ uc_eval c2.
Infix "≅" := uc_cong (at level 70).

Lemma uc_cong_refl : forall {dim : nat} (c1 : ucom dim), c1 ≅ c1.
Proof. intros. exists 0%R. rewrite Cexp_0. rewrite Mscale_1_l. reflexivity. Qed.

Lemma uc_cong_sym : forall {dim : nat} (c1 c2 : ucom dim), c1 ≅ c2 -> c2 ≅ c1.
Proof.
  intros. inversion H.
  exists (Ropp x). rewrite H0. rewrite Mscale_assoc. rewrite <- Cexp_add.
  rewrite Rplus_comm.
  rewrite Rplus_opp_r. rewrite Cexp_0. rewrite Mscale_1_l. reflexivity.
Qed.

Lemma uc_cong_trans : forall {dim : nat} (c1 c2 c3 : ucom dim), c1 ≅ c2 -> c2 ≅ c3 -> c1 ≅ c3.
Proof.
  intros. inversion H. inversion H0.
  exists (x + x0)%R. rewrite H1. rewrite H2.
  rewrite Mscale_assoc.
  rewrite Cexp_add. reflexivity.
Qed.

Lemma uc_equiv_cong : forall {dim : nat} (c c' : ucom dim), (c ≡ c')%ucom -> c ≅ c'.
Proof.
  intros.
  exists 0. rewrite Cexp_0, Mscale_1_l. 
  apply H.
Qed.

(** uc_eval is unitary iff well-typed **)

Lemma pad_unitary : forall n (u : Square (2^n)) start dim,
    (start + n <= dim)%nat -> 
    WF_Unitary u ->
    WF_Unitary (pad start dim u).
Proof.
  intros n u start dim B [WF U].
  split. apply WF_pad; auto.
  unfold pad.
  gridify.
  Msimpl.
  rewrite U.
  reflexivity.
Qed.
  
Lemma ueval_r_unitary : forall dim n θ ϕ λ,
    (n < dim)%nat ->
    WF_Unitary (ueval_r dim n θ ϕ λ).
Proof.
  intros. apply pad_unitary. lia.
  apply rotation_unitary. 
Qed.  

(* TODO: Move elsewhere *)
Lemma WF_Matrix_dim_change : forall (m n m' n' : nat) (A : Matrix m n),
  m = m' ->
  n = n' ->
  @WF_Matrix m n A ->
  @WF_Matrix m' n' A.
Proof. intros. subst. easy. Qed.

Hint Resolve WF_Matrix_dim_change.

Lemma ueval_cnot_unitary : forall dim m n,
    m <> n ->
    (m < dim)%nat ->
    (n < dim)%nat ->
    WF_Unitary (ueval_cnot dim m n).
Proof.
  intros dim m n NE Lm Ln.
  unfold ueval_cnot, pad.
  gridify.
  - split.
    + apply WF_Matrix_dim_change; try (unify_pows_two; lia).
      apply WF_plus; auto with wf_db.
    + Msimpl.
      unify_pows_two.
      replace (m + d + 1)%nat with (m + 1 + d)%nat by lia.
      gridify.
      autorewrite with cnot_db.
      Msimpl.
      replace (σx† × σx) with (I 2) by solve_matrix.
      repeat rewrite <- kron_plus_distr_r.
      repeat rewrite <- kron_plus_distr_l.
      unify_matrices.
      solve_matrix.
  - split.
    + apply WF_Matrix_dim_change; try (unify_pows_two; lia).
      apply WF_plus; auto with wf_db. (* shouldn't be necessary *)
    + Msimpl.
      unify_pows_two.
      replace (n + d + 1)%nat with (n + 1 + d)%nat by lia.
      gridify.
      autorewrite with cnot_db.
      Msimpl.
      replace (σx† × σx) with (I 2) by solve_matrix.
      repeat rewrite <- kron_plus_distr_r.
      repeat rewrite <- kron_plus_distr_l.
      unify_matrices.
      solve_matrix.
Qed.      

Lemma uc_eval_unitary : forall (dim : nat) (c : ucom dim),
    uc_well_typed c -> WF_Unitary (uc_eval c).
Proof.
  intros dim c H.
  unfold WF_Unitary.
  split. apply WF_uc_eval.
  induction c.
  - simpl. Msimpl. reflexivity.
  - inversion H; subst.
    simpl. Msimpl. rewrite <- Mmult_assoc. rewrite (Mmult_assoc (_)†).
    rewrite IHc2; trivial. Msimpl.
    rewrite IHc1; easy.
  - inversion H; subst.
    simpl. destruct (ueval_r_unitary dim n r r0 r1 H1) as [_ UU].
    assumption.
  - inversion H; subst.
    simpl. destruct (ueval_cnot_unitary dim n n0 H4 H2 H3) as [_ UU].
    assumption.
Qed.

Lemma WT_if_nonzero : forall (dim : nat) (c : ucom dim),
  uc_eval c <> Zero -> uc_well_typed c.
Proof.
  intros dim u.
  induction u; intros H.
  - constructor.
  - simpl in *.
    constructor.
    + apply IHu1.
      intros F. rewrite F in *.
      rewrite Mmult_0_r in H.
      contradiction.
    + apply IHu2.
      intros F. rewrite F in *.
      rewrite Mmult_0_l in H.
      contradiction.
  - simpl in *. 
    autorewrite with eval_db in H.
    bdestruct (n + 1 <=? dim); try contradiction. 
    constructor; lia.
  - simpl in *. 
    autorewrite with eval_db in H.
    bdestruct (n <? n0). 
    + bdestruct (n + (1 + (n0 - n - 1) + 1) <=? dim); try contradiction.
      constructor; lia.
    + bdestruct (n0 <? n); try contradiction.
      bdestruct (n0 + (1 + (n - n0 - 1) + 1) <=? dim); try contradiction.
      constructor; lia.
Qed.

(* Now we get bidirectionality for free! *)

Lemma uc_eval_unitary_iff : forall (dim : nat) (c : ucom dim),
    uc_well_typed c <-> WF_Unitary (uc_eval c).
Proof.
  split.
  - apply uc_eval_unitary.
  - intros H.
    apply WT_if_nonzero.
    intros F.
    rewrite F in H.
    apply zero_not_unitary in H.
    easy.
Qed.

Lemma uc_eval_nonzero_iff : forall (dim : nat) (c : ucom dim),
  uc_eval c <> Zero <-> uc_well_typed c.
Proof.
  split.
  - apply WT_if_nonzero.
  - intros H.
    intros F.
    apply uc_eval_unitary in H.
    rewrite F in H.
    apply zero_not_unitary in H.
    easy.
Qed.

(** Proofs about high-level functions over unitary programs **)

Local Close Scope C_scope.
Local Close Scope R_scope.

Lemma invert_ucom_correct : forall (dim : nat) (c : ucom dim),
  (uc_eval c)† = uc_eval (invert_ucom c).
Proof.
  intros.
  induction c.
  - simpl. Msimpl. reflexivity.
  - simpl. Msimpl. rewrite IHc1. rewrite IHc2. reflexivity.
  - simpl. autorewrite with eval_db.
    bdestruct (n + 1 <=? dim); try apply zero_adjoint_eq.
    repeat setoid_rewrite kron_adjoint; Msimpl.
    rewrite rotation_adjoint.
    reflexivity.
  - simpl.
    unfold ueval_cnot, pad.
    gridify; try (rewrite zero_adjoint_eq; reflexivity).
    Msimpl. rewrite σx_sa. reflexivity.
    Msimpl. rewrite σx_sa. reflexivity.
Qed.

