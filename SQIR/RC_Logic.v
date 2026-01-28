Require Import String.
From SQIR Require Export SQIR.
Require Import QuantumLib.Complex.
From SQIR Require Import RC_Syntax RC_Semantics.
Require Import Coq.Arith.PeanoNat.

Local Open Scope com_scope.
Local Open Scope matrix_scope.

(***********************************)
(** Approximation Unrolling       **)
(***********************************)

Section Approximation.
  Context {U : nat -> Set}.
  Context {dim : nat}.
  Variable proc_body : string -> RC_Syntax.com U dim.

  Fixpoint unroll_call (k : nat) (p : string) (c : RC_Syntax.com U dim) : RC_Syntax.com U dim :=
    let fix walk (c0 : RC_Syntax.com U dim) : RC_Syntax.com U dim :=
      match c0 with
      | CSkip => CSkip
      | CAbort => CAbort
      | CSeq c1 c2 => CSeq (walk c1) (walk c2)
      | CIf n c1 c2 => CIf n (walk c1) (walk c2)
      | CWhile n c1 => CWhile n (walk c1)
      | CUnitary u => CUnitary u
      | CMeasure n c1 c2 => CMeasure n (walk c1) (walk c2)
      | CCall p' =>
          if String.eqb p p'
          then match k with
               | 0 => CAbort
               | S k' => unroll_call k' p (proc_body p)
               end
          else CCall p'
      end
    in walk c.

  Definition approx_unroll (k : nat) (p : string) : RC_Syntax.com U dim :=
    unroll_call k p (proc_body p).

  Fixpoint while_unroll (k : nat) (n : nat) (c : RC_Syntax.com U dim) : RC_Syntax.com U dim :=
    match k with
    | 0 => CSkip
    | S k' => CIf n (CSeq c (while_unroll k' n c)) CSkip
    end.
End Approximation.

(************************)
(** Weakest Precondition **)
(************************)

Section WP.
  Context {dim : nat}.
  Variable proc_body : string -> RC_Syntax.base_com dim.

  Fixpoint wp_fuel (fuel : nat) (c : RC_Syntax.base_com dim) (Q : assert) : assert :=
    match fuel with
    | 0 => ATrue
    | S fuel' =>
        match c with
        | CSkip => Q
        | CAbort => AFalse
        | CSeq c1 c2 => wp_fuel fuel' c1 (wp_fuel fuel' c2 Q)
        | CIf n c1 c2 =>
            AAnd (AImp (AMeas n true) (wp_fuel fuel' c1 Q))
                 (AImp (AMeas n false) (wp_fuel fuel' c2 Q))
        | CWhile n c1 =>
            wp_fuel fuel' (while_unroll fuel' n c1) Q
        | CUnitary u => AUnitary u Q
        | CMeasure n c1 c2 =>
            AAnd (AImp (AMeas n true) (wp_fuel fuel' c1 Q))
                 (AImp (AMeas n false) (wp_fuel fuel' c2 Q))
        | CCall p =>
            wp_fuel fuel' (@approx_unroll base_Unitary dim proc_body fuel' p) Q
        end
    end.

  Definition wp (c : RC_Syntax.base_com dim) (Q : assert) : assert :=
    IConj (fun n => wp_fuel (S n) c Q).
End WP.

(*****************************)
(** Assertion Semantics       **)
(*****************************)

Parameter uc_eval_gen : forall {U dim}, ucom U dim -> Matrix (2^dim) (2^dim).
Axiom uc_eval_gen_base : forall {dim} (u : ucom base_Unitary dim),
  uc_eval_gen u = uc_eval u.

Definition traceR {dim} (ρ : DensityMatrix dim) : R :=
  Re (trace (n:=2^dim) ρ).

Definition subdist {dim} (ρ : DensityMatrix dim) : Prop :=
  0 <= traceR ρ /\ traceR ρ <= 1.

Definition proj_state {dim} (n : nat) (b : bool) (ρ : DensityMatrix dim) : DensityMatrix dim :=
  proj n dim b × ρ × (proj n dim b)†.

Axiom subdist_proj : forall {dim} n b (ρ : DensityMatrix dim),
  subdist (proj_state n b ρ).

Fixpoint assert_denote {dim} (P : assert) (ρ : DensityMatrix dim) : Prop :=
  match P with
  | ATrue => True
  | AFalse => False
  | AMeas n b => subdist ρ /\ proj_state n b ρ = ρ
  | AQState dim' ρ0 =>
      match Nat.eq_dec dim dim' with
      | left Heq =>
          exists p : R,
            0 <= p /\ p <= 1 /\
            ρ = (RtoC p) .* (eq_rect _ (fun d => DensityMatrix d) ρ0 _ (eq_sym Heq))
      | right _ => False
      end
  | AAnd P1 P2 => assert_denote P1 ρ /\ assert_denote P2 ρ
  | AOr P1 P2 => assert_denote P1 ρ \/ assert_denote P2 ρ
  | ANot P1 => ~ assert_denote P1 ρ
  | AImp P1 P2 => assert_denote P1 ρ -> assert_denote P2 ρ
  | AUnitary u P1 => assert_denote P1 (super_denot (uc_eval_gen u) ρ)
  | IConj f => forall i, assert_denote (f i) ρ
  end.

Axiom assert_closed_sum : forall {dim} (Q : assert) (ρ1 ρ2 : DensityMatrix dim),
  @assert_denote dim Q ρ1 -> @assert_denote dim Q ρ2 -> @assert_denote dim Q (ρ1 .+ ρ2).

Axiom meas_proj_state : forall {dim} n b (ρ : DensityMatrix dim),
  @assert_denote dim (AMeas n b) (proj_state n b ρ).

Axiom imp_proj : forall {dim} n b P (ρ : DensityMatrix dim),
  @assert_denote dim (AImp (AMeas n b) P) ρ ->
  @assert_denote dim P (proj_state n b ρ).

Definition assert_entails {dim} (P Q : assert) : Prop :=
  forall ρ : DensityMatrix dim, assert_denote P ρ -> assert_denote Q ρ.

Definition denotes_triple {dim}
  (proc_body : string -> RC_Syntax.base_com dim) (P : assert) (c : RC_Syntax.base_com dim) (Q : assert) : Prop :=
  forall ρ, assert_denote P ρ -> assert_denote Q (eval_recursive proc_body c ρ).

(*****************************)
(** Hoare Rules               **)
(*****************************)

Inductive is_valid_triple {dim}
  (proc_body : string -> RC_Syntax.base_com dim) : assert -> RC_Syntax.base_com dim -> assert -> Prop :=
| H_Skip : forall P,
    is_valid_triple proc_body P CSkip P
| H_Abort : forall Q,
    is_valid_triple proc_body AFalse CAbort Q
| H_Seq : forall P Q R c1 c2,
    is_valid_triple proc_body P c1 R ->
    is_valid_triple proc_body R c2 Q ->
    is_valid_triple proc_body P (CSeq c1 c2) Q
| H_If : forall n P1 P2 Q c1 c2,
    is_valid_triple proc_body P1 c1 Q ->
    is_valid_triple proc_body P2 c2 Q ->
    is_valid_triple proc_body
      (AAnd (AImp (AMeas n true) P1) (AImp (AMeas n false) P2))
      (CIf n c1 c2) Q
| H_While : forall n I Q c,
    is_valid_triple proc_body (AAnd I (AMeas n true)) c I ->
    @assert_entails dim (AAnd I (AMeas n false)) Q ->
    is_valid_triple proc_body I (CWhile n c) Q
| H_Unitary : forall u Q,
    is_valid_triple proc_body (AUnitary u Q) (CUnitary u) Q
| H_Measure : forall n P1 P2 Q c1 c2,
    is_valid_triple proc_body P1 c1 Q ->
    is_valid_triple proc_body P2 c2 Q ->
    is_valid_triple proc_body
      (AAnd (AImp (AMeas n true) P1) (AImp (AMeas n false) P2))
      (CMeasure n c1 c2) Q
| H_Call : forall (p : string) Q,
    is_valid_triple proc_body
      (IConj (fun i => (@wp dim proc_body) (@approx_unroll base_Unitary dim proc_body i p) Q))
      (CCall p) Q
| H_Conseq : forall P P' Q Q' c,
    @assert_entails dim P P' ->
    @assert_entails dim Q' Q ->
    is_valid_triple proc_body P' c Q' ->
    is_valid_triple proc_body P c Q.

(*****************************)
(** Soundness Statement       **)
(*****************************)

Lemma denotes_conseq : forall {dim} (proc_body : string -> RC_Syntax.base_com dim) P P' Q Q' c,
  @assert_entails dim P P' ->
  @assert_entails dim Q' Q ->
  denotes_triple proc_body P' c Q' ->
  denotes_triple proc_body P c Q.
Proof.
  intros dim proc_body P P' Q Q' c HP HQ Hden ρ HPρ.
  apply HQ. apply Hden. apply HP. exact HPρ.
Qed.

Lemma denotes_if : forall {dim} (proc_body : string -> RC_Syntax.base_com dim) n P1 P2 Q c1 c2,
  denotes_triple proc_body P1 c1 Q ->
  denotes_triple proc_body P2 c2 Q ->
  denotes_triple proc_body
    (AAnd (AImp (AMeas n true) P1) (AImp (AMeas n false) P2))
    (CIf n c1 c2) Q.
Proof.
  intros dim proc_body n P1 P2 Q c1 c2 H1 H2 ρ [HimpT HimpF].
  simpl.
  unfold eval_if, apply_proj.
  specialize (H1 (proj_state n true ρ)).
  specialize (H2 (proj_state n false ρ)).
  assert (assert_denote (AMeas n true) (proj_state n true ρ)) as HmeasT
    by apply meas_proj_state.
  assert (assert_denote (AMeas n false) (proj_state n false ρ)) as HmeasF
    by apply meas_proj_state.
  pose proof (imp_proj (dim:=dim) n true P1 ρ) as HprojT.
  pose proof (imp_proj (dim:=dim) n false P2 ρ) as HprojF.
  specialize (HprojT HimpT).
  specialize (HprojF HimpF).
  apply assert_closed_sum.
  - apply H1. exact HprojT.
  - apply H2. exact HprojF.
Qed.

Lemma denotes_measure : forall {dim} (proc_body : string -> RC_Syntax.base_com dim) n P1 P2 Q c1 c2,
  denotes_triple proc_body P1 c1 Q ->
  denotes_triple proc_body P2 c2 Q ->
  denotes_triple proc_body
    (AAnd (AImp (AMeas n true) P1) (AImp (AMeas n false) P2))
    (CMeasure n c1 c2) Q.
Proof.
  intros dim proc_body n P1 P2 Q c1 c2 H1 H2.
  apply denotes_if; assumption.
Qed.

Parameter while_sound : forall {dim} (proc_body : string -> RC_Syntax.base_com dim) n I Q c,
  denotes_triple proc_body (AAnd I (AMeas n true)) c I ->
  @assert_entails dim (AAnd I (AMeas n false)) Q ->
  denotes_triple proc_body I (CWhile n c) Q.

Parameter call_sound : forall {dim} (proc_body : string -> RC_Syntax.base_com dim) p Q,
  denotes_triple proc_body
    (IConj (fun i => (@wp dim proc_body) (@approx_unroll base_Unitary dim proc_body i p) Q))
    (CCall p) Q.

Lemma denotes_while : forall {dim} (proc_body : string -> RC_Syntax.base_com dim) n I Q c,
  denotes_triple proc_body (AAnd I (AMeas n true)) c I ->
  @assert_entails dim (AAnd I (AMeas n false)) Q ->
  denotes_triple proc_body I (CWhile n c) Q.
Proof. intros; eapply while_sound; eauto. Qed.

Lemma denotes_call : forall {dim} (proc_body : string -> RC_Syntax.base_com dim) p Q,
  denotes_triple proc_body
    (IConj (fun i => (@wp dim proc_body) (@approx_unroll base_Unitary dim proc_body i p) Q))
    (CCall p) Q.
Proof. intros; eapply call_sound. Qed.

Theorem soundness : forall {dim} (proc_body : string -> RC_Syntax.base_com dim) (c : RC_Syntax.base_com dim) (P Q : assert),
  is_valid_triple proc_body P c Q -> denotes_triple proc_body P c Q.
Proof.
  intros dim proc_body c P Q Hvalid.
  induction Hvalid.
  - intros ρ HP. exact HP.
  - intros ρ Hfalse. contradiction.
  - intros ρ HP. apply IHHvalid2. apply IHHvalid1. exact HP.
  - apply denotes_if; assumption.
  - apply denotes_while; assumption.
  - intros ρ HP. simpl in *. rewrite uc_eval_gen_base in HP. exact HP.
  - apply denotes_measure; assumption.
  - apply denotes_call.
  - eapply denotes_conseq; eauto.
Qed.
