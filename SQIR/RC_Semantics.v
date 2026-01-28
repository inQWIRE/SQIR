Require Import String.
Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Matrix.
Require Import QuantumLib.Quantum.
From SQIR Require Export UnitarySem UnitaryOps.
From SQIR Require Import RC_Syntax.

Local Open Scope matrix_scope.

(*********************)
(** Denotations      **)
(*********************)

Definition DensityMatrix (dim : nat) : Type := Matrix (2^dim) (2^dim).
Definition Denot (dim : nat) : Type := DensityMatrix dim -> DensityMatrix dim.
Definition Env (dim : nat) : Type := string -> Denot dim.

Definition denot_skip {dim} : Denot dim := fun ρ => ρ.
Definition denot_abort {dim} : Denot dim := fun _ => Zero.
Definition denot_compose {dim} (d2 d1 : Denot dim) : Denot dim :=
  fun ρ => d2 (d1 ρ).
Definition denot_plus {dim} (d1 d2 : Denot dim) : Denot dim :=
  fun ρ => d1 ρ .+ d2 ρ.

Definition super_denot {dim} (U : Matrix (2^dim) (2^dim)) : Denot dim :=
  fun ρ => U × ρ × U†.

Definition apply_proj {dim} (n : nat) (b : bool) : Denot dim :=
  fun ρ => proj n dim b × ρ × (proj n dim b)†.

Definition eval_if {dim} (n : nat) (d1 d2 : Denot dim) : Denot dim :=
  fun ρ => d1 (apply_proj n true ρ) .+ d2 (apply_proj n false ρ).

(************************)
(** Partial Order/CPO **)
(************************)

Definition traceR {dim} (ρ : DensityMatrix dim) : R :=
  Re (trace (n:=2^dim) ρ).

Definition le_denot {dim} (d1 d2 : Denot dim) : Prop :=
  forall ρ, traceR (d1 ρ) <= traceR (d2 ρ).

Definition denot_equiv {dim} (d1 d2 : Denot dim) : Prop :=
  le_denot d1 d2 /\ le_denot d2 d1.

Definition bottom_denot {dim} : Denot dim := denot_abort.

Definition chain {A : Type} (le : A -> A -> Prop) (f : nat -> A) : Prop :=
  forall n, le (f n) (f (S n)).

Lemma chain_shift : forall {A} (le : A -> A -> Prop) (f : nat -> A),
  chain le f -> chain le (fun n => f (S n)).
Proof. intros A le f H n. apply (H (S n)). Qed.

Parameter lub_denot : forall {dim}, (nat -> Denot dim) -> Denot dim.
Axiom lub_denot_upper : forall {dim} (f : nat -> Denot dim) n,
  chain le_denot f -> le_denot (f n) (lub_denot f).
Axiom lub_denot_least : forall {dim} (f : nat -> Denot dim) x,
  chain le_denot f -> (forall n, le_denot (f n) x) -> le_denot (lub_denot f) x.
Axiom bottom_least : forall {dim} (d : Denot dim), le_denot bottom_denot d.

Definition monotone {dim} (F : Denot dim -> Denot dim) : Prop :=
  forall d1 d2, le_denot d1 d2 -> le_denot (F d1) (F d2).

Definition continuous {dim} (F : Denot dim -> Denot dim) : Prop :=
  forall f, chain le_denot f ->
    denot_equiv (F (lub_denot f)) (lub_denot (fun n => F (f n))).

Lemma le_denot_refl : forall {dim} (d : Denot dim), le_denot d d.
Proof. intros dim d ρ. lra. Qed.

Lemma le_denot_trans : forall {dim} (d1 d2 d3 : Denot dim),
  le_denot d1 d2 -> le_denot d2 d3 -> le_denot d1 d3.
Proof. intros dim d1 d2 d3 H12 H23 ρ. specialize (H12 ρ). specialize (H23 ρ). lra. Qed.

Lemma lub_shift_equiv : forall {dim} (f : nat -> Denot dim),
  chain le_denot f -> denot_equiv (lub_denot f) (lub_denot (fun n => f (S n))).
Proof.
  intros dim f Hchain. split.
  - apply lub_denot_least; auto.
    intro n.
    pose proof (Hchain n) as Hstep.
    pose proof (lub_denot_upper (fun k => f (S k)) n (chain_shift le_denot f Hchain)) as Hlub.
    eapply le_denot_trans; eauto.
  - apply lub_denot_least.
    + apply chain_shift. exact Hchain.
    + intro n. apply lub_denot_upper. exact Hchain.
Qed.

(************************)
(** Fixed-Point Semantics **)
(************************)

Fixpoint iter_denot {dim} (n : nat) (F : Denot dim -> Denot dim) (x : Denot dim) : Denot dim :=
  match n with
  | 0 => x
  | S n' => F (iter_denot n' F x)
  end.

Definition Fix {dim} (F : Denot dim -> Denot dim) : Denot dim :=
  lub_denot (fun n => iter_denot n F bottom_denot).

Lemma iter_chain : forall {dim} (F : Denot dim -> Denot dim),
  monotone F -> chain le_denot (fun n => iter_denot n F bottom_denot).
Proof.
  intros dim F Hmono n. simpl.
  induction n.
  - apply bottom_least.
  - apply Hmono. apply IHn.
Qed.

Lemma Fix_least : forall {dim} (F : Denot dim -> Denot dim) x,
  monotone F ->
  (forall n, le_denot (iter_denot n F bottom_denot) x) ->
  le_denot (Fix F) x.
Proof.
  intros dim F x Hmono Hbound.
  apply lub_denot_least.
  - apply iter_chain; assumption.
  - exact Hbound.
Qed.

Lemma Fix_unfold : forall {dim} (F : Denot dim -> Denot dim),
  monotone F -> continuous F -> denot_equiv (Fix F) (F (Fix F)).
Proof.
  intros dim F Hmono Hcont.
  unfold Fix.
  specialize (Hcont (fun n => iter_denot n F bottom_denot) (iter_chain F Hmono)).
  destruct Hcont as [Hle1 Hle2].
  destruct (lub_shift_equiv (fun n => iter_denot n F bottom_denot) (iter_chain F Hmono))
    as [Hshift1 Hshift2].
  split.
  - eapply le_denot_trans; [exact Hshift1|exact Hle2].
  - eapply le_denot_trans; [exact Hle1|exact Hshift2].
Qed.

Definition le_env {dim} (e1 e2 : Env dim) : Prop :=
  forall p, le_denot (e1 p) (e2 p).

Definition env_equiv {dim} (e1 e2 : Env dim) : Prop :=
  forall p, denot_equiv (e1 p) (e2 p).

Definition bottom_env {dim} : Env dim := fun _ => bottom_denot.

Definition chain_env {dim} (f : nat -> Env dim) : Prop :=
  forall n p, le_denot (f n p) (f (S n) p).

Lemma chain_env_pointwise : forall {dim} (f : nat -> Env dim) (p : string),
  chain_env f -> chain le_denot (fun n => f n p).
Proof. intros dim f p H n. apply (H n p). Qed.

Definition lub_env {dim} (f : nat -> Env dim) : Env dim :=
  fun p => lub_denot (fun n => f n p).

Lemma lub_env_upper : forall {dim} (f : nat -> Env dim) n,
  chain_env f -> le_env (f n) (lub_env f).
Proof.
  intros dim f n Hchain p.
  refine (@lub_denot_upper dim (fun k => f k p) n _).
  apply (chain_env_pointwise f p Hchain).
Qed.

Lemma lub_env_least : forall {dim} (f : nat -> Env dim) x,
  chain_env f -> (forall n, le_env (f n) x) -> le_env (lub_env f) x.
Proof.
  intros dim f x Hchain Hbound p.
  refine (@lub_denot_least dim (fun k => f k p) (x p) _ _).
  - apply (chain_env_pointwise f p Hchain).
  - intro n. specialize (Hbound n p). exact Hbound.
Qed.

Lemma lub_env_shift_equiv : forall {dim} (f : nat -> Env dim),
  chain_env f -> env_equiv (lub_env f) (lub_env (fun n => f (S n))).
Proof.
  intros dim f Hchain p.
  apply lub_shift_equiv.
  intro n. apply Hchain.
Qed.

Definition monotone_env {dim} (F : Env dim -> Env dim) : Prop :=
  forall e1 e2, le_env e1 e2 -> le_env (F e1) (F e2).

Definition continuous_env {dim} (F : Env dim -> Env dim) : Prop :=
  forall f, chain_env f ->
    env_equiv (F (lub_env f)) (lub_env (fun n => F (f n))).

Fixpoint iter_env {dim} (n : nat) (F : Env dim -> Env dim) (x : Env dim) : Env dim :=
  match n with
  | 0 => x
  | S n' => F (iter_env n' F x)
  end.

Definition FixEnv {dim} (F : Env dim -> Env dim) : Env dim :=
  lub_env (fun n => iter_env n F bottom_env).

Lemma iter_env_chain : forall {dim} (F : Env dim -> Env dim),
  monotone_env F -> chain_env (fun n => iter_env n F bottom_env).
Proof.
  intros dim F Hmono n. simpl.
  induction n.
  - intro p. apply bottom_least.
  - intro p.
    apply (Hmono (iter_env n F bottom_env) (iter_env (S n) F bottom_env)).
    exact IHn.
Qed.

Lemma FixEnv_unfold : forall {dim} (F : Env dim -> Env dim),
  monotone_env F -> continuous_env F -> env_equiv (FixEnv F) (F (FixEnv F)).
Proof.
  intros dim F Hmono Hcont p.
  unfold FixEnv.
  specialize (Hcont (fun n => iter_env n F bottom_env) (iter_env_chain F Hmono) p).
  destruct Hcont as [Hle1 Hle2]. split.
  - pose proof (lub_env_shift_equiv (fun n => iter_env n F bottom_env)
      (iter_env_chain F Hmono) p) as [Hshift1 Hshift2].
    eapply le_denot_trans; [exact Hshift1|exact Hle2].
  - pose proof (lub_env_shift_equiv (fun n => iter_env n F bottom_env)
      (iter_env_chain F Hmono) p) as [Hshift1 Hshift2].
    eapply le_denot_trans; [exact Hle1|exact Hshift2].
Qed.

Fixpoint eval_com {dim} (env : Env dim) (c : RC_Syntax.base_com dim) : Denot dim :=
  match c with
  | CSkip => denot_skip
  | CAbort => denot_abort
  | CSeq c1 c2 => denot_compose (eval_com env c2) (eval_com env c1)
  | CIf n c1 c2 => eval_if n (eval_com env c1) (eval_com env c2)
  | CWhile n c1 =>
      Fix (fun X => eval_if n (denot_compose X (eval_com env c1)) denot_skip)
  | CUnitary u => super_denot (uc_eval u)
  | CMeasure n c1 c2 => eval_if n (eval_com env c1) (eval_com env c2)
  | CCall p => env p
  end.

Definition env_step {dim} (proc_body : string -> RC_Syntax.base_com dim) (env : Env dim) : Env dim :=
  fun p => eval_com env (proc_body p).

Definition resolve_env {dim} (proc_body : string -> RC_Syntax.base_com dim) : Env dim :=
  FixEnv (env_step proc_body).

Definition eval_recursive {dim} (proc_body : string -> RC_Syntax.base_com dim) (c : RC_Syntax.base_com dim) : Denot dim :=
  eval_com (resolve_env proc_body) c.
