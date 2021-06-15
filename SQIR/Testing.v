Require Import Arith Vector Bvector Equality MSets OrderedTypeEx Lia.
From QuickChick Require Import QuickChick.
Require Import VSQIR Utilities.
Import Vector (hd, tl).
Import Decidability (dec).
Import VSQIR (exp(..), pexp(..), CNOT).

Module Nat_as_OT := Update_OT Nat_as_OT.
(* Used for finite sets of variables *)
Module VarSet := Make Nat_as_OT.
Import VarSet.

Open Scope vector_scope.
Open Scope string_scope.
Open Scope nat_scope.
Open Scope bool_scope.
Open Scope exp_scope.

(* Bitwise xor *)
Infix "(+)" := (BVxor _) (at level 50, left associativity).

Definition show_bit b :=
  match b with
  | false => "0"
  | true => "1"
  end.

(* Order is reversed because Bvectors are little-endian *)
Fixpoint show_bvector' {n} : Bvector n -> string :=
  match n with
  | 0 => fun _ => ""
  | S n' => fun v => show_bvector' (tl v) ++ show_bit (hd v)
  end.

Instance show_bvector n : Show (Bvector n) := {| show := show_bvector' |}.

(* Lists Bvectors with one "1" flipped to "0" *)
Fixpoint shrink_bvector' {n} : Bvector n -> list (Bvector n) :=
  match n with
  | 0 => fun _ => nil
  | S n' =>
      fun v =>
      let tail := tl v in
      let shrink_tl := shrink_bvector' tail in 
      if hd v
        then cons (false :: tail) (map (Bcons true _) shrink_tl)
        else map (Bcons false _) shrink_tl
  end.

Instance shrink_bvector n : Shrink (Bvector n) :=
  {| shrink := shrink_bvector' |}.

(* Uniformly randomly selected boolean *)
Definition gen_bool :=
  elems_ false (false :: true :: nil)%list.

(* Uniformly randomly selected Bvector *)
Fixpoint gen_bvector' {n} : G (Bvector n) :=
  match n with
  | 0 => returnGen Bnil
  | S n' =>
      bind gen_bool (fun b => bind gen_bvector' (fun v => ret (b :: v)))
  end.

Instance gen_bvector n : Gen (Bvector n) := {| arbitrary := gen_bvector' |}.

(* The natural number represented in binary in the sequence of bits *)
Fixpoint bvector2nat {n} : Bvector n -> nat :=
  match n with
  | 0 => fun _ => 0
  | S n' => fun v => Nat.b2n (hd v) + 2 * bvector2nat (tl v)
  end.

(* Represents the natural number in binary, trucating if necessary *)
Fixpoint nat2bvector n : nat -> Bvector n :=
  match n with
  | 0 => fun _ => Bnil
  | S n' => fun i => Nat.odd i :: nat2bvector n' (i / 2)
  end.

Lemma bvector2nat2bvector :
  forall n v, nat2bvector n (bvector2nat v) = v.
Proof.
  intros n. induction n; intros v; dependent destruction v; try reflexivity.
  cbn - [ "*" Nat.div ].
  assert
    (forall h h' (t t' : Bvector n), h = h' -> t = t' -> h :: t = h' :: t').
  { intros. subst. reflexivity. }
  apply H.
  - destruct h; cbn - [ "*" ].
    + rewrite Nat.odd_succ, Nat.even_spec. econstructor. reflexivity.
    + rewrite <- Nat.negb_even, negb_false_iff, Nat.even_spec.
      econstructor. reflexivity.
  - rewrite Nat.add_b2n_double_div2. apply IHn.
Qed.

(* Rotation of 0, multiplication by 1 *)
Definition zero_angle : rz_val :=
  fun _ => false.

(* A single-qubit state representing either |0> or |1> *)
Definition basis_val b := nval b zero_angle.

(* The single-qubit state |0> *)
Definition zero_val := basis_val false.

(* A program state is a mapping from positions to values *)
Definition state := posi -> val.

(* A program state with all qubits set to |0>, used for initialization *)
Definition zero_state : state := fun p => zero_val.

Notation "x |-> vx , st" :=
    (eupdate st x vx) (at level 100, vx at next level, right associativity).
Infix "|->" := (eupdate zero_state) (at level 100).

(* Updates a whole variable rather than a single position *)
Reserved Notation "x |=> vx , st" 
    (at level 100, vx at next level, right associativity).
Fixpoint update_var {n} (st : state) x : Bvector n -> state :=
  match n with
  | 0 => fun _ => st
  | S n' => fun vx => (x |=> tl vx, (x, n') |-> basis_val (hd vx), st)
  end
where "x |=> vx , st" := (update_var st x vx).

Infix "|=>" := (update_var zero_state) (at level 100).

(* A finite set of variables (nats) *)
Definition var_set := VarSet.t.

(* Converts a decidable Prop to a boolean representing the decision *)
Definition dec2bool P `{H : Dec P} : bool :=
  let '{| dec := d |} := H in
  if d then true else false.

Lemma dec2bool_correct :
  forall P `{Dec P}, P <-> dec2bool P = true.
Proof.
  intros P H. destruct H as [[|]] eqn:E; simpl; split; auto.
  discriminate.
Qed.

(* A For_all Prop is decidable if the sub-Prop is decidable for all variables *)
Instance dec_var_set_for_all {P : var -> Prop} `{forall x, Dec (P x)} :
  forall vars, Dec (For_all P vars).
Proof.
  intros vars. constructor.
  replace P with (fun x => P x) by reflexivity.
  destruct (for_all (fun x => dec2bool (P x)) vars) eqn:E.
  - left. intros x Hi. rewrite for_all_spec in E.
    + specialize (E x Hi). simpl in E. apply dec2bool_correct in E. assumption.
    + intros y y' Hy. subst. reflexivity.
  - right. intros Hc. rewrite <- not_true_iff_false in E. apply E.
    apply for_all_spec.
    + intros y y' Hy. subst. reflexivity.
    + intros x Hx. apply dec2bool_correct. apply Hc. assumption.
Defined.

(* An environment mapping variables to their sizes *)
Definition f_env := var -> nat.

(* A Prop is true for every position in an environment *)
Definition for_all_env (P : posi -> Prop) (vars : var_set) (env : f_env) := 
  For_all (fun x => forall i, i < env x -> P (x, i)) vars.

(* It's decidable whether a Prop is true for a finite number of nats *)
Definition dec_fin :
  forall (P : nat -> Prop) `{forall i, Dec (P i)} n,
  Dec (forall i, i < n -> P i).
Proof.
  intros P Hd n. constructor. induction n as [| n IH].
  - left. intros i H. lia.
  - destruct IH.
    + destruct (Hd n) as [[|]].
      * left. intros i H. destruct (Nat.eq_dec i n).
        -- subst. assumption.
        -- assert (i < n) by lia. auto.
      * right. intros Hc. apply n0. apply Hc. constructor.
    + right. intros Hc. apply n0. intros i H. apply Hc. lia.
Qed.

Instance dec_for_all_env {P : posi -> Prop} `{forall x, Dec (P x)} :
  forall vars env, Dec (for_all_env P vars env).
Proof.
  intros vars env. constructor.
  assert (forall x, Dec (forall i, i < env x -> P (x, i))).
  { intros x. apply dec_fin. intros i. apply H0. }
  apply dec_var_set_for_all.
Defined.

(* Two rotations can be equivalent up to a given precision *)
Definition rz_val_equiv prec (z z' : rz_val) :=
  forall i, i < prec -> z i = z' i.

Instance dec_rz_val_equiv :
  forall prec z z', Dec (rz_val_equiv prec z z').
Proof.
  intros prec z z'. apply dec_fin.
  intros i. apply Eq__Dec.
Defined.

(* Value equivalence is based on rotation equivalence up to a given precision *)
Inductive val_equiv prec : val -> val -> Prop :=
  | val_equiv_nval b z z' :
      rz_val_equiv prec z z' -> val_equiv prec (nval b z) (nval b z')
  | val_equiv_hval b0 b1 z z' :
      rz_val_equiv prec z z' -> val_equiv prec (hval b0 b1 z) (hval b0 b1 z')
  | val_equiv_qval z0 z0' z1 z1' :
      rz_val_equiv prec z0 z0' ->
      rz_val_equiv prec z1 z1' ->
      val_equiv prec (qval z0 z1) (qval z0' z1').

Instance dec_val_equiv :
  forall prec v v', Dec (val_equiv prec v v').
Proof.
  intros prec v v'. constructor.
  destruct v as [b z | b0 b1 z | z0 z1 ], v' as [b' z' | b0' b1' z' | z0' z1'];
  try (right; intros H; inversion H; discriminate).
  - destruct (bool_dec b b'); try (right; intros H; inversion H; contradiction).
    subst. destruct (dec_rz_val_equiv prec z z') as [[|]].
    + left. constructor. assumption.
    + right. intros H. inversion H. contradiction.
  - destruct (bool_dec b0 b0'), (bool_dec b1 b1');
    try (right; intros H; inversion H; contradiction).
    subst. destruct (dec_rz_val_equiv prec z z') as [[|]].
    + left. constructor. assumption.
    + right. intros H. inversion H. contradiction.
  - destruct (dec_rz_val_equiv prec z0 z0') as [[|]],
             (dec_rz_val_equiv prec z1 z1') as [[|]];
    try (right; intros H; inversion H; contradiction).
    left. constructor; assumption.
Defined.
    
(* States are equivalent if all values in the environment are equivalent *)
Definition st_equiv vars env prec (st st' : state) :=
  for_all_env (fun x => val_equiv prec (st x) (st' x)) vars env.

(* Get the variables in an exp *)
Fixpoint get_exp_vars e :=
  match e with
  | SKIP p => singleton (fst p)
  | X p => singleton (fst p)
  | CU p e' => add (fst p) (get_exp_vars e')
  | RZ _ p => singleton (fst p)
  | RRZ _ p => singleton (fst p)
  | SR _ x => singleton x
  | SRR _ x => singleton x
  | HCNOT p1 p2 => add (fst p1) (singleton (fst p2))
  | Lshift x => singleton x
  | Rshift x => singleton x
  | Rev x => singleton x
  | e1; e2 => union (get_exp_vars e1) (get_exp_vars e2)
  end.

(* Get the variables in a pexp *)
Fixpoint get_vars e :=
  match e with
  | Exp e' => get_exp_vars e'
  | QFT x => singleton x
  | RQFT x => singleton x
  | H x => singleton x
  | PCU p e' => add (fst p) (get_vars e')
  | e1;; e2 => union (get_vars e1) (get_vars e2)
  end.

(* Get the maximum precision in rotations of an exp *)
Fixpoint get_exp_prec e :=
  match e with
  | SKIP _ => 0
  | X _ => 0
  | CU _ e' => get_exp_prec e'
  | RZ n _ => n
  | RRZ n _ => n
  | SR n _ => n
  | SRR n _ => n
  | HCNOT _ _ => 0
  | Lshift _ => 0
  | Rshift _ => 0
  | Rev _ => 0
  | e1; e2 => max (get_exp_prec e1) (get_exp_prec e2)
  end.

(* Get the maximum precision in rotations of a pexp *)
Fixpoint get_prec (env : f_env) e :=
  match e with
  | Exp e' => get_exp_prec e'
  | QFT x => env x
  | RQFT x => env x
  | H _ => 0
  | PCU _ e' => get_prec env e'
  | e1;; e2 => max (get_prec env e1) (get_prec env e2)
  end.

(* Is the pexp an oracle for a function from Bvectors to Bvectors? *)
Definition is_oracle x y env (f : Bvector (env x) -> Bvector (env y)) e :=
  forall vx vy,
  st_equiv (get_vars e) env (get_prec env e)
      (prog_sem env e (x |=> vx, y |=> vy)) (x |=> vx, y |=> vy (+) f vx).

(* Is the pexp an oracle for a function from Bvectors to bools? *)
Definition is_oracle_bool x y env (f : Bvector (env x) -> bool) e :=
  env y = 1 /\
  is_oracle x y env (fun v => Vector.const (f v) _) e.

(* Is the pexp an oracle for a function from nats to nats? *)
Definition is_oracle_nat x y env (f : nat -> nat) e :=
  is_oracle x y env (fun v => nat2bvector (env y) (f (bvector2nat v))) e.

(* Is the pexp an oracle for a function from nats to bools? *)
Definition is_oracle_nat_bool x y env (f : nat -> bool) e :=
  env y = 1 /\
  is_oracle x y env (fun v => Vector.const (f (bvector2nat v)) _) e.

Instance checkable_and {P Q : Prop} `{Checkable P} `{Checkable Q} :
  Checkable (P /\ Q) :=
  {|
    checker '(conj p q) := conjoin (checker p :: checker q :: nil)%list
  |}.

(* Example: an oracle for the "not" function *)
Module NotExample.

  Example x := 0.
  Example y := 1.

  (* Given a bvector of length 1, negate its only element *)
  Example not_function (vx : Bvector 1) := negb (hd vx).

  (* An oracle for the "not" function *)
  Example not_oracle := Exp (X (x, 0); CNOT (x, 0) (y, 0); X (x, 0)).

  (* The environment assumed by the "not" oracle *)
  Example not_oracle_env :=
    fun x' => if (x' =? x) || (x' =? y) then 1 else 0.

  Conjecture not_oracle_correct :
    is_oracle_bool x y not_oracle_env not_function not_oracle.

End NotExample.

(* Test the oracle (must be done outside of the module) *)
(*
QuickChick NotExample.not_oracle_correct.
*)
