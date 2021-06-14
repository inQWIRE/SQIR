Require Import Arith Vector Bvector MSets OrderedTypeEx Lia.
From QuickChick Require Import QuickChick.
Require Import VSQIR.
Import Vector (hd, tl).

Module Nat_as_OT := Update_OT Nat_as_OT.
Module VarSet := Make Nat_as_OT.
Import VarSet.

Open Scope vector_scope.
Open Scope string_scope.
Open Scope nat_scope.
Open Scope bool_scope.
Open Scope exp_scope.

Infix "(+)" := (BVxor _) (at level 50, left associativity).

Definition show_bit b :=
  match b with
  | false => "0"
  | true => "1"
  end.

Fixpoint show_bvector' {n} : Bvector n -> string :=
  match n with
  | 0 => fun _ => ""
  | S n' => fun v => show_bvector' (tl v) ++ show_bit (hd v)
  end.

Instance show_bvector n : Show (Bvector n) := {| show := show_bvector' |}.

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

Definition gen_bool :=
  elems_ false (Datatypes.cons false (Datatypes.cons true Datatypes.nil)).

Fixpoint gen_bvector' {n} : G (Bvector n) :=
  match n with
  | 0 => returnGen Bnil
  | S n' =>
      bind gen_bool (fun b => bind gen_bvector' (fun v => ret (b :: v)))
  end.

Instance gen_bvector n : Gen (Bvector n) := {| arbitrary := gen_bvector' |}.

Definition zero_angle : rz_val :=
  fun _ => false.

Definition basis_val b := nval b zero_angle.

Definition zero_val := basis_val false.

Definition state := posi -> val.

Definition zero_state : state := fun p => zero_val.

Notation "x |-> vx , st" :=
    (eupdate st x vx) (at level 100, vx at next level, right associativity).
Infix "|->" := (eupdate zero_state) (at level 100).

Reserved Notation "x |=> vx , st" 
    (at level 100, vx at next level, right associativity).
Fixpoint update_var {n} (st : state) x (vx : Bvector n) :=
  match n, vx with
  | 0, _ => st
  | S n', b :: vx' => (x |=> vx', (x, n') |-> basis_val b, st)
  | S _, _ => st
  end
where "x |=> vx , st" := (update_var st x vx).

Infix "|=>" := (update_var zero_state) (at level 100).

Definition var_set := VarSet.t.

Definition dec2bool P `{H : Dec P} : bool :=
  let '{| dec := d |} := H in
  if d then true else false.

Lemma dec2bool_correct :
  forall P `{Dec P}, P <-> dec2bool P = true.
Proof.
  intros P H. destruct H as [[|]] eqn:E; simpl; split; auto.
  discriminate.
Qed.

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

Definition f_env := var -> nat.

Definition for_all_env (P : posi -> Prop) (vars : var_set) (env : f_env) := 
  For_all (fun x => forall i, i < env x -> P (x, i)) vars.

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

Definition rz_val_equiv prec (z z' : rz_val) :=
  forall i, i < prec -> z i = z' i.

Instance dec_rz_val_equiv :
  forall prec z z', Dec (rz_val_equiv prec z z').
Proof.
  intros prec z z'. apply dec_fin.
  intros i. apply Eq__Dec.
Defined.

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
    
Definition st_equiv vars env prec (st st' : state) :=
  for_all_env (fun x => val_equiv prec (st x) (st' x)) vars env.

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

Fixpoint get_vars e :=
  match e with
  | Exp e' => get_exp_vars e'
  | QFT x => singleton x
  | RQFT x => singleton x
  | H x => singleton x
  | PCU p e' => add (fst p) (get_vars e')
  | e1;; e2 => union (get_vars e1) (get_vars e2)
  end.

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

Fixpoint get_prec (env : f_env) e :=
  match e with
  | Exp e' => get_exp_prec e'
  | QFT x => env x
  | RQFT x => env x
  | H _ => 0
  | PCU _ e' => get_prec env e'
  | e1;; e2 => max (get_prec env e1) (get_prec env e2)
  end.

Definition is_oracle x y env (f : Bvector (env x) -> Bvector (env y)) e :=
  forall vx vy,
  st_equiv (get_vars e) env (get_prec env e)
      (prog_sem env e (x |=> vx, y |=> vy)) (x |=> vx, y |=> vy (+) f vx).

Example x := 0.
Example y := 1.

Example not_function : Bvector 1 -> Bvector 1 := (Bneg 1).

Example not_oracle := Exp (X (x, 0); CNOT (x, 0) (y, 0); X (x, 0)).

Example not_oracle_env :=
  fun x' => if (x' =? x) || (x' =? y) then 1 else 0.

Conjecture not_oracle_correct :
  is_oracle x y not_oracle_env not_function not_oracle.

(* QuickChick not_oracle_correct. *)
