Require Import Arith NArith Vector Bvector Equality MSets OrderedTypeEx Lia BasicUtility VectorStates PQASM Utilities.
From QuickChick Require Import QuickChick.
Import Vector (hd, tl).
Import Decidability (dec).
Import PQASM (exp(..), CNOT).

Module Nat_as_OT := Update_OT Nat_as_OT.
(* Used for finite sets of variables *)
Module VarSet := Make Nat_as_OT.
Import VarSet.

Open Scope vector_scope.
Open Scope string_scope.
Open Scope positive_scope.
Open Scope N_scope.
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
Definition gen_bool : G bool := elems_ false (false :: true :: nil).

(* Uniformly randomly selected Bvector *)
Fixpoint gen_bvector' {n} : G (Bvector n) :=
  match n with
  | 0 => ret Bnil
  | S n' =>
      bind gen_bool (fun b => bind gen_bvector' (fun v => ret (b :: v)))
  end.

Instance gen_bvector n : Gen (Bvector n) := {| arbitrary := gen_bvector' |}.

(* The natural number represented in binary in the sequence of bits *)
Fixpoint bvector2n {n} : Bvector n -> N :=
  match n with
  | 0 => fun _ => N0
  | S n' =>
      fun v =>
      let tl_n := bvector2n (tl v) in
      if hd v
      then N.succ_double tl_n
      else N.double tl_n
  end.

(* Represents the natural number in binary, trucating if necessary *)
Fixpoint n2bvector n : N -> Bvector n :=
  match n with
  | 0 => fun _ => Bnil
  | S n' => fun i => N.odd i :: n2bvector n' (N.div2 i)
  end.

Lemma bvector2n2bvector :
  forall n v, n2bvector n (bvector2n v) = v.
Proof.
  intros n.
  induction n as [| n IH]; intros v; dependent destruction v; try reflexivity.
  cbn - [ N.mul N.div ].
  assert
    (forall h h' (t t' : Bvector n), h = h' -> t = t' -> h :: t = h' :: t').
  { intros. subst. reflexivity. }
  apply H; destruct h; auto using Ndouble_plus_one_bit0, Ndouble_bit0.
  - rewrite N.div2_succ_double. apply IH.
  - rewrite N.div2_double. apply IH.
Qed.

Definition bvector2nat {n} (v : Bvector n) := N.to_nat (bvector2n v).

(*
Definition num_bits n :=
  match n with
  | N0 => 1
  | Npos p => Pos.size_nat p
  end.

Lemma num_bits_le :
  forall n p, num_bits n <= p <-> N.to_nat n < 2 ^ p.
Proof.
Abort. (* TODO *)
*)

Lemma double_size :
  forall n, N.size_nat (N.double n) <= S (N.size_nat n).
Proof.
  intros [].
  - simpl. lia.
  - reflexivity.
Qed.

Lemma succ_double_size :
  forall n, N.size_nat (N.succ_double n) = S (N.size_nat n).
Proof. intros []; reflexivity. Qed.

Lemma size_bvector2n :
  forall n (v : Bvector n), N.size_nat (bvector2n v) <= n.
Proof.
  intros n. induction n as [| n IH]; intros v; simpl. try constructor.
  dependent destruction v. simpl. destruct h.
  - rewrite succ_double_size. auto using le_n_S.
  - eauto using le_trans, double_size, le_n_S.
Qed.

(*
Lemma size_div2_le :
  forall i n, N.size_nat i <= S n <-> N.size_nat (N.div2 i) <= n.
Proof.
  intros i n.
  split; intros H; generalize dependent i;
  induction n as [| n IH]; intros [|[]] H; simpl in *; lia.
Qed.
 *)

Lemma n2bvector2n :
  forall n i, N.size_nat i <= n -> bvector2n (n2bvector n i) = i.
Proof.
  intros n. induction n as [| n IH]; try (intros [|[]]; simpl; lia).
  intros [|[]] H; simpl; rewrite IH; simpl in *; try lia.
Qed.

(* Rotation of 0, scalar multiplication by 1 *)
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

Definition next_pos : posi -> posi := fun '(x, i) => (x, S i).

Fixpoint update_var' {n} (st : state) (x : posi) : Bvector n -> state :=
  match n with
  | 0 => fun _ => st
  | S n' =>
      fun vx => (x |-> basis_val (hd vx), update_var' st (next_pos x) (tl vx))
  end.

Definition update_var {n} st x : Bvector n -> state := update_var' st (x, 0).

Notation "x |=> vx , st" :=
    (update_var st x vx) (at level 100, vx at next level, right associativity).

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
Fixpoint get_vars e :=
  match e with
  | SKIP p => singleton (fst p)
  | X p => singleton (fst p)
  | CU p e' => add (fst p) (get_vars e')
  | RZ _ p => singleton (fst p)
  | RRZ _ p => singleton (fst p)
  | SR _ x => singleton x
  | SRR _ x => singleton x
  | HCNOT p1 p2 => add (fst p1) (singleton (fst p2))
  | Lshift x => singleton x
  | Rshift x => singleton x
  | Rev x => singleton x
  | QFT x => singleton x
  | RQFT x => singleton x
  | H x => singleton x
  | e1; e2 => union (get_vars e1) (get_vars e2)
  end.

(* Get the maximum precision in rotations of an exp *)
Fixpoint get_prec (env : f_env) e :=
  match e with
  | SKIP _ => 0
  | X _ => 0
  | CU _ e' => get_prec env e'
  | RZ n _ => n
  | RRZ n _ => n
  | SR n _ => n
  | SRR n _ => n
  | HCNOT _ _ => 0
  | Lshift _ => 0
  | Rshift _ => 0
  | Rev _ => 0
  | QFT x => env x
  | RQFT x => env x
  | H _ => 0
  | e1; e2 => max (get_prec env e1) (get_prec env e2)
  end.

Definition ospec m n := Bvector m -> Bvector n -> Prop.

Definition fun_adheres {m n} f (s : ospec m n) :=
  forall vx, s vx (f vx).

Definition ospec_fun {m n} f : ospec m n :=
  fun vx vy => f vx = vy.

Lemma ospec_fun_adheres :
  forall m n (f : Bvector m -> Bvector n), fun_adheres f (ospec_fun f).
Proof. congruence. Qed.

Definition ospec_bool {n} (s : Bvector n -> bool -> Prop) : ospec n 1 :=
  fun vx vy => s vx (hd vy).

Definition bool_fun_adheres {n} f (s : ospec n 1) :=
  forall vx, s vx (f vx :: Bnil).

Definition ospec_bool_fun {n} f : ospec n 1 :=
  ospec_bool (fun vx b => f vx = b).

Lemma ospec_bool_fun_adheres :
  forall n (f : Bvector n -> bool), bool_fun_adheres f (ospec_bool_fun f).
Proof.
  intros n f vx. unfold ospec_bool_fun, ospec_bool. reflexivity.
Qed.

Definition ospec_n m n (s : N -> N -> Prop) : ospec m n :=
  fun vx vy => s (bvector2n vx) (bvector2n vy).

Definition n_fun_adheres {m n} f (s : ospec m n) :=
  forall vx,
  let ny := f (bvector2n vx) in N.size_nat ny <= n /\ s vx (n2bvector n ny).

Definition ospec_n_fun m n f : ospec m n :=
  ospec_n m n (fun nx ny => f nx = ny).

Lemma ospec_n_fun_adheres :
  forall m n (f : N -> N),
  (forall nx, N.size_nat nx <= m -> N.size_nat (f nx) <= n) ->
  n_fun_adheres f (ospec_n_fun m n f).
Proof.
  intros m n f H vx. simpl. split.
  - auto using size_bvector2n.
  - unfold ospec_n_fun, ospec_n. rewrite n2bvector2n; auto using size_bvector2n.
Qed.

Definition ospec_n_bool n (s : N -> bool -> Prop) : ospec n 1 :=
  fun vx vy => s (bvector2n vx) (hd vy).

Definition ospec_n_bool_fun n f : ospec n 1 :=
  ospec_n_bool n (fun nx b => f nx = b).

Definition is_oracle_fun x y env (f : Bvector (env x) -> Bvector (env y)) e :=
  forall vx vy,
  st_equiv (get_vars e) env (get_prec env e)
      (exp_sem env e (x |=> vx, y |=> vy)) (x |=> vx, y |=> vy (+) f vx).

Definition is_oracle x y env (s : ospec (env x) (env y)) e :=
  exists f, fun_adheres f s /\ is_oracle_fun x y env f e.

Definition is_oracle_bool x y env (s : ospec (env x) 1) e :=
  exists H : env y = 1, is_oracle x y env (eq_rect_r (ospec (env x)) s H) e.

(*
Lemma is_oracle_fun_is_oracle :
  forall x y env f e,
  is_oracle_fun x y env f e <-> is_oracle x y env (ospec_fun f) e.
Proof.
  intros x y env f e. split.
  - intros H. exists f. auto using ospec_fun_adheres.
  - intros [f' [Ha Ho]].
  H. exists f. auto using ospec_fun_adheres.
Qed.

(* Is the pexp an oracle for a function from Bvectors to Bvectors? *)
Definition is_oracle x y env (f : Bvector (env x) -> Bvector (env y)) e :=
  forall vx vy,
  st_equiv (get_vars e) env (get_prec env e)
      (prog_sem env e (x |=> vx, y |=> vy)) (x |=> vx, y |=> vy (+) f vx).

(* Is the pexp an oracle for a function from Bvectors to bools? *)
Definition is_oracle_bool x y env (f : Bvector (env x) -> bool) e :=
  env y = 1 /\
  is_oracle x y env (fun v => Vector.const (f v) _) e.

(* Is the pexp an oracle for a function from N to N? *)
Definition is_oracle_n x y env (f : N -> N) e :=
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
 *)

(* Example: an oracle for the "not" function *)
Module NotExample.

  Example x := 0.
  Example y := 1.

  (* Given a bvector of length 1, negate its only element *)
  Example not_function (vx : Bvector 1) := negb (hd vx).

  Example not_ospec := ospec_bool_fun not_function.

  (* An oracle for the "not" function *)
  Example not_oracle := (X (x, 0); CNOT (x, 0) (y, 0); X (x, 0)).

  (* The environment assumed by the "not" oracle *)
  Example not_oracle_env :=
    fun x' => if (x' =? x) || (x' =? y) then 1 else 0.

  Conjecture not_oracle_correct :
    is_oracle x y not_oracle_env not_ospec not_oracle.

End NotExample.

(* Test the oracle (must be done outside of the module) *)
(*
QuickChick NotExample.not_oracle_correct.
*)

Definition dec2checker P `{Dec P} := checker (dec2bool P).

Infix "<*>" := kron (at level 40, only parsing).

Definition nat_bool_to_n_bool f n : bool := f (N.to_nat n).

Definition circuit_dim (env : f_env) e :=
  list_sum (map env (elements (get_vars e))).

Definition xy_first x y (env : f_env) (vs : vars) :=
  let '(xstart, _, _, _) := vs x in
  let '(ystart, _, _, _) := vs y in
  xstart = 0 /\ ystart = env x.

Lemma vkron_add :
  forall n m f,
  (forall i, i < n + m -> WF_Matrix (f i)) ->
  vkron (n + m) f = vkron n f <*> vkron m (fun i => f (i + n)).
Proof.
  intros n m f H.
  induction m as [| m IH]; simpl; Msimpl; auto with wf_db.
  assert (forall i, i < n -> WF_Matrix (f i)) as Hn by (intros; apply H; lia).
  assert (forall i, i < m -> WF_Matrix (f (i + n))) as Hm by (intros; apply H; lia).
  assert (WF_Matrix (f (m + n))) as Hf by (intros; apply H; lia).
  rewrite Nat.add_succ_r, <- kron_assoc; auto with wf_db. simpl.
  rewrite IH by (intros; apply H; lia).
  repeat apply f_equal. lia.
Qed.

Lemma update_var_eupdate_permute :
  forall n x y i bx (vy : Bvector n) st,
  x <> y -> ((x, i) |-> bx, y |=> vy, st) = (y |=> vy, (x, i) |-> bx, st).
Proof.
  intros n. unfold update_var. remember 0 as j. clear. generalize dependent j.
  induction n as [| n IH]; try reflexivity.
  intros j x y i bx vy st H. simpl.
  rewrite eupdate_twice_neq by congruence.
  rewrite IH by assumption. reflexivity.
Qed.

Lemma update_var_permute :
  forall m n x y (vx : Bvector m) (vy : Bvector n) st,
  x <> y -> (x |=> vx, y |=> vy, st) = (y |=> vy, x |=> vx, st).
Proof.
  intros m. unfold update_var. remember 0 as j.
  intros n x y. replace (y, j) with (y, 0) by (subst; reflexivity).
  generalize dependent y. generalize dependent x. generalize dependent n.
  clear. generalize dependent j.
  induction m as [| m IH]; try reflexivity.
  intros j n x y vx vy st H. dependent destruction vx. simpl.
  rewrite IH by assumption.
Abort.

Lemma trans_init_state :
  forall m n dim x y avs rmax (vx : Bvector m) (vy : Bvector n),
  x <> y ->
  m + n <= dim ->
  (forall i, i < m -> avs i = (x, i)) ->
  (forall i, i < n -> avs (i + m) = (y, i)) ->
  vkron dim (trans_state avs rmax (x |=> vx, y |=> vy)) =
  @pad_vector (m + n)
        dim
        (basis_vector (2 ^ m) (bvector2nat vx) <*>
           basis_vector (2 ^ n) (bvector2nat vy)).
Proof.
  intros m n dim x y avs rmax vx vy Nn He Hx Hy. unfold pad_vector.
  remember (dim - (m + n)) as ancillae.
  apply repad_lemma2 in Heqancillae; try assumption.
  clear He. subst. rewrite vkron_add; auto using WF_trans_state.
  rewrite Nat.pow_1_l. apply f_equal2.
  - rewrite vkron_add; auto using WF_trans_state.
    apply f_equal2.
    + unfold trans_state. admit.
Abort.
(*
    + rewrite update_var_permute by assumption. induction n as [| n IH].
      * dependent destruction vy. simpl.
        unfold bvector2nat. simpl. unfold basis_vector, I.
        apply functional_extensionality.
        intros []; apply functional_extensionality;
        intros []; bdestruct_all; reflexivity.
      * dependent destruction vy. unfold bvector2nat.
        cbn - [ Nat.mul ].
        rewrite vkron_eq with
          (f' := fun i => trans_state avs rmax (y |=> vy, x |=> vx) (i + m)).
        -- rewrite IH by (intros; apply Hy; lia).
           destruct h.
           ++ rewrite N2Nat.inj_succ_double.
              replace (S (2 * _)) with (2 * N.to_nat (bvector2n vy) + 1) by lia.
              rewrite <- (basis_vector_append_1 (2 ^ n)).
              ** unfold bvector2nat. apply f_equal.
                 unfold trans_state. rewrite Hy by constructor.
                 rewrite eupdate_index_eq. simpl. Search turn_angle.
*)

Lemma todo :
  forall x y env f e vs dim avs,
  let '(p, _, _) := trans_exp vs dim e avs in
  S (env x) <= dim ->
  xy_first x y env vs ->
  is_oracle_bool x y env (ospec_n_bool_fun (env x) (nat_bool_to_n_bool f)) e ->
  padded_boolean_oracle (env x) p f.
Proof.
  intros x y env f e vs dim avs.
  destruct (trans_exp vs dim e avs) as [[p vs'] avs'] eqn:E.
  assert (p = fst (fst (trans_exp vs dim e avs))) as Hp
                                                   by (rewrite E; reflexivity).
  intros Hd Hf [Hy H]. intros nx vy Hx. unfold pad_vector.
  remember (dim - S (env x)) as ancillae.
  apply repad_lemma2 in Heqancillae; try assumption.
  rewrite Hp.
Abort.
