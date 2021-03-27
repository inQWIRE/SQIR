Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto.
Require Import Dirac.
Require Import QPE.
(**********************)
(** Unitary Programs **)
(**********************)
Definition var := nat.

Definition posi : Type := (var * nat).

Definition posi_eq (r1 r2 : posi) : bool := 
                match r1 with (x1,y1)
                            => match r2
                               with (x2,y2) => (x1 =? x2) && (y1 =? y2)
                               end
                end.

Declare Scope scom_scope.
Delimit Scope scom_scope with scom.
Local Open Scope scom_scope.
Local Open Scope nat_scope.

Notation "i '==?' j" := (posi_eq i j) (at level 50).


Lemma posi_eqb_eq : forall a b, a ==? b = true -> a = b.
Proof.
 intros. unfold posi_eq in H.
 destruct a. destruct b.
 apply andb_true_iff in H.
 destruct H. apply Nat.eqb_eq in H.
 apply Nat.eqb_eq in H0. subst. easy.
Qed.

Lemma posi_eqb_neq : forall a b, a ==? b = false -> a <> b.
Proof.
 intros. unfold posi_eq in H.
 destruct a. destruct b.
 apply andb_false_iff in H.
 destruct H. apply Nat.eqb_neq in H.
 intros R. injection R as eq1.
 rewrite eq1 in H. easy.
 apply Nat.eqb_neq in H.
 intros R. injection R as eq1.
 rewrite H0 in H. easy.
Qed.

Lemma posi_eq_reflect : forall r1 r2, reflect (r1 = r2) (posi_eq r1 r2). 
Proof.
  intros.
  destruct (r1 ==? r2) eqn:eq1.
  apply  ReflectT.
  apply posi_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply posi_eqb_neq in eq1.
  assumption. 
Qed.

Hint Resolve posi_eq_reflect : bdestruct.


Definition rz_val : Type := (nat * (nat -> bool)).

Inductive val := nval (b:bool) (r:rz_val) | hval (b1:bool) (b2:bool) (r:rz_val) | qval (r:rz_val).

(* Update the value at one index of a boolean function. *)
Definition eupdate {S} (f : posi -> S) (i : posi) (x : S) :=
  fun j => if j ==? i then x else f j.

Lemma eupdate_index_eq {S} : forall (f : posi -> S) i b, (eupdate f i b) i = b.
Proof.
  intros. 
  unfold eupdate.
  bdestruct (i ==? i). easy.
  contradiction.
Qed.

Lemma eupdate_index_neq {S}: forall (f : posi -> S) i j b, i <> j -> (eupdate f i b) j = f j.
Proof.
  intros. 
  unfold eupdate.
  bdestruct (j ==? i).
  subst. contradiction.
  reflexivity.
Qed.

Lemma eupdate_same {S}: forall (f : posi -> S) i b,
  b = f i -> eupdate f i b = f.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold eupdate.
  bdestruct (x ==? i); subst; reflexivity.
Qed.

Lemma eupdate_same_1 {S}: forall (f f': posi -> S) i b b',
 f = f' -> b = b' -> eupdate f i b = eupdate f' i b'.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold eupdate.
  bdestruct (x ==? i); subst; reflexivity.
Qed.


Lemma eupdate_twice_eq {S}: forall (f : posi -> S) i b b',
  eupdate (eupdate f i b) i b' = eupdate f i b'.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold eupdate.
  bdestruct (x ==? i); subst; reflexivity.
Qed.  

Lemma eupdate_twice_neq {S}: forall (f : posi -> S) i j b b',
  i <> j -> eupdate (eupdate f i b) j b' = eupdate (eupdate f j b') i b.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold eupdate.
  bdestruct (x ==? i); bdestruct (x ==? j); subst; easy.
Qed.


Inductive scom := SKIP | X (p:posi) | CU (p:posi) (e:scom)
        | RZ (q:nat) (p:posi) (* 2 * PI * i / 2^q *)
        | RRZ (q:nat) (p:posi) 
        | Lshift (x:var)
        | Rshift (x:var)
        | Seq (s1:scom) (s2:scom).

Notation "p1 ; p2" := (Seq p1 p2) (at level 50) : scom_scope.
Notation "f '[' i '|->' x ']'" := (eupdate f i x) (at level 10).

Inductive face := Exp (s:scom) | QFT (x:var) | RQFT (x:var)
               | Reset (x:var) (* reset has no semantic meaning in the face level.
                                  It is to set shifted bits to the normal position. *)
               | Rev (x:var) (* move the positions in x to be upside-down. *)
               | H (x:var) | FSeq (p1:face) (p2:face).

Coercion Exp : scom >-> face.

Notation "p1 ;; p2" := (FSeq p1 p2) (at level 49) : scom_scope.

Inductive type := Had | Phi | Nor.

Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Module Env := FMapList.Make Nat_as_OT.

Definition env := Env.t type.

Inductive exp_WF : (var -> nat) -> scom -> Prop :=
      | skip_wf : forall env, exp_WF env SKIP
      | x_wf : forall env a b n, env a = n -> b < n -> exp_WF env (X (a,b))
      | cu_wf : forall env a b e n, env a = n -> b < n -> exp_WF env e -> exp_WF env (CU (a,b) e)
      | rz_wf : forall env a b q n, env a = n -> b < n -> exp_WF env (RZ q (a,b))
      | rrz_wf : forall env a b q n, env a = n -> b < n -> exp_WF env (RRZ q (a,b))
      | seq_wf : forall env e1 e2, exp_WF env e1 -> exp_WF env e2 -> exp_WF env (Seq e1 e2).

Inductive well_typed_exp : env -> scom -> Prop :=
    | skip_refl : forall env, well_typed_exp env (SKIP)
    | x_refl : forall env a b, Env.MapsTo a Nor env -> well_typed_exp env (X (a,b))
    | x_had : forall env a b, Env.MapsTo a Had env -> well_typed_exp env (X (a,b))
    | cu_refl : forall env a b e, Env.MapsTo a Nor env -> well_typed_exp env e -> well_typed_exp env (CU (a,b) e)
    | rz_refl :forall env q a b, Env.MapsTo a Nor env -> well_typed_exp env (RZ q (a,b))
    | rz_had : forall env a b, Env.MapsTo a Had env -> well_typed_exp env (RZ 1 (a,b))
    | rz_qft : forall env q a b, Env.MapsTo a Phi env -> well_typed_exp env (RZ q (a,b))
    | rrz_refl :forall env q a b, Env.MapsTo a Nor env -> well_typed_exp env (RRZ q (a,b))
    | rrz_had : forall env a b, Env.MapsTo a Had env -> well_typed_exp env (RRZ 1 (a,b))
    | rrz_qft : forall env q a b, Env.MapsTo a Phi env -> well_typed_exp env (RRZ q (a,b))
    | lshift_refl : forall env x, Env.MapsTo x Nor env -> well_typed_exp env (Lshift x)
    | rshift_refl : forall env x, Env.MapsTo x Nor env -> well_typed_exp env (Rshift x)
    | e_seq : forall env p1 p2, well_typed_exp env p1 -> well_typed_exp env p2 -> well_typed_exp env (p1 ; p2).

Inductive well_typed (f: var -> nat) : env -> face -> env -> Prop :=
   | t_exp : forall env e, well_typed_exp env e -> exp_WF f e -> well_typed f env (Exp e) env
   | t_qft : forall env x, Env.MapsTo x Nor env -> well_typed f env (QFT x) (Env.add x Phi env)
   | t_rqft : forall env x, Env.MapsTo x Phi env -> well_typed f env (RQFT x) (Env.add x Nor env)
   | t_had : forall env x, Env.MapsTo x Had env -> well_typed f env (H x) (Env.add x Nor env)
   | t_rhad : forall env x, Env.MapsTo x Nor env -> well_typed f env (H x) (Env.add x Had env)
   | t_rev : forall env x, Env.In x env -> well_typed f env (Rev x) env
   | t_seq : forall env p1 p2 env' env'', well_typed f env p1 env' -> well_typed f env' p2 env''
                         -> well_typed f env (p1 ;; p2) env''.

Fixpoint addto (f : nat -> bool) (n:nat) :=
   match n with 0 => update f 0 (¬ (f 0))
             | S m => if f n then update (addto f m) n false
                             else update f n true
   end.

Definition rotate (r :rz_val) (q:nat) :=
    match r with (n,f) => if q <? n then (n,addto f q) else (q+1,addto f q) end.

Definition times_rotate (v : val) (q:nat) := 
     match v with nval b r =>  nval b (rotate r q)
                  | hval b1 b2 r => hval b1 (¬ b2) r
                  | qval r =>  qval (rotate r q)
     end.

Fixpoint addto_n (f:nat -> bool) (n:nat) :=
    match n with 0 => f
               | S m => addto_n (addto f m) m
    end.

Definition r_rotate (r :rz_val) (q:nat) :=
    match r with (n,f) => if q <? n then (n,addto_n f q) else (q+1,addto_n f q) end.

Definition times_r_rotate (v : val) (q:nat) := 
     match v with nval b r =>  nval b (r_rotate r q)
                  | hval b1 b2 r => hval b1 (¬ b2) r
                  | qval r =>  qval (r_rotate r q)
     end.


Definition exchange (v: val) :=
     match v with nval b r => nval (¬ b) r
                  | hval b1 b2 r => hval b2 b1 r
                  | a => a
     end.

Definition get_cu (v : val) :=
    match v with nval b r => Some b 
                 | hval b1 b2 r => Some b1
                 | _ => None
    end.

Fixpoint lshift' (n:nat) (f:posi -> val) (x:var) := 
   match n with 0 => f
             | S m => lshift' m (f[(x,n) |-> f (x,m)]) x
   end.
Definition lshift (f:posi -> val) (x:var) (n:nat) := let v := f (x,n) in (lshift' n f x)[(x,0) |-> v].

Fixpoint rshift' (n:nat) (f:posi -> val) (x:var) := 
   match n with 0 => f
             | S m => ((rshift' m f x)[(x,m) |-> f (x,n)])
   end.
Definition rshift (f:posi -> val) (x:var) (n:nat) := 
              let v := f (x,0) in (rshift' n f x)[(x,n) |-> v].

Inductive exp_sem (env : var -> nat) : (posi -> val) -> scom -> (posi -> val) -> Prop :=
    | skip_sem : forall st, exp_sem env st (SKIP) st
    | x_sem : forall st p, exp_sem env st (X p) (st[p |-> (exchange (st p))])
    | cu_false_sem : forall st p e, get_cu (st p) = Some false -> exp_sem env st (CU p e) st
    | cu_true_sem : forall st p e st', get_cu (st p) = Some true -> exp_sem env st e st' -> exp_sem env st (CU p e) st'
    | rz_sem : forall st q p, exp_sem env st (RZ q p) (st[p |-> times_rotate (st p) q])
    | rrz_sem : forall st q p, exp_sem env st (RRZ q p) (st[p |-> times_r_rotate (st p) q])
    | lshift_sem : forall st x, get_cu (st (x,(env x)-1)) = Some false
                                                      ->  exp_sem env st (Lshift x) (lshift st x (env x))
    | rshift_sem : forall st x, get_cu (st (x,0)) = Some false
                                                        ->  exp_sem env st (Rshift x) (rshift st x (env x))
    | seq_sem : forall st st' st'' e1 e2, exp_sem env st e1 st' -> exp_sem env st' e2 st'' -> exp_sem env st (e1 ; e2) st''.

Definition h_case (v : val) :=
    match v with nval b r => if b then hval true false r else hval true true r
               | hval true true r => nval false r
               | hval true false r => nval true r
               | hval false true r => nval true (rotate r 1)
               | hval false false r => nval false (rotate r 1)
               | a => a
    end.

Fixpoint h_sem (f:posi -> val) (x:var) (n : nat) := 
    match n with 0 => f
              | S m => h_sem (f[(x,m) |-> h_case (f (x,m))]) x m
    end.

Definition seq_val (v:val) :=
  match v with nval b r => b
             | _ => false
  end.

Definition allfalse := fun (_:nat) => false.

Fixpoint get_seq (f:posi -> val) (x:var) (base:nat) (n:nat) : (nat -> bool) :=
     match n with 0 => allfalse
              | S m => fun (i:nat) => if i =? (base + m) then seq_val (f (x,base+m)) else ((get_seq f x base m) i)
     end.

Definition up_qft (v:val) (m: nat) (f:nat -> bool) :=
   match v with nval b (n,g) => qval (m,f)
              | a => a
   end.

Fixpoint qft_val' (f:posi -> val) (x:var) (n:nat) (base:nat) :=
    match n with 0 => f
              | S m => qft_val' (f[(x,base) |-> up_qft (f (x,base)) n (get_seq f x base n)]) x m (base +1)
    end.

Definition qft_val (f:posi -> val) (x:var) (n:nat) := qft_val' f x n 0.

Definition no_rot (f:posi -> val) (x:var) :=
    forall n, (exists b i r, (f (x,n)) = nval b (i,r) /\ r = allfalse).

Definition all_qft (f:posi -> val) (x:var) := forall n, (exists r, f (x,n) = qval r).

Definition reverse (f:posi -> val) (x:var) (n:nat) := fun a =>
             if ((fst a) =? x) && ((snd a) <? n) then f (x, (n-1) - (snd a)) else f a.

(* Semantics of the whole program. *)
Inductive prog_sem (f:var -> nat) : (posi -> val) -> face -> (posi -> val) -> Prop := 
        | sem_exp : forall st e st', exp_sem f st e st' -> prog_sem f st (Exp e) st'
        | sem_had : forall st x, prog_sem f st (H x) (h_sem st x (f x))
        | sem_qft : forall st x, no_rot st x -> prog_sem f st (QFT x) (qft_val st x (f x))
        | sem_rqft : forall st x st', all_qft st x -> st = qft_val st' x (f x) -> prog_sem f st (RQFT x) st'
        | sem_rev : forall st x, prog_sem f st (Rev x) (reverse st x (f x))
        | sem_seq : forall st e1 e2 st' st'', prog_sem f st e1 st' -> prog_sem f st' e2 st''
                              -> prog_sem f st (e1 ;; e2) st''.

Lemma rev_twice_same : forall f st x, reverse (reverse st x (f x)) x (f x) = st.
Proof.
  intros. unfold reverse.
  apply functional_extensionality.
  intros.
  destruct x0. simpl.
  bdestruct (n =? x).
  subst.
  bdestruct ((n0 <? f x)).
  simpl.
  bdestruct ((x =? x)).
  bdestruct ((f x - 1 - n0 <? f x)).
  simpl.
  assert (f x - 1 - (f x - 1 - n0)= n0) by lia.
  rewrite H3. easy.
  simpl. lia.
  lia. simpl. easy.
  simpl. easy.
Qed.

(* Adds an equality in the context *)
Ltac ctx e1 e2 :=
  let H := fresh "HCtx" in
  assert (e1 = e2) as H by reflexivity.

(* Standard inversion/subst/clear abbrev. *)
Tactic Notation "inv" hyp(H) := inversion H; subst; clear H.
Tactic Notation "inv" hyp(H) "as" simple_intropattern(p) :=
  inversion H as p; subst; clear H.


(* Definition of the adder and the modmult in the language. *)
Definition CNOT (x y : posi) := CU x (X y).
Definition SWAP (x y : posi) := if (x ==? y) then SKIP else (CNOT x y; CNOT y x; CNOT x y).
Definition CCX (x y z : posi) := CU x (CNOT y z).

Definition nor_mode (f : posi -> val)  (x:posi) : Prop :=
       match f x with nval a b => True | _ => False end.

Lemma nor_mode_nval : forall f x, nor_mode f x -> (exists r, f x = nval true r \/ f x = nval false r).
Proof.
  intros. unfold nor_mode in *. destruct (f x); inv H0.
  exists r.
  destruct b. left. easy. right. easy.
Qed.

Lemma neq_sym {A} : forall (x y: A), x <> y -> y <> x.
Proof.
 intros. intros R.
 subst. contradiction.
Qed.

Lemma nor_mode_up : forall f x y v, x <> y -> nor_mode f x -> nor_mode (f[y |-> v]) x.
Proof.
  intros. unfold nor_mode in *.
  assert ((f [y |-> v]) x = (f x)).
  rewrite eupdate_index_neq. reflexivity. apply neq_sym. assumption.
  rewrite H2.
  destruct (f x); inv H1. easy.
Qed.

Definition get_cua (v:val) := 
    match v with nval x r => x | a => false end.

Definition put_cu (v:val) (b:bool) :=
    match v with nval x r => nval b r | a => a end.

Fixpoint init_v (n:nat) (x:var) (M: nat -> bool) :=
      match n with 0 => SKIP
                | S m => if M m then X (x,m) ; init_v m x M else init_v m x M
      end.

Lemma nor_mode_ups : forall f f' x v, f x = f' x -> nor_mode f x ->
                                    nor_mode (f[x |-> put_cu (f' x) v]) x.
Proof.
  intros. unfold nor_mode in *.
  rewrite eupdate_index_eq.
  unfold put_cu. rewrite <- H0.
  destruct (f x); inv H1. easy.
Qed.

Lemma nor_mode_get : forall f x, nor_mode f x -> (exists b, get_cua (f x) = b).
Proof.
  intros. unfold nor_mode in *. destruct (f x); inv H0.
  exists b. unfold get_cua. reflexivity.
Qed.

Lemma x_nor : forall env f x v, nor_mode f x -> put_cu (f x) (¬ (get_cua (f x))) = v ->
                            exp_sem env f (X x) (f[x |-> v]).
Proof.
 intros.
 apply nor_mode_nval in H0.
 destruct H0. destruct H0.
 unfold get_cua in H1. rewrite H0 in H1. 
 unfold put_cu in H1. subst. 
 assert ((exchange (f x)) = nval (¬ true) x0).
 unfold exchange. rewrite H0. reflexivity.
 rewrite <- H1. apply x_sem.
 unfold get_cua in H1. rewrite H0 in H1.
 unfold put_cu in H1. subst.
 assert ((exchange (f x)) = nval (¬ false) x0).
 unfold exchange. rewrite H0.
 reflexivity. 
 rewrite <- H1. apply x_sem.
Qed.

Lemma cu_false_nor : forall env f f' x e, nor_mode f x -> get_cua (f x) = false
                                         ->  f' = f -> exp_sem env f (CU x e) f'.
Proof.
 intros. subst. constructor.
 unfold get_cu.
 apply nor_mode_nval in H0.
 destruct H0. destruct H0.
 rewrite H0 in H1. unfold get_cua in H1. inv H1.
 rewrite H0. reflexivity.
Qed.

Lemma put_get_cu : forall f x, nor_mode f x -> put_cu (f x) (get_cua (f x)) = f x.
Proof.
 intros. unfold put_cu, get_cua.
 unfold nor_mode in H0. destruct (f x); inv H0.
 reflexivity.
Qed.

Lemma get_put_cu : forall f x v, nor_mode f x -> get_cua (put_cu (f x) v) = v.
Proof.
 intros. unfold put_cu, get_cua.
 unfold nor_mode in H0. destruct (f x); inv H0.
 reflexivity.
Qed.

(*
Definition vxor (a b:val) := (get_cua a) ⊕ (get_cua b).

Definition vand (a b:val) := (get_cua a) && (get_cua b).

Notation "p1 '[⊕]' p2" := (vxor p1 p2) (at level 50) : scom_scope.

Notation "p1 '[&&]' p2" := (vand p1 p2) (at level 50) : scom_scope.

Lemma vxor_l_t : forall r b, vxor (nval true r) b = (¬ (get_cua b)).
Proof.
  intros. unfold vxor. unfold get_cua. destruct b.
  btauto. btauto. btauto.
Qed.

Lemma vxor_l_f : forall r b, vxor (nval false r) b = ((get_cua b)).
Proof.
  intros. unfold vxor. unfold get_cua. destruct b.
  btauto. btauto. btauto.
Qed.
*)

Lemma xorb_andb_distr_l : forall x y z, (x ⊕ y) && z = (x && z) ⊕ (y && z).
Proof.
 intros. btauto.
Qed.

Lemma xorb_andb_distr_r : forall x y z, z && (x ⊕ y) = (z && x) ⊕ (z && y).
Proof.
 intros. btauto.
Qed.


Ltac bt_simpl := repeat (try rewrite xorb_false_r; try rewrite xorb_false_l;
            try rewrite xorb_true_r; try rewrite xorb_true_r; 
            try rewrite andb_false_r; try rewrite andb_false_l;
            try rewrite andb_true_r; try rewrite andb_true_l;
            try rewrite xorb_andb_distr_l; try rewrite xorb_andb_distr_r;
            try rewrite andb_diag).



Lemma get_cua_t : forall b r, get_cua (nval b r) = b.
Proof.
 intros. unfold get_cua. reflexivity.
Qed.

Lemma cnot_sem : forall env f x y, nor_mode f x -> nor_mode f y -> 
              exp_sem env f (CNOT x y) (f[y |-> put_cu (f y) (get_cua (f x) ⊕ get_cua (f y))]).
Proof.
 intros.
 unfold CNOT.
 assert (eq1 := H0).
 apply nor_mode_nval in H0.
 destruct H0. destruct H0.
 constructor.
 unfold get_cu. rewrite H0. reflexivity.
 apply x_nor. assumption.
 rewrite H0. rewrite get_cua_t.
 easy.
 rewrite H0. rewrite get_cua_t.
 apply cu_false_nor.
 assumption.
 rewrite H0. rewrite get_cua_t. reflexivity.
 rewrite eupdate_same. reflexivity.
 rewrite  xorb_false_l.
 rewrite put_get_cu. reflexivity. assumption.
Qed.

Lemma cnot_nor : forall env f x y v, nor_mode f x -> nor_mode f y -> 
          put_cu (f y) (get_cua (f x) ⊕ get_cua (f y)) = v
           -> exp_sem env f (CNOT x y) (f[y |-> v]).
Proof.
  intros. subst. apply cnot_sem; assumption.
Qed.

Lemma cnot_nor_1 : forall env f f' x y v, nor_mode f x -> nor_mode f y -> 
          put_cu (f y) (get_cua (f x) ⊕ get_cua (f y)) = v
           -> f[y|-> v] = f'
           -> exp_sem env f (CNOT x y) f'.
Proof.
  intros. subst. apply cnot_sem; assumption.
Qed.

Lemma ccx_sem : forall env f x y z, nor_mode f x -> nor_mode f y -> nor_mode f z
                     -> x <> y -> y <> z -> x <> z -> 
                    exp_sem env f (CCX x y z) (f[z |-> put_cu (f z) (get_cua (f z) ⊕ (get_cua (f y) && get_cua (f x)))]).
Proof.
 intros. 
 assert (eq1 := H0).
 unfold CCX. apply nor_mode_nval in H0.
 destruct H0. destruct H0.
 constructor. rewrite H0. unfold get_cu. reflexivity.
 apply cnot_nor. 1-2:assumption.
 rewrite H0. rewrite get_cua_t.
 bt_simpl. rewrite xorb_comm. reflexivity.
 apply cu_false_nor.
 assumption. rewrite H0. rewrite get_cua_t. easy.
 rewrite H0. rewrite get_cua_t.
 bt_simpl. rewrite put_get_cu. apply eupdate_same. 
 easy. assumption.
Qed.

Lemma ccx_nor : forall env f f' x y z v, nor_mode f x -> nor_mode f y -> nor_mode f z
                     -> x <> y -> y <> z -> x <> z -> 
                       put_cu (f z) (get_cua (f z) ⊕ (get_cua (f y) && get_cua (f x))) = v ->
                       f = f' ->
                    exp_sem env f (CCX x y z) (f'[z |-> v]).
Proof.
 intros. subst. apply ccx_sem. 1 - 6: assumption. 
Qed.

Definition majb a b c := (a && b) ⊕ (b && c) ⊕ (a && c).

Definition MAJ a b c := CNOT c b ; CNOT c a ; CCX a b c.
Definition UMA a b c := CCX a b c ; CNOT c a ; CNOT a b.

Ltac nor_sym := try (apply neq_sym; assumption) ; try assumption.

Lemma MAJ_correct :
  forall a b c env f,
    nor_mode f a -> nor_mode f b -> nor_mode f c ->
    a <> b -> b <> c -> a <> c ->
    exp_sem env f (MAJ c b a) (((f[a |-> put_cu (f a) (majb (get_cua (f a)) (get_cua (f b)) (get_cua (f c)))])
                              [b |-> put_cu (f b) (get_cua (f b) ⊕ get_cua (f a))])
                              [c |-> put_cu (f c) (get_cua (f c) ⊕ (get_cua (f a)))]).
(*Admitted. 
(* The following proof works, but too slow. Admitted when debugging. *)*)
Proof.
  intros ? ? ? ? ? HNa HNb HNc Hab' Hbc' Hac'.
  unfold MAJ.
  eapply seq_sem.
  eapply seq_sem.
  apply cnot_sem. assumption. assumption.
  apply cnot_sem.
  apply nor_mode_up. assumption.
  assumption.
  apply nor_mode_up. apply neq_sym. assumption.
  assumption.
  rewrite eupdate_index_neq.
  rewrite eupdate_index_neq.
  assert ((((f [a
     |-> put_cu (f a)
           (majb (get_cua (f a)) (get_cua (f b)) (get_cua (f c)))]) [b
    |-> put_cu (f b) (get_cua (f b) ⊕ get_cua (f a))]) [c
   |-> put_cu (f c) (get_cua (f c) ⊕ get_cua (f a))])
      = (((f [b
    |-> put_cu (f b) (get_cua (f b) ⊕ get_cua (f a))]) [c
   |-> put_cu (f c) (get_cua (f c) ⊕ get_cua (f a))])
      [a
     |-> put_cu (f a)
           (majb (get_cua (f a)) (get_cua (f b)) (get_cua (f c)))])).
  rewrite (eupdate_twice_neq f).
  rewrite (eupdate_twice_neq (f [b |-> put_cu (f b) (get_cua (f b) ⊕ get_cua (f a))])).
  easy. 1-2:assumption.
  rewrite H0. clear H0.
  apply ccx_nor.
  apply nor_mode_ups. rewrite eupdate_index_neq.
  reflexivity. assumption.
  apply nor_mode_up. apply neq_sym. assumption.
  assumption.
  apply nor_mode_up. assumption.
  apply nor_mode_ups ; easy.
  apply nor_mode_up. assumption. apply nor_mode_up; assumption.
  1-3:nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu by assumption.
  rewrite get_put_cu by assumption.
  unfold majb.
  bt_simpl.
  assert ((get_cua (f a)
   ⊕ ((get_cua (f a) ⊕ (get_cua (f a) && get_cua (f c)))
      ⊕ ((get_cua (f b) && get_cua (f a))
         ⊕ (get_cua (f b) && get_cua (f c))))) = 
    (((get_cua (f a) && get_cua (f b)) ⊕ (get_cua (f b) && get_cua (f c)))
   ⊕ (get_cua (f a) && get_cua (f c)))) by btauto.
  rewrite H0. easy.
  rewrite xorb_comm.
  rewrite (xorb_comm (get_cua (f a))). easy.
  1 - 2 : nor_sym.
Qed.

Lemma MAJ_nor : 
  forall a b c env f f',
    nor_mode f a -> nor_mode f b -> nor_mode f c ->
    a <> b -> b <> c -> a <> c -> f' = (((f[a |-> put_cu (f a) (majb (get_cua (f a)) (get_cua (f b)) (get_cua (f c)))])
                              [b |-> put_cu (f b) (get_cua (f b) ⊕ get_cua (f a))])
                              [c |-> put_cu (f c) (get_cua (f c) ⊕ (get_cua (f a)))]) ->
    exp_sem env f (MAJ c b a) f'.
(*Admitted. 
(* The following proof works, but too slow. Admitted when debugging. *)*)
Proof.
  intros. subst. apply MAJ_correct.
  1-6:assumption.
Qed.


Lemma UMA_correct_partial :
  forall a b c env f' fa fb fc,
    nor_mode f' a -> nor_mode f' b -> nor_mode f' c ->
    a <> b -> b <> c -> a <> c ->
    get_cua (f' a) = majb fa fb fc ->
    get_cua (f' b) = (fb ⊕ fa) -> get_cua (f' c) = (fc ⊕ fa) ->
    exp_sem env f' (UMA c b a) (((f'[a |-> put_cu (f' a) fa])
                  [b |-> put_cu (f' b) (fa ⊕ fb ⊕ fc)])[c |-> put_cu (f' c) fc]).
(* Admitted.
(* The following proof works, but too slow. Admitted when debugging. *) *)
Proof.
  unfold majb. intros.
  unfold UMA.
  eapply seq_sem.
  eapply seq_sem.
  apply ccx_sem.
  1 - 3: assumption. 1 - 3: nor_sym.
  apply cnot_nor.
  apply nor_mode_ups. easy. assumption.
  apply nor_mode_up. nor_sym. assumption.
  reflexivity.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  eapply cnot_nor_1.
  apply nor_mode_ups.
  rewrite eupdate_index_neq. easy. nor_sym.
  apply nor_mode_up. nor_sym. assumption.
  apply nor_mode_up. nor_sym.
  apply nor_mode_up. nor_sym. assumption.
  reflexivity.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite get_put_cu by assumption.
  assert ((get_cua (f' a) ⊕ (get_cua (f' b) && get_cua (f' c))) = fa).
  rewrite H6. rewrite H7. rewrite H8.
  btauto. rewrite H9.
  assert (((fa ⊕ get_cua (f' c)) ⊕ get_cua (f' b)) = ((fa ⊕ fb) ⊕ fc)).
  rewrite H7. rewrite H8. btauto. rewrite H10.
  rewrite (eupdate_twice_neq (f' [a |-> put_cu (f' a) fa])).
  rewrite H8.
  assert ((fa ⊕ (fc ⊕ fa)) = fc) by btauto.
  rewrite H11. reflexivity. nor_sym. assumption.
Qed.

Lemma UMA_nor :
  forall a b c env f' f'' fa fb fc,
    nor_mode f' a -> nor_mode f' b -> nor_mode f' c ->
    a <> b -> b <> c -> a <> c ->
    get_cua (f' a) = majb fa fb fc ->
    get_cua (f' b) = (fb ⊕ fa) -> get_cua (f' c) = (fc ⊕ fa) ->
    f'' = (((f'[a |-> put_cu (f' a) fa])
                  [b |-> put_cu (f' b) (fa ⊕ fb ⊕ fc)])[c |-> put_cu (f' c) fc]) ->
    exp_sem env f' (UMA c b a) f''.
Proof.
 intros. subst. apply UMA_correct_partial.
 1 - 9 : assumption.
Qed.


(* The following defines n-bits MAJ and UMA circuit. 
   Eventually, MAJ;UMA circuit takes [x][y] and produce [x][(x+y) % 2 ^ n] *)
Fixpoint MAJseq' n x y c : scom :=
  match n with
  | 0 => MAJ c (y,0) (x,0)
  | S m => MAJseq' m x y c; MAJ (x, m) (y, n) (x, n)
  end.
Definition MAJseq n x y c := MAJseq' (n - 1) x y c.

Fixpoint UMAseq' n x y c : scom :=
  match n with
  | 0 => UMA c (y,0) (x,0)
  | S m => UMA (x, m) (y,n) (x, n); UMAseq' m x y c
  end.
Definition UMAseq n x y c := UMAseq' (n - 1) x y c.

Definition adder01 n x y c: scom := MAJseq n x y c; UMAseq n x y c.

(* Here we defined the specification of carry value for each bit. *)
(* fb_push is to take a qubit and then push it to the zero position 
        in the bool function representation of a number. *)
Definition fb_push b f : nat -> bool :=
  fun x => match x with
        | O => b
        | S n => f n
        end.

(* fb_push_n is the n repeatation of fb_push.
Definition fb_push_n n f g : nat -> bool :=
  fun i => if (i <? n) then f i else g (i - n).
*)

(* A function to compile positive to a bool function. *)
Fixpoint pos2fb p : nat -> bool :=
  match p with
  | xH => fb_push true allfalse
  | xI p' => fb_push true (pos2fb p')
  | xO p' => fb_push false (pos2fb p')
  end.

(* A function to compile N to a bool function. *)
Definition N2fb n : nat -> bool :=
  match n with
  | 0%N => allfalse
  | Npos p => pos2fb p
  end.

Definition add_c b x y :=
  match b with
  | false => Pos.add x y
  | true => Pos.add_carry x y
  end.

Fixpoint carry b n f g :=
  match n with
  | 0 => b
  | S n' => let c := carry b n' f g in
           let a := f n' in
           let b := g n' in
           (a && b) ⊕ (b && c) ⊕ (a && c)
  end.

Lemma carry_1 : forall b f g, carry b 1 f g = majb (f 0) (g 0) b.
Proof.
 intros. simpl. unfold majb. easy.
Qed.

Lemma carry_n : forall n b f g, carry b (S n) f g = majb (f n) (g n) (carry b n f g).
Proof.
 intros. simpl. unfold majb. easy.
Qed.

Lemma carry_sym :
  forall b n f g,
    carry b n f g = carry b n g f.
Proof.
  intros. induction n. reflexivity.
  simpl. rewrite IHn. btauto.
Qed.

Lemma carry_false_0_l: forall n f, 
    carry false n allfalse f = false.
Proof.
  unfold allfalse.
  induction n.
  simpl.
  reflexivity.
  intros. simpl.
  rewrite IHn. rewrite andb_false_r.
  reflexivity.
Qed.

Lemma carry_false_0_r: forall n f, 
    carry false n f allfalse = false.
Proof.
  unfold allfalse.
  induction n.
  simpl.
  reflexivity.
  intros. simpl.
  rewrite IHn. rewrite andb_false_r.
  reflexivity.
Qed.

Lemma carry_fbpush :
  forall n a ax ay fx fy,
    carry a (S n) (fb_push ax fx) (fb_push ay fy) = carry (majb a ax ay) n fx fy.
Proof.
  induction n; intros.
  simpl. unfold majb. btauto.
  remember (S n) as Sn. simpl. rewrite IHn. unfold fb_push. subst.
  simpl. easy.
Qed.

Lemma carry_succ :
  forall m p,
    carry true m (pos2fb p) allfalse = pos2fb (Pos.succ p) m ⊕ (pos2fb p) m.
Proof.
  induction m; intros. simpl. destruct p; reflexivity.
  replace allfalse with (fb_push false allfalse).
  2:{ unfold fb_push, allfalse. apply functional_extensionality. intros. destruct x; reflexivity.
  }
  Local Opaque fb_push carry.
  destruct p; simpl.
  rewrite carry_fbpush; unfold majb; simpl. rewrite IHm. reflexivity.
  rewrite carry_fbpush; unfold majb; simpl. rewrite carry_false_0_r. Local Transparent fb_push. simpl. btauto.
  rewrite carry_fbpush; unfold majb; simpl. Local Transparent carry. destruct m; reflexivity.
Qed.

Lemma carry_succ' :
  forall m p,
    carry true m allfalse (pos2fb p) = pos2fb (Pos.succ p) m ⊕ (pos2fb p) m.
Proof.
  intros. rewrite carry_sym. apply carry_succ.
Qed.

Lemma carry_succ0 :
  forall m, carry true m allfalse allfalse = pos2fb xH m.
Proof.
  induction m. easy. 
  replace allfalse with (fb_push false allfalse).
  2:{ unfold fb_push, allfalse. apply functional_extensionality. intros. destruct x; reflexivity.
  }
  rewrite carry_fbpush. unfold majb. simpl. rewrite carry_false_0_l. easy.
Qed.

Lemma carry_add_pos_eq :
  forall m b p q,
    carry b m (pos2fb p) (pos2fb q) ⊕ (pos2fb p) m ⊕ (pos2fb q) m = pos2fb (add_c b p q) m.
Proof.
  induction m; intros. simpl. destruct p, q, b; reflexivity.
  Local Opaque carry.
  destruct p, q, b; simpl; rewrite carry_fbpush; 
    try (rewrite IHm; reflexivity);
    try (unfold majb; simpl; 
         try rewrite carry_succ; try rewrite carry_succ'; 
         try rewrite carry_succ0; try rewrite carry_false_0_l;
         try rewrite carry_false_0_r;
         unfold allfalse; try btauto; try (destruct m; reflexivity)).
Qed.

Lemma carry_add_eq_carry0 :
  forall m x y,
    carry false m (N2fb x) (N2fb y) ⊕ (N2fb x) m ⊕ (N2fb y) m = (N2fb (x + y)) m.
Proof.
  intros.
  destruct x as [|p]; destruct y as [|q]; simpl; unfold allfalse.
  rewrite carry_false_0_l. easy.
  rewrite carry_false_0_l. btauto.
  rewrite carry_false_0_r. btauto.
  apply carry_add_pos_eq.
Qed.

Lemma carry_add_eq_carry1 :
  forall m x y,
    carry true m (N2fb x) (N2fb y) ⊕ (N2fb x) m ⊕ (N2fb y) m = (N2fb (x + y + 1)) m.
Proof.
  intros. 
  destruct x as [|p]; destruct y as [|q]; simpl; unfold allfalse.
  rewrite carry_succ0. destruct m; easy.
  rewrite carry_succ'. replace (q + 1)%positive with (Pos.succ q) by lia. btauto.
  rewrite carry_succ. replace (p + 1)%positive with (Pos.succ p) by lia. btauto.
  rewrite carry_add_pos_eq. unfold add_c. rewrite Pos.add_carry_spec. replace (p + q + 1)%positive with (Pos.succ (p + q)) by lia. easy.
Qed.

Definition fbxor f g := fun (i : nat) => f i ⊕ g i.

Definition msma i b f g := fun (x : nat) => if (x <? i) then 
        (carry b (S x) f g ⊕ (f (S x))) else (if (x =? i) then carry b (S x) f g else f x).

Definition msmb i (b : bool) f g := fun (x : nat) => if (x <=? i) then (f x ⊕ g x) else g x.

Definition msmc i b f g := fun (x : nat) => if (x <=? i) then (f x ⊕ g x) else (carry b x f g ⊕ f x ⊕ g x).

Definition sumfb b f g := fun (x : nat) => carry b x f g ⊕ f x ⊕ g x.

(*
Ltac fb_push_n_simpl := repeat (try rewrite fb_push_n_left by lia; try rewrite fb_push_n_right by lia).
Ltac update_simpl := repeat (try rewrite update_index_neq by lia); try rewrite update_index_eq by lia.
*)
Ltac BreakIfExpression :=
  match goal with
  | [ |- context[if ?X <? ?Y then _ else _] ] => bdestruct (X <? Y); try lia
  | [ |- context[if ?X <=? ?Y then _ else _] ] => bdestruct (X <=? Y); try lia
  | [ |- context[if ?X =? ?Y then _ else _] ] => bdestruct (X =? Y); try lia
  end.

Ltac IfExpSimpl := repeat BreakIfExpression.

Lemma msm_eq1 :
  forall n i c f g,
    S i < n ->
    msma i c f g i ⊕ msma i c f g (S i) = msma (S i) c f g i.
Proof.
  intros. unfold msma. IfExpSimpl. easy.
Qed.

Lemma msm_eq2 :
  forall n i c f g,
    S i < n ->
    msmb i c f g (S i) ⊕ msma i c f g (S i) = msmb (S i) c f g (S i).
Proof.
  intros. unfold msma. unfold msmb. IfExpSimpl. btauto.
Qed.
       

Lemma msm_eq3 :
  forall n i c f g,
    S i < n ->
    majb (msma i c f g (S i)) (msmb i c f g (S i)) (msma i c f g i) = msma (S i) c f g (S i).
Proof.
  intros. unfold msma. unfold msmb. IfExpSimpl.
  simpl. unfold majb. easy.
Qed.

Definition var_prop (f:var -> nat) (x y c : var) (n:nat) : Prop :=
      n <= (f x) /\  n <= f y /\ f c = 1.

Definition get_cus (f:posi -> val) (x:var) := fun i => match f (x,i) with nval b r => b | _ => false end.

Lemma get_cus_cua : forall f x n, get_cus f x n = get_cua (f (x,n)).
Proof.
  intros.
  unfold get_cus,get_cua.
  destruct (f (x,n)). easy. easy. easy.
Qed.

Definition put_cus (f:posi -> val) (x:var) (g:nat -> bool) (n:nat) : (posi -> val) :=
     fun a => if fst a =? x then if snd a <? n then put_cu (f a) (g (snd a)) else f a else f a.

Lemma cus_get_neq : forall (f:posi -> val) (x y :var) g n i, 
              x <> y -> get_cua ((put_cus f y g n) (x,i)) = get_cua (f (x,i)).
Proof.
 intros.
 unfold get_cua.
 unfold put_cus.
 simpl.
 bdestruct (x =? y).
 lia. easy.
Qed.

Lemma put_cus_out : forall (f:posi -> val) (x y :var) g n i, 
              n <= i -> ((put_cus f y g n) (x,i)) = (f (x,i)).
Proof. 
  intros.
  unfold put_cus.
  simpl.
  bdestruct (x =? y).
  bdestruct (i <? n). lia.
  easy. easy.
Qed.

Definition nor_modes (f:posi -> val) (x:var) (n:nat) :=
      forall i, i < n -> nor_mode f (x,i).

Lemma nor_mode_cus_eq: forall f x g n y i, 
       nor_mode f (y,i) -> nor_mode (put_cus f x g n) (y,i).
Proof.
  intros. unfold nor_mode in *.
  unfold put_cus.
  simpl.
  bdestruct (y =? x).
  bdestruct (i <? n).
  destruct (f (y, i)).
  unfold put_cu. easy.
  inv H0. inv H0.
  apply H0. apply H0.
Qed.

Lemma cus_get_eq : forall (f:posi -> val) (x :var) g n i, 
              i < n -> nor_modes f x n -> get_cua ((put_cus f x g n) (x,i)) = g i.
Proof.
 intros.
 unfold get_cua.
 unfold put_cus.
 simpl.
 bdestruct (x =? x).
 bdestruct (i <? n).
 unfold put_cu.
 specialize (H1 i H3). unfold nor_mode in *.
 destruct (f (x, i)) eqn:eq1. easy.
 inv H1. inv H1.
 lia. lia.
Qed.

Lemma put_cus_eq : forall (f:posi -> val) (x:var) g n i, 
          i < n -> (put_cus f x g n) (x,i) = put_cu (f (x,i)) (g i).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (x =? x).
 bdestruct (i <? n). easy. lia. lia.
Qed.

Lemma put_cus_neq : forall (f:posi -> val) (x y:var) g n i, 
              x <> y -> (put_cus f x g n) (y,i) = f (y,i).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (y =? x). lia. easy.
Qed.

Lemma put_cus_neq_1 : forall (f:posi -> val) (x:var) g n c, 
              x <> fst c -> (put_cus f x g n) c = f c.
Proof.
 intros.
 destruct c. apply put_cus_neq.
 simpl in H0. assumption.
Qed.

Lemma put_cus_neq_2 : forall (f:posi -> val) (y:var) g n i, 
           n <= i -> (put_cus f y g n) (y,i) = f (y,i).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (y =? y).
 bdestruct (i <? n). lia. easy.
 easy.
Qed.

Definition get_r (v:val) :=
   match v with nval x r => r
              | qval r => r
              | hval x y r => r
   end.

Lemma get_r_put_same : forall (f:posi -> val) x y g n i,
      get_r (put_cus f x g n (y,i)) = get_r (f (y,i)).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (y =? x).
 bdestruct (i <? n).
 unfold put_cu.
 destruct (f (y, i)).
 unfold get_r. easy. easy. easy. easy. easy.
Qed.

Lemma put_cu_mid_eq : forall (f g:posi -> val) a v, 
              nor_mode f a -> nor_mode g a -> get_r (f a) = get_r (g a) -> (put_cu (f a) v) = (put_cu (g a) v).
Proof.
 intros.
 unfold put_cu. unfold nor_mode in *.
 destruct (f a). destruct (g a).
 unfold get_r in H2. subst.
 easy. inv H1. inv H1.
 inv H0. inv H0.
Qed.

Lemma put_cus_twice_neq : forall (f:posi -> val) (x y:var) g1 g2 n, 
              x <> y -> (put_cus (put_cus f x g1 n) y g2 n)
                          = (put_cus (put_cus f y g2 n) x g1 n).
Proof.
 intros.
 apply functional_extensionality.
 unfold put_cus. intros.
 destruct x0. simpl.
 bdestruct (v =? y).
 bdestruct (v =? x). lia. easy.
 easy.
Qed.


Lemma msmb_put : forall n i st x b f g, 
        S i < n -> put_cus st x (msmb (S i) b f g) n = (put_cus st x
             (msmb i b f g) n)[(x,S i) |-> put_cu (st (x,S i)) (msmb i b f g (S i) ⊕ msma i b f g (S i))].
Proof.
  intros.
  apply functional_extensionality.
  intros. destruct x0.
  bdestruct (x =? v).
  subst.
  unfold put_cus. simpl.
  bdestruct (n0 =? S i). subst.
  rewrite eupdate_index_eq.
  bdestruct (v =? v).
  bdestruct (S i <? n).
  assert ((msmb (S i) b f g (S i)) = (msmb i b f g (S i) ⊕ msma i b f g (S i))).
  erewrite msm_eq2. easy. apply H0.
  rewrite H3. easy. lia. lia.
  rewrite eupdate_index_neq. simpl.
  bdestruct (v =? v).
  bdestruct (n0 <? n).
  unfold msmb.
  bdestruct (n0 <=? S i).
  bdestruct (n0 <=? i).
  easy. lia.
  bdestruct (n0 <=? i). lia. easy.
  easy. easy. intros R. inv R. lia.
  rewrite put_cus_neq. rewrite eupdate_index_neq.
  rewrite put_cus_neq. easy. assumption.
  intros R. inv R. lia. lia.
Qed.

Lemma iner_neq : forall (x y:var) (a b:nat), x <> y -> (x,a) <> (y,b).
Proof.
  intros. intros R.
  inv R. contradiction.
Qed.

Lemma iner_neq_1 : forall (x:var) (c:posi) a, x <> fst c -> (x,a) <> c.
Proof.
  intros. intros R.
  destruct c.
  inv R. contradiction.
Qed.

Lemma msma_put : forall n i st x b f g, 
        S i < n -> put_cus st x (msma (S i) b f g) n = ((put_cus st x
             (msma i b f g) n)[(x,S i) |-> put_cu (st (x,S i))
                          (majb (msma i b f g (S i)) (msmb i b f g (S i)) (msma i b f g i))])
                      [(x,i) |-> put_cu (st (x,i)) (msma i b f g i ⊕ msma i b f g (S i))].
Proof.
  intros.
  apply functional_extensionality.
  intros. destruct x0.
  unfold put_cus. simpl.
  bdestruct (v =? x). subst.
  bdestruct (n0 =? i). subst.
  rewrite eupdate_index_eq.
  bdestruct (i <? n).
  unfold put_cu.
  destruct (st (x, i)).
  assert ((msma (S i) b f g i)  = (msma i b f g i ⊕ msma i b f g (S i))).
  erewrite <- msm_eq1. easy. apply H0.
  rewrite H2. easy. easy. easy.
  lia.
  rewrite eupdate_index_neq.
  bdestruct (n0 =? S i). subst.
  rewrite eupdate_index_eq.
  bdestruct (S i <? n).
  unfold put_cu.
  destruct (st (x, S i)).
  assert ((msma (S i) b f g (S i))  = majb (msma i b f g (S i)) (msmb i b f g (S i)) (msma i b f g i)).
  erewrite <- msm_eq3. easy. apply H2.
  rewrite H3. easy. easy. easy. lia.
  rewrite eupdate_index_neq.
  simpl.
  bdestruct (n0 <? n).
  bdestruct (x =? x).
  assert ((msma (S i) b f g n0) = (msma i b f g n0)).
  unfold msma.
  bdestruct (n0 <? S i).
  bdestruct (n0 <? i).
  easy. lia.
  bdestruct (n0 =? S i).
  lia.
  bdestruct (n0 <? i). lia.
  bdestruct (n0 =? i). lia.
  easy.
  rewrite H5. easy.
  lia.
  bdestruct (x =? x). easy. easy.
  intros R. inv R. lia.
  intros R. inv R. lia.
  rewrite eupdate_index_neq.
  rewrite eupdate_index_neq. simpl.
  bdestruct (v =? x). lia.
  easy.
  apply iner_neq. lia.
  apply iner_neq. lia.
Qed.

Lemma eupdates_twice_neq : forall f x g n c v, x <> fst c 
           -> (put_cus f x g n)[c |-> v] = put_cus (f[c |-> v]) x g n.
Proof.
  intros. unfold put_cus.
  apply functional_extensionality.
  intros.
  bdestruct (x0 ==? c).
  subst.
  rewrite eupdate_index_eq.
  bdestruct (fst c =? x).
  subst. contradiction.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq.
  bdestruct (fst x0 =? x).
  rewrite eupdate_index_neq.
  easy. nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  easy. nor_sym.
Qed.

Lemma same_eupdate : forall (f f' : posi -> val) c v, f = f' -> f[c |-> v] = f'[c |-> v].
Proof.
  intros. 
  apply functional_extensionality.
  intros.
  bdestruct (c ==? x).
  subst.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq.
  rewrite eupdate_index_neq. subst. easy.
  assumption. assumption.
Qed.

Lemma same_eupdate_1 : forall (f f' : posi -> val) c v v', f = f' -> v = v' -> f[c |-> v] = f'[c |-> v'].
Proof.
  intros. 
  apply functional_extensionality.
  intros.
  bdestruct (c ==? x).
  subst.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq.
  rewrite eupdate_index_neq. subst. easy.
  assumption. assumption.
Qed.

Lemma msma_0 : forall f x b g n, 0 < n -> nor_modes f x n -> put_cus f x (msma 0 b (get_cus f x) g) n =
                     f[(x,0) |-> put_cu (f (x,0)) (carry b (S 0) (get_cus f x) g)].
Proof.
  intros.
  unfold put_cus, msma.
  apply functional_extensionality.
  intros.
  destruct x0. simpl in *.
  bdestruct (v =? x). subst.
  bdestruct (n0 <? n).
  bdestruct (n0 =? 0).
  subst.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq.
  rewrite get_cus_cua.
  rewrite put_get_cu. easy.
  unfold nor_modes in *. apply H1. lia.
  intros R. inv R. contradiction.
  rewrite eupdate_index_neq. easy.
  intros R. inv R. lia.
  rewrite eupdate_index_neq. easy.
  apply iner_neq. lia.
Qed.

Lemma msmb_0 : forall S f b y n, 0 < n -> nor_modes S y n -> put_cus S y (msmb 0 b f (get_cus S y)) n =
                     S[(y,0) |-> put_cu (S (y,0)) (f 0 ⊕ (get_cua (S (y,0))))].
Proof.
  intros.
  unfold put_cus, msmb.
  apply functional_extensionality.
  intros.
  destruct x. simpl in *.
  bdestruct (v =? y). subst.
  bdestruct (n0 <? n).
  bdestruct (n0 <=? 0).
  inv H3.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq.
  rewrite get_cus_cua.
  rewrite put_get_cu. easy.
  unfold nor_modes in *. apply H1. lia.
  intros R. inv R. lia.
  rewrite eupdate_index_neq. easy.
  intros R. inv R. lia.
  rewrite eupdate_index_neq. easy.
  apply iner_neq. lia.
Qed.

Lemma MAJseq'_correct :
  forall i n env S x y c,
    0 < n -> i < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem env S (MAJseq' i x y c) 
     (put_cus 
        (put_cus (S[c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x,0)))])
                   x (msma i (get_cua (S c)) (get_cus S x) (get_cus S y)) n)
          y (msmb i (get_cua (S c)) (get_cus S x) (get_cus S y)) n).
Proof.
  induction i; intros.
  - simpl. apply MAJ_nor.
    unfold nor_modes in *. apply H2. easy.
    unfold nor_modes in *. apply H3. easy.
    assumption.
    apply iner_neq; assumption.
    apply iner_neq_1; assumption.
    apply iner_neq_1; assumption.
    rewrite <- eupdates_twice_neq.
    rewrite <- eupdates_twice_neq.
    apply same_eupdate.
    rewrite msma_0.
    rewrite <- eupdates_twice_neq.
    rewrite eupdate_twice_neq.
    apply same_eupdate_1.
    rewrite msmb_0.
    apply eupdate_same_1. easy.
    rewrite get_cus_cua.
    rewrite xorb_comm. easy. lia.
    assumption. simpl.
    rewrite carry_1.
    rewrite get_cus_cua.
    rewrite get_cus_cua. easy.
    apply iner_neq ; assumption.
    simpl. nor_sym. lia.
    assumption. assumption. assumption.
  - simpl. econstructor.
    apply IHi. apply H0. lia.
    1 - 6 : assumption.
    apply MAJ_nor.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1; assumption.
    unfold nor_modes in *. apply H2. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1; assumption.
    unfold nor_modes in *. apply H3. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1; assumption.
    unfold nor_modes in *. apply H2. lia.
    apply iner_neq; assumption.
    apply iner_neq; lia.
    intros R. inv R. lia.
    rewrite cus_get_neq by assumption.
    rewrite cus_get_eq.
    rewrite cus_get_eq.
    rewrite msmb_put.
    rewrite eupdate_twice_neq.
    apply same_eupdate_1.
    rewrite put_cus_twice_neq.
    rewrite msma_put.
    apply same_eupdate_1.
    apply same_eupdate_1.
    rewrite put_cus_twice_neq. easy. lia.
    rewrite put_cus_twice_neq. 
    rewrite cus_get_eq.
    apply put_cu_mid_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1; assumption.
    unfold nor_modes in H3. apply H2. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1; assumption.
    unfold nor_modes in H3. apply H2. lia.
    rewrite get_r_put_same.
    rewrite get_r_put_same. rewrite get_r_put_same. easy.  lia.
    unfold nor_modes in *.
    intros.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H2. lia. assumption.
    rewrite put_cus_neq.
    rewrite put_cus_neq.
    rewrite cus_get_eq.
    apply put_cu_mid_eq.
    apply nor_mode_up. apply iner_neq_1; assumption.
    unfold nor_modes in H2. apply H2. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1; assumption.
    unfold nor_modes in H2. apply H2. lia.
    rewrite get_r_put_same. easy.
    lia.
    unfold nor_modes in *. intros.
    apply nor_mode_up. apply iner_neq_1; assumption.
    unfold nor_modes in H2. apply H2.
    1- 5: lia.
    rewrite put_cus_neq.
    apply put_cu_mid_eq.
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H3. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H3. lia.
    rewrite get_r_put_same.
    rewrite get_r_put_same. easy.
    assumption. apply iner_neq. lia.
    lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H3. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H2. lia.
Qed.

Lemma nor_mode_up_1 : forall f x v, nor_mode f x -> nor_mode (f[x |-> put_cu (f x) v]) x.
Proof.
  intros.
  unfold nor_mode in *.
  rewrite eupdate_index_eq.
  unfold put_cu.
  destruct (f x).
  easy. inv H0. inv H0.
Qed.

Lemma get_cua_eq : forall f x v, nor_mode f x -> get_cua ((f[x |-> put_cu (f x) v]) x) = v.
Proof.
  intros.
  unfold get_cua.
  rewrite eupdate_index_eq.
  unfold put_cu.
  unfold nor_mode in H0.
  destruct (f x). easy. inv H0. inv H0.
Qed.

Lemma double_put_cu : forall (f:posi -> val) x v v', put_cu (put_cu (f x) v) v' = put_cu (f x) v'.
Proof.
  intros.
  unfold put_cu.
  destruct (f x). easy. easy. easy.
Qed.

Lemma put_cu_cus : forall (f:posi -> val) x y g i n v, put_cu (put_cus f y g n (x,i)) v = put_cu (f (x,i)) v.
Proof.
  intros.
  unfold put_cus,put_cu.
  simpl.
  bdestruct (x =? y).
  bdestruct (i <? n).
  destruct (f (x,i)). easy. easy. easy. easy. easy.
Qed.

Local Transparent carry.

Lemma UMAseq'_correct :
  forall i n env S x y c,
    0 < n -> i < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem env (put_cus 
        (put_cus (S[c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x,0)))])
                   x (msma i (get_cua (S c)) (get_cus S x) (get_cus S y)) n)
          y (msmc i (get_cua (S c)) (get_cus S x) (get_cus S y)) n) (UMAseq' i x y c) 
         (put_cus S y (sumfb (get_cua (S c)) (get_cus S x) (get_cus S y)) n).
Proof.
  induction i; intros. 
  - simpl.
    apply UMA_nor with (fa := (get_cus S x) 0) (fb := (get_cus S y) 0)
                   (fc := carry (get_cua (S c)) 0 (get_cus S x) (get_cus S y)).
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1; assumption. apply H2. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1; assumption. apply H3. lia.
    destruct c.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up_1. apply H4. apply iner_neq. assumption.
    apply iner_neq_1; assumption.
    apply iner_neq_1; assumption.
    rewrite put_cus_neq by lia.
    rewrite cus_get_eq.
    unfold msma.
    bdestruct (0 <? 0). lia.
    bdestruct (0 =? 0). 
    rewrite carry_1.
    unfold carry. easy. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_up. apply iner_neq_1. assumption.
    apply H2. lia.
    rewrite cus_get_eq.
    unfold msmc.
    bdestruct (0 <=? 0).
    rewrite xorb_comm. easy.
    lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1. assumption.
    apply H3. lia.
    rewrite put_cus_neq_1 by lia.
    rewrite put_cus_neq_1 by lia.
    rewrite get_cua_eq.
    simpl. rewrite get_cus_cua. easy.
    assumption.
    apply functional_extensionality. intros.
    bdestruct (x0 ==? c).
    subst. rewrite eupdate_index_eq.
    rewrite put_cus_neq_1. simpl.
    rewrite put_cus_neq_1.
    rewrite put_cus_neq_1.
    rewrite eupdate_index_eq.
    rewrite double_put_cu.
    rewrite put_get_cu. easy. 
    1 - 4: assumption.
    rewrite eupdate_index_neq by nor_sym.
    bdestruct (x0 ==? (y,0)).
    subst.
    rewrite eupdate_index_eq.
    simpl.
    rewrite put_cu_cus.
    rewrite put_cu_cus.
    rewrite eupdate_index_neq by nor_sym.
    rewrite get_cus_cua.
    rewrite put_cus_eq.
    unfold sumfb. simpl.
    rewrite get_cus_cua.
    rewrite xorb_assoc.
    rewrite xorb_comm. easy. lia.
    rewrite eupdate_index_neq by nor_sym.
    bdestruct (x0 ==? (x,0)).
    subst. rewrite eupdate_index_eq.
    rewrite put_cus_neq_1.
    rewrite put_cu_cus.
    rewrite put_cu_cus.
    rewrite eupdate_index_neq.
    rewrite put_get_cu. easy.
    apply H2. lia. nor_sym. simpl. lia.
    rewrite eupdate_index_neq by nor_sym.
    destruct x0.
    bdestruct (v =? y). subst.
    bdestruct (n0 <? n).
    rewrite put_cus_eq by assumption.
    rewrite put_cus_eq by assumption.
    rewrite put_cus_neq by assumption.
    rewrite eupdate_index_neq by nor_sym.
    unfold sumfb,msmc.
    bdestruct (n0 <=? 0).
    assert (n0 <> 0). intros R. subst. contradiction.
    lia. easy.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    unfold put_cus. simpl.
    bdestruct (v =? x).
    bdestruct (n0 <? n).
    subst.
    rewrite eupdate_index_neq by nor_sym.
    unfold put_cu.
    destruct (S (x, n0)) eqn:eq1.
    unfold msma.
    bdestruct (n0 <? 0). lia.
    bdestruct (n0 =? 0).
    assert (n0 <> 0). intros R. subst. contradiction.
    lia. rewrite get_cus_cua.
    rewrite eq1. rewrite get_cua_t. easy. easy. easy.
    rewrite eupdate_index_neq. easy. nor_sym.
    rewrite eupdate_index_neq. easy. nor_sym.
  - simpl.
    eapply seq_sem.
    2 : { apply IHi. 
          1-2: lia. 
          1-6: assumption. }
    apply UMA_nor with (fa := (get_cus S x) (Datatypes.S i)) (fb := (get_cus S y) (Datatypes.S i))
                   (fc := carry (get_cua (S c)) (Datatypes.S i) (get_cus S x) (get_cus S y)).
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1. assumption.
    apply H2. assumption.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1. assumption.
    apply H3. assumption.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1. assumption.
    apply H2. lia.
    apply iner_neq; assumption.
    apply iner_neq; lia.
    intros R. inv R. lia.
    rewrite cus_get_neq by lia.
    rewrite cus_get_eq.
    simpl.
    unfold msma.
    bdestruct (Datatypes.S i <? Datatypes.S i). lia.
    bdestruct (Datatypes.S i =? Datatypes.S i).
    rewrite carry_n. simpl. easy. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_up. apply iner_neq_1. assumption.
    apply H2. lia.
    rewrite cus_get_eq. unfold msmc.
    bdestruct ( Datatypes.S i <=? Datatypes.S i).
    rewrite xorb_comm. easy. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_cus_eq.
    apply nor_mode_up. apply iner_neq_1. assumption.
    apply H3. lia.
    rewrite cus_get_neq by lia.
    rewrite cus_get_eq.
    unfold msma.
    bdestruct (i <? Datatypes.S i). easy. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_up. apply iner_neq_1. assumption.
    apply H2. lia.
    repeat rewrite put_cu_cus.
    apply functional_extensionality.
    intros.
    bdestruct (x0 ==? (x,i)).
    subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_twice_neq.
    rewrite put_cus_eq.
    rewrite put_cu_cus.
    unfold msma.
    bdestruct (i <? i). lia.
    bdestruct (i =? i). easy. lia. lia. lia.
    rewrite eupdate_index_neq by nor_sym.
    bdestruct (x0 ==? (y,Datatypes.S i)).
    subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_eq.
    rewrite put_cu_cus.
    unfold msmc.
    bdestruct (Datatypes.S i <=? i). lia.
    assert (((carry (get_cua (S c)) (Datatypes.S i) 
      (get_cus S x) (get_cus S y) ⊕ get_cus S x (Datatypes.S i))
   ⊕ get_cus S y (Datatypes.S i)) = 
     ((get_cus S x (Datatypes.S i) ⊕ get_cus S y (Datatypes.S i))
   ⊕ carry (get_cua (S c)) (Datatypes.S i) 
       (get_cus S x) (get_cus S y))) by btauto.
    rewrite H10. easy. lia. 
    rewrite eupdate_index_neq by nor_sym.
    bdestruct (x0 ==? (x,Datatypes.S i)).
    subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_twice_neq.
    rewrite put_cus_eq.
    rewrite put_cu_cus.
    unfold msma.
    bdestruct (Datatypes.S i <? i). lia.
    bdestruct (Datatypes.S i =? i). lia. easy.
    lia. lia.
    rewrite eupdate_index_neq by nor_sym.
    destruct x0.
    bdestruct (v =? y).
    bdestruct (n0 <? n).
    subst.
    rewrite put_cus_eq.
    rewrite put_cus_eq.
    rewrite put_cu_cus.
    rewrite put_cu_cus.
    unfold msmc.
    bdestruct (n0 <=? i).
    bdestruct (n0 <=? Datatypes.S i). easy.
    lia.
    bdestruct (n0 <=? Datatypes.S i).
    assert (n0 <> Datatypes.S i).
    intros R. subst. contradiction.
    lia. easy. lia. lia.
    rewrite put_cus_out by lia.
    rewrite put_cus_out by lia.
    rewrite put_cus_out by lia.
    rewrite put_cus_out by lia.
    easy.
    bdestruct (v =? x).
    bdestruct (n0 <? n).
    subst.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    unfold msma.
    bdestruct (n0 <? i).
    bdestruct (n0 <? Datatypes.S i).
    easy. lia.
    bdestruct (n0 =? i).
    subst. contradiction.
    bdestruct (n0 <? Datatypes.S i). lia.
    bdestruct (n0 =? Datatypes.S i).
    subst. contradiction.
    easy.
    rewrite put_cus_out by lia.
    rewrite put_cus_out by lia.
    rewrite put_cus_out by lia.
    rewrite put_cus_out by lia.
    easy.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    easy.
Qed.

(* The following will do the negation of the first input value in the qubit sequence 00[x][y][z].
   THe actual effect is to make the sequence to be 00[-x][y][z]. *)
Fixpoint negator0 i x : scom :=
  match i with
  | 0 => SKIP
  | S i' => negator0 i' x; X (x, i')
  end.



(* The following implements an comparator. 
   THe first step is to adjust the adder circuit above to be
    MAJ;high_bit_manipulate;UMA.
    This is based on a binary number circuit observation that:
    To compare if x < y, we just need to do x - y, and see the high bit of the binary
    format of x - y. If the high_bit is zero, that means that x >= y;
    otherwise x < y. *)
Fixpoint sinv p :=
  match p with
  | SKIP => SKIP
  | X n => X n
  | CU n p => CU n (sinv p)
  | Seq p1 p2 => sinv p2; sinv p1
  | Lshift x => Rshift x
  | Rshift x => Lshift x
  | RZ q p1 => RRZ q p1
  | RRZ q p1 => RZ q p1
  end.

Fixpoint finv p :=
   match p with 
    | Exp s => Exp (sinv s)
    | QFT x => RQFT x
    | RQFT x => QFT x
    | Reset x => Reset x
    | Rev x => Rev x
    | H x => H x
    | FSeq p1 p2 => FSeq (finv p2) (finv p1)
   end.

Definition highb01 n x y c1 c2: scom := MAJseq n x y c1; CNOT (x,n) c2; sinv (MAJseq n x y c1).

(* The actual comparator implementation. 
    We first flip the x positions, then use the high-bit comparator above. 
    Then, we use an inverse circuit of flipping x positions to turn the
    low bits back to store the value x.
    The actual implementation in the comparator is to do (x' + y)' as x - y,
    and then, the high-bit actually stores the boolean result of x - y < 0.  *)
Definition comparator01 n x y c1 c2 := (X c1; negator0 n x); highb01 n x y c1 c2; sinv (X c1; negator0 n x).

(* The implementation of a subtractor. It takes two values [x][y], and the produces
    the result of [x][y + 2^n - x]. *)
Definition substractor01 n x y c1:= (X c1; negator0 n x); adder01 n x y c1; sinv (X c1; negator0 n x).


(* The implementation of a modulo adder. It takes [M][x][y], and then produces the result of [M][x+y % M][y]. 
   The modulo operation is not reversible. It will flip the high-bit to be the comparator factor.
   To flip the high-bit to zero, we use the inverse circuit of the comparator in the modulo adder to
   flip the high-bit back to zero.*)
Definition modadder21 n x y M c1 c2 := adder01 n y x c1 ; (*  adding y to x *)
                                       comparator01 n M x c1 c2; (* compare M < x + y (in position x) *)
                                       CU c2 (substractor01 n M x c1) ; X c2; (* doing -M + x to x, then flip c2. *)
                                       comparator01 n y x c1 c2. (* compare M with x+y % M to clean c2. *)

(* Here we implement the doubler circuit based on binary shift operation.
   It assumes an n-1 value x that live in a cell of n-bits (so the high-bit must be zero). 
   Then, we shift one position, so that the value looks like 2*x in a n-bit cell. *)
Definition doubler1 y := Rshift y.

(* Another version of the mod adder only for computing [x][M] -> [2*x % M][M].
   This version will mark the high-bit, and the high-bit is not clearable.
   However, eventually, we will clean all high-bit
   by using a inverse circuit of the whole implementation. *)
Definition moddoubler01 n x M c1 c2 :=
                doubler1 x; comparator01 n x M c1 c2; CU c2 (substractor01 n x M c1).

(* The following implements the modulo adder for all bit positions in the
   binary boolean function of C. 
   For every bit in C, we do the two items:
   we first to double the factor (originally 2^(i-1) * x %M, now 2^i * x %M).
   Then, we see if we need to add the factor result to the sum of C*x%M
   based on if the i-th bit of C is zero or not.
modadder21 n x y M c1 c2
[M][x][0][0] -> [M][2^i * x % M][C^i*x % M][0]
 *)
(* A function to compile positive to a bool function. *)
(* fb_push is to take a qubit and then push it to the zero position 
        in the bool function representation of a number. *)

Definition nat2fb n := N2fb (N.of_nat n).

(* A function to compile a natural number to a bool function. *)

Fixpoint modsummer' i n M x y c1 c2 s (fC : nat -> bool) :=
  match i with
  | 0 => if (fC 0) then adder01 n x y c1 else SKIP
  | S i' => modsummer' i' n M x y c1 c2 s fC; moddoubler01 n x M c1 c2; 
          SWAP c2 (s,i);
        (if (fC i) then modadder21 n y x M c1 c2 else SKIP)
  end.
Definition modsummer n M x y c1 c2 s C := modsummer' (n - 1) n M x y c1 c2 s (nat2fb C).

(* This is the final clean-up step of the mod multiplier to do C*x %M. 
    Here, modmult_half will first clean up all high bits.  *)
Definition modmult_half n M x y c1 c2 s C := modsummer n M x y c1 c2 s C; (sinv (modsummer n M x y c1 c2 s 0)).

Definition modmult_full C Cinv n M x y c1 c2 s := modmult_half n M x y c1 c2 s C; sinv (modmult_half n M x y c1 c2 s Cinv).

Definition modmult M C Cinv n x y z s c1 c2 := init_v n z M; modmult_full C Cinv n z x y c1 c2 s; sinv (init_v n z M).

Definition modmult_rev M C Cinv n x y z s c1 c2 := Rev x;; Exp (modmult M C Cinv n x y z s c1 c2);; Rev x.

(* another modmult adder based on QFT. *)
Fixpoint rz_adding (x:var) (n:nat) (pos:nat) (M: nat -> bool) :=
    match n with 0 => SKIP
               | S m => (if M (pos+m) then RZ n (x,pos) else SKIP) ; rz_adding x m pos M
    end.

(* adding x and M. *)
Fixpoint rz_adder' (x:var) (n:nat) (pos:nat) (M:nat -> bool) :=
     match n with 0 => SKIP
               | S m => rz_adding x n pos M ; rz_adder' x m (pos+1) M
     end.

Definition rz_adder (x:var) (n:nat) (M: nat -> bool) := rz_adder' x n 0 M.

Definition one_cu_adder (x:var) (n:nat) (c3:posi) (M:nat -> bool) := CU c3 (rz_adder x n M).
(*
Definition two_cu_adder (x:var) (n:nat) (c1 c2:posi) (M:nat -> bool) := CU c1 (CU c2 (rz_adder x n M)).
*)

(* assuming the input is in qft stage. *)
Definition rz_modadder (x:var) (n:nat) (y c: posi) (a:nat -> bool) (N:nat -> bool) :=
    Exp (one_cu_adder x n y a ; rz_adder x n N) ;; RQFT x;; Exp (CNOT (x,n-1) c) ;; QFT x
          ;; Exp (one_cu_adder x n c N ; one_cu_adder x n y a);;
     RQFT x ;; Exp (X (x,n-1) ; CNOT (x,n-1) c; X (x,n-1));; QFT x;;  one_cu_adder x n y a.

(* Mod adder. [x][0] -> [x][ax%N] having the a and N as constant. *)
Fixpoint rz_modmult' (y:var) (x:var) (n:nat) (size:nat) (c:posi) (a:nat -> bool) (N:nat -> bool) :=
     match n with 0 => Exp SKIP
               | S m => rz_modadder x size (y,m) c a N ;; rz_modmult' y x m size c a N
     end.
Definition rz_modmult_half (y:var) (x:var) (n:nat) (c:posi) (a:nat -> bool) (N:nat -> bool) :=
                 QFT x ;; rz_modmult' y x n n c a N ;; RQFT x.

Definition rz_modmult_full (y:var) (x:var) (n:nat) (c:posi) (C:nat -> bool) (Cinv : nat -> bool) (N:nat -> bool) :=
                 rz_modmult_half y x n c C N ;; finv (rz_modmult_half y x n c Cinv N).



(*  Compilation to bcom. *)
(* Controlled rotation cascade on n qubits. *)


Inductive varType := NType | SType.

Definition id_fun := fun (i:nat) => i.

Fixpoint compile_var' (l: list (var * nat * varType)) (dim:nat) :=
   match l with [] => fun _ => (0,0,NType,0,id_fun)
              | (x,n,NType):: l' => fun i => if x =? i
                           then (dim,n,NType,0%nat,id_fun) else (compile_var' l' (dim + n)) i
              | (x,n,SType):: l' => fun i => if x =? i
                           then (dim,n,SType,0%nat,id_fun) else (compile_var' l' (dim + n+1)) i
   end.
Definition compile_var l := compile_var' l 0.

Fixpoint get_dim (l: list (var * nat * varType)) :=
   match l with [] => 0
             | (x,n,NType) :: l' => n + get_dim l'
             | (x,n,SType) :: l' => (n+1) + get_dim l'
   end.

Definition inter_num (size:nat) (t : varType) :=
   match t with NType => size
              | SType => size+1
   end.

Definition adj_offset (index:nat) (offset:nat) (size:nat) (t:varType) :=
    (index + offset) mod (inter_num size t).

Definition rz_ang (n:nat) : R := ((2%R * PI)%R / 2%R^n).

Definition rrz_ang (n:nat) : R := (1 - ((2%R * PI)%R / 2%R^n)).

Definition vars := nat -> (nat * nat * varType * nat * (nat -> nat)).

Definition shift_fun (f:nat -> nat) (offset:nat) (size:nat) := fun i => f ((i + offset) mod size).

Definition trans_lshift (f:vars) (x:var) :=
     match f x with (start, size, t, offset,g) => 
              fun i => if i =? x then (start, size, t, 
                            (offset + 1) mod (inter_num size t),
                              shift_fun g (offset + 1) (inter_num size t)) else f i
     end.

Definition trans_rshift (f:vars) (x:var) :=
     match f x with (start, size, t, offset,g) => 
              fun i => if i =? x then (start, size, t, 
                     (offset + (inter_num size t) - 1) mod (inter_num size t),
               shift_fun g (offset + (inter_num size t) - 1) (inter_num size t)) else f i
     end.

Definition find_pos (f : vars) (a:var) (b:nat) :=
       match f a with (start, size, t, offset,g) => start + g b
       end.

Fixpoint trans_exp (f : vars) (dim:nat) (exp:scom) :
                 (base_ucom dim * vars) :=
  match exp with SKIP => (SQIR.SKIP, f)
              | X (a,b) => (SQIR.X (find_pos f a b),f)
              | RZ q (a,b) => (SQIR.Rz (rz_ang q) (find_pos f a b),f)
              | RRZ q (a,b) => (SQIR.Rz (rrz_ang q) (find_pos f a b),f)
              | Lshift x => (SQIR.SKIP, trans_lshift f x)
              | Rshift x => (SQIR.SKIP, trans_rshift f x)
              | CU (a,b) (X (c,d)) => (SQIR.CNOT (find_pos f a b) (find_pos f c d),f)
              | CU (a,b) e1 => match trans_exp f dim e1 with (e1',f') => 
                                  ((control (find_pos f a b) e1'),f')
                               end
              | e1 ; e2 => match trans_exp f dim e1 with (e1',f') => 
                             match trans_exp f' dim e2 with (e2',f'') => 
                                        (SQIR.useq e1' e2', f'')
                             end
                            end
  end.

(* generalized Controlled rotation cascade on n qubits. *)
Fixpoint controlled_rotations_gen {dim} (start n : nat) : base_ucom dim :=
  match n with
  | 0 | 1 => SQIR.SKIP
  | 2     => control (start+1) (Rz (2 * PI / 2 ^ n)%R start) (* makes 0,1 cases irrelevant *)
  | S n'  => SQIR.useq (controlled_rotations_gen start n')
                 (control (start + n') (Rz (2 * PI / 2 ^ n)%R start))
  end.

(* generalized Quantum Fourier transform on n qubits. 
   We use the definition below (with cast and map_qubits) for proof convenience.
   For a more standard functional definition of QFT see Quipper:
   https://www.mathstat.dal.ca/~selinger/quipper/doc/src/Quipper/Libraries/QFT.html *)
Fixpoint QFT_gen {dim} (start n:nat) : base_ucom dim :=
  match n with
  | 0    => SQIR.SKIP
  | 1    => SQIR.H start
  | S n' => SQIR.useq (SQIR.H start) (SQIR.useq (controlled_rotations_gen start n)
            (map_qubits S (QFT_gen start n')))
  end.

Definition trans_qft {dim} (f:vars) (x:var) : base_ucom dim :=
          match f x with (start, size, t, offset,g) => QFT_gen start size end.

Definition trans_rqft {dim} (f:vars) (x:var) : base_ucom dim :=
          match f x with (start, size, t, offset,g) => invert (QFT_gen start size) end.

Fixpoint nH {dim} (start offset size n:nat) : base_ucom dim :=
     match n with 0 => SQIR.SKIP
               | S m => SQIR.useq (SQIR.H (((start + offset) mod size) + m)) (nH start offset size m)
     end.

Definition trans_h {dim} (f:vars) (x:var) : base_ucom dim :=
   match f x with (start, size, t, offset, g) => nH start offset (inter_num size t) size end.

Check cons.

Definition rev_meaning (g:nat -> nat) (offset size:nat) :=
       fun i => g (((size - 1) - ((i + size - offset) mod size)) + offset).

Definition trans_rev (f:vars) (x:var) := 
    match f x with (start,size,t,offset,g) => 
               fun i => if x =? i then (start,size,t,offset,rev_meaning g offset (inter_num size t)) else f i
    end.

Fixpoint move_bits {dim} (lstart rstart n:nat) : base_ucom dim :=
   match n with 0 => SQIR.SKIP
             | S m => SQIR.useq (SQIR.SWAP (lstart + m) (rstart + m)) (move_bits lstart rstart m)
   end.

Fixpoint move_left' {dim} (n start m : nat) : base_ucom dim :=
       match n with 0 => SQIR.SKIP
                 | S i => SQIR.useq (move_bits start (start + m) m) (move_left' i (start+m) m)
       end.

Definition move_left {dim} (start m size: nat) : base_ucom dim := move_left' (size/m) start m.

Fixpoint move_right' {dim} (n start m : nat) : base_ucom dim :=
       match n with 0 => SQIR.SKIP
               | S i => SQIR.useq (move_bits (start - m) start m) (move_right' i (start - m) m)
       end.
Definition move_right {dim} (start m size: nat) : base_ucom dim := move_right' (size/m) (start+size) m.

Fixpoint small_move_left' {dim} (start n : nat) : base_ucom dim :=
   match n with 0 => SQIR.SKIP
             | S m => SQIR.useq (SQIR.SWAP (start+m) (start+n)) (small_move_left' start m)
   end.

Fixpoint small_move_left {dim} (start m size: nat) : base_ucom dim :=
   match size with 0 => SQIR.SKIP
            | S i => SQIR.useq (small_move_left' start m) (small_move_left (start+1) m i)
   end.

Fixpoint small_move_right' {dim} (start n : nat) : base_ucom dim :=
   match n with 0 => SQIR.SKIP
             | S m => SQIR.useq (small_move_right' start m) (SQIR.SWAP (start+m) (start+n))
   end.

Fixpoint small_move_right {dim} (start m size: nat) : base_ucom dim :=
   match size with 0 => SQIR.SKIP
            | S i => SQIR.useq (small_move_right' start m) (small_move_right (start-1) m i)
   end.

Definition move_reset {dim} (start offset size : nat) : base_ucom dim :=
   if offset <? size - offset then SQIR.useq (move_left start offset size)
                                   (small_move_left (start+(size/offset)*offset) offset (size mod offset))
      else SQIR.useq (move_right start offset size) (small_move_right (start+size mod offset - 1) offset (size mod offset)).

Definition set_reset_fun (f:vars) (x:var) (start size:nat) (t:varType) :=
      fun i => if i =? x then (start,size,t,0%nat,id_fun) else f i.

Definition trans_reset {dim} (f:vars) (x:var) : (base_ucom dim * vars) :=
   match f x with  (start,size,t,offset,g) =>
            (move_reset start offset (inter_num size t), set_reset_fun f x start size t)
   end.

Fixpoint trans_face (f:vars) (dim:nat) (exp:face) : (base_ucom dim * vars) :=
     match exp with Exp s => trans_exp f dim s
                 | QFT x => (trans_qft f x, f)
                 | RQFT x => (trans_qft f x, f)
                 | H x => (trans_h f x, f)
                 | FSeq e1 e2 =>  
                         match trans_face f dim e1 with (e1',f') => 
                             match trans_face f' dim e2 with (e2',f'') => 
                                        (SQIR.useq e1' e2', f'')
                             end
                            end
                 | Rev x => (SQIR.SKIP, trans_rev f x)
                 | Reset x => trans_reset f x
     end.

Definition x := 1.

Definition y := 2.

Definition z := 3.

Definition s := 4.

Definition c1 := 5.

Definition c2 := 6.

Definition csplit (p : scom) :=
  match p with
  | SKIP => SKIP
  | X n => X n
  | RZ q p => RZ q p
  | RRZ q p => RRZ q p
  | Lshift x => Lshift x
  | Rshift x => Rshift x
  | CU n (p1; p2) => CU n p1; CU n p2
  | CU n p => CU n p
  | p1; p2 => p1; p2
  end.

Fixpoint csplit_face (p : face) :=
  match p with
  | Exp s => Exp (csplit s)
  | FSeq e1 e2 => FSeq (csplit_face e1) (csplit_face e2)
  | p => p
  end.

Fixpoint bcelim p :=
  match p with
  | SKIP => SKIP
  | X q => X q
  | RZ q p => RZ q p
  | RRZ q p => RRZ q p
  | Lshift x => Lshift x
  | Rshift x => Rshift x
  | CU q p => match bcelim p with
                 | SKIP => SKIP
                 | p' => CU q p'
                 end
  | Seq p1 p2 => match bcelim p1, bcelim p2 with
                  | SKIP, p2' => p2'
                  | p1', SKIP => p1'
                  | p1', p2' => Seq p1' p2'
                  end
  end.

Fixpoint bcelim_face p :=
   match p with 
     | Exp s => Exp (bcelim s)
     | FSeq e1 e2 => match bcelim_face e1, bcelim_face e2 with
                           |  Exp SKIP, e2' => e2'
                           | e1', Exp SKIP => e1'
                           | e1',e2' => e1' ;; e2'
                     end
     | e => e
   end.

Definition modmult_vars (n:nat) := cons (x,n,SType) (cons (y,n,NType) (cons (z,n,NType)
                               (cons (s,n,NType) (cons (c1,1,NType) (cons (c2,1,NType) []))))).

Definition modmult_var_fun (n:nat) := compile_var (modmult_vars n).

Definition modmult_sqir M C Cinv n := trans_face (modmult_var_fun n)
            (get_dim (modmult_vars n)) (csplit_face (bcelim_face(modmult_rev (nat2fb M) C Cinv n x y z s (c1,0) (c2,0)))).

Definition f_modmult_circuit a ainv N n := fun i => modmult_sqir N (a^(2^i) mod N) (ainv^(2^i) mod N) n.

Definition rz_mod_vars (n:nat) := cons (x,n,NType) (cons (y,n,NType) (cons (c1,1,NType) [])).

Definition rz_var_fun (n:nat) := compile_var (rz_mod_vars n).

Definition rz_mod_sqir M C Cinv n := trans_face (rz_var_fun n)
            (get_dim (rz_mod_vars n)) (csplit_face (bcelim_face (rz_modmult_full x y n (c1,0) (nat2fb C) (nat2fb Cinv) (nat2fb M)))).

Definition rz_f_modmult_circuit a ainv N n := fun i => 
                            rz_mod_sqir N (a^(2^i) mod N) (ainv^(2^i) mod N) n.


