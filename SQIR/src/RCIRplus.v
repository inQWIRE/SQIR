Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto.
Require Import Dirac.

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
      | seq_wf : forall env e1 e2, exp_WF env e1 -> exp_WF env e2 -> exp_WF env (Seq e1 e2).

Inductive well_typed_exp : env -> scom -> Prop :=
    | skip_refl : forall env, well_typed_exp env (SKIP)
    | x_refl : forall env a b, Env.MapsTo a Nor env -> well_typed_exp env (X (a,b))
    | x_had : forall env a b, Env.MapsTo a Had env -> well_typed_exp env (X (a,b))
    | cu_refl : forall env a b e, Env.MapsTo a Nor env -> well_typed_exp env e -> well_typed_exp env (CU (a,b) e)
    | rz_refl :forall env q a b, Env.MapsTo a Nor env -> well_typed_exp env (RZ q (a,b))
    | rz_had : forall env a b, Env.MapsTo a Had env -> well_typed_exp env (RZ 1 (a,b))
    | rz_qft : forall env q a b, Env.MapsTo a Phi env -> well_typed_exp env (RZ q (a,b))
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


(* The following will swap the result of the addition of two numbers x and y (x+y) to the position
   starting in 2 + n + n. Then, the original position that resides x+y will be empty for new computation. 
Fixpoint swapper02' i n :=
  match i with
  | 0 => bcskip
  | S i' => swapper02' i' n; bcswap (2 + i') (2 + n + n + i')
  end.
Definition swapper02 n := swapper02' n n.

Lemma swapper02'_eWF: forall i n, eWF (swapper02' i n).
Proof.
 intros. induction i.
 simpl. apply eWF_skip.
 simpl. apply eWF_seq.
 apply IHi. apply bcswap_eWF.
Qed.

Lemma swapper02'_eWT: forall i n dim, (2 + n + n + i) < dim -> eWT dim (swapper02' i n).
Proof.
 intros. induction i.
 simpl. constructor.
 lia. simpl. constructor.
 apply IHi. lia. apply bcswap_eWT.
 1 - 2: lia.
Qed.

Lemma swapper02_eWF: forall n, eWF (swapper02 n).
Proof.
 intros. unfold swapper02. apply swapper02'_eWF.
Qed.

Lemma swapper02_eWT: forall n dim, (2 + n + n + n) < dim -> eWT dim (swapper02 n).
Proof.
 intros. unfold swapper02. apply swapper02'_eWT. lia.
Qed.

Definition swapma i (f g : nat -> bool) := fun x => if (x <? i) then g x else f x.
Definition swapmb i (f g : nat -> bool) := fun x => if (x <? i) then f x else g x.

Lemma swapma_gtn_invariant :
  forall n f g h,
    fb_push_n n (swapma n f g) h = fb_push_n n g h.
Proof.
  intros. apply functional_extensionality; intro.
  bdestruct (x <? n). fb_push_n_simpl. unfold swapma. IfExpSimpl. easy.
  fb_push_n_simpl. easy.
Qed.

Lemma swapmb_gtn_invariant :
  forall n f g h,
    fb_push_n n (swapmb n f g) h = fb_push_n n f h.
Proof.
  intros. apply functional_extensionality; intro.
  bdestruct (x <? n). fb_push_n_simpl. unfold swapmb. IfExpSimpl. easy.
  fb_push_n_simpl. easy.
Qed.

Local Opaque bcswap.
Lemma swapper02'_correct :
  forall i n f g h u b1 b2,
    0 < n ->
    i <= n ->
    bcexec (swapper02' i n) (b1 ` b2 ` fb_push_n n f (fb_push_n n g (fb_push_n n h u))) 
= b1 ` b2 ` fb_push_n n (swapma i f h) (fb_push_n n g (fb_push_n n (swapmb i f h) u)).
Proof.
  induction i; intros.
  - simpl.
    replace (swapma 0 f h) with f by (apply functional_extensionality; intro; IfExpSimpl; easy).
    replace (swapmb 0 f h) with h by (apply functional_extensionality; intro; IfExpSimpl; easy).
    easy.
  - simpl. rewrite IHi by lia.
    apply functional_extensionality; intro. rewrite bcswap_correct by lia.
    bdestruct (x =? S (S i)). subst. simpl. fb_push_n_simpl. unfold swapma, swapmb. IfExpSimpl. apply f_equal. lia.
    bdestruct (x =? S (S (n + n + i))). subst. simpl. fb_push_n_simpl. unfold swapma, swapmb. IfExpSimpl. apply f_equal. lia.
    destruct x. easy. simpl. destruct x. easy. simpl.
    bdestruct (x <? n). fb_push_n_simpl. unfold swapma. IfExpSimpl; easy.
    bdestruct (x <? n + n). fb_push_n_simpl. easy.
    bdestruct (x <? n + n + n). fb_push_n_simpl. unfold swapmb. IfExpSimpl; easy.
    fb_push_n_simpl. easy.
Qed.

Lemma swapper02_correct :
  forall n x y z f b0 b1,
    0 < n ->
    bcexec (swapper02 n) (b0 ` b1 ` [x]_n [y]_n [z]_n f) = b0 ` b1 ` [z]_n [y]_n [x]_n f.
Proof.
  intros. unfold reg_push, swapper02. rewrite swapper02'_correct by lia.
  rewrite swapma_gtn_invariant. rewrite swapmb_gtn_invariant. easy.
Qed.

Opaque swapper02.
*)

(* The following will do the negation of the first input value in the qubit sequence 00[x][y][z].
   THe actual effect is to make the sequence to be 00[-x][y][z]. *)
Fixpoint negator0 i x : scom :=
  match i with
  | 0 => SKIP
  | S i' => negator0 i' x; X (x, i')
  end.

(*
Lemma negator0'_eWF :
  forall i, eWF (negator0' i).
Proof.
  induction i. simpl. constructor. simpl. constructor. easy. constructor.
Qed.

Lemma negator0'_eWT :
  forall i dim, 2 + i < dim -> eWT dim (negator0' i).
Proof.
  intros.
  induction i. simpl. constructor. lia.
  simpl. constructor.
  apply IHi. lia. constructor. lia.
Qed.

Lemma negator0_eWF :
  forall n, eWF (negator0 n).
Proof.
  intros. unfold negator0. apply negator0'_eWF.
Qed.

Lemma negator0_eWT :
  forall n dim, 2 + n < dim -> eWT dim (negator0 n).
Proof.
  intros. unfold negator0. apply negator0'_eWT. lia.
Qed.

Lemma negator0'_efresh :
  forall i, efresh 1 (negator0' i).
Proof.
  induction i. simpl. constructor. simpl. constructor. easy. constructor. lia.
Qed.

Lemma negator0_efresh :
  forall n, efresh 1 (negator0 n).
Proof.
  intros. unfold negator0. apply negator0'_efresh.
Qed.

Definition negatem i (f : nat -> bool) := fun (x : nat) => if (x <? i) then ¬ (f x) else f x.

Lemma negator0'_correct :
  forall i n f g b1 b2,
    0 < n ->
    i <= n ->
    bcexec (negator0' i) (b1 ` b2 ` fb_push_n n f g) = b1 ` b2 ` fb_push_n n (negatem i f) g.
Proof.
  induction i; intros.
  - simpl. replace (negatem 0 f) with f by (apply functional_extensionality; intro; IfExpSimpl; easy).
    easy.
  - simpl. rewrite IHi by lia. apply functional_extensionality; intro.
    bdestruct (x =? 2 + i). subst. simpl. update_simpl. fb_push_n_simpl. unfold negatem. IfExpSimpl. easy.
    update_simpl. destruct x. easy. simpl. destruct x. easy. simpl.
    bdestruct (x <? n). fb_push_n_simpl. unfold negatem. IfExpSimpl; easy.
    fb_push_n_simpl. easy.
Qed.

Lemma negatem_Nlnot :
  forall (n : nat) (x : N) i,
    negatem n (N2fb x) i = N.testbit (N.lnot x (N.of_nat n)) (N.of_nat i).
Proof.
  intros. unfold negatem. rewrite N2fb_Ntestbit. symmetry.
  bdestruct (i <? n). apply N.lnot_spec_low. lia.
  apply N.lnot_spec_high. lia.
Qed.

Lemma negatem_arith :
  forall n x,
    x < 2^n ->
    negatem n (nat2fb x) = nat2fb (2^n - 1 - x).
Proof.
  intros. unfold nat2fb. apply functional_extensionality; intro i.
  rewrite negatem_Nlnot. rewrite N2fb_Ntestbit.
  do 2 rewrite Nnat.Nat2N.inj_sub. rewrite Nofnat_pow. simpl.
  bdestruct (x =? 0). subst. simpl. rewrite N.ones_equiv. rewrite N.pred_sub. rewrite N.sub_0_r. easy.
  rewrite N.lnot_sub_low. rewrite N.ones_equiv. rewrite N.pred_sub. easy.
  apply N.log2_lt_pow2. assert (0 < x) by lia. lia.
  replace 2%N with (N.of_nat 2) by lia. rewrite <- Nofnat_pow. lia.
Qed.

(* The correctness represents the actual effect of flip all bits for the number x.
   The effect is to make the x number positions to store the value  2^n - 1 - x. *)
Lemma negator0_correct :
  forall n x f b0 b1,
    0 < n ->
    x < 2^n ->
    bcexec (negator0 n) (b0 ` b1 ` [x]_n f) = b0 ` b1 ` [2^n - 1 - x]_n f.
Proof.
  intros. unfold negator0. unfold reg_push. rewrite negator0'_correct by lia. rewrite negatem_arith; easy.
Qed.

Opaque negator0.
*)

(* The following implements an comparator. 
   THe first step is to adjust the adder circuit above to be
    MAJ;high_bit_manipulate;UMA.
    This is based on a binary number circuit observation that:
    To compare if x < y, we just need to do x - y, and see the high bit of the binary
    format of x - y. If the high_bit is zero, that means that x >= y;
    otherwise x < y. *)
Fixpoint nRZ (q:nat) (x:posi) (n:nat) := 
   match n with 0 => SKIP
             | S m => RZ q x; nRZ q x m 
   end.

Fixpoint sinv p :=
  match p with
  | SKIP => SKIP
  | X n => X n
  | CU n p => CU n (sinv p)
  | Seq p1 p2 => sinv p2; sinv p1
  | Lshift x => Rshift x
  | Rshift x => Lshift x
  | RZ q p1 => nRZ q p1 (2^q - 1)
  end.

Definition highb01 n x y c1 c2: scom := MAJseq n x y c1; CNOT (x,n) c2; sinv (MAJseq n x y c1).

(*
Lemma highb01_eWF :
  forall n,
    0 < n ->
    eWF (highb01 n).
Proof.
  intros. unfold highb01. constructor. constructor. unfold MAJseq. apply MAJseq'_eWF. easy.
  apply bccnot_eWF. lia. apply eWF_bcinv. unfold MAJseq. apply MAJseq'_eWF. easy.
Qed.

Lemma highb01_eWT :
  forall n dim,
    0 < n ->
    S (S (S (n + n))) < dim ->
    eWT dim (highb01 n).
Proof.
  intros. unfold highb01. constructor. constructor. unfold MAJseq. apply MAJseq'_eWT; lia.
  apply bccnot_eWT; lia. unfold MAJseq. apply bcinv_eWT. apply MAJseq'_eWT; lia.
Qed.

Local Opaque bccnot.
Lemma highb01_correct :
  forall n b f g h,
    0 < n ->
    bcexec (highb01 n) (b ` false ` fb_push_n n f (fb_push_n n g h))
             = b ` (carry b n f g) ` fb_push_n n f (fb_push_n n g h).
Proof.
  intros. unfold highb01. simpl. unfold MAJseq. rewrite MAJseq'_correct by lia.
  assert (forall u b0, bcexec (bccnot (S n) 1) (b0 ` false ` u) = b0 ` (u (n - 1)) ` u).
  { intros. rewrite bccnot_correct by lia. apply functional_extensionality; intro.
    bdestruct (x =? 1). subst. update_simpl. Local Opaque xorb. simpl.
    destruct n eqn:E. lia. simpl. rewrite Nat.sub_0_r. btauto.
    update_simpl. destruct x. easy. destruct x. lia. easy.
  }
  rewrite H0. fb_push_n_simpl.
  erewrite bcinv_reverse. 3: apply MAJseq'_correct; lia.
  unfold msma. IfExpSimpl. replace (S (n - 1)) with n by lia. easy.
  apply MAJseq'_eWF. easy.
Qed.

Opaque highb01.
*)
(* The actual comparator implementation. 
    We first flip the x positions, then use the high-bit comparator above. 
    Then, we use an inverse circuit of flipping x positions to turn the
    low bits back to store the value x.
    The actual implementation in the comparator is to do (x' + y)' as x - y,
    and then, the high-bit actually stores the boolean result of x - y < 0.  *)
Definition comparator01 n x y c1 c2 := (X c1; negator0 n x); highb01 n x y c1 c2; sinv (X c1; negator0 n x).

(*
Lemma comparator01_eWF :
  forall n,
    0 < n ->
    eWF (comparator01 n).
Proof.
  intros. unfold comparator01. repeat constructor. apply negator0_eWF. 
  apply highb01_eWF. easy. apply eWF_bcinv. apply negator0_eWF.
Qed.

Lemma comparator01_eWT :
  forall n dim,
    0 < n -> S (S (S (n + n))) < dim ->
    eWT dim (comparator01 n).
Proof.
  intros. unfold comparator01. constructor.
  constructor.  constructor. constructor. lia.
  apply negator0_eWT. lia. 
  apply highb01_eWT. easy. easy.
  simpl. constructor. apply bcinv_eWT. apply negator0_eWT.
  lia.  constructor. lia.
Qed.

Lemma negations_aux :
  forall n x f b,
    0 < n ->
    x < 2^n ->
    bcexec (bcx 0; negator0 n) (false ` b ` [x]_n f) = true ` b ` [2^n - 1 - x]_n f.
Proof.
  intros. simpl.
  assert ((false ` b ` [x ]_ n f) [0 |-> true] = true ` b ` [x]_n f).
  { apply functional_extensionality; intro i. destruct i; update_simpl; easy.
  }
  rewrite H1. apply negator0_correct; easy.
Qed.

Lemma pow2_predn :
  forall n x,
    x < 2^(n-1) -> x < 2^n.
Proof.
  intros. destruct n. simpl in *. lia.
  simpl in *. rewrite Nat.sub_0_r in H. lia.
Qed.

Lemma Ntestbit_lt_pow2n :
  forall x n,
    (x < 2^n)%N ->
    N.testbit x n = false.
Proof.
  intros. apply N.mod_small in H. rewrite <- H. apply N.mod_pow2_bits_high. lia.
Qed.

Lemma Ntestbit_in_pow2n_pow2Sn :
  forall x n,
    (2^n <= x < 2^(N.succ n))%N ->
    N.testbit x n = true.
Proof.
  intros. assert (N.log2 x = n) by (apply N.log2_unique; lia).
  rewrite <- H0. apply N.bit_log2.
  assert (2^n <> 0)%N by (apply N.pow_nonzero; easy).
  lia.
Qed.

Lemma carry_leb_equiv_true :
  forall n x y,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    x <= y ->
    carry true n (nat2fb (2^n - 1 - x)) (nat2fb y) = true.
Proof.
  intros. unfold nat2fb. specialize (carry_add_eq_carry1 n (N.of_nat (2 ^ n - 1 - x)) (N.of_nat y)) as G.
  do 2 apply xorb_move_l_r_2 in G. rewrite G.
  do 2 (pattern N2fb at 1; rewrite N2fb_Ntestbit).
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. apply pow2_predn in H1. lia.
  }
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
      assert (0 < 2^n) by (apply pow_positive; easy). lia.
  }
  replace 1%N with (N.of_nat 1) by easy. do 2 rewrite <- Nnat.Nat2N.inj_add.
  rewrite N2fb_Ntestbit. rewrite Ntestbit_in_pow2n_pow2Sn. btauto.
  split.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
  replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
  destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
  rewrite <- Nnat.Nat2N.inj_succ.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
  replace (2^(S n)) with (2^n + 2^n) by (simpl; lia).
  replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
  destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma carry_leb_equiv_false :
  forall n x y,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    x > y ->
    carry true n (nat2fb (2^n - 1 - x)) (nat2fb y) = false.
Proof.
  intros. unfold nat2fb. specialize (carry_add_eq_carry1 n (N.of_nat (2 ^ n - 1 - x)) (N.of_nat y)) as G.
  do 2 apply xorb_move_l_r_2 in G. rewrite G.
  do 2 (pattern N2fb at 1; rewrite N2fb_Ntestbit).
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow. apply pow2_predn in H1. lia.
  }
  rewrite Ntestbit_lt_pow2n.
  2:{ replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
      assert (0 < 2^n) by (apply pow_positive; easy). lia.
  }
  replace 1%N with (N.of_nat 1) by easy. do 2 rewrite <- Nnat.Nat2N.inj_add.
  rewrite N2fb_Ntestbit. rewrite Ntestbit_lt_pow2n. btauto.
  replace 2%N with (N.of_nat 2) by easy. rewrite <- Nofnat_pow.
  replace (2^n) with (2^(n-1) + 2^(n-1)). lia.
  destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
Qed.

Lemma carry_leb_equiv :
  forall n x y,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    carry true n (nat2fb (2^n - 1 - x)) (nat2fb y) = (x <=? y).
Proof.
  intros. bdestruct (x <=? y). apply carry_leb_equiv_true; easy. apply carry_leb_equiv_false; easy.
Qed.

*)
(* The correctness of comparator. We can see that the comparator will finally
   produce no changes to the positions storing values x and y, 
   but the high-bit will be a boolean predicate of(x <=? y). 
Lemma comparator01_correct :
  forall n x y f,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    bcexec (comparator01 n) (false ` false ` [x]_n [y]_n f) = (false ` (x <=? y) ` [x]_n [y]_n f).
Proof.
  intros. specialize (pow2_predn n x H0) as G0. specialize (pow2_predn n y H1) as G1.
  unfold comparator01. remember (bcx 0; negator0 n) as negations. simpl. subst.
  rewrite negations_aux by easy. unfold reg_push. rewrite highb01_correct by easy.
  erewrite bcinv_reverse. 3: apply negations_aux; easy. rewrite carry_leb_equiv by easy. easy.
  constructor. constructor. apply negator0_eWF.
Qed.

Opaque comparator01.
*)

(* The implementation of a subtractor. It takes two values [x][y], and the produces
    the result of [x][y + 2^n - x]. *)
Definition substractor01 n x y c1:= (X c1; negator0 n x); adder01 n x y c1; sinv (X c1; negator0 n x).

(*
Lemma substractor01_efresh:
   forall n, 0 < n -> efresh 1 (substractor01 n).
Proof.
  intros.
  unfold substractor01.
  constructor. constructor.
  constructor. constructor.
  lia.
  apply negator0_efresh.
  apply adder01_efresh.
  assumption.
  apply efresh_bcinv.
  constructor. constructor.
  lia.
  apply negator0_efresh.
Qed.

Lemma substractor01_eWF:
   forall n, 0 < n -> eWF (substractor01 n).
Proof.
  intros.
  unfold substractor01.
  constructor. constructor.
  constructor. constructor.
  apply negator0_eWF.
  apply adder01_eWF.
  assumption.
  apply eWF_bcinv.
  constructor. constructor.
  apply negator0_eWF.
Qed.

Lemma substractor01_eWT:
   forall n dim, 0 < n -> S (S (S (n + n))) < dim -> eWT dim (substractor01 n).
Proof.
  intros.
  unfold substractor01.
  constructor. constructor.
  constructor. constructor. lia.
  apply negator0_eWT. lia.
  apply adder01_eWT.
  assumption. lia.
  simpl. constructor.
  apply bcinv_eWT. 
  apply negator0_eWT. lia.
  constructor. lia.
Qed.

(* The correctness proof of the substractor. *)
Lemma substractor01_correct :
  forall n x y b1 f,
    0 < n ->
    x < 2^(n-1) ->
    y < 2^(n-1) ->
    bcexec (substractor01 n) (false ` b1 ` [x]_n [y]_n f) = (false ` b1 ` [x]_n [y + 2^n - x]_n f).
Proof.
  intros. specialize (pow2_predn n x H0) as G0. specialize (pow2_predn n y H1) as G1.
  unfold substractor01. remember (bcx 0; negator0 n) as negations. simpl. subst.
  rewrite negations_aux by easy. rewrite adder01_correct_carry1 by easy.
  erewrite bcinv_reverse. 3: apply negations_aux; easy.
  replace (2^n) with (2^(n-1) + 2^(n-1)).
  replace (2 ^ (n - 1) + 2 ^ (n - 1) - 1 - x + y + 1) with (y + (2 ^ (n - 1) + 2 ^ (n - 1)) - x) by lia.
  easy. destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
  constructor. constructor. apply negator0_eWF.
Qed.

Opaque substractor01.
*)

(* The implementation of a modulo adder. It takes [M][x][y], and then produces the result of [M][x+y % M][y]. 
   The modulo operation is not reversible. It will flip the high-bit to be the comparator factor.
   To flip the high-bit to zero, we use the inverse circuit of the comparator in the modulo adder to
   flip the high-bit back to zero.*)
Definition modadder21 n x y M c1 c2 := adder01 n y x c1 ; (*  adding y to x *)
                                       comparator01 n M x c1 c2; (* compare M < x + y (in position x) *)
                                       CU c2 (substractor01 n M x c1) ; X c2; (* doing -M + x to x, then flip c2. *)
                                       comparator01 n y x c1 c2. (* compare M with x+y % M to clean c2. *)
         
(*
Lemma modadder21_eWF:
 forall n, 0 < n -> eWF (modadder21 n).
Proof.
  intros. unfold modadder21.
  constructor.  constructor.
  constructor.  constructor.
  constructor.  constructor.
  constructor. 
  apply swapper02_eWF.
  apply adder01_eWF.
  assumption.
  apply swapper02_eWF.
  apply comparator01_eWF.
  assumption.
  constructor. constructor.
  apply substractor01_efresh.
  lia.
  apply substractor01_eWF.
  lia.
  constructor. 
  apply swapper02_eWF.
  apply eWF_bcinv. 
  apply comparator01_eWF.
  lia.   apply swapper02_eWF.
Qed.

Lemma modadder21_eWT:
 forall n dim, 0 < n -> 2 + n + n + n < dim -> eWT dim (modadder21 n).
Proof.
  intros. unfold modadder21.
  constructor.  constructor.
  constructor.  constructor.
  constructor.  constructor.
  constructor. 
  apply swapper02_eWT. lia.
  apply adder01_eWT.
  assumption. lia.
  apply swapper02_eWT; lia.
  apply comparator01_eWT; lia.
  constructor. constructor. lia.
  apply substractor01_efresh.
  lia.
  apply substractor01_eWT.
  lia. lia.
  constructor. lia. 
  apply swapper02_eWT;lia.
  apply bcinv_eWT.
  apply comparator01_eWT; lia.
  apply swapper02_eWT;lia.
Qed.

Lemma mod_sum_lt :
  forall x y M,
    x < M ->
    y < M ->
    (x + y) mod M < x <-> x + y >= M.
Proof.
  intros. split; intros.
  - assert ((x + y) mod M < x + y) by lia.
    rewrite Nat.div_mod with (y := M) in H2 by lia.
    assert (0 < (x + y) / M) by nia.
    rewrite Nat.div_str_pos_iff in H3 by lia. lia.
  - rewrite Nat.mod_eq by lia.
    assert (1 <= (x + y) / M < 2).
    { split.
      apply Nat.div_le_lower_bound; lia.
      apply Nat.div_lt_upper_bound; lia.
    }
    replace (M * ((x + y) / M)) with M by nia.
    lia.
Qed.

Lemma mod_sum_lt_bool :
  forall x y M,
    x < M ->
    y < M ->
    ¬ (M <=? x + y) = (x <=? (x + y) mod M).
Proof.
  intros. bdestruct (M <=? x + y); bdestruct (x <=? (x + y) mod M); try easy.
  assert ((x + y) mod M < x) by (apply mod_sum_lt; lia). lia.
  assert (x + y >= M) by (apply mod_sum_lt; lia). lia.
Qed.

(* The correctness statement of the modulo adder. *)
Lemma modadder21_correct :
  forall n x y M f,
    1 < n ->
    x < M ->
    y < M ->
    M < 2^(n-2) ->
    bcexec (modadder21 n) (false ` false ` [M]_n [y]_n [x]_n f) = false ` false ` [M]_n [(x + y) mod M]_n [x]_n  f.
Proof.
  intros.
  assert (M < 2^(n-1)).
  { apply pow2_predn. replace (n - 1 - 1) with (n - 2) by lia. easy.
  }
  assert (x + y < 2^(n-1)).
  { replace (2^(n-1)) with (2^(n-2) + 2^(n-2)). lia.
    destruct n. lia. destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
  }
  unfold modadder21. remember (bccont 1 (substractor01 n); bcx 1) as csub01. simpl. subst.
  rewrite swapper02_correct by lia. rewrite adder01_correct_carry0 by lia.
  rewrite swapper02_correct by lia. rewrite comparator01_correct by lia.
  replace (bcexec (bccont 1 (substractor01 n); bcx 1)
      (false ` (M <=? x + y) ` [M ]_ n [x + y ]_ n [x ]_ n f))
              with (false ` ¬ (M <=? x + y) ` [M ]_ n [(x + y) mod M]_ n [x ]_ n f). 
  2:{ simpl. bdestruct (M <=? x + y).
      - rewrite substractor01_correct by lia.
        replace (x + y + 2^n - M) with (x + y - M + 2^n) by lia.
        rewrite reg_push_exceed with (x := x + y - M + 2 ^ n).
        assert (2^n <> 0) by (apply Nat.pow_nonzero; easy).
        rewrite <- Nat.add_mod_idemp_r with (a := x + y - M) by easy.
        rewrite Nat.mod_same by easy.
        rewrite Nat.add_0_r. rewrite <- reg_push_exceed.
        rewrite Nat.mod_eq by lia.
        assert (x + y < 2 * M) by lia.
        assert ((x + y) / M < 2) by (apply Nat.div_lt_upper_bound; lia).
        assert (1 <= (x + y) / M) by (apply Nat.div_le_lower_bound; lia).
        assert ((x + y) / M = 1) by lia.
        replace (x + y - M * ((x + y) / M)) with (x + y - M) by lia.
        apply functional_extensionality; intro i.
        destruct i. easy. destruct i. simpl. update_simpl. easy. update_simpl. easy.
      - rewrite Nat.mod_small by lia. 
        apply functional_extensionality; intro i.
        destruct i. easy. destruct i. simpl. update_simpl. easy. update_simpl. easy.
  }
  rewrite swapper02_correct by lia. erewrite bcinv_reverse.
  3:{ assert ((x + y) mod M < M) by (apply Nat.mod_upper_bound; lia).
      rewrite mod_sum_lt_bool by easy. rewrite comparator01_correct. reflexivity.
      1-3 : lia.
  }
  rewrite swapper02_correct by lia. easy.
  apply comparator01_eWF. lia.
Qed.

Opaque modadder21.
*)
(* The swapper12 swaps the [x][y][z] to be [x][z][y]. 
Fixpoint swapper12' i n :=
  match i with
  | 0 => bcskip
  | S i' => swapper12' i' n; bcswap (2 + n + i') (2 + n + n + i')
  end.
Definition swapper12 n := swapper12' n n.

Lemma swapper12'_eWF:
  forall i n, eWF (swapper12' i n).
Proof.
  intros.
  induction i.
  simpl.
  apply eWF_skip.
  simpl. apply eWF_seq.
  apply IHi. apply bcswap_eWF.
Qed.

Lemma swapper12'_eWT:
  forall i n dim, (2 + n + n + i) < dim -> eWT dim (swapper12' i n).
Proof.
  intros.
  induction i.
  simpl. constructor. lia.
  simpl. constructor.
  apply IHi. lia. apply bcswap_eWT; lia.
Qed.

Lemma swapper12_eWF:
  forall n, eWF (swapper12 n).
Proof.
 intros. unfold swapper12. apply swapper12'_eWF.
Qed.

Lemma swapper12_eWT:
  forall n dim, (2 + n + n + n) < dim -> eWT dim (swapper12 n).
Proof.
 intros. unfold swapper12. apply swapper12'_eWT. lia.
Qed.

Local Opaque bcswap.
Lemma swapper12'_correct :
  forall i n f g h u b1 b2,
    0 < n ->
    i <= n ->
    bcexec (swapper12' i n) (b1 ` b2 ` fb_push_n n f (fb_push_n n g (fb_push_n n h u)))
                 = b1 ` b2 ` fb_push_n n f (fb_push_n n (swapma i g h) (fb_push_n n (swapmb i g h) u)).
Proof.
  induction i; intros.
  - simpl.
    replace (swapma 0 f h) with f by (apply functional_extensionality; intro; IfExpSimpl; easy).
    replace (swapmb 0 f h) with h by (apply functional_extensionality; intro; IfExpSimpl; easy).
    easy.
  - simpl. rewrite IHi by lia.
    apply functional_extensionality; intro. rewrite bcswap_correct by lia.
    bdestruct (x =? S (S (n + i))). subst. simpl. fb_push_n_simpl. 
    unfold swapma, swapmb. IfExpSimpl. replace (n + n + i - n - n) with (n + i - n) by lia. easy.
    bdestruct (x =? S (S (n + n + i))). subst. simpl. fb_push_n_simpl. 
    unfold swapma, swapmb. IfExpSimpl. replace (n + n + i - n - n) with (n + i - n) by lia. easy.
    destruct x. easy. simpl. destruct x. easy. simpl.
    bdestruct (x <? n). fb_push_n_simpl. easy. 
    bdestruct (x <? n + n). fb_push_n_simpl. unfold swapma. IfExpSimpl; easy.
    bdestruct (x <? n + n + n). fb_push_n_simpl. unfold swapmb. IfExpSimpl; easy.
    fb_push_n_simpl. easy.
Qed.

Lemma swapper12_correct :
  forall n x y z f b0 b1,
    0 < n ->
    bcexec (swapper12 n) (b0 ` b1 ` [x]_n [y]_n [z]_n f) = b0 ` b1 ` [x]_n [z]_n [y]_n f.
Proof.
  intros. unfold reg_push, swapper12. rewrite swapper12'_correct by lia.
  rewrite swapma_gtn_invariant. rewrite swapmb_gtn_invariant. easy.
Qed.

Opaque swapper12.
*)
(* Here we implement the doubler circuit based on binary shift operation.
   It assumes an n-1 value x that live in a cell of n-bits (so the high-bit must be zero). 
   Then, we shift one position, so that the value looks like 2*x in a n-bit cell. *)
Definition doubler1 y := Lshift y.

(*
Fixpoint doubler1' i n :=
  match i with
  | 0 => bcskip
  | S i' => bcswap (n + i') (n + i); doubler1' i' n
  end.
Definition doubler1 n := doubler1' (n - 1) (2 + n).

Definition double_prop x n (f:nat -> bool) :=
         fun i => if i <? n then f i
                   else if i =? n then f (n + x)
                   else if (n <? i) && (i <=? n + x) then f (i-1) else f i.


Lemma doubler1'_eWF :
  forall i n, eWF (doubler1' i n).
Proof.
  intros.
  induction i.
  simpl. constructor. 
  simpl. constructor. 
  apply bcswap_eWF.
  apply IHi.  
Qed.

Lemma doubler1'_eWT :
  forall i n dim, (n + i) < dim -> eWT dim (doubler1' i n).
Proof.
  intros.
  induction i.
  simpl. constructor. 
  simpl. lia. 
  simpl. constructor. 
  apply bcswap_eWT; lia.
  apply IHi. lia.  
Qed.

Lemma doubler1_eWF :
  forall n, eWF (doubler1 n).
Proof.
  intros. unfold doubler1. apply doubler1'_eWF.
Qed.

Lemma doubler1_eWT :
  forall n dim, 0 < n -> (n + n + 1) < dim -> eWT dim (doubler1 n).
Proof.
  intros. unfold doubler1. apply doubler1'_eWT; lia.
Qed.

Lemma N_inj_pow: forall n, (N.of_nat (2 ^ n) = 2 ^ (N.of_nat n))%N.
Proof.
  intros.
 induction n.
 simpl. rewrite N.pow_0_r.
 reflexivity.
 simpl.
 assert (N.pos (Pos.of_succ_nat n) = N.succ (N.of_nat n)) by lia.
 rewrite H.
 rewrite N.pow_succ_r.
 rewrite <- IHn. lia. lia.
Qed.

(* This lemma says that if x is a value less than 2^(n-1), then the highest bit of
   the n-bit cell is zero. *)
Lemma reg_push_high_bit_zero:
   forall n x f, 
    0 < n -> x < 2^(n-1) -> ([x]_n f) (n - 1) = false.
Proof.
  intros. unfold reg_push. unfold nat2fb.
  fb_push_n_simpl.
  rewrite N2fb_Ntestbit.
  rewrite Ntestbit_lt_pow2n.
  reflexivity.
  apply N2Z.inj_lt.
  assert (N.of_nat ( 2 ^ (n - 1)) = (2 ^ N.of_nat (n - 1)))%N.
  rewrite N_inj_pow.
  reflexivity.
  rewrite <- H1.
  rewrite nat_N_Z.
  rewrite nat_N_Z.
  apply Nat2Z.inj_lt.
  assumption.
Qed.

(* This is a generalized case of the above lemma. *)
Lemma reg_push_high_bit_gen_zero:
   forall i m n x f,
    0 < n -> i <= m < n -> x < 2^i -> ([x]_n f) m = false.
Proof.
  intros. unfold reg_push. unfold nat2fb.
  fb_push_n_simpl.
  rewrite N2fb_Ntestbit.
  rewrite Ntestbit_lt_pow2n.
  reflexivity.
  apply N2Z.inj_lt.
  assert (N.of_nat ( 2 ^ m) = (2 ^ N.of_nat m))%N.
  rewrite N_inj_pow.
  reflexivity.
  rewrite <- H2.
  rewrite nat_N_Z.
  rewrite nat_N_Z.
  apply Nat2Z.inj_lt.
  assert (2 ^ i <= 2 ^ m).
  apply Nat.pow_le_mono_r.
  1 - 3 : lia.
Qed.

(* This is a generalized case of the above lemma in terms of making the case for
   any value x located in any places in a bool function. *)
Lemma reg_push_high_bit_gen_zero_1:
  forall i m n x y f b0 b1,
    0 < n -> i <= m < n ->
    y < 2^i -> (b0 ` b1 ` [x]_n [y]_n f) (2 + n + m) = false.
Proof.
  intros.
  rewrite fb_push_right by lia. rewrite fb_push_right by lia.
  assert (([x ]_ n [y ]_ n f) (2 + n + m - 1 - 1)
         = ([y ]_ n f) ((2 + n + m - 1 - 1) - n)).
  unfold reg_push.
  rewrite fb_push_n_right.
  reflexivity.
  lia.
  rewrite H2.
  assert ((2 + n + m - 1 - 1 - n) = m) by lia.
  rewrite H3.
  rewrite (reg_push_high_bit_gen_zero i).
  reflexivity.
  1 - 3 : assumption.
Qed.

Lemma bcswap_same: forall a b f, f a = f b -> bcexec (bcswap a b) f = f.
Proof.
  intros.
  rewrite bcswap_correct.
  apply functional_extensionality; intros.
  bdestruct (x =? a).
  rewrite <- H. rewrite H0.
  reflexivity.
  bdestruct (x =? b).
  rewrite H. rewrite H1.
  reflexivity.
  reflexivity.
Qed.

Lemma bcswap_neq :
  forall a b c f, a <> c -> b <> c -> bcexec (bcswap a b) f c = f c.
Proof.
  intros.
  rewrite bcswap_correct.
  IfExpSimpl.
  reflexivity.
Qed.

Definition times_two_spec (f:nat -> bool) :=  fun i => if i =? 0 then false else f (i-1).

(* Showing the times_two spec is correct. *)

Lemma nat2fb_even_0:
  forall x, nat2fb (2 * x) 0 = false.
Proof.
  intros.
  unfold nat2fb.
  rewrite Nat2N.inj_double.
  unfold N.double.
  destruct (N.of_nat x).
  unfold N2fb,allfalse.
  reflexivity.
  unfold N2fb.
  simpl.
  reflexivity.
Qed.

Lemma pos2fb_times_two_eq:
  forall p x, x <> 0 -> pos2fb p (x - 1) = pos2fb p~0 x.
Proof.
  intros.
  induction p.
  simpl.
  assert ((false ` true ` pos2fb p) x = (true ` pos2fb p) (x - 1)).
  rewrite fb_push_right.
  reflexivity. lia.
  rewrite H0.
  reflexivity.
  simpl.
  rewrite (fb_push_right x).
  reflexivity. lia.
  simpl.
  rewrite (fb_push_right x).
  reflexivity. lia.
Qed.

Lemma times_two_correct:
   forall n x, 0 < n -> x < 2^(n-1)
         -> (times_two_spec (nat2fb x)) = (nat2fb (2*x)).
Proof.
  intros.
  unfold times_two_spec.
  apply functional_extensionality; intros.
  unfold nat2fb.
  bdestruct (x0 =? 0).
  rewrite H1.
  specialize (nat2fb_even_0 x) as H2.
  unfold nat2fb in H2.
  rewrite H2.
  reflexivity.
  rewrite Nat2N.inj_double.
  unfold N.double,N2fb.
  destruct (N.of_nat x).
  unfold allfalse.
  reflexivity.
  rewrite pos2fb_times_two_eq.
  reflexivity. lia.
Qed.

Lemma doubler1_correct_aux :
  forall i n f, bcexec (doubler1' i n) f = double_prop i n f.
Proof.
  intros i.
  induction i.
  unfold double_prop.
  simpl.
  intros.
  apply functional_extensionality; intros.
  bdestruct (x <? n).
  reflexivity.
  bdestruct (x =? n).
  rewrite H0.
  rewrite Nat.add_0_r.
  reflexivity.
  bdestruct (n <? x).
  bdestruct (x <=? n + 0).
  lia.
  simpl.
  reflexivity.
  simpl. reflexivity.
  intros.
  simpl.
  rewrite IHi.
  unfold double_prop.
  apply functional_extensionality; intros.
  IfExpSimpl.
  rewrite bcswap_neq.
  reflexivity. lia. lia.
  rewrite bcswap_correct.
  IfExpSimpl.
  reflexivity.
  bdestruct (n <? x).
  bdestruct ((x <=? n + i)).
  simpl.
  rewrite bcswap_correct.
  bdestruct (x - 1 =? n + i). lia.
  bdestruct (x - 1 =? n + S i).
  lia.
  bdestruct (x <=? n + S i).
  reflexivity.
  lia.
  simpl.
  rewrite bcswap_correct.
  bdestruct (x =? n + i).
  lia.
  bdestruct (x =? n + S i).
  bdestruct (x <=? n + S i). subst.
  assert (n + S i - 1 = n + i) by lia.
  rewrite H4. reflexivity.
  lia.
  bdestruct (x <=? n + S i). lia.
  reflexivity.
  simpl.
  assert (x = n) by lia.
  rewrite bcswap_correct.
  bdestruct (x =? n + i).
  lia.
  bdestruct (x =? n + S i). 
  lia.
  reflexivity.
Qed.

(* This is the correctness statement and proof of the doubler. *)
Lemma doubler1_correct :
  forall n x y f b0 b1,
    0 < n ->
    y < 2^(n - 1) ->
    bcexec (doubler1 n) (b0 ` b1 ` [x]_n [y]_n f) = b0 ` b1 ` [x]_n [2 * y]_n f.
Proof.
  intros.
  unfold doubler1.
  rewrite doubler1_correct_aux; try lia.
  apply functional_extensionality; intros.
  unfold double_prop.
  bdestruct (x0 <? 2 + n).
  destruct x0. simpl. reflexivity.
  rewrite fb_push_right by lia.
  rewrite (fb_push_right (S x0)) by lia.
  assert ((S x0 - 1) = x0) by lia.
  rewrite H2.
  destruct x0. simpl. reflexivity.
  rewrite fb_push_right by lia.
  rewrite (fb_push_right (S x0)) by lia.
  assert ((S x0 - 1) = x0) by lia.
  rewrite H3.
  rewrite reg_push_inv by lia.
  rewrite reg_push_inv by lia.
  reflexivity.
  bdestruct (x0 =? 2 + n).
  rewrite H2.
  repeat rewrite fb_push_right by lia.
  assert (([x ]_ n [y ]_ n f) (2 + n + (n - 1) - 1 - 1)
            = ([y ]_ n f) ((2 + n + (n - 1) - 1 - 1) - n)).
  unfold reg_push.
  rewrite fb_push_n_right by lia.
  reflexivity.
  rewrite H3.
  assert (([x ]_ n [2 * y ]_ n f) (2 + n - 1 - 1) 
          = ([2 * y ]_ n f) (2 + n - 1 - 1 - n)).
  unfold reg_push.
  rewrite fb_push_n_right by lia.
  reflexivity.
  rewrite H4.
  assert ((2 + n + (n - 1) - 1 - 1 - n) = n - 1) by lia.
  rewrite H5.
  rewrite reg_push_high_bit_zero by lia.
  assert ( (2 + n - 1 - 1 - n) = 0) by lia.
  rewrite H6.
  rewrite reg_push_inv by lia.
  rewrite nat2fb_even_0.
  reflexivity.
  bdestruct ((2 + n <? x0)).
  bdestruct ((x0 <=? 2 + n + (n - 1))).
  simpl.
  repeat rewrite fb_push_right by lia.
  assert (([x ]_ n [y ]_ n f) (x0 - 1 - 1 - 1)
       = ([y ]_ n f) (x0 - 1 - 1 - 1 - n)).
  unfold reg_push.
  rewrite fb_push_n_right by lia.
  reflexivity.
  assert (([x ]_ n [y + (y + 0) ]_ n f) (x0 - 1 - 1)
        = ([y + (y + 0) ]_ n f) (x0 - 1 - 1 - n)).
  unfold reg_push.
  rewrite fb_push_n_right by lia.
  reflexivity.
  rewrite H5. rewrite H6.
  assert (y + (y + 0) = 2 * y) by lia.
  rewrite H7.
  remember (x0 - (2 + n)) as y0.
  assert ((x0 - 1 - 1 - 1 - n) = y0 - 1) by lia.
  assert ((x0 - 1 - 1 - n) = y0) by lia.
  rewrite H8. rewrite H9.
  repeat rewrite reg_push_inv by lia.
  rewrite <- (times_two_correct n).
  unfold times_two_spec.
  bdestruct (y0 =? 0).
  lia.
  reflexivity.
  1 - 2 : lia.
  simpl.
  repeat rewrite fb_push_right by lia.
  unfold reg_push.
  repeat rewrite fb_push_n_right by lia.
  reflexivity.
  lia.
Qed.

Opaque doubler1.
*)

(* Another version of the mod adder only for computing [x][M] -> [2*x % M][M].
   This version will mark the high-bit, and the high-bit is not clearable.
   However, eventually, we will clean all high-bit
   by using a inverse circuit of the whole implementation. *)
Definition moddoubler01 n x M c1 c2 :=
                doubler1 x; comparator01 n x M c1 c2; CU c2 (substractor01 n x M c1).
(*
Lemma moddoubler01_eWF :
  forall n, 0 < n -> eWF (moddoubler01 n).
Proof.
  intros.
  unfold moddoubler01.
  constructor. constructor.
  apply doubler1_eWF. 
  apply comparator01_eWF.
  lia. 
  constructor. 
  apply substractor01_efresh.
  lia. 
  apply substractor01_eWF.
  lia. 
Qed.

Lemma moddoubler01_eWT :
  forall n dim, 0 < n -> (n + n + 3) < dim -> eWT dim (moddoubler01 n).
Proof.
  intros.
  unfold moddoubler01.
  constructor. constructor.
  apply doubler1_eWT; lia. 
  apply comparator01_eWT;lia.
  constructor. lia. 
  apply substractor01_efresh.
  lia. 
  apply substractor01_eWT;lia.
Qed.

(* The correctness statement and proof of the mod doubler.  *)
Lemma moddoubler01_correct :
  forall n M x f,
    1 < n ->
    x < M ->
    M < 2^(n - 2) ->
    bcexec (moddoubler01 n) (false ` false ` [M]_n [x]_n f) = false ` (M <=? 2 * x) ` [M]_n [2 * x mod M]_n f.
Proof.
  intros.
  assert (M < 2^(n-1)).
  { apply pow2_predn. replace (n - 1 - 1) with (n - 2) by lia. easy.
  }
  assert (x + x < 2^(n-1)).
  { replace (2^(n-1)) with (2^(n-2) + 2^(n-2)). lia.
    destruct n. lia. destruct n. lia. simpl. rewrite Nat.sub_0_r. lia.
  }
 unfold moddoubler01.
 rewrite bcseq_correct.
 rewrite bcseq_correct.
 rewrite doubler1_correct; try lia.
 rewrite comparator01_correct; try lia.
 simpl. bdestruct (M <=? x + (x + 0)).
  - rewrite substractor01_correct; try lia.
    replace (x + (x + 0) + 2 ^ n - M) with (x + (x + 0) - M + 2^n) by lia.
    rewrite reg_push_exceed with (x := (x + (x + 0) - M + 2^n)).
    assert (2^n <> 0) by (apply Nat.pow_nonzero; easy).
    rewrite <- Nat.add_mod_idemp_r with (a := x + (x + 0) - M) by easy.
    rewrite Nat.mod_same by easy.
    rewrite Nat.add_0_r. rewrite <- reg_push_exceed.
    rewrite Nat.add_0_r. rewrite Nat.add_0_r in H4.
    rewrite Nat.mod_eq by lia.
    assert (x + x < 2 * M) by lia.
    assert ((x + x) / M < 2) by (apply Nat.div_lt_upper_bound; lia).
    assert (1 <= (x + x) / M) by (apply Nat.div_le_lower_bound; lia).
    assert ((x + x) / M = 1) by lia.
    replace (x + x - M * ((x + x) / M)) with (x + x - M) by lia.
    reflexivity.
  - rewrite Nat.mod_small by lia. 
    reflexivity.
Qed.

Opaque moddoubler01.
*)
(* A new version of the modulo adder to do addition only [y][x] -> [y][x+y mod M]. *)
(*
Definition modadder12 n := swapper12 n; modadder21 n; swapper12 n.

Lemma modadder12_eWF :
  forall n, 0 < n -> eWF (modadder12 n).
Proof.
  intros.
  unfold modadder12.
  apply eWF_seq.
  apply eWF_seq.
  apply swapper12_eWF.
  apply modadder21_eWF.
  lia. 
  apply swapper12_eWF.
Qed.

Lemma modadder12_eWT :
  forall n dim, 0 < n -> 2 + n + n + n < dim -> eWT dim (modadder12 n).
Proof.
  intros.
  unfold modadder12.
  constructor. constructor. 
  apply swapper12_eWT;lia.
  apply modadder21_eWT;lia.
  apply swapper12_eWT;lia.
Qed.

(* The correctness statement and proof of the second mod adder. *)
Lemma modadder12_correct :
  forall n x y M f,
    1 < n ->
    x < M ->
    y < M ->
    M < 2^(n-2) ->
    bcexec (modadder12 n) (false ` false ` [M]_n [x]_n [y]_n f) = false ` false ` [M]_n [x]_n [(x + y) mod M]_n f.
Proof.
 intros.
 unfold modadder12.
 rewrite bcseq_correct.
 rewrite bcseq_correct.
 rewrite swapper12_correct by lia.
 rewrite modadder21_correct; try lia.
 rewrite swapper12_correct by lia.
 reflexivity.
Qed.

Opaque modadder12.
*)
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
Definition fb_push b f : nat -> bool :=
  fun x => match x with
        | O => b
        | S n => f n
        end.

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

(*
Lemma modsummer'_eWF :
  forall i n f, 0 < n -> eWF (modsummer' i n f).
Proof.
  intros.
  induction i.
  simpl.
  destruct (f 0).
  apply modadder12_eWF.
  lia. 
  constructor. 
  simpl.
  constructor. constructor. constructor.  
  apply IHi.
  apply moddoubler01_eWF.
  lia. 
  apply bcswap_eWF.
  destruct (f (S i)).
  apply modadder12_eWF.
  lia. constructor. 
Qed.

Lemma modsummer'_eWT :
  forall i n f dim, 0 < n ->
       (2 + n + n + n + i) < dim -> eWT dim (modsummer' i n f).
Proof.
  intros.
  induction i.
  simpl.
  destruct (f 0).
  apply modadder12_eWT;lia. 
  constructor. lia. 
  simpl.
  constructor. constructor. constructor.  
  apply IHi. lia.
  apply moddoubler01_eWT;lia.
  apply bcswap_eWT;lia.
  destruct (f (S i)).
  apply modadder12_eWT;lia.
  constructor. lia. 
Qed.

Lemma modsummer_eWF :
  forall n C, 0 < n ->  eWF (modsummer n C).
Proof.
  intros. unfold modsummer. 
  apply modsummer'_eWF.
  lia.
Qed. 

Lemma modsummer_eWT :
  forall n C dim, 0 < n -> (2 + n + n + n + n) < dim -> eWT dim (modsummer n C).
Proof.
  intros. unfold modsummer. 
  apply modsummer'_eWT;lia.
Qed. 

Definition hbf n M x := fun (i : nat) =>
                          if (i =? 0) then false
                          else if (i <=? n)
                               then (M <=? 2 * ((2^(i-1) * x) mod M)) else false.
Fixpoint natsum n (f : nat -> nat) :=
  match n with
  | 0 => 0
  | S n' => f n' + natsum n' f
  end.

Lemma natsum_mod :
  forall n f M,
    M <> 0 ->
    (natsum n f) mod M = natsum n (fun i => f i mod M) mod M.
Proof.
  induction n; intros. easy.
  simpl. rewrite Nat.add_mod by easy. rewrite IHn by easy. 
  rewrite <- Nat.add_mod by easy. rewrite Nat.add_mod_idemp_l by easy. easy.
Qed.

Lemma parity_decompose :
  forall n, exists k, n = 2 * k \/ n = 2 * k + 1.
Proof.
  induction n. exists 0. lia. 
  destruct IHn as [k [H | H]]. exists k. lia. exists (S k). lia.
Qed.

Lemma Natodd_Ntestbit_even :
  forall k, Nat.odd (2 * k) = N.testbit (N.of_nat (2 * k)) 0.
Proof.
  induction k. easy.
  replace (2 * (S k)) with (S (S (2 * k))) by lia.
  rewrite Nat.odd_succ_succ. rewrite IHk.
  do 2 rewrite N.bit0_odd.
  replace (N.of_nat (S (S (2 * k)))) 
   with (N.succ (N.succ (N.of_nat (2 * k)))) by lia.
   rewrite N.odd_succ_succ. easy.
Qed.

Lemma Natodd_Ntestbit_odd :
  forall k, Nat.odd (2 * k + 1) = N.testbit (N.of_nat (2 * k + 1)) 0.
Proof.
  induction k. easy.
  replace (2 * (S k) + 1) with (S (S (2 * k + 1))) by lia.
  rewrite Nat.odd_succ_succ. rewrite IHk.
  do 2 rewrite N.bit0_odd.
  replace (N.of_nat (S (S (2 * k + 1)))) 
     with (N.succ (N.succ (N.of_nat (2 * k + 1)))) by lia.
  rewrite N.odd_succ_succ. easy.
Qed.

Lemma nat_is_odd_testbit:
  forall n, N.testbit (N.of_nat n) 0 = true -> Nat.odd n = true.
Proof.
  intros.
  specialize (parity_decompose n) as [k [Hk | Hk]]; subst.
  rewrite Natodd_Ntestbit_even.
  assumption.
  rewrite Natodd_Ntestbit_odd.
  assumption.
Qed.

Lemma nat_is_even_testbit:
  forall n, N.testbit (N.of_nat n) 0 = false -> Nat.even n = true.
Proof.
  intros.
  assert (Nat.odd n = false).
  specialize (parity_decompose n) as [k [Hk | Hk]]; subst.
  rewrite Natodd_Ntestbit_even.
  assumption.
  rewrite Natodd_Ntestbit_odd.
  assumption.
  unfold Nat.odd in H0.
  apply negb_false_iff in H0.
  assumption.
Qed.
            

Lemma Nattestbit_Ntestbit :
  forall m n,
    Nat.testbit n m = N.testbit (N.of_nat n) (N.of_nat m).
Proof.
  induction m; intros. simpl. specialize (parity_decompose n) as [k [Hk | Hk]]; subst.
   apply Natodd_Ntestbit_even. apply Natodd_Ntestbit_odd.
  remember (N.of_nat (S m)) as NSm. simpl. rewrite IHm. rewrite Nnat.Nat2N.inj_div2.
   rewrite <- N.testbit_succ_r_div2 by lia. subst. rewrite Nnat.Nat2N.inj_succ. easy.
Qed.  

Definition bindecomp n x := natsum n (fun i => Nat.b2n ((nat2fb x) i) * 2^i).

Lemma bindecomp_spec :
  forall n x,
    bindecomp n x = x mod 2^n.
Proof.
  unfold bindecomp. induction n; intros. easy.
  simpl. rewrite IHn. unfold nat2fb. rewrite N2fb_Ntestbit. rewrite <- Nattestbit_Ntestbit.
  rewrite Nat.testbit_spec'. replace (2 ^ n + (2 ^ n + 0)) with ((2 ^ n) * 2) by lia. 
  rewrite Nat.mod_mul_r. lia. apply Nat.pow_nonzero. easy. easy.
Qed.

Lemma bindecomp_seq :
  forall n x, bindecomp (S n) x = bindecomp n x + Nat.b2n ((nat2fb x) n) * 2^n.
Proof.
 intros.
 unfold bindecomp.
 simpl. lia.
Qed.

Lemma modsummer'_correct :
  forall i n x y M C,
    i < n ->
    1 < n ->
    x < M ->
    y < M ->
    C < M ->
    M < 2^(n-2) ->
    bcexec (modsummer' i n (nat2fb C)) (false ` false ` [M]_n [x]_n [y]_n allfalse)
          = false ` false ` [M]_n [2^i * x mod M]_n
                     [((bindecomp (i+1) C) * x + y) mod M]_n (hbf i M x).
Proof.
  intros.
  induction i.
  simpl.
  unfold nat2fb.
  assert ((fun i : nat =>
     if i =? 0
     then false
     else
      if i <=? 0
      then M <=? (2 ^ (i - 1) * x) mod M + ((2 ^ (i - 1) * x) mod M + 0)
      else false)
              = (fun _ : nat => false)).
  apply functional_extensionality.
  intros. bdestruct (x0 =? 0). reflexivity.
  bdestruct (x0 <=? 0).
  lia. reflexivity.
  destruct (N2fb (N.of_nat C) 0) eqn:eq.
  rewrite N2fb_Ntestbit in eq.
  unfold hbf,allfalse. simpl. rewrite H5.
  rewrite bindecomp_spec.
  apply nat_is_odd_testbit in eq.
  apply Nat.odd_spec in eq.
  assert (2 ^ 1 = 2) by easy.
  rewrite H6.
  assert (0 <= C) by lia.
  assert (0 < 2) by lia.
  specialize (Nat.mod_bound_pos C 2 H7 H8) as eq1.
  assert (C mod 2 = 0 \/ C mod 2 = 1) by lia.
  destruct H9.
  unfold Nat.Odd in eq.
  destruct eq.
  rewrite H10 in H9.
  assert (2 * x0 + 1 = 1 + x0 * 2) by lia.
  rewrite H11 in H9.
  rewrite Nat.mod_add in H9.
  easy. lia.
  rewrite H9.
  rewrite Nat.add_0_r.
  rewrite Nat.mul_1_l.
  apply Nat.mod_small_iff in H1 as eq2.
  rewrite eq2.
  rewrite modadder12_correct.
  reflexivity.
  1 - 4 : assumption.
  lia.
  rewrite N2fb_Ntestbit in eq.
  apply nat_is_even_testbit in eq.
  apply Nat.even_spec in eq.
  unfold Nat.Even in eq.
  destruct eq.
  rewrite bindecomp_spec.
  assert (2 ^ 1 = 2) by easy.
  rewrite H7.
  assert (2 * x0 = x0 * 2) by lia.
  rewrite H8 in H6.
  rewrite H6.
  rewrite Nat.mod_mul.
  simpl.
  rewrite Nat.add_0_r.
  apply Nat.mod_small_iff in H1 as eq1.
  apply Nat.mod_small_iff in H2 as eq2.
  rewrite eq1. rewrite eq2.
  unfold hbf,allfalse. simpl. rewrite H5.
  reflexivity.
  1 - 3 : lia.
  simpl.
  rewrite IHi.
  rewrite moddoubler01_correct.
  assert (forall i n M x y z u, 
        bcexec (bcswap 1 (S (S (n + n + n + S i)))) 
            (false ` (M <=? 2 * ((2 ^ i * x) mod M))
                    ` [y]_n [z]_n [u]_n (hbf i M x))
         = (false ` false
                    ` [y]_n [z]_n [u]_n (hbf (S i) M x))).
  { intros.
    rewrite bcswap_correct.
    apply functional_extensionality.
    intros.
    bdestruct (x1 =? 1).
    rewrite fb_push_right by lia.
    rewrite fb_push_right by lia.
    rewrite H5. simpl.
    unfold reg_push.
    rewrite fb_push_n_right by lia.
    rewrite fb_push_n_right by lia.
    rewrite fb_push_n_right by lia.
    assert ((n0 + n0 + n0 + S i0 - 0 - n0 - n0 - n0) = S i0) by lia.
    rewrite H6.
    unfold hbf.
    bdestruct (S i0 =? 0).
    lia.
    bdestruct (S i0 <=? i0).
    lia.
    reflexivity.
    bdestruct (x1 =? S (S (n0 + n0 + n0 + S i0))).
    simpl.
    rewrite H6.
    rewrite fb_push_right by lia.
    rewrite fb_push_right by lia.
    unfold reg_push.
    rewrite fb_push_n_right by lia.
    rewrite fb_push_n_right by lia.
    rewrite fb_push_n_right by lia.
    assert ((S (S (n0 + n0 + n0 + S i0)) - 1 - 1 - n0 - n0 - n0) = S i0) by lia.
    rewrite H7.
    unfold hbf.
    bdestruct (S i0 =? 0).
    lia.
    bdestruct (S i0 <=? S i0).
    assert ((S i0 - 1) = i0) by lia.
    rewrite H10.
    simpl. reflexivity.
    lia.
    bdestruct (x1 =? 0).
    subst. simpl.
    reflexivity.
    bdestruct (2 <=? x1).
    rewrite fb_push_right by lia.
    rewrite fb_push_right by lia.  
    rewrite fb_push_right by lia.
    rewrite fb_push_right by lia.  
    unfold reg_push.
    unfold fb_push_n.
    bdestruct (x1 - 1 - 1 <? n0).
    reflexivity.
    bdestruct ( x1 - 1 - 1 - n0 <? n0).
    reflexivity.
    bdestruct (x1 - 1 - 1 - n0 - n0 <? n0).
    reflexivity.
    unfold hbf.
    bdestruct (x1 - 1 - 1 - n0 - n0 - n0 =? 0).
    reflexivity.
    bdestruct (x1 - 1 - 1 - n0 - n0 - n0 <=? i0).
    bdestruct (x1 - 1 - 1 - n0 - n0 - n0 <=? S i0).
    reflexivity. lia.
    bdestruct (x1 - 1 - 1 - n0 - n0 - n0 <=? S i0).
    lia.
    reflexivity.
    lia.
   }
  rewrite H5.
  destruct (nat2fb C (S i)) eqn:eq.
  rewrite modadder12_correct.
  simpl.
  rewrite Nat.add_0_r.
  rewrite <- Nat.add_mod.
  rewrite <- Nat.add_mod.
  rewrite bindecomp_seq.
  assert (S i = i + 1) by lia.
  rewrite H6 in eq.
  rewrite eq.
  simpl.
  assert ((2 ^ i * x + 2 ^ i * x) = ((2 ^ i + (2 ^ i + 0)) * x)) by lia.
  rewrite H7.
  assert (2 ^ (i + 1) = 2 ^ (S i)).
  rewrite H6. reflexivity.
  rewrite H8.
  simpl.
  assert (((2 ^ i + (2 ^ i + 0)) * x + (bindecomp (i + 1) C * x + y))
       = ((bindecomp (i + 1) C + (2 ^ i + (2 ^ i + 0) + 0)) * x + y)) by lia.
  rewrite H9.
  reflexivity.
  1 - 3 : lia.
  apply Nat.mod_bound_pos. lia. lia.
  apply Nat.mod_bound_pos. lia. lia.
  assumption.
  simpl.
  rewrite Nat.add_0_r.
  rewrite <- Nat.add_mod.
  rewrite bindecomp_seq.
  assert (S i = i + 1) by lia.
  rewrite H6 in eq.
  rewrite eq.
  simpl.
  assert ((2 ^ i * x + 2 ^ i * x) = ((2 ^ i + (2 ^ i + 0)) * x)) by lia.
  rewrite H7.
  rewrite Nat.add_0_r.
  rewrite Nat.add_0_r.
  reflexivity.
  1 - 2 : lia.
  apply Nat.mod_bound_pos. lia. lia.
  lia. lia.
Qed.

(* This is the correctness statement and proof of the C*x%M sum implementation. *)
Lemma modsummer_correct :
  forall n x y M C,
    1 < n ->
    x < M ->
    y < M ->
    C < M ->
    M < 2^(n-2) ->
    bcexec (modsummer n C) (false ` false ` [M]_n [x]_n [y]_n allfalse)
        = false ` false ` [M]_n [2^(n-1) * x mod M]_n [(C * x + y) mod M]_n (hbf (n-1) M x).
Proof.
  intros.
  unfold modsummer.
  rewrite modsummer'_correct.
  assert ((n - 1 + 1) = n) by lia.
  rewrite H4.
  rewrite bindecomp_spec.
  assert (C mod 2 ^ n = C).
  rewrite Nat.mod_small.
  reflexivity.
  assert (n = S (S (n - 2))) by lia.
  rewrite H5. simpl.
  lia.
  rewrite H5.
  reflexivity.
  lia.
  1 - 5: assumption.
Qed.

Opaque modsummer.
*)
(* This is the final clean-up step of the mod multiplier to do C*x %M. 
    Here, modmult_half will first clean up all high bits.  *)
Definition modmult_half n M x y c1 c2 s C := modsummer n M x y c1 c2 s C; (sinv (modsummer n M x y c1 c2 s 0)).

Definition modmult_full C Cinv n M x y c1 c2 s := modmult_half n M x y c1 c2 s C; sinv (modmult_half n M x y c1 c2 s Cinv).

Definition modmult M C Cinv n x y z s c1 c2 := init_v n z M; modmult_full C Cinv n z x y c1 c2 s; sinv (init_v n z M).

Definition modmult_rev M C Cinv n x y z s c1 c2 := Rev x;; Exp (modmult M C Cinv n x y z s c1 c2);; Rev x.


