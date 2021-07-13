Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
(**********************)
(** Unitary Programs **)
(**********************)

Declare Scope exp_scope.
Delimit Scope exp_scope with exp.
Local Open Scope exp_scope.
Local Open Scope nat_scope.

(* irrelavent vars. *)
Definition vars_neq (l:list var) := forall n m x y,
   nth_error l m = Some x ->  nth_error l n = Some y -> n <> m -> x <> y.


Inductive exp := SKIP (p:posi) | X (p:posi) | CU (p:posi) (e:exp)
        | RZ (q:nat) (p:posi) (* 2 * PI * i / 2^q *)
        | RRZ (q:nat) (p:posi) 
        | SR (q:nat) (x:var) (* a series of RZ gates for QFT mode. *)
        | SRR (q:nat) (x:var) (* a series of RRZ gates for QFT mode. *)
        | HCNOT (p1:posi) (p2:posi)
        | Lshift (x:var)
        | Rshift (x:var)
        | Rev (x:var)
        | QFT (x:var)
        | RQFT (x:var)
        | H (x:var)
        | Seq (s1:exp) (s2:exp).

Notation "p1 ; p2" := (Seq p1 p2) (at level 50) : exp_scope.

Fixpoint exp_elim (p:exp) :=
  match p with
  | CU q p => match exp_elim p with
                 | SKIP a => SKIP a 
                 | p' => CU q p'
                 end
  | Seq p1 p2 => match exp_elim p1, exp_elim p2 with
                  | SKIP _, p2' => p2'
                  | p1', SKIP _ => p1'
                  | p1', p2' => Seq p1' p2'
                  end
  | _ => p
  end.

Definition Z (p:posi) := RZ 1 p.

Fixpoint inv_exp p :=
  match p with
  | SKIP a => SKIP a
  | X n => X n
  | CU n p => CU n (inv_exp p)
  | SR n x => SRR n x
  | SRR n x => SR n x
  | Lshift x => Rshift x
  | Rshift x => Lshift x
  | Rev x => Rev x
  | HCNOT p1 p2 => HCNOT p1 p2
  | RZ q p1 => RRZ q p1
  | RRZ q p1 => RZ q p1
  | QFT x => RQFT x
  | RQFT x => QFT x
  | H x => H x
  | Seq p1 p2 => inv_exp p2; inv_exp p1
   end.


Fixpoint GCCX' x n size :=
  match n with
  | O | S O => X (x,n - 1)
  | S m => CU (x,size-n) (GCCX' x m size)
  end.
Definition GCCX x n := GCCX' x n n.

Fixpoint nX x n := 
   match n with 0 => X (x,0)
            | S m => X (x,m); nX x m
   end.

(* Grover diffusion operator. *)
Definition diff_half (x c:var) (n:nat) := H x ; H c ;  ((nX x n; X (c,0))). 

Definition diff_1 (x c :var) (n:nat) :=
  diff_half x c n ; ((GCCX x n)) ; (inv_exp (diff_half x c n)).

(*The second implementation of grover's diffusion operator.
  The whole circuit is a little different, and the input for the diff_2 circuit is asssumed to in Had mode. *)
Definition diff_2 (x c :var) (n:nat) :=
  H x ; ((GCCX x n)) ; H x.

Fixpoint is_all_true C n :=
  match n with 0 => true
           | S m => C m && is_all_true C m
  end.

Definition const_u (C :nat -> bool) (n:nat) c := if is_all_true C n then ((X (c,0))) else SKIP (c,0).

Fixpoint niter_prog n (c:var) (P : exp) : exp :=
  match n with
  | 0    => SKIP (c,0)
  | 1    => P
  | S n' => niter_prog n' c P ; P
  end.

Definition body (C:nat -> bool) (x c:var) (n:nat) := const_u C n c; diff_2 x c n.

Definition grover_e (i:nat) (C:nat -> bool) (x c:var) (n:nat) := 
        H x; H c ; ((Z (c,0))) ; niter_prog i c (body C x c n).

(** Definition of Deutsch-Jozsa program. **)

Definition deutsch_jozsa (x c:var) (n:nat) :=
  ((nX x n; X (c,0))) ; H x ; H c ; ((X (c,0))); H c ; H x.

Inductive type := Had | Phi (n:nat) | Nor.

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Module Env := FMapList.Make Nat_as_OT.
Module EnvFacts := FMapFacts.Facts (Env).

Definition env := Env.t type.
Definition empty_env := @Env.empty type.

Lemma mapsto_always_same : forall k v1 v2 s,
           @Env.MapsTo (type) k v1 s ->
            @Env.MapsTo (type) k v2 s -> 
                       v1 = v2.
Proof.
     intros.
     apply Env.find_1 in H0.
     apply Env.find_1 in H1.
     rewrite H0 in H1.
     injection H1.
     easy.
Qed.

Lemma find_add : forall k v m,
        @Env.find (type) k (Env.add k v m) = Some v.
Proof.
      intros.
      apply Env.find_1.
      apply Env.add_1.
      easy.
Qed.

Lemma mapsto_add1 : forall k v1 v2 s,
        @Env.MapsTo (type) k v1 (Env.add k v2 s) -> v1 = v2.
Proof.
      intros.
      apply Env.find_1 in H0.
      rewrite find_add in H0.
      inversion H0.
      reflexivity.
Qed.

Lemma mapsto_equal : forall k v s1 s2,
   @Env.MapsTo type k v s1 ->
   Env.Equal s1 s2 ->
   Env.MapsTo k v s2.
Proof.
      intros.
      unfold Env.Equal in H1.
      apply Env.find_2. rewrite <- H1.
      apply Env.find_1.
      assumption.
Qed.


Lemma map_find_add : forall x v env, @Env.find (type) x (Env.add x v env) = Some v.
Proof.
  intros.
  apply Env.find_1.
  apply Env.add_1. easy.
Qed.

Lemma map_find_neq : forall x y v env, x <> y -> @Env.find (type) x (Env.add y v env) = Env.find x env.
Proof.
  intros.
  destruct (Env.find (elt:=type) x env0) eqn:eq1.
  apply Env.find_1. apply Env.add_2. lia. 
  apply Env.find_2 in eq1. easy.
  destruct (Env.find (elt:=type) x (Env.add y v env0)) eqn:eq2.
  apply Env.find_2 in eq2. apply Env.add_3 in eq2.
  apply Env.find_1 in eq2. rewrite eq1 in eq2. inv eq2. lia.
  easy.
Qed.

Definition or_not_r (x y:var) (n1 n2:nat) := x <> y \/ n1 < n2.

Definition or_not_eq (x y:var) (n1 n2:nat) := x <> y \/ n1 <= n2.


Inductive exp_fresh (aenv:var->nat): posi -> exp -> Prop :=
      | skip_fresh : forall p p1, p <> p1 -> exp_fresh aenv p (SKIP p1)
      | x_fresh : forall p p' , p <> p' -> exp_fresh aenv p (X p')
      | sr_fresh : forall p x n, or_not_r (fst p) x n (snd p) -> exp_fresh aenv p (SR n x)
      | srr_fresh : forall p x n, or_not_r (fst p) x n (snd p) -> exp_fresh aenv p (SRR n x)
      | lshift_fresh : forall p x, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (Lshift x)
      | rshift_fresh : forall p x, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (Rshift x)
      | rev_fresh : forall p x, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (Rev x)
      | cu_fresh : forall p p' e, p <> p' -> exp_fresh aenv p e -> exp_fresh aenv p (CU p' e)
      | cnot_fresh : forall p p1 p2, p <> p1 -> p <> p2 -> exp_fresh aenv p (HCNOT p1 p2)
      | rz_fresh : forall p p' q, p <> p' -> exp_fresh aenv p (RZ q p')
      | rrz_fresh : forall p p' q, p <> p' -> exp_fresh aenv p (RRZ q p')
      | qft_fresh : forall p x , or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (QFT x)
      | rqft_fresh : forall p x , or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (RQFT x)
      | h_fresh : forall p x , or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (H x)
      | seq_fresh : forall p e1 e2, exp_fresh aenv p e1 -> exp_fresh aenv p e2 -> exp_fresh aenv p (Seq e1 e2).

(* Defining matching shifting stack. *)
Inductive sexp := Ls | Rs | Re.

Definition opp_ls (s : sexp) := match s with Ls => Rs | Rs => Ls | Re => Re end.

Definition fst_not_opp (s:sexp) (l : list sexp) := 
   match l with [] => True
              | (a::al) => s <> opp_ls a
   end.

Inductive exp_neu_l (x:var) : list sexp -> exp ->  list sexp -> Prop :=
      | skip_neul : forall l p, exp_neu_l x l (SKIP p) l
      | x_neul : forall l p,  exp_neu_l x l (X p) l
      | sr_neul : forall l y n, exp_neu_l x l (SR n y) l
      | srr_neul : forall l y n, exp_neu_l x l (SRR n y) l
      | cu_neul : forall l p e, exp_neu_l x l (CU p e) l
      | hcnot_neul : forall l p1 p2, exp_neu_l x l (HCNOT p1 p2) l
      | rz_neul : forall l p q, exp_neu_l x l (RZ q p) l
      | rrz_neul : forall l p q, exp_neu_l x l (RRZ q p) l
      | qft_neul : forall l y, exp_neu_l x l (QFT y) l
      | rqft_neul : forall l y , exp_neu_l x l (RQFT y) l
      | h_neul : forall l y, exp_neu_l x l (H y) l
      | lshift_neul_a : forall l, exp_neu_l x (Rs::l) (Lshift x) l
      | lshift_neul_b : forall l, fst_not_opp Ls l -> exp_neu_l x l (Lshift x) (Ls::l)
      | lshift_neul_ne : forall l y, x <> y -> exp_neu_l x l (Lshift y) l
      | rshift_neul_a : forall l, exp_neu_l x (Ls::l) (Rshift x) l
      | rshift_neul_b : forall l, fst_not_opp Rs l -> exp_neu_l x l (Rshift x) (Rs::l)
      | rshift_neul_ne : forall l y, x <> y -> exp_neu_l x l (Rshift y) l
      | rev_neul_a : forall l, exp_neu_l x (Re::l) (Rev x) l
      | rev_neul_b : forall l, fst_not_opp Re l -> exp_neu_l x l (Rev x) (Re::l)
      | rev_neul_ne : forall l y, x <> y -> exp_neu_l x l (Rev y) l
      | seq_neul : forall l l' l'' e1 e2, exp_neu_l x l e1 l' -> exp_neu_l x l' e2 l'' -> exp_neu_l x l (Seq e1 e2) l''.

Inductive exp_neu (xl : list var) : exp -> Prop :=
      | skip_neu : forall p, exp_neu xl (SKIP p)
      | x_neu : forall p,  exp_neu xl (X p)
      | sr_neu : forall n y, exp_neu xl (SR n y)
      | srr_neu : forall y n, exp_neu xl (SRR n y)
      | cu_neu : forall p e, (forall x , In x xl -> exp_neu_l x [] e []) -> exp_neu xl (CU p e)
      | hcnot_neu : forall p1 p2, exp_neu xl (HCNOT p1 p2)
      | rz_neu : forall p q, exp_neu xl (RZ q p)
      | rrz_neu : forall p q, exp_neu xl (RRZ q p)
      | qft_neu : forall y, exp_neu xl (QFT y)
      | rqft_neu : forall y , exp_neu xl (RQFT y)
      | h_neu : forall y, exp_neu xl (H y)
      | lshift_neu : forall y, exp_neu xl (Lshift y)
      | rshift_neu : forall y, exp_neu xl (Rshift y)
      | rev_neu : forall y, exp_neu xl (Rev y)
      | seq_neu : forall e1 e2, exp_neu xl e1 -> exp_neu xl e2 -> exp_neu xl (e1 ; e2).

Definition exp_neu_prop (l:list sexp) :=
    (forall i a, i + 1 < length l -> nth_error l i = Some a -> nth_error l (i+1) <> Some (opp_ls a)).

Lemma exp_neu_t_prop : forall p x l l', exp_neu_l x l p l' -> exp_neu_prop l -> exp_neu_prop l'.
Proof.
 induction p; intros; try easy.
 1-8:inv H0; easy.
 unfold exp_neu_prop in *.
 intros. inv H0.
 destruct l'. simpl in *. lia.
 destruct i. simpl in *.
 destruct l'. easy.
 specialize (H1 1 a).
 assert (1 + 1 < S (S (length (s0 :: l')))) by lia.
 apply H1 in H0. simpl in *. easy.
 simpl in *. easy.
 specialize (H1 (S (S i)) a).
 assert (S (S i) + 1 < length (Rs :: s :: l')).
 simpl in *. lia.
 apply H1 in H0.
 simpl in *. easy.
 simpl in *. easy.
 unfold fst_not_opp in H6. destruct l. simpl in *. lia.
 destruct i. simpl in *. inv H3.
 unfold opp_ls in *. intros R. inv R. easy.
 specialize (H1 i a).
 assert (i + 1 < length (s :: l)). simpl in *. lia.
 apply H1 in H0. simpl in *. easy. simpl in *. easy.
 apply H1; try easy.
 unfold exp_neu_prop in *.
 intros. inv H0.
 destruct l'. simpl in *. lia.
 destruct i. simpl in *.
 destruct l'. easy.
 specialize (H1 1 a).
 assert (1 + 1 < S (S (length (s0 :: l')))) by lia.
 apply H1 in H0. simpl in *. easy.
 simpl in *. easy.
 specialize (H1 (S (S i)) a).
 assert (S (S i) + 1 < length (Ls :: s :: l')).
 simpl in *. lia.
 apply H1 in H0.
 simpl in *. easy.
 simpl in *. easy.
 unfold fst_not_opp in *. destruct l. simpl in *. lia.
 destruct i. simpl in *. inv H3.
 unfold opp_ls. intros R. inv R. easy.
 specialize (H1 i a).
 assert (i + 1 < length (s :: l)). simpl in *. lia.
 apply H1 in H0. simpl in *. easy. simpl in *. easy.
 apply H1; try easy.
 unfold exp_neu_prop in *.
 intros. inv H0.
 destruct i. simpl in *.
 destruct l'. easy.
 specialize (H1 1 a).
 assert (1 + 1 < S (length (s :: l'))) by lia.
 apply H1 in H0. simpl in *. easy.
 simpl in *. easy.
 specialize (H1 (S (S i)) a).
 assert (S (S i) + 1 < length (Re :: l')).
 simpl in *. lia.
 apply H1 in H0.
 simpl in *. easy.
 simpl in *. easy.
 unfold fst_not_opp in *. destruct l. simpl in *. lia.
 destruct i. simpl in *. inv H3.
 unfold opp_ls. intros R. inv R. easy.
 specialize (H1 i a).
 assert (i + 1 < length (s :: l)). simpl in *. lia.
 apply H1 in H0. simpl in *. easy. simpl in *. easy.
 apply H1; try easy.
 1-3:inv H0; easy.
 inv H0.
 apply IHp2 with (x := x) (l := l'0); try easy. 
 apply IHp1 with (x:=x) (l := l); try easy.
Qed.



(* Type System. *)
Inductive well_typed_exp : env -> exp -> Prop :=
    | skip_refl : forall env, forall p, well_typed_exp env (SKIP p)
    | x_nor : forall env p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (X p)
    | x_had : forall env p, Env.MapsTo (fst p) Had env -> well_typed_exp env (X p)
    | cnot_had : forall env p1 p2, p1 <> p2 -> Env.MapsTo (fst p1) Had env -> Env.MapsTo (fst p2) Had env
                         -> well_typed_exp env (HCNOT p1 p2)
    | rz_nor : forall env q p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (RZ q p)
    | rz_had : forall env p, Env.MapsTo (fst p) Had env -> well_typed_exp env (RZ 1 p)
    | rrz_nor : forall env q p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (RRZ q p)
    | rrz_had : forall env p, Env.MapsTo (fst p) Had env -> well_typed_exp env (RRZ 1 p)
    | sr_phi : forall env n m x, Env.MapsTo x (Phi n) env -> m < n -> well_typed_exp env (SR m x)
    | srr_phi : forall env n m x, Env.MapsTo x (Phi n) env -> m < n -> well_typed_exp env (SRR m x)
    | lshift_nor : forall env x, Env.MapsTo x Nor env -> well_typed_exp env (Lshift x)
    | lshift_had : forall env x, Env.MapsTo x Had env -> well_typed_exp env (Lshift x)
    | rshift_nor : forall env x, Env.MapsTo x Nor env -> well_typed_exp env (Rshift x)
    | rshift_had : forall env x, Env.MapsTo x Had env -> well_typed_exp env (Rshift x)
    | rev_nor : forall env x, Env.MapsTo x Nor env -> well_typed_exp env (Rev x)
    | rev_had : forall env x, Env.MapsTo x Had env -> well_typed_exp env (Rev x).

(*
Definition opp_ls (s : sexp) := match s with Ls => Rs | Rs => Ls | Re => Re end.
*)

Inductive well_typed_pexp (avar : list var) (aenv: var -> nat) : env -> exp -> env -> Prop :=
    | exp_refl : forall env e, 
                well_typed_exp env e -> well_typed_pexp avar aenv env e env
    | qft_nor :  forall env env' x, Env.MapsTo x Nor env -> Env.Equal env' (Env.add x (Phi (aenv x)) env)
                   -> well_typed_pexp avar aenv env (QFT x) env'
    | rqft_phi :  forall env env' x, Env.MapsTo x (Phi (aenv x)) env -> Env.Equal env' (Env.add x Nor env) -> 
                 well_typed_pexp avar aenv env (RQFT x) env'
    | h_nor : forall env env' x, Env.MapsTo x Nor env -> Env.Equal env' (Env.add x Had env) ->  
                  well_typed_pexp avar aenv env (H x) env'
    | h_had : forall env env' x, Env.MapsTo x Had env -> Env.Equal env' (Env.add x Nor env) ->  
                                   well_typed_pexp avar aenv env (H x) env'
    | pcu_nor : forall env p e, Env.MapsTo (fst p) Nor env -> exp_fresh aenv p e -> exp_neu avar e ->
                       well_typed_pexp avar aenv env e env -> well_typed_pexp avar aenv env (CU p e) env
    | pe_seq : forall env env' env'' e1 e2, well_typed_pexp avar aenv env e1 env' -> 
                 well_typed_pexp avar aenv env' e2 env'' -> well_typed_pexp avar aenv env (e1 ; e2) env''.

Inductive exp_WF (aenv:var -> nat): exp -> Prop :=
      | skip_wf : forall p, snd p < aenv (fst p) -> exp_WF aenv (SKIP p)
      | x_wf : forall p, snd p < aenv (fst p)  -> exp_WF aenv  (X p)
      | cu_wf : forall p e, snd p < aenv (fst p)  -> exp_WF aenv  e -> exp_WF aenv  (CU p e)
      | hcnot_wf : forall p1 p2, snd p1 < aenv (fst p1) 
                              -> snd p2 < aenv (fst p2)  -> exp_WF aenv  (HCNOT p1 p2)
      | rz_wf : forall p q, snd p < aenv (fst p)  -> exp_WF aenv  (RZ q p)
      | rrz_wf : forall p q, snd p < aenv (fst p)  -> exp_WF aenv  (RRZ q p)
      | sr_wf : forall n x, S n < aenv x -> exp_WF aenv  (SR n x)
      | ssr_wf : forall n x, S n < aenv x -> exp_WF aenv  (SRR n x)       
      | seq_wf : forall e1 e2, exp_WF aenv e1 -> exp_WF aenv  e2 -> exp_WF aenv  (Seq e1 e2)
      | lshift_wf : forall x, 0 < aenv x -> exp_WF aenv  (Lshift x)
      | rshift_wf : forall x, 0 < aenv x -> exp_WF aenv  (Rshift x)
      | rev_wf : forall x, 0 < aenv x -> exp_WF aenv  (Rev x)
      | qft_wf : forall x, 0 < aenv x -> exp_WF aenv (QFT x)
      | rqft_wf : forall x, 0 < aenv x -> exp_WF aenv (RQFT x)
      | h_wf : forall x, 0 < aenv x -> exp_WF aenv (H x).

Fixpoint get_vars e : list var :=
    match e with SKIP p => [(fst p)]
              | X p => [(fst p)]
              | CU p e => (fst p)::(get_vars e)
              | HCNOT p1 p2 => ((fst p1)::(fst p2)::[])
              | RZ q p => ((fst p)::[])
              | RRZ q p => ((fst p)::[])
              | SR n x => (x::[])
              | SRR n x => (x::[])
              | Lshift x => (x::[])
              | Rshift x => (x::[])
              | Rev x => (x::[])
              | QFT x => (x::[])
              | RQFT x => (x::[])
              | H x => (x::[])
              | Seq e1 e2 => get_vars e1 ++ (get_vars e2)
   end.

Fixpoint init_v (n:nat) (x:var) (M: nat -> bool) :=
      match n with 0 => (SKIP (x,0))
                | S m => if M m then X (x,m) ; init_v m x M else init_v m x M
      end.

Inductive right_mode_val : type -> val -> Prop :=
    | right_nor: forall b r, right_mode_val Nor (nval b r)
    | right_had: forall b1 b2 r, r 0 = false -> right_mode_val Had (hval b1 b2 r)
    | right_phi: forall n rc r, right_mode_val (Phi n) (qval rc r).

Definition right_mode_env (aenv: var -> nat) (env: env) (st: posi -> val)
            := forall t p, snd p < aenv (fst p) -> Env.MapsTo (fst p) t env -> right_mode_val t (st p).

(* helper functions/lemmas for NOR states. *)
Definition nor_mode (f : posi -> val)  (x:posi) : Prop :=
       match f x with nval a b => True | _ => False end.

Definition nor_modes (f:posi -> val) (x:var) (n:nat) :=
      forall i, i < n -> nor_mode f (x,i).

Lemma type_nor_mode :  forall f aenv env p, 
    Env.MapsTo (fst p) Nor env -> snd p < aenv (fst p) -> right_mode_env aenv env f -> nor_mode f p.
Proof.
 intros. unfold right_mode_env in *.
 apply (H2 Nor) in H1 ; try easy.
 inv H1. unfold nor_mode.
 rewrite <- H3. easy.
Qed.


Lemma type_nor_modes :  forall f aenv env x, 
    Env.MapsTo x Nor env -> right_mode_env aenv env f -> nor_modes f x (aenv x).
Proof.
 intros. unfold right_mode_env in *.
 unfold nor_modes. intros.
 specialize (H1 Nor (x,i)).
 simpl in H1. apply H1 in H2; try easy.
 inv H2. unfold nor_mode.
 assert ((@pair var nat x i) = (@pair Env.key nat x i)) by easy.
 rewrite H2 in *.
 rewrite <- H3. easy.
Qed.

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

Definition put_cu (v:val) (b:bool) :=
    match v with nval x r => nval b r | a => a end.

Definition get_cua (v:val) := 
    match v with nval x r => x | _ => false end.

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

Definition get_cus (n:nat) (f:posi -> val) (x:var) := 
          fun i => if i <? n then (match f (x,i) with nval b r => b | _ => false end) else allfalse i.

Lemma get_cus_cua : forall n f x m, m < n -> get_cus n f x m = get_cua (f (x,m)).
Proof.
  intros.
  unfold get_cus,get_cua.
  bdestruct (m <? n).
  destruct (f (x,n)). easy. easy. easy.
  lia.
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

Lemma put_cus_neq_2 : forall (f:posi -> val) (x y:var) g n i, 
           n <= i -> (put_cus f x g n) (y,i) = f (y,i).
Proof.
 intros.
 unfold put_cus.
 simpl.
 bdestruct (y =? x).
 bdestruct (i <? n). lia. easy.
 easy.
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

Lemma nor_mode_up_1 : forall f x v, nor_mode f x -> nor_mode (f[x |-> put_cu (f x) v]) x.
Proof.
  intros.
  unfold nor_mode in *.
  rewrite eupdate_index_eq.
  unfold put_cu.
  destruct (f x).
  easy. inv H0. inv H0.
Qed.


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

Lemma put_get_cus_eq :
   forall f x n, nor_modes f x n -> (put_cus f x (get_cus n f x) n) = f.
Proof.
  intros.
  unfold put_cus,get_cus,put_cu.
  apply functional_extensionality. intros.
  destruct x0. simpl.
  bdestruct (v =? x). bdestruct (n0 <? n).
  subst.
  unfold nor_modes in H0.
  specialize (H0 n0 H2) as eq1. unfold nor_mode in eq1.
  destruct (f (x,n0)). easy. inv eq1. inv eq1.
  easy. easy.
Qed.

Lemma get_cus_put_eq :
   forall f x v n, v < 2^n -> nor_modes f x n -> get_cus n (put_cus f x (nat2fb v) n) x = (nat2fb v).
Proof.
  intros.
  unfold get_cus.
  apply functional_extensionality. intros.
  bdestruct (x0 <? n).
  simpl.
  unfold nor_modes in H0.
  assert (nor_mode (put_cus f x (nat2fb v) n) (x, x0)).
  apply nor_mode_cus_eq. apply H1. easy.
  unfold nor_mode in H3.
  destruct (put_cus f x ((nat2fb v)) n (x, x0)) eqn:eq2.
  unfold put_cus in eq2. simpl in eq2.
  bdestruct (x =? x).
  bdestruct (x0 <? n).
  unfold put_cu in eq2.
  assert (nor_mode f (x,x0)).
  apply H1. easy.
  unfold nor_mode in H6.
  destruct (f (x, x0)). inv eq2. easy. inv H6. inv H6. lia. lia.
  inv H3. inv H3.
  unfold allfalse.
  rewrite nat2fb_bound with (n := n); try easy.
Qed.

Lemma put_cus_same : forall f x g n, nor_modes f x n 
               -> get_cus n f x = g -> put_cus f x g n = f.
Proof.
  intros.
  rewrite <- H1. 
  rewrite put_get_cus_eq. easy. easy.
Qed.

Lemma get_cus_put_neq :
   forall f x y g n, x <> y -> get_cus n (put_cus f x g n) y = get_cus n f y.
Proof.
  intros. unfold get_cus,put_cus.
  apply functional_extensionality. intros.
  simpl.
  bdestruct ( y =? x). lia.
  destruct (f (y, x0)). easy. easy. easy.
Qed.

Lemma get_put_cus_cut_n : forall n f x g, nor_modes f x n
             -> (get_cus n (put_cus f x g n) x) = cut_n g n.
Proof.
  intros. unfold get_cus,put_cus,cut_n.
  apply functional_extensionality. intros.
  bdestruct (x0 <? n). simpl.
  bdestruct (x =? x).
  bdestruct (x0 <? n).
  unfold put_cu.
  unfold nor_modes in H0.
  specialize (H0 x0 H3). unfold nor_mode in H0.
  destruct (f (x,x0)). easy. lia. lia.
  lia. lia. easy.
Qed.

Definition get_cu (v : val) :=
    match v with nval b r => Some b 
                 | hval b1 b2 r => Some b1
                 | _ => None
    end.

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

Lemma get_cua_t : forall b r, get_cua (nval b r) = b.
Proof.
 intros. unfold get_cua. reflexivity.
Qed.

(* Proofs of types and syntax. *)
Ltac nor_sym := try (apply neq_sym; assumption) ; try assumption.


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

Lemma iner_neq_2 : forall (x:var) (c:posi) a, x <> fst c -> c <> (x,a).
Proof.
  intros. intros R.
  destruct c.
  inv R. contradiction.
Qed.

Ltac tuple_eq := intros R; inv R; lia.

Ltac iner_p := try nor_sym; try tuple_eq ; try (apply iner_neq ; assumption)
           ; try (apply iner_neq_1 ; assumption) ; try (apply iner_neq_2 ; assumption).


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

Lemma get_cus_up : forall n f x c v, fst c <> x -> get_cus n (f[c |-> v]) x = get_cus n f x.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold get_cus.
  bdestruct (x0 <? n). destruct c. simpl in *. rewrite eupdate_index_neq by iner_p.
  easy. easy.
Qed.

Lemma get_cus_up_ge : forall n f x c v, n <= snd c -> get_cus n (f[c |-> v]) x = get_cus n f x.
Proof.
  intros.
  apply functional_extensionality; intro.
  unfold get_cus.
  bdestruct (x0 <? n). destruct c. simpl in *. rewrite eupdate_index_neq by iner_p.
  easy. easy.
Qed.

(*A function to get the rotation angle of a state. *)
Definition get_r (v:val) :=
   match v with nval x r => r
              | qval rc r => rc
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


Lemma put_cu_twice_eq : forall (f:posi -> val) (x:var) v1 v2 i, 
        put_cu (put_cu (f (x,i)) v1) v2 = put_cu (f (x,i)) v2.
Proof.
  intros. unfold put_cu.
  destruct (f (x, i)). easy. easy. easy.
Qed.

Lemma put_cu_twice_eq_1 : forall (f:posi -> val) c v1 v2, 
        put_cu (put_cu (f c) v1) v2 = put_cu (f c) v2.
Proof.
  intros. unfold put_cu.
  destruct (f c). easy. easy. easy.
Qed.


Lemma put_cus_twice_eq : forall (f:posi -> val) (x:var) g1 g2 n, 
              (put_cus (put_cus f x g1 n) x g2 n)
                          = (put_cus f x g2 n).
Proof.
 intros.
 apply functional_extensionality.
 unfold put_cus. intros.
 destruct x0. simpl.
 bdestruct (v =? x).
 bdestruct (n0 <? n). rewrite put_cu_twice_eq. easy.
 easy.
 easy.
Qed.

Lemma put_cus_sem_eq : forall (f:posi -> val) (x:var) g1 g2 n, 
           (forall m, m < n -> g1 m = g2 m) -> 
                 (put_cus f x g1 n) = (put_cus f x g2 n).
Proof.
 intros.
 apply functional_extensionality.
 unfold put_cus. intros.
 destruct x0. simpl.
 bdestruct (v =? x).
 bdestruct (n0 <? n). rewrite H0. easy.
 lia. easy. easy. 
Qed.


(* Defining program semantic functions. *)
Definition rotate (r :rz_val) (q:nat) := addto r q.

Definition times_rotate (v : val) (q:nat) := 
     match v with nval b r => if b then nval b (rotate r q) else nval b r
                  | hval b1 b2 r => hval b1 (¬ b2) r
                  | qval rc r =>  qval rc (rotate r q)
     end.

Fixpoint sr_rotate' (st: posi -> val) (x:var) (n:nat) (size:nat) :=
   match n with 0 => st
              | S m => (sr_rotate' st x m size)[(x,m) |-> times_rotate (st (x,m)) (size - m)]
   end.
Definition sr_rotate st x n := sr_rotate' st x (S n) (S n).

Definition r_rotate (r :rz_val) (q:nat) := addto_n r q.

Definition times_r_rotate (v : val) (q:nat) := 
     match v with nval b r =>  if b then nval b (r_rotate r q) else nval b r
                  | hval b1 b2 r => hval b1 (¬ b2) r
                  | qval rc r =>  qval rc (r_rotate r q)
     end.

Fixpoint srr_rotate' (st: posi -> val) (x:var) (n:nat) (size:nat) :=
   match n with 0 => st
              | S m => (srr_rotate' st x m size)[(x,m) |-> times_r_rotate (st (x,m)) (size - m)]
   end.
Definition srr_rotate st x n := srr_rotate' st x (S n) (S n).


Definition exchange (v: val) :=
     match v with nval b r => nval (¬ b) r
                  | hval b1 b2 r => hval b2 b1 r
                  | a => a
     end.

Fixpoint lshift' (n:nat) (size:nat) (f:posi -> val) (x:var) := 
   match n with 0 => f[(x,0) |-> f(x,size)]
             | S m => ((lshift' m size f x)[ (x,n) |-> f(x,m)])
   end.
Definition lshift (f:posi -> val) (x:var) (n:nat) := lshift' (n-1) (n-1) f x.

Fixpoint rshift' (n:nat) (size:nat) (f:posi -> val) (x:var) := 
   match n with 0 => f[(x,size) |-> f(x,0)]
             | S m => ((rshift' m size f x)[(x,m) |-> f (x,n)])
   end.
Definition rshift (f:posi -> val) (x:var) (n:nat) := rshift' (n-1) (n-1) f x.

(*
Inductive varType := SType (n1:nat) (n2:nat).

Definition inter_env (enva: var -> nat) (x:var) :=
             match  (enva x) with SType n1 n2 => n1 + n2 end.
*)

Definition hexchange (v1:val) (v2:val) :=
  match v1 with hval b1 b2 r1 => 
    match v2 with hval b3 b4 r2 => if eqb b3 b4 then v1 else hval b1 (¬ b2) r1
                | _ => v1
    end
             | _ => v1
  end.

Definition reverse (f:posi -> val) (x:var) (n:nat) := fun (a: var * nat) =>
             if ((fst a) =? x) && ((snd a) <? n) then f (x, (n-1) - (snd a)) else f a.

(* Semantic definition for H gate. *)
Definition h_case (v : val) :=
    match v with nval b r => if r 0 then hval false b (rotate r 1) else hval true (¬ b) r
               | hval true true r => nval false r
               | hval true false r => nval true r
               | hval false true r => nval true (rotate r 1)
               | hval false false r => nval false (rotate r 1)
               | a => a
    end.

Fixpoint h_sem (f:posi -> val) (x:var) (n : nat) := 
    match n with 0 => f
              | S m => (h_sem f x m)[(x,m) |-> h_case (f (x,m))]
    end.

(* Semantics function for QFT gate. *)
Definition seq_val (v:val) :=
  match v with nval b r => b
             | _ => false
  end.

Fixpoint get_seq (f:posi -> val) (x:var) (base:nat) (n:nat) : (nat -> bool) :=
     match n with 0 => allfalse
              | S m => fun (i:nat) => if i =? (base + m) then seq_val (f (x,base+m)) else ((get_seq f x base m) i)
     end.

Definition up_qft (v:val) (f:nat -> bool) :=
   match v with nval b r => qval r f
              | a => a
   end.

Definition lshift_fun (f:nat -> bool) (n:nat) := fun i => f (i+n).


Fixpoint assign_r (f:posi -> val) (x:var) (r : nat -> bool) (n:nat) := 
    match n with 0 => f
              | S m => (assign_r f x r m)[(x,m) |-> up_qft (f (x,m)) (lshift_fun r m)]
    end.

Definition turn_qft (st : posi -> val) (x:var) (rmax : nat) := 
       assign_r st x (get_cus rmax st x) rmax.


(* Semantic function for RQFT gate. *)
Fixpoint assign_seq (f:posi -> val) (x:var) (vals : nat -> bool) (n:nat) := 
   match n with 0 => f
              | S m => (assign_seq f x vals m)[(x,m) |-> nval (vals m) (get_r (f (x,m)))]
   end.

Definition get_r_qft (f:posi -> val) (x:var) :=
      match f (x,0) with qval rc g => g
                      | _ => allfalse
      end.

Definition turn_rqft (st : posi -> val) (x:var) (rmax : nat) := assign_seq st x (get_r_qft st x) rmax.

(* Here, we define the addto / addto_n functions for angle rotation. 
Definition cut_n (f:nat -> bool) (n:nat) := fun i => if i <? n then f i else allfalse i.
 
Definition fbrev' i n (f : nat -> bool) := fun (x : nat) => 
            if (x <=? i) then f (n - 1 - x) else if (x <? n - 1 - i) 
                         then f x else if (x <? n) then f (n - 1 - x) else f x.
Definition fbrev {A} n (f : nat -> A) := fun (x : nat) => if (x <? n) then f (n - 1 - x) else f x.
*)


(* Helper theorems for fbrev and rotation. *)
Lemma fbrev_1_same {A}: forall f, @fbrev A 1 f = f.
Proof.
  intros.
  unfold fbrev.
  apply functional_extensionality. intros.
  bdestruct (x<?1).
  assert (1 - 1 - x = x) by lia.
  rewrite H1. easy. easy. 
Qed.


Lemma rotate_twice_same_1 : forall r, (rotate (rotate r 1) 1) = r.
Proof.
  intros. unfold rotate.
  unfold addto.
  apply functional_extensionality. intros.
  bdestruct (x <? 1).
  assert ( x = 0) by lia. subst.
  repeat rewrite fbrev_1_same.
  destruct (r 0) eqn:eq1.
  specialize (cut_n_1_1 r eq1) as eq2.
  rewrite eq2.
  rewrite sumfb_correct_carry0.
  rewrite cut_n_mod.
  assert (((1 + 1) mod 2 ^ 1) = 0).
  assert ((1 + 1) = 2) by lia. rewrite H1.
  rewrite Nat.pow_1_r. rewrite Nat.mod_same. easy. lia.
  rewrite H1.
  rewrite cut_n_if_cut.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r. rewrite Nat.mod_small by lia.
  rewrite sumfb_correct_carry0.
  rewrite plus_0_l. 
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r.
  rewrite Nat.mod_small by lia.
  unfold nat2fb. simpl. easy.
  rewrite (cut_n_1_0 r eq1).
  rewrite sumfb_correct_carry0.
  rewrite plus_0_l.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r. rewrite Nat.mod_small by lia.
  rewrite cut_n_if_cut.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r. rewrite Nat.mod_small by lia.
  rewrite sumfb_correct_carry0.
  assert ((1 + 1) = 2) by lia. rewrite H1.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r.
  rewrite Nat.mod_same by lia.
  unfold nat2fb. easy.
  easy.
Qed.

Lemma rotate_1_0: forall r, r 0 = false -> rotate r 1 0 = true.
Proof.
  unfold rotate, addto.
  intros.
  bdestruct (0 <? 1).
  repeat rewrite fbrev_1_same.
  rewrite (cut_n_1_0 r H0). 
  rewrite sumfb_correct_carry0.
  rewrite plus_0_l. 
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r.
  rewrite Nat.mod_small by lia. easy. lia.
Qed.

Lemma rotate_1_1: forall r, r 0 = true -> rotate r 1 0 = false.
Proof.
  unfold rotate, addto.
  intros.
  bdestruct (0 <? 1).
  repeat rewrite fbrev_1_same.
  rewrite (cut_n_1_1 r H0). 
  rewrite sumfb_correct_carry0.
  rewrite cut_n_mod.
  rewrite Nat.pow_1_r.
  rewrite Nat.mod_same by lia. easy. lia.
Qed.

Lemma h_case_twice_same : 
   forall t v, right_mode_val t v -> h_case (h_case v) = v.
Proof.
  intros. unfold h_case.
  destruct v.
  destruct (r 0) eqn:eq1.
  destruct b.
  rewrite rotate_twice_same_1. easy.
  rewrite rotate_twice_same_1. easy.
  destruct b. simpl. easy. simpl. easy.
  inv H0.
  destruct b1.
  destruct b2. rewrite H3. simpl. easy.
  rewrite H3. simpl. easy.
  destruct b2.
  rewrite (rotate_1_0 r H3).
  rewrite rotate_twice_same_1. easy.
  rewrite (rotate_1_0 r H3).
  rewrite rotate_twice_same_1. easy.
  easy.
Qed.

Lemma hexchange_twice_same :
  forall v1 v2, hexchange (hexchange v1 v2) v2 = v1.
Proof.
  intros.
  unfold hexchange.
  destruct v1 eqn:eq1. easy.
  destruct v2 eqn:eq2. easy.
  destruct (eqb b0 b3) eqn:eq3. easy.
  assert ((¬ (¬ b2)) = b2) by btauto. rewrite H0. easy.
  easy. easy.
Qed.

Lemma assign_r_right_mode : forall n i size f x r, i < n <= size -> 
       (forall i, i < size -> right_mode_val Nor (f (x,i))) ->
       right_mode_val (Phi size) (assign_r f x r n (x,i)).
Proof.
  induction n; intros; simpl. inv H0. inv H2.
  bdestruct (i =? n).
  subst. rewrite eupdate_index_eq.
  unfold up_qft.
  specialize (H1 n).
  assert (n < size) by lia. apply H1 in H2. inv H2.
  constructor.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy.
Qed.

Lemma assign_r_right_mode_out : forall n t f x r v i, v <> x -> 
        right_mode_val t (f (v,i)) ->
       right_mode_val t (assign_r f x r n (v,i)).
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy. 
Qed.

Lemma assign_seq_right_mode : forall n i f x r, i < n -> 
       right_mode_val Nor (assign_seq f x r n (x,i)).
Proof.
  induction n; intros; simpl.
  inv H0.
  bdestruct (i =? n).
  subst. rewrite eupdate_index_eq.
  constructor.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia.
Qed.

Lemma assign_seq_right_mode_out : forall n t f x r v i, v <> x -> 
        right_mode_val t (f (v,i)) ->
       right_mode_val t (assign_seq f x r n (v,i)).
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy.
Qed.

Lemma h_sem_right_mode_nor : forall n i f x, i < n -> 
       right_mode_val Nor (f (x,i)) ->
       right_mode_val Had (h_sem f x n (x,i)).
Proof.
  induction n; intros; simpl. lia.
  inv H1.
  bdestruct (i =? n). subst.
  rewrite eupdate_index_eq.
  rewrite <- H2. unfold h_case. destruct (r 0) eqn:eq1; constructor.
  rewrite rotate_1_1; try easy. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. rewrite <- H2. constructor.
Qed.


Lemma h_sem_right_mode_had : forall n i f x, i < n -> 
       right_mode_val Had (f (x,i)) ->
       right_mode_val Nor (h_sem f x n (x,i)).
Proof.
  induction n; intros; simpl. lia.
  inv H1.
  bdestruct (i =? n). subst.
  rewrite eupdate_index_eq.
  rewrite <- H2. unfold h_case.
  destruct b1. destruct b2; constructor.
  destruct b2; constructor.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. rewrite <- H2. constructor. easy.
Qed.

Lemma h_sem_right_mode_out : forall n t f x v i, v <> x -> 
       right_mode_val t (f (v,i)) ->
       right_mode_val t(h_sem f x n (v,i)).
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_index_neq by iner_p.
  apply IHn. lia. easy.
Qed.

(* This is the semantics for basic gate set of the language. *)
Fixpoint exp_sem (env:var -> nat) (e:exp) (st: posi -> val) : (posi -> val) :=
   match e with (SKIP p) => st
              | X p => (st[p |-> (exchange (st p))])
              | HCNOT p1 p2 => (st[p1 |-> (hexchange (st p1) (st p2))])
              | CU p e' => if get_cua (st p) then exp_sem env e' st else st
              | RZ q p => (st[p |-> times_rotate (st p) q])
              | RRZ q p => (st[p |-> times_r_rotate (st p) q])
              | SR n x => sr_rotate st x n (*n is the highest position to rotate. *)
              | SRR n x => srr_rotate st x n
              | Lshift x => (lshift st x (env x))
              | Rshift x => (rshift st x (env x))
              | Rev x => (reverse st x (env x))
               | H x => h_sem st x (env x)
               | QFT x => turn_qft st x (env x)
               | RQFT x => turn_rqft st x (env x)
              | e1 ; e2 => exp_sem env e2 (exp_sem env e1 st)
    end.

Lemma x_nor_sem : forall aenv f x v, nor_mode f x -> put_cu (f x) (¬ (get_cua (f x))) = v ->
                            exp_sem aenv (X x) f = (f[x |-> v]).
Proof.
 intros.
 apply nor_mode_nval in H0.
 destruct H0. destruct H0.
 unfold get_cua in H1. rewrite H0 in H1. 
 unfold put_cu in H1. subst. 
 assert ((exchange (f x)) = nval (¬ true) x0).
 unfold exchange. rewrite H0. reflexivity.
 rewrite <- H1. simpl. easy.
 unfold get_cua in H1. rewrite H0 in H1.
 unfold put_cu in H1. subst.
 assert ((exchange (f x)) = nval (¬ false) x0).
 unfold exchange. rewrite H0.
 reflexivity. 
 rewrite <- H1. simpl. easy. 
Qed.

Lemma lshift'_irrelevant :
   forall n size f x p, fst p <> x -> lshift' n size f x p = f p.
Proof.
  intros.
  induction n.
  simpl.
  rewrite eupdate_index_neq. easy.
  apply iner_neq_1. lia.
  simpl.
  rewrite eupdate_index_neq.
  rewrite IHn.
  easy.
  apply iner_neq_1. lia.
Qed.


Lemma rshift'_irrelevant :
   forall n size f x p, fst p <> x -> rshift' n size f x p = f p.
Proof.
  intros.
  induction n.
  intros. simpl.
  rewrite eupdate_index_neq. easy.
  apply iner_neq_1. lia.
  intros. simpl.
  rewrite eupdate_index_neq.
  rewrite IHn. easy.
  apply iner_neq_1. lia.
Qed.

Lemma sr_rotate'_ge : 
   forall n size f x p, n <= snd p -> sr_rotate' f x n size p = f p.
Proof.
 intros. induction n.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia.
 destruct p.
 bdestruct (x =? v).  subst.
 intros R. inv R. simpl in H0. lia.
 intros R. inv R. lia.
Qed.

Lemma sr_rotate'_lt : 
   forall n size f p, snd p < n -> n <= size -> 
        sr_rotate' f (fst p) n size p = times_rotate (f p) (size - (snd p)).
Proof.
 intros. induction n.
 easy.
 simpl.
 destruct p. simpl in *.
 bdestruct (n =? n0). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia. lia.
Qed.

Lemma sr_rotate'_irrelevant : 
   forall n size f x p, fst p <> x -> sr_rotate' f x n size p = f p.
Proof.
 intros. induction n.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy.
 destruct p. iner_p.
Qed.

Lemma srr_rotate'_lt : 
   forall n size f p, snd p < n -> n <= size -> 
        srr_rotate' f (fst p) n size p = times_r_rotate (f p) (size - (snd p)).
Proof.
 intros. induction n.
 easy.
 simpl.
 destruct p. simpl in *.
 bdestruct (n =? n0). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia. lia.
Qed.

Lemma srr_rotate'_ge : 
   forall n size f x p, n <= snd p -> srr_rotate' f x n size p = f p.
Proof.
 intros. induction n.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia.
 destruct p.
 bdestruct (x =? v).  subst.
 intros R. inv R. simpl in H0. lia.
 intros R. inv R. lia.
Qed.

Lemma srr_rotate'_irrelevant : 
   forall n size f x p, fst p <> x -> srr_rotate' f x n size p = f p.
Proof.
 intros. induction n.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy.
 destruct p. iner_p.
Qed.

Lemma lshift'_0 : forall m n f x, m <= n -> lshift' m n f x (x,0) = f (x,n).
Proof.
 intros.
 induction m.
 simpl. 
 rewrite eupdate_index_eq.
 easy.
 simpl.
 rewrite eupdate_index_neq by tuple_eq.
 rewrite IHm. easy. lia.
Qed.

Lemma lshift'_gt : forall i m n f x, m < i -> lshift' m n f x (x,i) = f (x,i).
Proof.
  intros.
  induction m.
  simpl.
  rewrite eupdate_index_neq. easy.
  tuple_eq.
  simpl.
  rewrite eupdate_index_neq.
  rewrite IHm.
  easy. lia.
  tuple_eq.
Qed.

Lemma lshift'_le : forall i m n f x, S i <= m <= n  -> lshift' m n f x (x,S i) = f (x,i).
Proof.
  induction m.
  simpl.
  intros. inv H0. inv H1.
  intros.
  simpl.
  bdestruct (i =? m). subst.
  rewrite eupdate_index_eq. easy. 
  rewrite eupdate_index_neq.
  rewrite IHm. easy.
  lia.
  tuple_eq.
Qed.

Lemma rshift'_0 : forall m n f x, m <= n -> rshift' m n f x (x,n) = f (x,0).
Proof.
 intros.
 induction m.
 simpl. 
 rewrite eupdate_index_eq.
 easy.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHm. easy. lia.
 tuple_eq.
Qed.

Lemma rshift'_gt : forall i m n f x, m <= n < i -> rshift' m n f x (x,i) = f (x,i).
Proof.
  induction m.
  simpl.
  intros.
  rewrite eupdate_index_neq. easy.
  tuple_eq.
  intros.
  simpl.
  rewrite eupdate_index_neq.
  rewrite IHm. easy.
  lia.
  tuple_eq.
Qed.

Lemma rshift'_le : forall i m n f x, i < m <= n  -> rshift' m n f x (x,i) = f (x,S i).
Proof.
  induction m.
  simpl.
  intros. inv H0. inv H1.
  intros.
  simpl.
  bdestruct (i =? m). subst.
  rewrite eupdate_index_eq. easy. 
  rewrite eupdate_index_neq.
  rewrite IHm. easy.
  lia.
  tuple_eq.
Qed.

Lemma assign_r_angle_same : forall n i f x r, i < n -> nor_modes f x n ->
              get_r ((assign_r f x r n) (x,i)) = get_r (f (x,i)).
Proof.
  induction n; intros; simpl.
  easy.
  bdestruct (i =? n). subst.
  rewrite eupdate_index_eq.
  unfold up_qft.
  unfold nor_modes in H1. unfold nor_mode in H1.
  specialize (H1 n H0). 
  destruct (f (x,n)). unfold get_r. easy. lia. lia.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn. easy. lia.
  unfold nor_modes in *. intros. apply H1. lia.
Qed.

Lemma assign_seq_covers : forall m n i f x g h, i < m <= n ->
            nor_modes f x n -> h i = get_cua (f (x,i)) ->
            assign_seq (assign_r f x g n) x h m (x,i) = f (x,i).
Proof.
 induction m; intros; simpl. lia.
 bdestruct (i =? m).
 subst.
 rewrite eupdate_index_eq.
 rewrite assign_r_angle_same; try easy.
 rewrite H2. 
 unfold nor_modes in H1.
 assert (m < n) by lia.
 specialize (H1 m H3). unfold nor_mode in H1.
 destruct (f (x,m)). unfold get_cua,get_r. easy. lia. lia.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHm; try easy. lia.
Qed.

Lemma assign_seq_ge : forall n i f x h, n <= i -> assign_seq f x h n (x,i) = f (x,i).
Proof.
 induction n; intros; simpl.
 easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma assign_seq_out : forall n p f x h, fst p <> x -> assign_seq f x h n p = f p.
Proof.
 induction n; intros; simpl.
 easy. destruct p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. easy.
Qed.

Lemma qft_start_nor_modes : forall avars aenv tenv tenv' x f, well_typed_pexp avars aenv tenv (QFT x) tenv'
        -> right_mode_env aenv tenv f -> nor_modes f x (aenv x).
Proof.
  intros. inv H0. unfold right_mode_env in H1.
  unfold nor_modes. intros.
  specialize (H1 Nor (x,i)). simpl in H1.
  inv H2.
  apply type_nor_modes with (env := tenv); try easy.
Qed.

Lemma assign_r_same_0 : forall n size f x h, 0 < n <= size
          -> nor_modes f x size -> (assign_r f x h n (x,0)) = qval (get_r (f (x,0))) h.
Proof.
  induction n; intros; simpl.
  lia.
  bdestruct (n =? 0). subst.
  rewrite eupdate_index_eq.
  unfold nor_modes in H1.
  assert (0 < size) by lia.
  specialize (H1 0 H2). unfold nor_mode in H1.
  unfold lshift_fun.
  unfold up_qft.
  destruct (f (x,0)). unfold get_r.
  assert ((fun i : nat => h (i + 0)) = h).
  apply functional_extensionality.
  intros. rewrite plus_0_r. easy. rewrite H3. easy. lia. lia. 
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn with (size := size); try easy. lia.
Qed.

Lemma assign_r_ge : forall n i f x h, n <= i -> assign_r f x h n (x,i) = f (x,i).
Proof.
 induction n; intros; simpl.
 easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma assign_r_out : forall n p f x h, fst p <> x -> assign_r f x h n p = f p.
Proof.
 induction n; intros; simpl.
 easy. destruct p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. easy.
Qed.


Lemma assign_seq_out_1 : forall n f h x y i, x <> y -> assign_seq f x h n (y,i) = f (y,i).
Proof.
 induction n; intros; simpl.
 easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. easy.
Qed.

Lemma h_sem_out : forall n f x y i, x <> y -> h_sem f x n (y,i) = f (y,i).
Proof.
 induction n; intros; simpl. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn; try easy.
Qed.

Lemma h_sem_ge : forall n f x i, n <= i -> h_sem f x n (x,i) = f (x,i).
Proof.
 induction n; intros; simpl. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn; try easy. lia.
Qed.

Lemma assign_r_lt : forall n f x r i, i < n -> assign_r f x r n (x,i) = up_qft (f (x,i)) (lshift_fun r i).
Proof.
 induction n; intros; simpl.
 lia.
 bdestruct (i =? n). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma lshift_fun_0 : forall f, lshift_fun f 0 = f.
Proof.
  intros. apply functional_extensionality. intros.
  unfold lshift_fun. rewrite plus_0_r. easy.
Qed.

Lemma efresh_exp_sem_irrelevant :
  forall e aenv  p f,
    exp_fresh aenv p e ->
    exp_sem aenv e f p = f p.
Proof.
  induction e;intros.
  subst. simpl. easy.
  simpl in *. inv H0.
  rewrite eupdate_index_neq. easy. nor_sym.
  simpl.
  destruct (get_cua (f p)).
  eapply IHe. inv H0. assumption. easy.
  simpl in *. inv H0.
  rewrite eupdate_index_neq. easy. nor_sym.
  simpl in *. inv H0.
  rewrite eupdate_index_neq. easy. nor_sym.
  inv H0.
  destruct H3.
  simpl. unfold sr_rotate.
  rewrite sr_rotate'_irrelevant; try easy.
  simpl. unfold sr_rotate.
  rewrite sr_rotate'_ge; try easy.
  inv H0.
  destruct H3.
  simpl. unfold srr_rotate.
  rewrite srr_rotate'_irrelevant; try easy.
  simpl. unfold srr_rotate.
  rewrite srr_rotate'_ge; try easy.
  inv H0. simpl.
  rewrite eupdate_index_neq by iner_p. easy.
  simpl. unfold lshift. inv H0.
  unfold or_not_eq in H3.
  destruct H3.
  apply lshift'_irrelevant. easy.
  destruct p.
  bdestruct (x =? v). subst.
  bdestruct (aenv v =? 0).  rewrite H1 in *. simpl.
  rewrite eupdate_same; try easy.
  rewrite lshift'_gt. easy. simpl in H0. lia.
  apply lshift'_irrelevant. iner_p.
  simpl. unfold rshift. inv H0.
  unfold or_not_eq in H3.
  destruct H3.
  apply rshift'_irrelevant. easy.
  destruct p.
  bdestruct (x =? v). subst.
  bdestruct (aenv v =? 0).  rewrite H1 in *. simpl.
  rewrite eupdate_same; try easy.
  rewrite rshift'_gt. easy. simpl in H0. lia.
  apply rshift'_irrelevant. iner_p.
  simpl. unfold reverse. inv H0.
  unfold or_not_eq in H3. destruct H3.
  bdestruct ((fst p =? x)). lia. simpl. easy.
  bdestruct ((snd p <? aenv x)). lia. 
  bdestruct ((fst p =? x)). simpl. easy. simpl. easy.
  simpl. inv H0. unfold or_not_eq in H3.
  unfold turn_qft.
  destruct H3.
  rewrite assign_r_out; try easy.
  destruct p.
  bdestruct (x =? v). subst.
  rewrite assign_r_ge; try easy.
  rewrite assign_r_out; try easy. iner_p.
  simpl. inv H0. unfold or_not_eq in H3.
  unfold turn_rqft.
  destruct H3.
  rewrite assign_seq_out; try easy.
  destruct p.
  bdestruct (x =? v). subst.
  rewrite assign_seq_ge; try easy.
  rewrite assign_seq_out; try easy. iner_p.
  simpl. inv H0. unfold or_not_eq in H3.
  destruct H3.
  destruct p.
  rewrite h_sem_out; try easy. iner_p.
  destruct p.
  bdestruct (x =? v). subst. simpl in H0.
  rewrite h_sem_ge; try easy.
  rewrite h_sem_out; try easy.
  inv H0. simpl.
  apply (IHe1) with (aenv := aenv) (f := f) in H4.
  apply (IHe2) with (aenv := aenv) (f := (exp_sem aenv e1 f)) in H5.
  rewrite H5. rewrite H4. easy.
Qed.

Lemma two_cu_same : forall aenv f p e1 e2, get_cua (f p) = true ->
                     exp_fresh aenv p e1 -> exp_sem aenv (e1 ; e2) f = exp_sem aenv (CU p e1; CU p e2) f. 
Proof.
  intros.
  simpl.
  destruct (get_cua (f p)) eqn:eq1.
  rewrite (efresh_exp_sem_irrelevant e1 aenv p f) by assumption.
  destruct (get_cua (f p)). easy.
  inv eq1. inv H0.
Qed.

Lemma well_typed_right_mode_exp : forall e aenv env f, well_typed_exp env e
          -> right_mode_env aenv env f -> right_mode_env aenv env (exp_sem aenv e f).
Proof.
  intros. induction H0; simpl; try easy.
  unfold right_mode_env in *. intros. 
  bdestruct (p ==? p0). subst.
  rewrite eupdate_index_eq.
  unfold exchange.
  specialize (H1 Nor p0 H2 H0). 
  destruct (f p0) eqn:eq1.
  apply mapsto_always_same with (v1:=Nor) in H3; try easy.
  rewrite <- H3 in *. constructor. inv H1. inv H1.
  rewrite eupdate_index_neq. apply H1; try easy. easy.
  unfold right_mode_env in *. intros. 
  bdestruct (p ==? p0). subst.
  rewrite eupdate_index_eq.
  unfold exchange.
  specialize (H1 Had p0 H2 H0). 
  destruct (f p0) eqn:eq1. inv H1.
  apply mapsto_always_same with (v1:=Had) in H3; try easy.
  rewrite <- H3 in *. constructor.
  inv H1. easy. inv H1.
  rewrite eupdate_index_neq. apply H1; try easy. easy.
  unfold right_mode_env in *. intros. 
  bdestruct (p ==? p1). subst.
  apply mapsto_always_same with (v1:=Had) in H5; try easy.
  rewrite <- H5.
  rewrite eupdate_index_eq.
  unfold hexchange.
  specialize (H1 Had p1 H4 H2). inv H1.
  destruct (f p2). constructor. easy.
  destruct (eqb b0 b3). constructor. easy.
  constructor. easy.
  constructor. easy.
  rewrite eupdate_index_neq by iner_p.
  apply H1. easy. easy.
  unfold right_mode_env in *.
  intros.
  bdestruct (p ==? p0). subst.
  rewrite eupdate_index_eq.
  unfold times_rotate.
  apply mapsto_always_same with (v1:=Nor) in H3; try easy.  
  rewrite <- H3 in *.
  specialize (H1 Nor p0 H2 H0).
  destruct (f p0) eqn:eq1.
  destruct b. constructor. constructor.
  inv H1. inv H1.
  rewrite eupdate_index_neq by iner_p. apply H1. easy. easy.
  unfold right_mode_env in *.
  intros.
  bdestruct (p ==? p0). subst.
  rewrite eupdate_index_eq.
  unfold times_rotate.
  apply mapsto_always_same with (v1:=Had) in H3; try easy.  
  rewrite <- H3 in *.
  specialize (H1 Had p0 H2 H0).
  destruct (f p0) eqn:eq1. inv H1.
  constructor. inv H1. easy.
  inv H1. 
  rewrite eupdate_index_neq by iner_p. apply H1. easy. easy.
  unfold right_mode_env in *.
  intros.
  bdestruct (p ==? p0). subst.
  rewrite eupdate_index_eq.
  unfold times_r_rotate.
  apply mapsto_always_same with (v1:=Nor) in H3; try easy.  
  rewrite <- H3 in *.
  specialize (H1 Nor p0 H2 H0).
  destruct (f p0) eqn:eq1.
  destruct b. constructor. constructor.
  inv H1. inv H1.
  rewrite eupdate_index_neq by iner_p. apply H1. easy. easy.
  unfold right_mode_env in *.
  intros.
  bdestruct (p ==? p0). subst.
  rewrite eupdate_index_eq.
  unfold times_rotate.
  apply mapsto_always_same with (v1:=Had) in H3; try easy.  
  rewrite <- H3 in *.
  specialize (H1 Had p0 H2 H0).
  destruct (f p0) eqn:eq1. inv H1.
  constructor. inv H1. easy.
  inv H1. 
  rewrite eupdate_index_neq by iner_p. apply H1. easy. easy.
  unfold right_mode_env in *.
  intros.
  unfold sr_rotate.
  bdestruct (x =? fst p). subst.
  bdestruct (snd p <=? m).
  rewrite sr_rotate'_lt; try lia.
  apply mapsto_always_same with (v1:=(Phi n)) in H4; try easy.
  rewrite <- H4 in *.
  unfold times_rotate.
  specialize (H1 (Phi n) p H3 H0).
  destruct (f p). inv H1. inv H1. constructor.
  rewrite sr_rotate'_ge; try lia.
  apply H1 ; try easy.
  rewrite sr_rotate'_irrelevant.
  apply H1; try easy. lia.
  unfold right_mode_env in *.
  intros. unfold srr_rotate.
  bdestruct (x =? fst p). subst.
  bdestruct (snd p <=? m).
  rewrite srr_rotate'_lt; try lia.
  apply mapsto_always_same with (v1:=(Phi n)) in H4; try easy.
  rewrite <- H4 in *.
  unfold times_r_rotate.
  specialize (H1 (Phi n) p H3 H0).
  destruct (f p). inv H1. inv H1. constructor.
  rewrite srr_rotate'_ge; try lia.
  apply H1 ; try easy.
  rewrite srr_rotate'_irrelevant.
  apply H1; try easy. lia.
  unfold right_mode_env in *. intros.
  unfold lshift.
  destruct p. 
  bdestruct (x =? v). subst. simpl in H2.
  destruct n.
  rewrite lshift'_0 by lia.
  apply H1. simpl in *. lia. easy.
  rewrite lshift'_le by lia. apply H1. simpl in *. lia. easy.
  rewrite lshift'_irrelevant by iner_p.
  apply H1. simpl in *. easy. easy.
  unfold right_mode_env in *. intros.
  unfold lshift.
  destruct p. 
  bdestruct (x =? v). subst. simpl in H2.
  destruct n.
  rewrite lshift'_0 by lia.
  apply H1. simpl in *. lia. easy.
  rewrite lshift'_le by lia. apply H1. simpl in *. lia. easy.
  rewrite lshift'_irrelevant by iner_p.
  apply H1. simpl in *. easy. easy.
  unfold right_mode_env in *. intros.
  unfold rshift.
  destruct p. 
  bdestruct (x =? v). subst. simpl in H2.
  bdestruct (n <? (aenv v - 1)).
  rewrite rshift'_le by lia. apply H1. simpl in *. lia. easy.
  bdestruct (n =? (aenv v - 1)).
  subst.
  rewrite rshift'_0 by lia. apply H1. simpl in *. lia. easy. lia.
  rewrite rshift'_irrelevant by iner_p. apply H1. simpl in *. lia. easy.
  unfold right_mode_env in *. intros.
  unfold rshift.
  destruct p. 
  bdestruct (x =? v). subst. simpl in H2.
  bdestruct (n <? (aenv v - 1)).
  rewrite rshift'_le by lia. apply H1. simpl in *. lia. easy.
  bdestruct (n =? (aenv v - 1)).
  subst.
  rewrite rshift'_0 by lia. apply H1. simpl in *. lia. easy. lia.
  rewrite rshift'_irrelevant by iner_p. apply H1. simpl in *. lia. easy.
  unfold right_mode_env in *. intros.
  destruct p. simpl in H2.
  unfold reverse. simpl.
  bdestruct (v =? x). bdestruct (n <? aenv x). simpl.
  subst. apply H1. simpl in *. lia. easy.
  simpl in *. apply H1. easy. easy.
  simpl in *. apply H1. easy. easy.
  unfold right_mode_env in *. intros.
  destruct p. simpl in H2.
  unfold reverse. simpl.
  bdestruct (v =? x). bdestruct (n <? aenv x). simpl.
  subst. apply H1. simpl in *. lia. easy.
  simpl in *. apply H1. easy. easy.
  simpl in *. apply H1. easy. easy.
Qed.

Lemma well_typed_right_mode_pexp : forall e avars aenv tenv tenv' f, 
        (forall u, In u (get_vars e) -> In u avars) ->
        well_typed_pexp avars aenv tenv e tenv'
          -> right_mode_env aenv tenv f -> right_mode_env aenv tenv' (exp_sem aenv e f).
Proof.
  induction e; intros.
  inv H1.
  apply well_typed_right_mode_exp; try easy.
  inv H1.
  apply well_typed_right_mode_exp; try easy.
  inv H1. inv H3.
  specialize (IHe avars aenv tenv' tenv' f).
  apply IHe in H10; try easy.
  unfold right_mode_env in *.
  intros.
  simpl.
  destruct (get_cua (f p)) eqn:eq1.
  apply H10; try easy.
  apply H2; try easy.
  intros.
  simpl in H0.
  apply H0. right; easy.
  inv H1.
  apply well_typed_right_mode_exp; try easy.
  inv H1.
  apply well_typed_right_mode_exp; try easy.
  inv H1.
  apply well_typed_right_mode_exp; try easy.
  inv H1.
  apply well_typed_right_mode_exp; try easy.
  inv H1.
  apply well_typed_right_mode_exp; try easy.
  inv H1.
  apply well_typed_right_mode_exp; try easy.
  inv H1.
  apply well_typed_right_mode_exp; try easy.
  inv H1.
  apply well_typed_right_mode_exp; try easy.
  simpl. inv H1. inv H3. unfold turn_qft.
  unfold right_mode_env in *. intros.
  destruct p. simpl in *.
  bdestruct (x =? v). subst.
  apply mapsto_equal with (s2 := (Env.add v (Phi (aenv v)) tenv)) in H3; try easy.
  apply mapsto_add1 in H3. subst.
  apply assign_r_right_mode. lia.
  intros. apply H2. easy. easy.
  apply assign_r_right_mode_out; try lia.
  apply H2. easy. simpl.
  apply mapsto_equal with (s2 := (Env.add x (Phi (aenv x)) tenv)) in H3; try easy.
  apply Env.add_3 in H3; try lia. easy.
  simpl.
  inv H1. inv H3. unfold turn_rqft.
  unfold right_mode_env in *. intros.
  destruct p. simpl in *.
  bdestruct (x =? v). subst.
  apply mapsto_equal with (s2 := (Env.add v Nor tenv)) in H3; try easy.
  apply mapsto_add1 in H3. subst.
  apply assign_seq_right_mode. lia.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H3; try easy.
  apply Env.add_3 in H3; try lia.
  apply assign_seq_right_mode_out; try lia.
  apply H2. easy. easy.
  simpl.
  inv H1. inv H3.
  unfold right_mode_env in *. intros.
  destruct p. simpl in *.
  bdestruct (x =? v). subst.
  apply mapsto_equal with (s2 := (Env.add v Had tenv)) in H3; try easy.
  apply mapsto_add1 in H3. subst.
  apply h_sem_right_mode_nor. lia. apply H2. easy. easy.
  apply mapsto_equal with (s2 := (Env.add x Had tenv)) in H3; try easy.
  apply Env.add_3 in H3; try lia.
  apply h_sem_right_mode_out. lia. apply H2. easy. easy.
  unfold right_mode_env in *. intros.
  destruct p. simpl in *.
  bdestruct (x =? v). subst.
  apply mapsto_equal with (s2 := (Env.add v Nor tenv)) in H3; try easy.
  apply mapsto_add1 in H3. subst.
  apply h_sem_right_mode_had. lia. apply H2; easy.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H3; try easy.
  apply Env.add_3 in H3; try lia.
  apply h_sem_right_mode_out. lia. apply H2; easy.
  simpl.
  inv H1. inv H3.
  simpl in H0.
  assert ((forall u : var, In u (get_vars e1) -> In u avars)).
  intros. apply H0.
  apply in_or_app. left. easy.
  specialize (IHe1 avars aenv tenv env' f H1 H6 H2).
  assert ((forall u : var, In u (get_vars e2) -> In u avars)). intros.
  apply H0.
  apply in_or_app. right. easy.
  specialize (IHe2 avars aenv env' tenv' (exp_sem aenv e1 f) H3 H8 IHe1).
  easy.
Qed.

Lemma rev_twice_same : forall f st x, reverse (reverse st x (f x)) x (f x) = st.
Proof.
  intros. unfold reverse.
  apply functional_extensionality.
  intros.
  destruct x0. simpl.
  bdestruct (v =? x).
  subst.
  bdestruct ((n <? f x)).
  simpl.
  bdestruct ((x =? x)).
  bdestruct (( f x - 1 - n <? f x)).
  simpl.
  assert ( f x - 1 - ( f x - 1 - n)= n) by lia.
  rewrite H3. easy.
  simpl. lia.
  lia. simpl. easy.
  simpl. easy.
Qed.

(*
  The following defines the inverse function of a given RCIRplus circuit. 
*)

Lemma inv_exp_involutive :
  forall p,
    inv_exp (inv_exp p) = p.
Proof.
  induction p; simpl; try easy.
  - rewrite IHp. easy.
  - rewrite IHp1, IHp2. easy.
Qed.

Lemma fresh_inv_exp :
  forall aenv p e,
    exp_fresh aenv p e ->
    exp_fresh aenv p (inv_exp e).
Proof.
  intros. induction H0; simpl; try constructor; try assumption.
Qed.

Lemma neu_l_inv_exp :
  forall e x l l',
    exp_neu_prop l ->
    exp_neu_l x l e l' ->
    exp_neu_l x l' (inv_exp e) l.
Proof.
  induction e; intros; simpl.
  1-8: inv H1 ; constructor.
  specialize (exp_neu_t_prop (Lshift x) x0 l l' H1 H0) as eq1.
  inv H1.
  destruct l'.
  apply rshift_neul_b.
  unfold fst_not_opp. easy.
  apply rshift_neul_b.
  unfold fst_not_opp.
  unfold exp_neu_prop in H0.
  specialize (H0 0 Rs).
  assert (0 + 1 < length (Rs :: s :: l')). simpl. lia.
  apply H0 in H1.
  simpl in *. unfold opp_ls. destruct s. contradiction.
  intros R. inv R. intros R. inv R. simpl in *. easy.
  unfold fst_not_opp in H4. destruct l.
  apply rshift_neul_a.
  apply rshift_neul_a.
  apply rshift_neul_ne. easy.
  specialize (exp_neu_t_prop (Rshift x) x0 l l' H1 H0) as eq1.
  inv H1.
  destruct l'.
  apply lshift_neul_b.
  unfold fst_not_opp. easy.
  apply lshift_neul_b.
  unfold fst_not_opp.
  unfold exp_neu_prop in H0.
  specialize (H0 0 Ls).
  assert (0 + 1 < length (Ls :: s :: l')). simpl. lia.
  apply H0 in H1.
  simpl in *. unfold opp_ls. destruct s.
  intros R. inv R. contradiction. intros R. inv R. simpl in *. easy.
  unfold fst_not_opp in H4. destruct l.
  apply lshift_neul_a.
  apply lshift_neul_a.
  apply lshift_neul_ne. easy.
  specialize (exp_neu_t_prop (Rev x) x0 l l' H1 H0) as eq1.
  inv H1.
  destruct l'.
  apply rev_neul_b.
  unfold fst_not_opp. easy.
  apply rev_neul_b.
  unfold fst_not_opp.
  unfold exp_neu_prop in H0.
  specialize (H0 0 Re).
  assert (0 + 1 < length (Re :: s :: l')). simpl. lia.
  apply H0 in H1.
  simpl in *. unfold opp_ls. destruct s.
  intros R. inv R. intros R. inv R. contradiction. simpl in *. easy.
  unfold fst_not_opp in H4. destruct l.
  apply rev_neul_a.
  apply rev_neul_a.
  apply rev_neul_ne. easy.
  1-3: inv H1 ; constructor.
  inv H1. 
  specialize (exp_neu_t_prop e1 x l l'0 H5 H0) as eq1.
  specialize (exp_neu_t_prop e2 x l'0 l' H7 eq1) as eq2.
  econstructor.
  apply IHe2.
  apply eq1. apply H7.
  apply IHe1; try easy.
Qed.

Lemma neu_inv_exp :
  forall l p,
    exp_neu l p ->
    exp_neu l (inv_exp p).
Proof.
  induction p; intros; simpl.
  1-2:constructor.
  constructor. inv H0.
  intros.
  apply H2 in H0.
  apply neu_l_inv_exp.
  unfold exp_neu_prop. intros. simpl in *. lia. easy.
  1-11:constructor.
  constructor. inv H0.
  apply IHp2. easy. apply IHp1. inv H0. easy.
Qed.

Lemma typed_inv_exp :
  forall tenv p,
    well_typed_exp tenv p ->
    well_typed_exp tenv (inv_exp p).
Proof.
  intros. induction p; simpl; try assumption.
  inv H0. inv H0. constructor. assumption.
  apply rrz_had. easy.
  inv H0.  constructor. easy.
  apply rz_had. easy.
  inv H0. apply srr_phi with (n := n); try easy.
  inv H0. apply sr_phi with (n := n); try easy.
  inv H0. constructor. easy.
  apply rshift_had. easy.
  inv H0.
  constructor.  easy.
  apply lshift_had. easy.
  inv H0. inv H0. inv H0.
Qed.

Lemma typed_inv_pexp :
  forall p avars aenv tenv tenv',
    well_typed_pexp avars aenv tenv p tenv' ->
    well_typed_pexp avars aenv tenv' (inv_exp p) tenv.
Proof.
  induction p; intros; simpl; try assumption.
  inv H0. constructor. easy.
  inv H0. constructor. easy.
  inv H0. inv H1.
  apply pcu_nor; try easy.
  apply fresh_inv_exp. easy.
  apply neu_inv_exp.  easy.
  apply IHp. easy.
  inv H0. constructor.
  apply typed_inv_exp in H1. simpl in H1. easy.
  inv H0. constructor.
  apply typed_inv_exp in H1. simpl in H1. easy.
  inv H0. constructor.
  apply typed_inv_exp in H1. simpl in H1. easy.
  inv H0. constructor.
  apply typed_inv_exp in H1. simpl in H1. easy.
  inv H0. constructor.
  apply typed_inv_exp in H1. simpl in H1. easy.
  inv H0. constructor.
  apply typed_inv_exp in H1. simpl in H1. easy.
  inv H0. constructor.
  apply typed_inv_exp in H1. simpl in H1. easy.
  inv H0. constructor.
  apply typed_inv_exp in H1. simpl in H1. easy.
  inv H0. inv H1.
  apply rqft_phi.
  apply mapsto_equal with (s1 := (Env.add x (Phi (aenv x)) tenv)).
  apply Env.add_1. easy.
  apply EnvFacts.Equal_sym. easy.
  unfold Env.Equal in *. intros.
  bdestruct ( x =? y). subst.
  rewrite find_add.
  apply Env.find_1 in H2. easy.
  rewrite EnvFacts.add_neq_o; try easy.
  rewrite H4.
  rewrite EnvFacts.add_neq_o; try easy.
  inv H0. inv H1.
  apply qft_nor.
  apply mapsto_equal with (s1 := (Env.add x Nor tenv)).
  apply Env.add_1. easy.
  apply EnvFacts.Equal_sym. easy.
  unfold Env.Equal in *. intros.
  bdestruct ( x =? y). subst.
  rewrite find_add.
  apply Env.find_1 in H2. easy.
  rewrite EnvFacts.add_neq_o; try easy.
  rewrite H4.
  rewrite EnvFacts.add_neq_o; try easy.
  inv H0. inv H1.
  apply h_had.
  apply mapsto_equal with (s1 := (Env.add x Had tenv)).
  apply Env.add_1. easy.
  apply EnvFacts.Equal_sym. easy.
  unfold Env.Equal in *. intros.
  bdestruct ( x =? y). subst.
  rewrite find_add.
  apply Env.find_1 in H2. easy.
  rewrite EnvFacts.add_neq_o; try easy.
  rewrite H4.
  rewrite EnvFacts.add_neq_o; try easy.
  constructor.
  apply mapsto_equal with (s1 := (Env.add x Nor tenv)).
  apply Env.add_1. easy.
  apply EnvFacts.Equal_sym. easy.
  unfold Env.Equal in *. intros.
  bdestruct ( x =? y). subst.
  rewrite find_add.
  apply Env.find_1 in H2. easy.
  rewrite EnvFacts.add_neq_o; try easy.
  rewrite H4.
  rewrite EnvFacts.add_neq_o; try easy.
  inv H0. inv H1.
  econstructor.
  apply IHp2. apply H6.
  apply IHp1. easy.
Qed.

Lemma exchange_twice_same :
   forall (f: posi -> val) p, exchange (exchange (f p)) = f p.
Proof.
  intros. unfold exchange.
  destruct (f p) eqn:eq1.
  assert ((¬ (¬ b)) = b) by btauto.
  rewrite H0. easy.
  easy.
  easy.
Qed.   


Lemma rotate_r_same : forall r q, (rotate (r_rotate r q) q) = r.
Proof.
  intros. unfold rotate,r_rotate.
  rewrite add_to_r_same.
  easy.
Qed.

Lemma rotate_same : forall r q, (r_rotate (rotate r q) q) = r.
Proof.
  intros. unfold rotate,r_rotate.
  rewrite add_to_same.
  easy.
Qed.


Lemma times_rotate_r_same: forall r q, times_rotate (times_r_rotate r q) q = r.
Proof.
  intros.
  unfold times_rotate, times_r_rotate.
  destruct r.
  destruct b.
  rewrite rotate_r_same.
  easy. easy.
  assert ((¬ (¬ b2)) = b2) by btauto.
  rewrite H0. easy.
  rewrite rotate_r_same.
  easy.
Qed.

Lemma times_rotate_same: forall r q, times_r_rotate (times_rotate r q) q = r.
Proof.
  intros.
  unfold times_rotate, times_r_rotate.
  destruct r.
  destruct b. 
  rewrite rotate_same.
  easy. easy.
  assert ((¬ (¬ b2)) = b2) by btauto.
  rewrite H0. easy.
  rewrite rotate_same.
  easy.
Qed.


Lemma lr_shift_same : forall n f x, 
                 lshift ((rshift f x n)) x n = f.
Proof.
  intros.
  unfold lshift,rshift.
  apply functional_extensionality.
  intros.
  destruct x0.
  bdestruct (v =? x). subst.
  bdestruct (n0 =? 0). subst.
  rewrite lshift'_0.
  rewrite rshift'_0. easy. easy. easy.
  destruct n0. lia.
  bdestruct (S n0 <=? n-1).
  rewrite lshift'_le.
  rewrite rshift'_le.
  easy. lia. lia.
  rewrite lshift'_gt.
  rewrite rshift'_gt. easy.
  lia. lia.
  rewrite lshift'_irrelevant.
  rewrite rshift'_irrelevant.
  easy. simpl; assumption.
  simpl;assumption.
Qed.

Lemma rl_shift_same : forall n f x,
                 rshift ((lshift f x n)) x n = f.
Proof.
  intros.
  unfold lshift,rshift.
  apply functional_extensionality.
  intros.
  destruct x0.
  bdestruct (v =? x). subst.
  bdestruct (n0 =? n-1). subst.
  rewrite rshift'_0.
  rewrite lshift'_0. easy. easy. easy.
  bdestruct (n0 <? n-1).
  rewrite rshift'_le.
  rewrite lshift'_le.
  easy. lia. lia.
  rewrite rshift'_gt.
  rewrite lshift'_gt. easy.
  lia. lia.
  rewrite rshift'_irrelevant.
  rewrite lshift'_irrelevant.
  easy. simpl; assumption.
  simpl;assumption.
Qed.

Lemma h_sem_gt : forall m n f x v,
      m <= n -> 
       h_sem (f[(x,n) |-> v]) x m = (h_sem f x m)[(x,n) |-> v].
Proof.
  induction m; intros.
  simpl. easy.
  simpl.
  rewrite eupdate_twice_neq by iner_p.
  rewrite IHm by lia.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

Lemma had_twice_same : forall n f x t, 
     (forall i, i < n -> right_mode_val t (f (x,i))) ->
    h_sem (h_sem f x n) x n = f.
Proof.
  induction n; intros.
  simpl. easy.
  simpl.
  rewrite h_sem_gt by lia.
  rewrite eupdate_twice_eq.
  rewrite eupdate_index_eq.
  rewrite h_case_twice_same with (t := t).
  rewrite IHn with (t := t).
  rewrite eupdate_same. easy. easy.
  intros. apply H0. lia. apply H0. lia.
Qed.

Lemma sr_rotate_up : forall m n f x size v, m <= n -> 
     sr_rotate' (f[(x,n) |-> v]) x m size = (sr_rotate' f x m size)[(x,n) |-> v].
Proof.
  induction m; intros; simpl.
  easy.
  rewrite eupdate_twice_neq by iner_p.
  rewrite <- (IHm n f).
  rewrite eupdate_index_neq by iner_p. easy. lia.
Qed.

Lemma sr_rotate_rotate: forall f x n size, sr_rotate' (srr_rotate' f x n size) x n size = f.
Proof.
  intros. induction n;simpl. easy.
  simpl. rewrite sr_rotate_up by lia.
  rewrite eupdate_twice_eq.
  rewrite IHn.
  rewrite eupdate_same. easy.
  rewrite eupdate_index_eq.
  rewrite times_rotate_r_same. easy.
Qed.

Lemma srr_rotate_up : forall m n f x size v, m <= n -> 
     srr_rotate' (f[(x,n) |-> v]) x m size = (srr_rotate' f x m size)[(x,n) |-> v].
Proof.
  induction m; intros; simpl.
  easy.
  rewrite eupdate_twice_neq by iner_p.
  rewrite <- (IHm n f).
  rewrite eupdate_index_neq by iner_p. easy. lia.
Qed.

Lemma srr_rotate_rotate: forall f x n size, srr_rotate' (sr_rotate' f x n size) x n size = f.
Proof.
  intros. induction n;simpl. easy.
  simpl. rewrite srr_rotate_up by lia.
  rewrite eupdate_twice_eq.
  rewrite IHn.
  rewrite eupdate_same. easy.
  rewrite eupdate_index_eq.
  rewrite times_rotate_same. easy.
Qed.

Lemma exp_sem_assoc : forall aenv f e1 e2 e3, 
               exp_sem aenv (e1 ; e2 ; e3) f = exp_sem aenv (e1 ; (e2 ; e3)) f.
Proof.
  intros. simpl. easy.
Qed.

(* QFT uniformity. For any varible x that is in Phi mode, 
   all qubits form a special format. *)
Lemma pexp_sem_assoc : forall env f e1 e2 e3, 
               exp_sem env (e1 ; e2 ; e3) f = exp_sem env (e1 ; (e2 ; e3)) f.
Proof.
  intros. simpl. easy.
Qed.

Definition phi_mode (f : posi -> val)  (x:posi) : Prop :=
       match f x with qval rc r => True | _ => False end.

Definition phi_modes (f:posi -> val) (x:var) (n:nat) :=
      forall i, i < n -> phi_mode f (x,i).

Definition get_snd_r (f:posi -> val) (p:posi) :=
    match (f p) with qval rc r => r | _ => allfalse end.

Lemma assign_seq_lt : forall n i f x h, i < n -> assign_seq f x h n (x,i) = nval (h i) (get_r (f (x,i))).
Proof.
 induction n; intros; simpl.
 easy.
 bdestruct (i =? n). subst.
 rewrite eupdate_index_eq. 
 easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma assign_r_covers : forall m n i f x g h, i < m <= n ->
            phi_modes f x n -> lshift_fun h i  = get_snd_r f (x,i) ->
            assign_r (assign_seq f x g n) x h m (x,i) = f (x,i).
Proof.
 induction m; intros; simpl. lia.
 bdestruct (i =? m).
 subst.
 rewrite eupdate_index_eq.
 rewrite assign_seq_lt; try lia.
 unfold up_qft.
 unfold phi_modes in H1.
 specialize (H1 m).
 assert (m < n) by lia. apply H1 in H3.
 unfold phi_mode in H3.
 unfold get_snd_r in H2.
 destruct (f (x,m)). lia. lia.
 rewrite <- H2.
 unfold get_r. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHm; try easy. lia.
Qed.

Lemma rqft_start_phi_modes : forall avars aenv tenv tenv' x f, well_typed_pexp avars aenv tenv (RQFT x) tenv'
        -> right_mode_env aenv tenv f -> phi_modes f x (aenv x).
Proof.
  intros. inv H0. inv H2.
  unfold right_mode_env in H1.
  unfold phi_modes. intros.
  specialize (H1 (Phi (aenv x)) (x,i)). simpl in H1. 
  specialize (H1 H0 H3). inv H1.
  unfold phi_mode. rewrite <- H6. easy.
Qed.

Lemma sr_rotate'_lt_1
     : forall (n size : nat) (f : posi -> val) x i,
       i < n <= size ->
       sr_rotate' f x n size (x,i) = times_rotate (f (x,i)) (size - i).
Proof.
 intros. induction n.
 easy.
 simpl.
 bdestruct (n =? i). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Lemma srr_rotate'_lt_1
     : forall (n size : nat) (f : posi -> val) x i,
       i < n <= size ->
       srr_rotate' f x n size (x,i) = times_r_rotate (f (x,i)) (size - i).
Proof.
 intros. induction n.
 easy.
 simpl.
 bdestruct (n =? i). subst.
 rewrite eupdate_index_eq. easy.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn. easy. lia.
Qed.

Definition qft_uniform (aenv: var -> nat) (tenv:env) (f:posi -> val) :=
   forall x, Env.MapsTo x (Phi (aenv x)) tenv -> 
             (forall i, i < aenv x -> get_snd_r f (x,i) = (lshift_fun (get_r_qft f x) i)).

Lemma addto_shift_same : forall r n size x, n < size -> addto (fun i => r (i+n)) (size - n) x = addto r size (x + n).
Proof.
  intros. unfold addto.
  unfold cut_n, fbrev.
  bdestruct (x <? size - n). bdestruct (x + n <? size). 
  assert ((size - 1 - (x + n)) = (size - n - 1 - x)) by lia. rewrite H3.
  unfold sumfb.
  bdestruct (size - n - 1 - x <? size - n).
  bdestruct (size - n - 1 - x <? size).
  assert ((size - n - 1 - (size - n - 1 - x) + n) = (size - 1 - (size - n - 1 - x))) by lia.
  rewrite H6.
  rewrite carry_lt_same with (n:= size - n) (g := (fun i : nat =>
    if i <? size
    then if i <? size then r (size - 1 - i) else r i
    else allfalse i)); try lia. easy.
  intros.
  bdestruct (i <? size - n).
  bdestruct (i <? size).
  assert (size - n - 1 - i + n = size - 1 - i) by lia. rewrite H10. easy.
  1-5:lia.
  bdestruct (x + n <? size). lia. easy.
Qed.

Lemma sumfb_lt_same : forall m n f g h h' b, m < n -> (forall i, i < n -> f i = g i)
               -> (forall i, i < n -> h i = h' i) -> sumfb b f h m = sumfb b g h' m.
Proof.
 intros. unfold sumfb.
 rewrite  carry_lt_same_1 with (n:= n) (g:=g) (h' := h'); try lia.
 rewrite H1 by lia. rewrite H2 by lia. easy.
 easy. easy.
Qed.


Lemma addto_n_shift_same : forall r n size x, n < size -> addto_n (fun i => r (i+n)) (size - n) x = addto_n r size (x + n).
Proof.
  intros. unfold addto_n.
  unfold cut_n, fbrev.
  bdestruct (x <? size - n). bdestruct (x + n <? size). 
  assert ((size - 1 - (x + n)) = (size - n - 1 - x)) by lia. rewrite H3.
  rewrite sumfb_lt_same with (n:= size - n) (g:= (fun i : nat =>
   if i <? size
   then if i <? size then r (size - 1 - i) else r i
   else allfalse i)) (h' := (negatem size (nat2fb 0))); try lia. easy.
  intros. 
  bdestruct (i <? size - n).
  bdestruct (i <? size).
  assert ((size - n - 1 - i + n) = (size - 1 - i)) by lia. rewrite H7. easy. lia. lia.
  intros.
  rewrite nat2fb_0. unfold negatem.
  bdestruct (i <? size - n).
  bdestruct (i <? size). easy.
  1-3:lia.
  bdestruct (x + n <? size). lia. easy.
Qed.

Lemma qft_uniform_sr_rotate : forall n i size f x, i < n <= size -> phi_modes f x size ->
           get_snd_r f (x, i) = lshift_fun (get_r_qft f x) i
     -> get_snd_r (sr_rotate' f x n size) (x, i) = lshift_fun (get_r_qft (sr_rotate' f x n size) x) i.
Proof.
 induction n;intros;simpl. lia.
 bdestruct (i =? n). subst.
 unfold get_snd_r,get_r_qft.
 bdestruct (n =? 0). subst.
 rewrite eupdate_index_eq.
 unfold lshift_fun.
 apply functional_extensionality. intros.
 rewrite plus_0_r. easy.
 rewrite eupdate_index_eq.
 rewrite eupdate_index_neq by iner_p.
 rewrite sr_rotate'_lt_1.
 unfold lshift_fun.
 unfold get_snd_r,get_r_qft,lshift_fun in H2.
 apply functional_extensionality. intros.
 unfold times_rotate.
 unfold phi_modes in H1.
 assert (eq1 := H1).
 assert (n < size) by lia. assert (0 < size) by lia.
 specialize (H1 n H4).
 specialize (eq1 0 H5).
 unfold phi_mode in *.
 destruct (f (x, n)). lia. lia.
 destruct (f (x,0)). lia. lia.
 subst. unfold rotate.
 rewrite addto_shift_same; try lia.
 assert ((size - 0)  = size) by lia. rewrite H2. easy. lia.
 unfold get_snd_r,get_r_qft in *.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn; try easy. lia.
Qed.

Lemma qft_uniform_srr_rotate : forall n i size f x, i < n <= size -> phi_modes f x size ->
           get_snd_r f (x, i) = lshift_fun (get_r_qft f x) i
     -> get_snd_r (srr_rotate' f x n size) (x, i) = lshift_fun (get_r_qft (srr_rotate' f x n size) x) i.
Proof.
 induction n;intros;simpl. lia.
 bdestruct (i =? n). subst.
 unfold get_snd_r,get_r_qft.
 bdestruct (n =? 0). subst.
 rewrite eupdate_index_eq.
 unfold lshift_fun.
 apply functional_extensionality. intros.
 rewrite plus_0_r. easy.
 rewrite eupdate_index_eq.
 rewrite eupdate_index_neq by iner_p.
 rewrite srr_rotate'_lt_1.
 unfold lshift_fun.
 unfold get_snd_r,get_r_qft,lshift_fun in H2.
 apply functional_extensionality. intros.
 unfold times_r_rotate.
 unfold phi_modes in H1.
 assert (eq1 := H1).
 assert (n < size) by lia. assert (0 < size) by lia.
 specialize (H1 n H4).
 specialize (eq1 0 H5).
 unfold phi_mode in *.
 destruct (f (x, n)). lia. lia.
 destruct (f (x,0)). lia. lia.
 subst. unfold r_rotate.
 rewrite addto_n_shift_same; try lia.
 assert ((size - 0)  = size) by lia. rewrite H2. easy. lia.
 unfold get_snd_r,get_r_qft in *.
 rewrite eupdate_index_neq by iner_p.
 rewrite eupdate_index_neq by iner_p.
 rewrite IHn; try easy. lia.
Qed.

Lemma sr_rotate'_get_snd_r_ge : forall n i size f x, n <= i -> n <= size -> 
         get_snd_r (sr_rotate' f x n size) (x,i) = get_snd_r f (x,i).
Proof.
 intros. induction n.
 easy. unfold get_snd_r in *.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia. lia. iner_p.
Qed.

Lemma sr_rotate'_get_snd_r_out : forall n i size f x x0, n <= size -> x <> x0 -> 
         get_snd_r (sr_rotate' f x n size) (x0,i) = get_snd_r f (x0,i).
Proof.
 intros. induction n.
 easy. unfold get_snd_r in *.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia. iner_p.
Qed.

Lemma srr_rotate'_get_snd_r_ge : forall n i size f x, n <= i -> n <= size -> 
         get_snd_r (srr_rotate' f x n size) (x,i) = get_snd_r f (x,i).
Proof.
 intros. induction n.
 easy. unfold get_snd_r in *.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia. lia. iner_p.
Qed.

Lemma srr_rotate'_get_snd_r_out : forall n i size f x x0, n <= size -> x <> x0 -> 
         get_snd_r (srr_rotate' f x n size) (x0,i) = get_snd_r f (x0,i).
Proof.
 intros. induction n.
 easy. unfold get_snd_r in *.
 simpl.
 rewrite eupdate_index_neq.
 rewrite IHn. easy. lia. iner_p.
Qed.

Lemma qft_uniform_exp_trans : 
    forall e f avars aenv tenv tenv', qft_uniform aenv tenv f -> well_typed_pexp avars aenv tenv e tenv'
            -> right_mode_env aenv tenv f -> 
                  (forall u, In u (get_vars e) -> In u avars)
                    -> qft_uniform aenv tenv' (exp_sem aenv e f).
Proof.
  induction e; intros; simpl.
  inv H1. easy.
  inv H1.
  unfold qft_uniform in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  simpl in *. inv H4.
  apply mapsto_always_same with (v2:=Nor) in H1; try easy.
  apply mapsto_always_same with (v2:=Had) in H1; try easy.
  simpl in *.
  unfold get_snd_r,get_r_qft in *.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  inv H1. inv H4.
  destruct (get_cua (f p)) eqn:eq1.
  apply IHe with (avars := avars) (tenv := tenv'); try easy.
  intros. apply H3. simpl. right. easy.
  easy.
  inv H1.
  unfold qft_uniform in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  inv H4. simpl in *.
  apply mapsto_always_same with (v2:=Nor) in H1; try easy.
  apply mapsto_always_same with (v2:=Had) in H1; try easy.
  unfold get_snd_r,get_r_qft in *.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  inv H1.
  unfold qft_uniform in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  inv H4.
  apply mapsto_always_same with (v2:=Nor) in H1; try easy.
  apply mapsto_always_same with (v2:=Had) in H1; try easy.
  unfold get_snd_r,get_r_qft in *.
  repeat rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  inv H1.
  unfold qft_uniform in *. intros.
  unfold sr_rotate.
  bdestruct (x =? x0). subst.
  bdestruct (i <? S q).
  rewrite qft_uniform_sr_rotate. easy. lia.
  inv H4.
  apply mapsto_always_same with (v2:=(Phi n)) in H1; try easy.
  inv H1.
  unfold right_mode_env in H2.
  unfold phi_modes. intros.
  specialize (H2 (Phi (aenv x0)) (x0,i0)).
  simpl in H2. assert (i0 < aenv x0) by lia.
  apply H2 in H4; try easy.
  inv H4. unfold phi_mode.
  assert ((f (@pair Env.key nat x0 i0)) = (f (@pair var nat x0 i0))) by easy.
  rewrite H4 in *. rewrite <- H9. lia.
  rewrite H0; try easy.
  rewrite sr_rotate'_get_snd_r_ge; try lia.
  rewrite H0; try easy.
  unfold lshift_fun.
  apply functional_extensionality. intros.
  unfold get_r_qft.
  inv H4.
  apply mapsto_always_same with (v2:=(Phi n)) in H1; try easy.
  inv H1.
  rewrite sr_rotate'_lt_1; try lia.
  unfold right_mode_env in H2.
  specialize (H2 (Phi (aenv x0)) (x0,0)).
  simpl in *.
  apply H2 in H10.
  inv H10.
  assert ((f (@pair Env.key nat x0 0)) = (f (@pair var nat x0 0))) by easy.
  rewrite H1 in *. rewrite <- H7.
  unfold times_rotate, rotate,addto.
  bdestruct (x + i <? S q). lia. easy. simpl. lia.
  rewrite sr_rotate'_get_snd_r_out; try lia.
  rewrite H0; try easy.
  unfold lshift_fun.
  apply functional_extensionality. intros.
  unfold get_r_qft.
  rewrite sr_rotate'_irrelevant; try lia. easy.
  iner_p.
  inv H1. inv H4.
  unfold qft_uniform in *. intros.
  unfold srr_rotate.
  bdestruct (x =? x0). subst.
  bdestruct (i <? S q).
  rewrite qft_uniform_srr_rotate. easy. lia.
  apply mapsto_always_same with (v2:=(Phi n)) in H1; try easy.
  inv H1.
  unfold right_mode_env in H2.
  unfold phi_modes. intros.
  specialize (H2 (Phi (aenv x0)) (x0,i0)).
  simpl in H2. assert (i0 < aenv x0) by lia.
  apply H2 in H6; try easy.
  inv H6. unfold phi_mode.
  assert ((f (@pair Env.key nat x0 i0)) = (f (@pair var nat x0 i0))) by easy.
  rewrite H6 in *. rewrite <- H11. lia.
  rewrite H0; try easy.
  rewrite srr_rotate'_get_snd_r_ge; try lia.
  rewrite H0; try easy.
  unfold lshift_fun.
  apply functional_extensionality. intros.
  unfold get_r_qft.
  apply mapsto_always_same with (v2:=(Phi n)) in H1; try easy.
  inv H1.
  rewrite srr_rotate'_lt_1; try lia.
  unfold right_mode_env in H2.
  specialize (H2 (Phi (aenv x0)) (x0,0)).
  apply H2 in H7.
  inv H7.
  assert ((f (@pair Env.key nat x0 0)) = (f (@pair var nat x0 0))) by easy.
  rewrite H1 in *. rewrite <- H9.
  unfold times_r_rotate, r_rotate,addto_n.
  bdestruct (x + i <? S q - 0). lia. easy. simpl. lia.
  rewrite srr_rotate'_get_snd_r_out; try lia.
  rewrite H0; try easy.
  unfold lshift_fun.
  apply functional_extensionality. intros.
  unfold get_r_qft.
  rewrite srr_rotate'_irrelevant; try lia. easy.
  iner_p.
  inv H1. inv H4.
  unfold qft_uniform in *. intros.
  bdestruct (p1 ==? (x,i)). subst.
  simpl in H8.
  apply mapsto_always_same with (v2:=Had) in H1; try easy.
  unfold get_snd_r in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  destruct p1.
  bdestruct (v =? x). subst. simpl in *.
  apply mapsto_always_same with (v2:=Had) in H1; try easy.
  unfold get_r_qft.
  rewrite eupdate_index_neq by iner_p. easy.
  inv H1. inv H4.
  unfold qft_uniform in *.
  intros.
  bdestruct (x0 =? x). subst.
  apply mapsto_always_same with (v2:=Nor) in H1; try easy.
  assert (get_snd_r (lshift f x (aenv x)) (x0, i) = get_snd_r f (x0,i)).
  unfold get_snd_r,lshift. rewrite lshift'_irrelevant. easy. easy.
  rewrite H7. rewrite H0.
  assert ((get_r_qft (lshift f x (aenv x)) x0) = get_r_qft f x0).
  unfold get_r_qft,lshift.
  rewrite lshift'_irrelevant. easy. easy.
  rewrite H8. easy. 1-2:easy.
  unfold qft_uniform in *.
  intros.
  bdestruct (x0 =? x). subst.
  apply mapsto_always_same with (v2:=Had) in H1; try easy.
  assert (get_snd_r (lshift f x (aenv x)) (x0, i) = get_snd_r f (x0,i)).
  unfold get_snd_r,lshift. rewrite lshift'_irrelevant. easy. easy.
  rewrite H7. rewrite H0.
  assert ((get_r_qft (lshift f x (aenv x)) x0) = get_r_qft f x0).
  unfold get_r_qft,lshift.
  rewrite lshift'_irrelevant. easy. easy.
  rewrite H8. easy. 1-2:easy.
  unfold qft_uniform in *.
  intros.
  bdestruct (x0 =? x). subst. inv H1. inv H6.
  apply mapsto_always_same with (v2:=Nor) in H4; try easy.
  apply mapsto_always_same with (v2:=Had) in H4; try easy.
  unfold get_snd_r, rshift,get_r_qft.
  repeat rewrite rshift'_irrelevant; try easy.
  unfold get_snd_r,get_r_qft in H0.
  rewrite H0. easy.
  inv H1. easy. easy.
  unfold qft_uniform in *.
  intros.
  bdestruct (x0 =? x). subst.
  inv H1. inv H6.
  apply mapsto_always_same with (v2:=Nor) in H4; try easy.
  apply mapsto_always_same with (v2:=Had) in H4; try easy.
  unfold get_snd_r,reverse,get_r_qft in *.
  simpl in *.
  bdestruct (x0 =? x). lia. simpl.
  rewrite H0. easy. inv H1. easy. easy.
  inv H1. inv H4.
  unfold qft_uniform in *. intros.
  bdestruct (x0 =? x). subst. 
  unfold turn_qft,get_snd_r.
  rewrite assign_r_lt; try lia.
  unfold get_r_qft.
  rewrite assign_r_lt; try lia.
  unfold up_qft.
  unfold right_mode_env in H2. 
  specialize (H2 Nor (x,i)) as eq1. simpl in eq1. 
  specialize (H2 Nor (x,0)) as eq2. simpl in eq2.
  assert (0 < aenv x) by lia.
  specialize (eq1 H4 H5). specialize (eq2 H6 H5).
  inv eq1. inv eq2.
  rewrite lshift_fun_0. easy.
  apply mapsto_equal with (s2 := (Env.add x (Phi (aenv x)) tenv)) in H1; try easy.
  apply Env.add_3 in H1 ; try lia. 
  assert (get_snd_r (turn_qft f x (aenv x)) (x0, i) = get_snd_r f (x0, i)).
  unfold get_snd_r,turn_qft.
  rewrite assign_r_out; try easy. rewrite H8.
  rewrite H0; try easy.
  unfold get_r_qft,turn_qft.
  rewrite assign_r_out; try easy.
  unfold qft_uniform in *. intros.
  inv H1. inv H6. 
  bdestruct (x =? x0). subst.
  apply mapsto_equal with (k := x0) (v:= (Phi (aenv x0))) in H9; try easy.
  apply mapsto_add1 in H9. inv H9.
  unfold turn_rqft.
  unfold get_snd_r in *.
  rewrite assign_seq_out_1.
  rewrite H0; try easy.
  unfold get_r_qft.
  destruct (f (x, 0)) eqn:eq1.
  rewrite assign_seq_out_1 by lia. easy.
  rewrite assign_seq_out_1 by lia. easy.
  rewrite assign_seq_out_1 by lia. easy.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H4.
  apply Env.add_3 in H4. easy. lia. easy. lia.
  unfold qft_uniform in *. intros.
  bdestruct (x =? x0). subst.
  inv H1. inv H6.
  apply mapsto_equal with (k := x0) (v:= (Phi (aenv x0))) in H9; try easy.
  apply mapsto_add1 in H9. inv H9.
  apply mapsto_equal with (k := x0) (v:= (Phi (aenv x0))) in H9; try easy.
  apply mapsto_add1 in H9. inv H9.
  unfold get_snd_r in *.
  rewrite h_sem_out by easy. rewrite H0; try easy.
  unfold get_r_qft.
  rewrite h_sem_out by easy. easy.
  inv H1. inv H7.
  apply mapsto_equal with (k := x0) (v:= (Phi (aenv x0))) in H10; try easy.
  apply Env.add_3 in H10. easy. lia.
  apply mapsto_equal with (k := x0) (v:= (Phi (aenv x0))) in H10; try easy.
  apply Env.add_3 in H10. easy. lia.
  inv H1. inv H4.
  assert ((forall u : var, In u (get_vars e1) -> In u avars)). intros.
  apply H3. simpl. apply in_or_app. left. easy.
  specialize (IHe1 f avars aenv tenv env' H0 H7 H2 H1).
  apply well_typed_right_mode_pexp with (avars := avars) (e := e1) (tenv' := env') in H2; try easy.
  specialize (IHe2 (exp_sem aenv e1 f) avars aenv env' tenv' IHe1 H9). apply IHe2; try easy.
  intros. apply H3. simpl. apply in_or_app. right. easy.
Qed.

Lemma qft_uniform_put_cus_same : 
    forall f x g n aenv tenv, qft_uniform aenv tenv f -> right_mode_env aenv tenv f 
                 -> qft_uniform aenv tenv (put_cus f x g n).
Proof.
  intros. 
  unfold qft_uniform in *. intros.
  unfold put_cus,get_snd_r,get_r_qft in *.
  simpl in *.
  bdestruct (x0 =? x). subst.
  unfold right_mode_env in H1.
  specialize (H1 (Phi (aenv x)) (x,i)) as eq1.
  simpl in eq1.
  specialize (eq1 H3 H2).
  specialize (H1 (Phi (aenv x)) (x,0)) as eq2.
  simpl in eq2.
  assert (0 < aenv x) by lia.
  specialize (eq2 H4 H2).
  bdestruct (i <? n). simpl.
  bdestruct (0 <? n).
  specialize (H0 x H2 i H3).
  unfold put_cu.
  inv eq1. inv eq2.
  assert ((@pair var nat x i) = (@pair Env.key nat x i)) by easy.
  rewrite H7 in *.
  rewrite <- H9 in *.
  assert ((@pair var nat x 0) = (@pair Env.key nat x 0)) by easy.
  rewrite H8 in *.
  rewrite <- H10 in *.
  easy. lia.
  bdestruct (0 <? n).
  specialize (H0 x H2 i H3).
  unfold put_cu.
  inv eq1. inv eq2.
  assert ((@pair var nat x i) = (@pair Env.key nat x i)) by easy.
  rewrite H7 in *.
  rewrite <- H9 in *.
  assert ((@pair var nat x 0) = (@pair Env.key nat x 0)) by easy.
  rewrite H8 in *.
  rewrite <- H10 in *. easy.
  assert (n = 0) by lia. subst.
  apply H0; try easy.
  apply H0; try easy.
Qed.

Lemma get_r_qft_lshift : forall f x m n, m < n -> (forall i, n <= i -> get_r_qft f x i = false) ->
            (forall i, n - m <= i -> lshift_fun (get_r_qft f x) m i = false).
Proof.
  intros.
  unfold lshift_fun.
  apply H1. lia.
Qed. 

Definition qft_gt (aenv: var -> nat) (tenv:env) (f:posi -> val) :=
   forall x, Env.MapsTo x (Phi (aenv x)) tenv -> (forall i, 0 < (aenv x) <= i -> get_r_qft f x i = false).

Lemma qft_gt_exp_trans : 
    forall e f avars aenv tenv tenv', qft_gt aenv tenv f -> well_typed_pexp avars aenv tenv e tenv'
            -> right_mode_env aenv tenv f -> (forall u, In u (get_vars e) -> In u avars)
            -> qft_gt aenv tenv' (exp_sem aenv e f).
Proof.
  induction e; intros; simpl.
  inv H1. easy.
  unfold qft_gt in *. intros.
  unfold get_r_qft in *.
  bdestruct (p ==? (x,0)).
  subst.
  inv H1. inv H6. simpl in *.
  apply mapsto_always_same with (v1 := (Phi (aenv x))) in H8. inv H8. easy.
  apply mapsto_always_same with (v1 := (Phi (aenv x))) in H8. inv H8. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  inv H1. easy.
  inv H1. inv H4.
  destruct (get_cua (f p)). apply IHe with (avars := avars) (tenv := tenv') (tenv' := tenv') ; try easy.
  intros. apply H3. simpl. right. easy.
  easy.
  unfold qft_gt in *. intros.
  unfold get_r_qft in *.
  bdestruct (p ==? (x,0)).
  subst.
  inv H1. inv H6. simpl in H8.
  apply mapsto_always_same with (v1 := (Phi (aenv x))) in H8. inv H8. easy.
  apply mapsto_always_same with (v1 := (Phi (aenv x))) in H8. inv H8. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  inv H1. easy.
  unfold qft_gt in *. intros.
  unfold get_r_qft in *.
  bdestruct (p ==? (x,0)).
  subst.
  inv H1. inv H6. simpl in H8.
  apply mapsto_always_same with (v1 := (Phi (aenv x))) in H8. inv H8. easy.
  apply mapsto_always_same with (v1 := (Phi (aenv x))) in H8. inv H8. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  inv H1. easy.
  unfold qft_gt in *. intros.
  unfold get_r_qft in *.
  bdestruct (x =? x0). subst.
  unfold sr_rotate.
  rewrite sr_rotate'_lt_1; try lia.
  inv H1. inv H6.
  apply mapsto_always_same with (v1 := (Phi (aenv x0))) in H9. inv H9.
  specialize (H0 x0 H4 i H5).
  unfold right_mode_env in H2.
  specialize (H2 (Phi (aenv x0)) (x0,0)). simpl in H2.
  apply H2 in H4; try lia. inv H4.
  unfold times_rotate.
  assert ((f (@pair Env.key nat x0 O)) = (f (@pair var nat x0 O))) by easy.
  rewrite H1 in *.
  rewrite <- H7 in *. unfold rotate,addto.
  bdestruct (i <? S q - 0). lia. easy. easy.
  unfold sr_rotate.
  rewrite sr_rotate'_irrelevant; try easy.
  rewrite H0; try easy.
  inv H1. easy. simpl. lia.
  unfold qft_gt in *. intros.
  unfold get_r_qft in *.
  bdestruct (x =? x0). subst.
  unfold srr_rotate.
  rewrite srr_rotate'_lt_1; try lia.
  inv H1. inv H6.
  apply mapsto_always_same with (v1 := (Phi (aenv x0))) in H9. inv H9.
  specialize (H0 x0 H4 i H5).
  unfold right_mode_env in H2.
  specialize (H2 (Phi (aenv x0)) (x0,0)). simpl in H2.
  apply H2 in H4; try lia. inv H4.
  unfold times_r_rotate.
  assert ((f (@pair Env.key nat x0 O)) = (f (@pair var nat x0 O))) by easy.
  rewrite H1 in *.
  rewrite <- H7 in *. unfold r_rotate,addto_n.
  bdestruct (i <? S q - 0). lia. easy. easy.
  unfold srr_rotate.
  rewrite srr_rotate'_irrelevant; try easy.
  rewrite H0; try easy.
  inv H1. easy. simpl. lia.
  unfold qft_gt in *. intros.
  inv H1. inv H6. destruct p1.
  simpl in H10. bdestruct (x =? v). subst.
  apply mapsto_always_same with (v1 := (Phi (aenv v))) in H10. inv H10. easy.
  unfold get_r_qft in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite H0; try easy.
  unfold qft_gt in *.
  intros.
  bdestruct (x0 =? x). subst.
  inv H1. inv H6.
  apply mapsto_always_same with (v2:=Nor) in H4; try easy.
  apply mapsto_always_same with (v2:=Had) in H4; try easy.
  unfold get_r_qft in *.
  unfold lshift. rewrite lshift'_irrelevant by iner_p.
  rewrite H0 ; try easy.
  inv H1. easy.
  unfold qft_gt in *.
  intros.
  bdestruct (x0 =? x). subst.
  inv H1. inv H6.
  apply mapsto_always_same with (v2:=Nor) in H4; try easy.
  apply mapsto_always_same with (v2:=Had) in H4; try easy.
  unfold get_r_qft in *.
  unfold rshift. rewrite rshift'_irrelevant by iner_p.
  rewrite H0 ; try easy.
  inv H1. easy.
  unfold qft_gt in *.
  intros.
  bdestruct (x0 =? x). subst.
  inv H1. inv H6.
  apply mapsto_always_same with (v2:=Nor) in H4; try easy.
  apply mapsto_always_same with (v2:=Had) in H4; try easy.
  unfold get_snd_r,reverse,get_r_qft in *.
  simpl in *.
  bdestruct (x0 =? x). lia. simpl.
  rewrite H0. easy. inv H1. easy. easy.
  inv H1. inv H4.
  unfold qft_gt in *. intros.
  bdestruct (x0 =? x). subst. 
  unfold turn_qft,get_r_qft in *.
  rewrite assign_r_lt; try lia.
  rewrite lshift_fun_0.
  unfold up_qft.
  unfold right_mode_env in H2. specialize (H2 Nor (x,0)).
  simpl in H2. destruct H4. apply H2 in H4; try easy.
  inv H4. unfold get_cus. bdestruct (i <? aenv x). lia. easy.
  unfold get_r_qft,turn_qft in *.
  rewrite assign_r_out.
  rewrite H0; try easy.
  apply mapsto_equal with (s2 := (Env.add x (Phi (aenv x)) tenv)) in H1; try easy.
  apply Env.add_3 in H1. easy. lia. easy.
  inv H1. inv H4.
  unfold qft_gt in *. intros.
  unfold turn_rqft,get_r_qft in *.
  unfold right_mode_env in H2.
  destruct (f (x, 0)) eqn:eq1.
  bdestruct (x =? x0). subst.
  rewrite assign_seq_lt. simpl. easy. lia.
  rewrite assign_seq_out.
  rewrite H0; try easy. simpl.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H1; try easy.
  apply Env.add_3 in H1. easy. lia. simpl. lia.
  bdestruct (x =? x0). subst.
  rewrite assign_seq_lt. simpl. easy. lia.
  rewrite assign_seq_out.
  rewrite H0; try easy. simpl.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H1; try easy.
  apply Env.add_3 in H1. easy. lia. simpl. lia.
  bdestruct (x =? x0). subst.
  rewrite assign_seq_lt. simpl. easy. lia.
  rewrite assign_seq_out.
  rewrite H0; try easy. simpl.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H1; try easy.
  apply Env.add_3 in H1. easy. lia. simpl. lia.
  unfold qft_gt in *. intros.
  bdestruct (x0 =? x). subst.
  inv H1. inv H6.
  apply mapsto_always_same with (v2:=Nor) in H4; try easy.
  apply mapsto_always_same with (v2:=Had) in H4; try easy.
  unfold get_r_qft in *.
  apply EnvFacts.Equal_sym in H9.
  apply mapsto_equal with (s1 := (Env.add x Had tenv)).
  apply Env.add_1. easy. easy.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H4; try easy.
  apply mapsto_add1 in H4. inv H4.
  unfold get_r_qft in *.
  rewrite h_sem_out by lia. rewrite H0; try easy.
  inv H1. inv H7.
  apply mapsto_equal with (s2 := (Env.add x Had tenv)) in H4; try easy.
  apply Env.add_3 in H4. easy. lia.
  apply mapsto_equal with (s2 := (Env.add x Nor tenv)) in H4; try easy.
  apply Env.add_3 in H4. easy. lia.
  assert ((forall u : var, In u (get_vars e1) -> In u avars)).
  intros. apply H3. simpl. apply in_or_app. left. easy.
  inv H1. inv H5.
  specialize (IHe1 f avars aenv tenv env' H0 H8 H2 H4).
  apply IHe2 with (avars := avars) (tenv:=env') (tenv' := tenv') ; try easy.
  apply well_typed_right_mode_pexp with (avars := avars) (tenv:=tenv); easy.
  intros. apply H3. simpl. apply in_or_app. right. easy.
Qed.

Lemma qft_gt_put_cus_same : 
    forall f x g n aenv tenv, qft_gt aenv tenv f -> nor_modes f x n
                 -> qft_gt aenv tenv (put_cus f x g n).
Proof.
  intros. 
  unfold qft_gt in *. intros.
  unfold put_cus,get_r_qft in *.
  simpl in *.
  bdestruct (x0 =? x). subst.
  bdestruct (0 <? n).
  unfold put_cu.
  unfold nor_modes in H1. specialize (H1 0 H4).
  unfold nor_mode in H1.
  destruct (f (x,0)) eqn:eq1. easy. lia. lia.
  apply H0; try easy.
  apply H0; try easy.
Qed.

Lemma inv_exp_correct_rev :
  forall e tenv tenv' avars aenv f,
   (forall u, In u (get_vars e) -> In u avars) ->
    well_typed_pexp avars aenv tenv e tenv' -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f -> exp_sem aenv (e; inv_exp e) f = f.
Proof.
  induction e; intros.
  - simpl. easy.
  - simpl.
    remember (f [p |-> exchange (f p)]) as f'.
    assert (f = f'[p |-> exchange (f' p)]).
    subst.
    rewrite eupdate_index_eq.
    rewrite eupdate_twice_eq.
    rewrite exchange_twice_same.
    rewrite eupdate_same. easy. easy.
    rewrite H5. easy.
  - specialize (typed_inv_pexp (CU p e) avars aenv tenv tenv' H1) as eq1.
    simpl in eq1.
    assert (inv_exp (CU p e) = CU p (inv_exp e)). simpl. easy.
    rewrite H5.
    destruct (get_cua (f p)) eqn:eq3.
    rewrite <- two_cu_same.
    apply IHe with (tenv := tenv) (tenv' := tenv') (avars := avars); try easy.
    intros. apply H0.
    simpl. right. easy. inv H1. inv H6. easy. easy. inv H1. inv H6. easy.
    simpl. rewrite eq3. rewrite eq3. easy.
  - simpl.
    assert ((f [p |-> times_rotate (f p) q])
                  [p |-> times_r_rotate ((f [p |-> times_rotate (f p) q]) p) q] = f).
    rewrite eupdate_index_eq.
    rewrite eupdate_twice_eq.
    apply functional_extensionality.
    intros. 
    bdestruct (x ==? p).
    subst.
    rewrite eupdate_index_eq.
    rewrite times_rotate_same. easy.
    rewrite eupdate_index_neq. easy. nor_sym.
    rewrite H5. easy.
  - simpl.
    assert ((f [p |-> times_r_rotate (f p) q])
                  [p |-> times_rotate ((f [p |-> times_r_rotate (f p) q]) p) q] = f).
    rewrite eupdate_index_eq.
    rewrite eupdate_twice_eq.
    apply functional_extensionality.
    intros. 
    bdestruct (x ==? p).
    subst.
    rewrite eupdate_index_eq.
    rewrite times_rotate_r_same. easy.
    rewrite eupdate_index_neq. easy. nor_sym.
    rewrite H5. easy.
  - simpl.
    unfold sr_rotate,srr_rotate.
    rewrite srr_rotate_rotate. easy.
  - simpl.
    unfold sr_rotate,srr_rotate.
    rewrite sr_rotate_rotate. easy.
  - simpl.
    rewrite eupdate_twice_eq.
    rewrite eupdate_same. easy.
    rewrite eupdate_index_eq.
    inv H1. inv H5. rewrite eupdate_index_neq by easy.
    rewrite hexchange_twice_same. easy.
 - simpl.
   rewrite rl_shift_same. easy.
 - simpl.
   rewrite lr_shift_same. easy.
 - simpl.
   rewrite rev_twice_same. easy.
 - simpl. unfold turn_qft,turn_rqft.
   apply functional_extensionality. intros.
   destruct x0.
   bdestruct (x =? v). subst.
   bdestruct (n <? aenv v).
   rewrite assign_seq_covers; try easy.
   eapply qft_start_nor_modes. apply H1. easy.
   unfold get_r_qft.
   rewrite assign_r_same_0 with (size := (aenv v)); try lia.
   rewrite get_cus_cua. easy. lia.
   eapply qft_start_nor_modes. apply H1. easy.
   rewrite assign_seq_ge by lia.
   rewrite assign_r_ge by lia. easy.
   rewrite assign_seq_out by iner_p.
   rewrite assign_r_out by iner_p. easy.
 - simpl. unfold turn_qft,turn_rqft.
   apply functional_extensionality. intros.
   destruct x0.
   bdestruct (x =? v). subst.
   bdestruct (n <? aenv v).
   rewrite assign_r_covers; try easy.
   eapply rqft_start_phi_modes. apply H1. easy.
   unfold qft_uniform in H3.
   inv H1. inv H6. rewrite H3; try easy.
   unfold qft_gt in H4. 
   assert ((get_cus (aenv v) (assign_seq f v (get_r_qft f v) (aenv v)) v)
           = (get_r_qft f v)).
   apply functional_extensionality. intros.
   bdestruct (x <? aenv v).
   rewrite get_cus_cua; try lia.
   rewrite assign_seq_lt; try lia.
   unfold get_cua. easy.
   unfold get_cus. bdestruct (x <? aenv v). lia.
   rewrite H4; try easy. lia.
   rewrite H1. easy.
   rewrite assign_r_ge; try lia.
   rewrite assign_seq_ge; try lia. easy.
   rewrite assign_r_out by iner_p.
   rewrite assign_seq_out by iner_p. easy.
 - simpl.
   inv H1.
   rewrite had_twice_same with (t := Nor). easy. intros. 
   unfold right_mode_env in H2. apply H2. easy. easy.
   rewrite had_twice_same with (t := Nor). easy. intros. 
   unfold right_mode_env in H2. apply H2. easy. easy.
   rewrite had_twice_same with (t := Had). easy. intros. 
   unfold right_mode_env in H2. apply H2. easy. easy.
 - assert (inv_exp (e1; e2) = inv_exp e2; inv_exp e1). simpl. easy.
   rewrite H5.
   rewrite pexp_sem_assoc.
   assert (exp_sem aenv (e1; (e2; (inv_exp e2; inv_exp e1))) f
             = exp_sem aenv (e2 ; (inv_exp e2 ; inv_exp e1)) (exp_sem aenv (e1) f)).
   simpl. easy.
   rewrite H6.
   rewrite <- pexp_sem_assoc.
   assert ( forall f', exp_sem aenv ((e2; inv_exp e2); inv_exp e1) f'
            = exp_sem aenv (inv_exp e1) (exp_sem aenv ((e2; inv_exp e2)) f')).
   intros. simpl. easy.
   rewrite H7.
   inv H1. inv H8.
   rewrite (IHe2 env' tenv' avars aenv).
   assert (exp_sem aenv (inv_exp e1) (exp_sem aenv e1 f) = exp_sem aenv (e1 ; inv_exp e1) f).
   simpl. easy.
   rewrite H1.
   rewrite (IHe1 tenv env' avars). easy.
   intros. apply H0. simpl. apply in_or_app. left. easy.
   1-4:easy.
   intros. apply H0. simpl. apply in_or_app. right. easy. easy.
   apply well_typed_right_mode_pexp with (tenv := tenv) (tenv' := env') (avars := avars).
   intros. apply H0. simpl. apply in_or_app. left. easy. easy. easy.
   apply qft_uniform_exp_trans with (tenv := tenv) (avars := avars); try easy.
   intros. apply H0. simpl. apply in_or_app. left. easy.
   apply qft_gt_exp_trans with (tenv := tenv) (avars := avars); try easy.
   intros. apply H0. simpl. apply in_or_app. left. easy.
Qed.

Lemma inv_get_vars : forall e x, In x (get_vars (inv_exp e)) -> In x (get_vars e).
Proof.
  induction e; intros; simpl; try easy.
  simpl in H0. destruct H0. left. easy.
  right. apply IHe. easy.
  simpl in H0.
  apply in_or_app.
  apply in_app_or in H0.
  destruct H0. right. apply IHe2. easy.
  left. apply IHe1. easy.
Qed.

Lemma inv_exp_correct :
  forall e tenv tenv' avars aenv f,
   (forall u, In u (get_vars e) -> In u avars) ->
    well_typed_pexp avars aenv tenv e tenv' -> right_mode_env aenv tenv' f ->
    qft_uniform aenv tenv' f -> qft_gt aenv tenv' f -> exp_sem aenv (inv_exp e;e) f = f.
Proof.
  intros.
  assert ((inv_exp e;e) = inv_exp e; inv_exp (inv_exp e)).
  rewrite inv_exp_involutive. easy.
  rewrite H5.
  apply (inv_exp_correct_rev (inv_exp e) tenv' tenv avars aenv).
  intros. apply H0. apply inv_get_vars. easy.
  apply typed_inv_pexp. easy.
  1-3:assumption.
Qed.

Lemma exp_sem_same_out:
   forall e aenv f g1 g2, exp_sem aenv e f = g1 -> exp_sem aenv e f = g2 -> g1 = g2.
Proof.
 intros e.
 induction e;simpl; intros; subst; try easy.
Qed.

Lemma inv_pexp_reverse :
  forall (tenv tenv':env) avars (aenv: var -> nat) e f g,
   (forall u, In u (get_vars e) -> In u avars) ->
    well_typed_pexp avars aenv tenv e tenv' -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    exp_sem aenv e f = g ->
    exp_sem aenv (inv_exp e) g = f.
Proof.
  intros. 
  specialize (inv_exp_correct_rev e tenv tenv' avars aenv f H0 H1 H2 H3 H4) as G.
  simpl in G.
  subst. easy.
Qed.


Ltac nor_mode_simpl := repeat (try (apply nor_mode_up ; iner_p); try apply nor_mode_cus_eq; try easy). 

Lemma right_mode_val_cus_same : 
   forall f t p x g n, right_mode_val t (f p)
    -> right_mode_val t (put_cus f x g n p).
Proof.
  intros. unfold put_cus.
  destruct p.
  simpl. 
  bdestruct (v =? x). subst.
  bdestruct (n0 <? n).
  unfold put_cu.
  destruct (f (x,n0)). inv H0. constructor.
  inv H0. constructor. easy.
  inv H0.  constructor. easy. easy.
Qed.

Lemma right_mode_exp_put_cus_same :
    forall aenv tenv f x g n,
     right_mode_env aenv tenv f ->
     right_mode_env aenv tenv (put_cus f x g n).
Proof.
  intros. 
  unfold right_mode_env in *. intros.
  unfold put_cus.
  destruct p. simpl in *.
  bdestruct (v=?x). bdestruct (n0 <? n).
  specialize (H0 t (v,n0)). simpl in H0.
  apply H0 in H1; try easy.
  unfold put_cu.
  destruct (f (v,n0)). inv H1. constructor.
  easy. easy. apply H0; try easy.
  apply H0; try easy.
Qed.

Lemma right_mode_exp_up_same_1 :
    forall aenv tenv f f' c b,
     nor_mode f c -> nor_mode f' c ->
     right_mode_env aenv tenv f ->
     right_mode_env aenv tenv (f[c |-> put_cu (f' c) b]).
Proof.
  intros. 
  unfold right_mode_env in *. intros.
  bdestruct (p ==? c).
  subst. rewrite eupdate_index_eq.
  unfold nor_mode in *.
  destruct (f' c).
  unfold put_cu.
  apply H2 in H4. inv H4. rewrite <- H7 in *. constructor.
  rewrite <- H5 in *. lia. rewrite <- H7 in *. lia. easy.
  lia. lia.
  rewrite eupdate_index_neq by iner_p. apply H2; try easy.
Qed.

Lemma put_cus_update_flip : forall n f g x c v, fst c <> x -> put_cus (f[c |-> v]) x g n = (put_cus f x g n)[c |-> v].
Proof.
  intros.
  apply functional_extensionality; intro.
  bdestruct (c ==? x0). subst. rewrite eupdate_index_eq.
  destruct x0. rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq by iner_p.
  destruct x0.
  bdestruct (v0 =? x). subst. bdestruct (n0 <? n). 
  rewrite put_cus_eq by iner_p.
  rewrite put_cus_eq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_out by lia.
  rewrite put_cus_out by lia.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite put_cus_neq by iner_p.
  rewrite put_cus_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
Qed.

Lemma right_mode_exp_up_same :
    forall aenv tenv f c b,
     right_mode_env aenv tenv f ->
     right_mode_env aenv tenv (f[c |-> put_cu (f c) b]).
Proof.
  intros.
  unfold right_mode_env in *.
  intros.
  bdestruct (c ==? p). subst.
  rewrite eupdate_index_eq.
  apply (H0 t) in H1; try easy.
  destruct (f p). unfold put_cu. inv H1. constructor.
  unfold put_cu. easy.
  unfold put_cu. easy.
  rewrite eupdate_index_neq by iner_p.
  apply H0; try easy.
Qed.

Ltac right_simpl := repeat (try apply right_mode_exp_put_cus_same; try apply right_mode_exp_up_same;
                 (try (apply right_mode_exp_up_same_1; nor_mode_simpl)); try easy).


Lemma sr_rotate'_out_1 : forall n size f x p v, n <= size -> fst p <> x ->
       sr_rotate' (f[p |-> v]) x n size = (sr_rotate' f x n size)[p |-> v].
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_twice_neq.
  rewrite IHn; try easy.
  rewrite eupdate_index_neq. easy.
  destruct p. iner_p. lia.
  destruct p. iner_p.
Qed.

Lemma sr_rotate'_gt_1 : forall n size f x p v, n <= size -> size <= snd p ->
       sr_rotate' (f[p |-> v]) x n size = (sr_rotate' f x n size)[p |-> v].
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_twice_neq.
  rewrite IHn; try easy.
  rewrite eupdate_index_neq. easy.
  destruct p. intros R. inv R. simpl in H1. lia.
  lia.
  destruct p. intros R. inv R. simpl in H1. lia.
Qed.

Lemma srr_rotate'_out_1 : forall n size f x p v, n <= size -> fst p <> x ->
       srr_rotate' (f[p |-> v]) x n size = (srr_rotate' f x n size)[p |-> v].
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_twice_neq.
  rewrite IHn; try easy.
  rewrite eupdate_index_neq. easy.
  destruct p. iner_p. lia.
  destruct p. iner_p.
Qed.

Lemma srr_rotate'_gt_1 : forall n size f x p v, n <= size -> size <= snd p ->
       srr_rotate' (f[p |-> v]) x n size = (srr_rotate' f x n size)[p |-> v].
Proof.
  induction n; intros; simpl. easy.
  rewrite eupdate_twice_neq.
  rewrite IHn; try easy.
  rewrite eupdate_index_neq. easy.
  destruct p. intros R. inv R. simpl in H1. lia.
  lia.
  destruct p. intros R. inv R. simpl in H1. lia.
Qed.

Lemma lshift'_out : forall n size f x p v, n <= size -> fst p <> x ->
       lshift' n size (f[p |-> v]) x = (lshift' n size f x)[p |-> v].
Proof.
  induction n; intros; simpl. destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  rewrite IHn; try easy.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy. lia.
Qed.

Lemma lshift'_ge_switch : forall n size f x p v, n <= size -> size < snd p ->
       lshift' n size (f[p |-> v]) x = (lshift' n size f x)[p |-> v].
Proof.
  induction n; intros; simpl. destruct p.
  simpl in H1.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  rewrite IHn; try easy.
  destruct p. simpl in H1.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy. lia.
Qed.

Lemma rshift'_out : forall n size f x p v, n <= size -> fst p <> x ->
       rshift' n size (f[p |-> v]) x = (rshift' n size f x)[p |-> v].
Proof.
  induction n; intros; simpl. destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  rewrite IHn; try easy.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy. lia.
Qed.


Lemma rshift'_ge_switch : forall n size f x p v, n <= size -> size < snd p ->
       rshift' n size (f[p |-> v]) x = (rshift' n size f x)[p |-> v].
Proof.
  induction n; intros; simpl. destruct p.
  simpl in H1.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  rewrite IHn; try easy.
  destruct p. simpl in H1.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy. lia.
Qed.

Lemma assign_r_out_fun : forall n f x h p v, fst p <> x ->
            assign_r (f[p |-> v]) x h n = ((assign_r f x h n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn by easy.
  rewrite eupdate_twice_neq by iner_p. easy.
Qed.

Lemma assign_r_ge_fun : forall n f x h p v, n <= snd p ->
            assign_r (f[p |-> v]) x h n = ((assign_r f x h n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p. simpl in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn.
  rewrite eupdate_twice_neq by iner_p. easy. simpl. lia.
Qed.

Lemma assign_seq_out_fun : forall n f x h p v, fst p <> x ->
            assign_seq (f[p |-> v]) x h n = ((assign_seq f x h n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn by easy.
  rewrite eupdate_twice_neq by iner_p. easy.
Qed.

Lemma assign_seq_ge_fun : forall n f x h p v, n <= snd p ->
            assign_seq (f[p |-> v]) x h n = ((assign_seq f x h n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p. simpl in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn.
  rewrite eupdate_twice_neq by iner_p. easy. simpl; lia.
Qed.

Lemma h_sem_out_fun : forall n f x p v, fst p <> x ->
            h_sem (f[p |-> v]) x n = ((h_sem f x n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn by easy.
  rewrite eupdate_twice_neq by iner_p. easy.
Qed.

Lemma h_sem_ge_fun : forall n f x p v, n <= snd p ->
            h_sem (f[p |-> v]) x n = ((h_sem f x n)[p |-> v]).
Proof.
  induction n; intros;simpl. easy.
  destruct p. simpl in *.
  rewrite eupdate_index_neq by iner_p.
  rewrite IHn.
  rewrite eupdate_twice_neq by iner_p. easy. simpl;lia.
Qed.

Lemma efresh_exp_sem_out :
  forall e aenv  p f v,
    exp_fresh aenv p e ->
    exp_sem aenv e (f[p |-> v]) = ((exp_sem aenv e f)[p |-> v]).
Proof.
  induction e;intros.
  subst. simpl. easy.
  simpl in *. inv H0.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  simpl.
  inv H0. rewrite eupdate_index_neq by iner_p.
  destruct (get_cua (f p)) eqn:eq1.
  rewrite IHe; try easy. easy.
  simpl in *. inv H0.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  simpl in *. inv H0.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p. easy.
  simpl in *. inv H0.
  unfold or_not_r in H3. destruct H3.
  unfold sr_rotate.
  rewrite sr_rotate'_out_1; try easy.
  unfold sr_rotate.
  rewrite sr_rotate'_gt_1; try easy.
  simpl in *. inv H0.
  unfold or_not_r in H3. destruct H3.
  unfold srr_rotate.
  rewrite srr_rotate'_out_1; try easy.
  unfold srr_rotate.
  rewrite srr_rotate'_gt_1; try easy.
  simpl in *. inv H0.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_twice_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. easy.
  inv H0. unfold or_not_eq in H3. simpl.
  unfold lshift.
  destruct H3.
  rewrite lshift'_out; try lia. easy.
  destruct p.
  bdestruct (x =? v0). subst.
  simpl in H0.
  bdestruct (aenv v0 =? 0). rewrite H1 in *. simpl.
  rewrite eupdate_same.
  apply eupdate_same_1.
  rewrite eupdate_same; try easy. easy. easy.
  rewrite lshift'_ge_switch; try lia. easy. simpl. lia.
  rewrite lshift'_out; try lia. easy. iner_p.
  inv H0. unfold or_not_eq in H3. simpl.
  unfold rshift.
  destruct H3.
  rewrite rshift'_out; try lia. easy.
  destruct p.
  bdestruct (x =? v0). subst.
  simpl in H0.
  bdestruct (aenv v0 =? 0). rewrite H1 in *. simpl.
  rewrite eupdate_same.
  apply eupdate_same_1.
  rewrite eupdate_same; try easy. easy. easy.
  rewrite rshift'_ge_switch; try lia. easy. simpl. lia.
  rewrite rshift'_out; try lia. easy. iner_p.
  inv H0. unfold or_not_eq in H3. simpl.
  unfold reverse.
  apply functional_extensionality; intros; simpl.
  destruct p.
  destruct H3.
  rewrite eupdate_index_neq by iner_p.
  bdestruct (fst x0 =? x). 
  bdestruct (snd x0 <? aenv x). simpl.
  destruct x0. simpl in H0.
  subst. rewrite eupdate_index_neq.
  simpl. bdestruct (v1 =? v1).
  bdestruct ((n0 <? aenv v1)). simpl. easy. simpl in H2. lia. lia.
  iner_p. simpl in *.
  bdestruct ((v0,n) ==? x0).
  rewrite <- H3.  repeat rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_neq by iner_p.
  bdestruct (fst x0 =? x). 
  bdestruct (snd x0 <? aenv x). simpl. lia. simpl. easy. simpl. easy.
  simpl.
  bdestruct ((v0,n) ==? x0).
  rewrite <- H2.  repeat rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_neq by iner_p.
  bdestruct (fst x0 =? x). 
  bdestruct (snd x0 <? aenv x). simpl. lia. simpl. easy. simpl. easy.
  simpl in *.
  bdestruct (fst x0 =? x). 
  bdestruct (snd x0 <? aenv x). simpl.
  destruct x0. simpl in *.
  subst. repeat rewrite eupdate_index_neq by iner_p.
  simpl. bdestruct (x =? x).
  bdestruct ((n0 <? aenv x)). simpl. easy. lia. lia.
  destruct x0. simpl in *.
  subst. bdestruct (n0 =? n). subst.
  bdestruct (x =? v0). subst.
  repeat rewrite eupdate_index_eq. easy.
  repeat rewrite eupdate_index_neq by iner_p.
  simpl in *.
  bdestruct (x =? x).
  bdestruct ((n <? aenv x)). simpl. lia. simpl. easy.
  simpl. easy.
  repeat rewrite eupdate_index_neq by iner_p.
  simpl in *.
  bdestruct (x =? x).
  bdestruct ((n0 <? aenv x)). simpl. lia. simpl. easy.
  simpl. easy.
  destruct x0. simpl in *.
  bdestruct (v0 =? v1). bdestruct (n =? n0). subst.
  repeat rewrite eupdate_index_eq. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. simpl.
  bdestruct (v1 =? x). lia. simpl. easy. 
  rewrite eupdate_index_neq by iner_p.
  rewrite eupdate_index_neq by iner_p. simpl.
  bdestruct (v1 =? x). lia. simpl. easy. 
  simpl in *. inv H0.
  unfold turn_qft.
  unfold or_not_eq in H3. destruct H3.
  rewrite get_cus_up by easy.
  rewrite assign_r_out_fun by easy. easy.
  rewrite get_cus_up_ge by easy.
  rewrite assign_r_ge_fun by easy. easy.
  simpl. inv H0. unfold turn_rqft.
  unfold or_not_eq in H3. destruct H3.
  unfold get_r_qft.
  destruct p.
  rewrite eupdate_index_neq by iner_p.
  rewrite assign_seq_out_fun by iner_p. easy.
  unfold get_r_qft.
  destruct p. simpl in *.
  bdestruct (v0 =? x). bdestruct (n =? 0). subst.
  rewrite eupdate_index_eq.
  assert (aenv x = 0) by lia. rewrite H1 in *.
  simpl. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite assign_seq_ge_fun by iner_p. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite assign_seq_out_fun by iner_p. easy.
  simpl. inv H0.
  unfold or_not_eq in H3. destruct H3.
  rewrite h_sem_out_fun by iner_p. easy.
  rewrite h_sem_ge_fun by iner_p. easy.
  simpl. inv H0.
  rewrite IHe1 by easy.
  rewrite IHe2 by easy. easy.
Qed.

Lemma inv_pexp_reverse_1 :
  forall (tenv tenv':env) avars (aenv: var -> nat) e f g c v,
   (forall u, In u (get_vars e) -> In u avars) ->
    well_typed_pexp avars aenv tenv e  tenv' -> right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    exp_fresh aenv c e ->
    exp_sem aenv e f = g ->
    exp_sem aenv (inv_exp e) (g[c |-> v]) = (f[c |-> v]).
Proof.
  intros. 
  Check inv_pexp_reverse.
  specialize (inv_pexp_reverse tenv tenv' avars aenv e f g H0 H1 H2 H3 H4) as G.
  apply functional_extensionality; intros.
  bdestruct (x ==? c). rewrite H7 in *.
  rewrite efresh_exp_sem_out. rewrite G. easy. easy.
  apply fresh_inv_exp. easy.
  rewrite efresh_exp_sem_out. rewrite G. easy. easy.
  apply fresh_inv_exp. easy.
Qed.


(*  Compilation to bcom. *)
(* Controlled rotation cascade on n qubits. *)

(* States that is useful in compiling RCIR+ to SQIR. *)
Definition id_fun := fun (i:nat) => i.

Definition adj_offset (index:nat) (offset:nat) (size:nat) :=
    (index + offset) mod size.

Definition rz_ang (n:nat) : R := ((2%R * PI)%R / 2%R^n).

Definition rrz_ang (n:nat) : R := ((2%R * PI)%R - ((2%R * PI)%R / 2%R^n)).

Definition vars := nat -> (nat * nat * (nat -> nat) * (nat -> nat)).

Definition start (vs :vars) (x:var) := fst (fst (fst (vs x))).

Definition vsize (vs:vars) (x:var) := snd (fst (fst (vs x))).

Definition vmap (vs:vars) (x:var) := snd (fst (vs x)).

Definition avmap (vs:vars) (x:var) := snd (vs x).

Definition find_pos (f : vars) (p:posi) :=
      let (a,b) := p in start f a + (vmap f a b).

(* Compilinng input variables to a format that will be used on RCIR+. *)


Fixpoint compile_var' (l: list (var * nat)) (dim:nat) :=
   match l with [] => fun _ => (0,0,id_fun,id_fun)
              | (x,n):: l' => fun i => if x =? i
                           then (dim,n,id_fun,id_fun) else (compile_var' l' (dim + n)) i
   end.

Definition compile_var l := compile_var' l 0.

Fixpoint get_dim (l: list (var * nat)) :=
   match l with [] => 0
             | (x,n) :: l' => n + get_dim l'
   end.


Inductive vars_WF : (list (var * nat)) -> Prop :=
    vars_WF_empty : vars_WF (List.nil)
    | vars_WF_many : forall x y xl, 0 < y -> vars_WF xl -> vars_WF ((x,y)::xl).

Fixpoint avars (l: list (var * nat)) (dim:nat) : (nat -> posi) :=
    match l with [] => fun i => (dim,dim)
              | (x,n):: l' => fun i => if (dim <? i) && (i - dim <? n) then (x, i - dim)
                                       else avars l' (dim + n) i
    end.
       
(*                                                                            
Lemma vs_bij : forall l dim vs avs, dim = get_dim l ->
            vs = compile_var' l 0 -> vars_WF l -> avs = avars l 0 ->
         (forall x y, y < vsize vs x -> 
              (forall i, i < dim -> avs (find_pos vs (x,y)) = (x,y))).
Proof.
  intros. subst.
  induction l. simpl in H5. lia.
  simpl.
  destruct a eqn:eq1.
Admitted.
*)

Lemma compile_var'_WF : forall l dim p vs, vs = compile_var' l dim
              -> snd p < vsize vs (fst p) -> find_pos vs p < dim + get_dim l.
Proof.
 induction l; intros; simpl in *.
 rewrite H0 in H1. unfold vsize in H1. simpl in H1. lia.
 destruct a eqn:eq1.
 destruct p eqn:eq2.
 simpl in *. subst.
 unfold start,vsize,vmap. unfold vsize in H1.
 bdestruct (v =? v0). subst. simpl in *.
 unfold id_fun. lia.
 remember (compile_var' l (dim + n)) as vs'.
 assert (snd (fst (fst (vs' v0))) = vsize vs' v0) by easy.
 rewrite H2 in H1.
 specialize (IHl (dim + n) (v0,n0) vs' Heqvs' H1).
 subst.
 unfold find_pos,start,vmap in IHl. lia.
Qed.

Lemma compile_var_WF : forall l p vs, vs = compile_var l
              -> snd p < vsize vs (fst p) -> find_pos vs p < get_dim l.
Proof.
  intros. unfold compile_var.
  specialize (compile_var'_WF l 0 p vs H0 H1) as eq1. lia.
Qed.
(*
Definition inter_num (size:nat) (t : varType) :=
   match t with NType => size
              | SType => size+1
   end.
*)


(* the compilation state properties with lemmas. *)
Definition vars_start_diff (vs: vars) :=
        forall x y,  x <> y -> start vs x <> start vs y.

(* A weaker property sometimes easier to prove. *)
Definition weak_finite_bijection (n : nat) (f : nat -> nat) :=
  (forall x, x < n -> f x < n)%nat /\ 
  (exists g, (forall y, y < n -> g y < n)%nat /\
        (forall x, (x < n)%nat -> g (f x) = x) /\ 
        (forall y, (y < n)%nat -> f (g y) = y)).

Definition vars_finite_bij (vs:vars) :=
   forall x,  weak_finite_bijection (vsize vs x) (vmap vs x).

Definition vars_sparse (vs:vars) :=
   forall x y, x <> y -> (forall i j, i < vsize vs x -> j < vsize vs y -> start vs x + i <> start vs y + j).

Lemma finite_bij_lt : forall vs, vars_finite_bij vs 
         -> (forall x i, i < vsize vs x -> vmap vs x i < vsize vs x).
Proof.
  intros. unfold vars_finite_bij in H0.
  unfold weak_finite_bijection in H0.
  destruct (H0 x).
  apply H2. easy.
Qed.

Lemma finite_bij_inj : forall vs x, vars_finite_bij vs 
         -> (forall i j, i < vsize vs x -> j < vsize vs x -> i <> j -> vmap vs x i <> vmap vs x j).
Proof.
  intros. unfold vars_finite_bij in H0.
  unfold weak_finite_bijection in H0.
  destruct (H0 x).
  destruct H5. destruct H5. destruct H6.
  specialize (H6 i H1) as eq1.
  specialize (H6 j H2) as eq2.
  intros R.
  rewrite R in eq1. rewrite eq1 in eq2. subst. contradiction.
Qed.



(* Compiled RCIR+ circuit well-formedness. *)
Inductive exp_rmax : nat -> exp -> Prop :=
      | skip_rmax : forall rs p, exp_rmax rs (SKIP p)
      | x_rmax : forall rs p, exp_rmax rs (X p)
      | hcnot_rmax : forall rs p1 p2, exp_rmax rs (HCNOT p1 p2)
      | cu_rmax : forall vs p e, exp_rmax vs e -> exp_rmax vs (CU p e)
      | rz_rmax : forall rs p q, q < rs -> exp_rmax rs (RZ q p)
      | rrz_rmax : forall rs p q, q < rs -> exp_rmax rs (RRZ q p)
      | sr_rmax : forall rs n x, S n < rs -> exp_rmax rs (SR n x)
      | srr_rmax : forall rs n x, S n < rs -> exp_rmax rs (SRR n x)
      | seq_rmax : forall rs e1 e2, exp_rmax rs e1 -> exp_rmax rs e2 -> exp_rmax rs (Seq e1 e2)
      | lshift_rmax : forall vs x, exp_rmax vs (Lshift x)
      | rshift_rmax : forall vs x, exp_rmax vs (Rshift x)
      | rev_rmax : forall vs x, exp_rmax vs (Rev x).


Fixpoint gen_sr_gate' (f:vars) (dim:nat) (x:var) (n:nat) (size:nat) : base_ucom dim := 
   match n with 0 => SQIR.ID (find_pos f (x,0))
             | S m => SQIR.useq (gen_sr_gate' f dim x m size) (SQIR.Rz (rz_ang (size - m)) (find_pos f (x,m)))
   end.
Definition gen_sr_gate (f:vars) (dim:nat) (x:var) (n:nat) := gen_sr_gate' f dim x (S n) (S n).

Fixpoint gen_srr_gate' (f:vars) (dim:nat) (x:var) (n:nat) (size:nat) : base_ucom dim := 
   match n with 0 => SQIR.ID (find_pos f (x,0))
             | S m => SQIR.useq (gen_srr_gate' f dim x m size) (SQIR.Rz (rrz_ang (size - m)) (find_pos f (x,m)))
   end.
Definition gen_srr_gate (f:vars) (dim:nat) (x:var) (n:nat) := gen_srr_gate' f dim x (S n) (S n).

Definition shift_fun (f:nat -> nat) (offset:nat) (size:nat) :=
         fun i => if i <? size then f ((i + offset) mod size) else f i.

Definition ashift_fun (f:nat -> nat) (offset:nat) (size:nat) :=
         fun i => if i <? size then (((f i) + offset) mod size) else f i.

Lemma shift_fun_back : forall f g off size,
     (forall i, i < size -> f i < size) ->
     (forall i, i >= size -> f i >= size) ->
     (forall i, i < size -> g i < size) ->
     (forall i, i >= size -> g i >= size) ->
     (forall i, f (g i) = i) -> (forall i, g (f i) = i) -> off <= size ->
          (forall i, ashift_fun f off size (shift_fun g (size - off) size i) = i).
Proof.
  intros.
  unfold shift_fun,ashift_fun.
  bdestruct (i <? size).
  bdestruct (g ((i + (size - off)) mod size) <? size).
  rewrite H4.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_mod by lia.
  rewrite <- Nat.add_mod by lia.
  assert ((i + (size - off) + off) = i + size) by lia.
  rewrite H9.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia. easy.
  assert (g ((i + (size - off)) mod size) < size).
  apply H2.
  apply Nat.mod_bound_pos. lia. lia. lia.
  apply H3 in H7.
  bdestruct (g i <? size). lia.
  rewrite H4. easy.
Qed.

Lemma shift_fun_back_1 : forall f g off size,
     (forall i, i < size -> f i < size) ->
     (forall i, i >= size -> f i >= size) ->
     (forall i, i < size -> g i < size) ->
     (forall i, i >= size -> g i >= size) ->
     (forall i, f (g i) = i) -> (forall i, g (f i) = i) -> off <= size ->
          (forall i, shift_fun f (size-off) size (ashift_fun g off size i) = i).
Proof.
  intros.
  unfold shift_fun,ashift_fun.
  bdestruct (i <? size).
  bdestruct ((g i + off) mod size <? size).
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_mod by lia.
  rewrite <- Nat.add_mod by lia.
  assert ((g i + off + (size - off)) = g i + size) by lia.
  rewrite H9.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small.
  rewrite H4. easy. apply H2. easy.
  assert ((g i + off) mod size < size).
  apply Nat.mod_bound_pos. lia. lia. lia.
  bdestruct (g i <? size).
  apply H3 in H7. lia.
  rewrite H4. easy.
Qed.

Definition afbrev (f:nat -> nat) (size:nat) :=
         fun (x : nat) => if (x <? size) then size - 1 - f x else f x.


Lemma fbrev_back : forall f g size,
     (forall i, i < size -> f i < size) ->
     (forall i, i >= size -> f i >= size) ->
     (forall i, i < size -> g i < size) ->
     (forall i, i >= size -> g i >= size) ->
     (forall i, f (g i) = i) -> (forall i, g (f i) = i) ->
          (forall i, afbrev f size (fbrev size g i) = i).
Proof.
  intros.
  unfold afbrev,fbrev.
  bdestruct (i <? size).
  bdestruct (g (size - 1 - i) <? size).
  rewrite H4. lia.
  assert (size - 1 - i < size) by lia.
  apply H2 in H8. lia.
  bdestruct (g i <? size ).
  apply H3 in H6. lia. 
  rewrite H4. easy.
Qed.


Lemma afbrev_back : forall f g size,
     (forall i, i < size -> f i < size) ->
     (forall i, i >= size -> f i >= size) ->
     (forall i, i < size -> g i < size) ->
     (forall i, i >= size -> g i >= size) ->
     (forall i, f (g i) = i) -> (forall i, g (f i) = i) ->
          (forall i, fbrev size f (afbrev g size i) = i).
Proof.
  intros.
  unfold afbrev,fbrev.
  bdestruct (i <? size).
  bdestruct (size - 1 - g i <? size).
  assert (g i < size). apply H2 in H6. easy.
  assert ((size - 1 - (size - 1 - g i)) = g i) by lia.
  rewrite H9. rewrite H4. easy. lia. 
  bdestruct (g i <? size ).
  apply H3 in H6. lia. 
  rewrite H4. easy.
Qed.

Definition trans_lshift (f:vars) (x:var) :=
     match f x with (start, size,g,ag) => 
              fun i => if i =? x then (start, size, 
               shift_fun g (size - 1) size,ashift_fun ag 1 size) else f i
     end.

Definition trans_rshift (f:vars) (x:var) :=
     match f x with (start, size,g,ag) => 
              fun i => if i =? x then (start, size,
                              shift_fun g 1 size,ashift_fun ag (size - 1) size) else f i
     end.

Definition lshift_avs (dim:nat) (f : vars) (avs : nat -> posi) (x:var)
           := (fun i => if (i <? dim) && (start f x <=? i) && (i - start f x  <? vsize f x)
                                       then (x, avmap (trans_lshift f x) x (i - start f x)) else avs i).

Definition rshift_avs (dim:nat) (f : vars) (avs : nat -> posi) (x:var)
           := (fun i => if (i <? dim) && (start f x <=? i) && (i - start f x <? vsize f x)
                            then (x,avmap (trans_rshift f x) x (i - start f x)) else avs i).

Definition trans_rev (f: vars) (x:var) :=
     match f x with (start, size,g,ag) => 
              fun i => if i =? x then (start, size, fbrev size g,afbrev ag size) else f i
     end.

Definition rev_avs (dim:nat) (f : vars) (avs : nat -> posi) (x:var)
           := (fun i => if (i <? dim) && (start f x <=? i) && (i - start f x <? vsize f x)
                            then (x,avmap (trans_rev f x) x (i - start f x)) else avs i).

Fixpoint trans_exp (f : vars) (dim:nat) (exp:exp) (avs: nat -> posi) : (base_ucom dim * vars  * (nat -> posi)) :=
  match exp with SKIP p => (SQIR.ID (find_pos f p), f, avs)
              | X p => (SQIR.X (find_pos f p), f, avs)
              | RZ q p => (SQIR.Rz (rz_ang q) (find_pos f p), f, avs)
              | RRZ q p => (SQIR.Rz (rrz_ang q) (find_pos f p), f, avs)
              | SR n x => (gen_sr_gate f dim x n, f, avs)
              | SRR n x => (gen_srr_gate f dim x n, f, avs)
              | Lshift x => (SQIR.ID (find_pos f (x,0)), trans_lshift f x, lshift_avs dim f avs x)
              | Rshift x => (SQIR.ID (find_pos f (x,0)), trans_rshift f x, rshift_avs dim f avs x)
              | Rev x => (SQIR.ID (find_pos f (x,0)), trans_rev f x, rev_avs dim f avs x)
              | HCNOT p1 p2 => (SQIR.CNOT (find_pos f p1) (find_pos f p2), f, avs)
              | CU p1 (X p2) => (SQIR.CNOT (find_pos f p1) (find_pos f p2), f, avs)
              | CU p e1 => match trans_exp f dim e1 avs with (e1', f',avs')
                              => (control (find_pos f p) e1', f, avs) end
              | e1 ; e2 => match trans_exp f dim e1 avs with (e1', f', avs') => 
                                  match trans_exp f' dim e2 avs' with (e2',f'',avs'') => (SQIR.useq e1' e2', f'', avs'') end
                           end
   end.

(*
  (base_ucom dim * vars  * (nat -> posi)) :=
  match exp with Lshift x => (SQIR.ID (find_pos f (x,0)), trans_lshift f x, 
                              lshift_avs dim f avs x)

              | Rshift x => (SQIR.ID (find_pos f (x,0)),trans_rshift f x, rshift_avs dim f avs x)

              | Rev x => (SQIR.ID (find_pos f (x,0)),trans_rev f x,rev_avs dim f avs x)
*)

Definition exp_com_WF (vs:vars) (dim:nat) :=
    forall p, snd p < vsize vs (fst p) -> find_pos vs p < dim.

Definition exp_com_gt (vs:vars) (avs: nat -> posi) (dim:nat) :=
    forall i, i >= dim -> vsize vs (fst (avs i)) = 0.

Fixpoint turn_angle (rval : nat -> bool) (n : nat) : R :=
  match n with 0 => (0:R)
            | S m => ((1/ (2^(Nat.b2n(rval m))))%R + turn_angle rval m)%R
  end.

Definition z_phase (b:bool) : R := if b then 1%R else (-1)%R.

Definition compile_val (v:val) (r_max : nat) : Vector 2 := 
   match v with nval b r => Cexp (2*PI * (turn_angle r r_max)) .* ∣ Nat.b2n b ⟩
             | hval b1 b2 r => Cexp (2*PI * (turn_angle r r_max)) .*
                              ((RtoC ((z_phase b1))) .* ∣0⟩ .+ (RtoC ((z_phase b2))) .* ∣1⟩)
             | qval q r => Cexp (2*PI * (turn_angle q r_max)) .* (∣0⟩ .+ (Cexp (2*PI * (turn_angle r r_max))) .* ∣1⟩)
  end.

Lemma WF_compile_val : forall v r, WF_Matrix (compile_val v r).
Proof.
  intros. unfold compile_val.
  destruct v;auto with wf_db.
Qed.

Hint Resolve WF_compile_val : wf_db.

Definition trans_state (avs : nat -> posi) (rmax : nat) (f : posi -> val) : (nat -> Vector 2) :=
        fun i => compile_val (f (avs i)) rmax.

Lemma WF_trans_state : forall avs r f i, WF_Matrix (trans_state avs r f i).
Proof.
  intros. unfold trans_state. auto with wf_db.
Qed.

Hint Resolve WF_trans_state : wf_db.

Lemma trans_exp_cu : forall vs avs dim p e, 
       (exists p1, e = X p1 /\ 
             trans_exp vs dim (CU p e) avs = (SQIR.CNOT (find_pos vs p) (find_pos vs p1),vs,avs))
    \/ (trans_exp vs dim (CU p e) avs = ((control (find_pos vs p) (fst (fst (trans_exp vs dim e avs))), vs, avs))).
Proof.
  intros.
  simpl in *.
  destruct e. right. easy.
  left.
  exists p0. easy.
  right. destruct (trans_exp vs dim (CU p0 e) avs) eqn:eq1.
  destruct p1. easy.
  right. easy. right. easy. right. easy.
  right. easy. right. easy. right. easy.
  right. easy. right. easy. right. simpl.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p0.
  destruct (trans_exp v dim e2 p1) eqn:eq2. destruct p0. simpl. easy.
Qed.

Lemma find_pos_prop : forall vs p1 p2, vars_start_diff vs -> vars_finite_bij vs ->
            vars_sparse vs ->
            snd p1 < vsize vs (fst p1) -> snd p2 < vsize vs (fst p2) ->
            p1 <> p2 -> find_pos vs p1 <> find_pos vs p2.
Proof.
  intros.
  unfold find_pos,vars_start_diff in *.
  destruct p1. destruct p2.
  simpl in *.
  destruct (vs v) eqn:eq1.
  destruct (vs v0) eqn:eq2.
  destruct p. destruct p0.
  bdestruct (v =? v0).
  subst.
  assert (n <> n0). intros R. subst. contradiction.
  rewrite eq1 in eq2.
  inv eq2.
  specialize (finite_bij_inj vs v0 H1) as eq3.
  specialize (eq3 n n0 H3 H4 H6) as eq4. lia.
  specialize (H2 v v0 H6).
  apply H2.
  apply finite_bij_lt;  assumption.
  apply finite_bij_lt;  assumption.
Qed.

Lemma trans_state_update : forall dim (vs:vars) (avs: nat -> posi) rmax f (p:posi) v,
      (snd p < vsize vs (fst p)) ->
     (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
     (forall i, i < dim -> find_pos vs (avs i) = i) ->
    (forall x , x < dim -> (trans_state avs rmax (f [p |-> v]))  x
            = update (trans_state avs rmax f) (find_pos vs p) (compile_val v rmax) x).
Proof.
  intros.
  unfold trans_state.
  bdestruct (x =? (find_pos vs p)).
  subst.
  rewrite H1 by assumption.
  rewrite eupdate_index_eq.
  rewrite update_index_eq. easy.
  rewrite eupdate_index_neq.
  rewrite update_index_neq. easy. lia.
  intros R. subst. rewrite H2 in H4. lia. lia.
Qed.

(*We define helper properties for vars during translation. *)
Definition size_env (vs : vars):= fun i => vsize vs i.

Definition vars_anti_same (vs:vars) :=
     forall x, (forall i, i < vsize vs x -> vmap vs x i < vsize vs x) /\
     (forall i, i >= vsize vs x -> vmap vs x i >= vsize vs x) /\
     (forall i, i < vsize vs x -> avmap vs x i < vsize vs x) /\
     (forall i, i >= vsize vs x -> avmap vs x i >= vsize vs x) /\
     (forall i, vmap vs x (avmap vs x i) = i) /\ (forall i, avmap vs x (vmap vs x i) = i).

Definition avs_prop (vs:vars) (avs: nat -> posi) (dim : nat) :=
       forall i, i < dim -> (start vs (fst (avs i)) <= i /\ i - start vs (fst (avs i))  < vsize vs (fst (avs i))
              /\ avmap vs (fst (avs i)) (i - start vs (fst (avs i))) = snd (avs i)).
(*
Definition avs_prop_gt (vs:vars) (avs: nat -> posi) (dim : nat) :=
       forall i, i >= dim -> i - start vs (fst (avs i))  >= vsize vs (fst (avs i))
     /\ avs (find_pos vs n) = n.
*)
(* This defines when avs i and avs j will be the same. *)
Lemma var_not_over_lap : forall (p1 p2:posi) (vs:vars),  vars_sparse vs -> 
       vars_anti_same vs -> (snd p2 < vsize vs (fst p2))
       ->  fst p1 <> fst p2 ->
       start vs (fst p1) > find_pos vs p2 \/ find_pos vs p2 - start vs (fst p1) >= vsize vs (fst p1).
Proof.
  intros. unfold vars_sparse in H0. 
  bdestruct (start vs (fst p1) <=? find_pos vs p2).
  right.
  specialize (H0 (fst p1) (fst p2) H3).
  unfold find_pos in *. destruct p2. destruct p1. simpl in *.
  bdestruct (start vs v + vmap vs v n - start vs v0 <? vsize vs v0).
  unfold vars_anti_same in H1.
  destruct (H1 v). apply H6 in H2.
  specialize (H0 (start vs v + vmap vs v n - start vs v0) (vmap vs v n) H5 H2).
  assert (start vs v0 + (start vs v + vmap vs v n - start vs v0) = start vs v + vmap vs v n) by lia.
  rewrite H8 in H0. lia. assumption.
  left. assumption.
Qed.

Lemma var_not_over_lap_1 : forall (x:var) (p:posi) (vs:vars),  vars_sparse vs -> 
       vars_anti_same vs -> (snd p < vsize vs (fst p))
       ->  fst p <> x ->
       start vs x > find_pos vs p \/ find_pos vs p - start vs x >= vsize vs x.
Proof.
  intros. unfold vars_sparse in H0. 
  bdestruct (start vs x <=? find_pos vs p).
  right.
  specialize (H0 (fst p) x H3).
  unfold find_pos in *. destruct p. simpl in *.
  bdestruct (start vs v + vmap vs v n - start vs x <? vsize vs x).
  unfold vars_anti_same in H1.
  destruct (H1 v). apply H6 in H2.
  specialize (H0 (vmap vs v n) (start vs v + vmap vs v n - start vs x) H2 H5).
  assert (start vs x + (start vs v + vmap vs v n - start vs x) = start vs v + vmap vs v n) by lia.
  rewrite H8 in H0. lia. assumption.
  left. assumption.
Qed.

Lemma var_over_lap_1 : forall (x:var) (p:posi) (vs:vars),  vars_sparse vs -> 
       vars_anti_same vs -> (snd p < vsize vs (fst p))
       -> start vs x <= find_pos vs p  -> find_pos vs p - start vs x < vsize vs x
          -> fst p = x.
Proof.
  intros.
  bdestruct (fst p =? x). easy.
  specialize (var_not_over_lap_1 x p vs H0 H1 H2 H5) as eq1.
  destruct eq1. lia. lia.
Qed.


Lemma var_over_lap_exists : forall (x:var) (n:nat) (vs:vars), 
       vars_anti_same vs -> start vs x <= n -> n - start vs x < vsize vs x
       -> exists p, find_pos vs (x,p) = n.
Proof.
  intros. unfold find_pos.
  unfold vars_anti_same in H0. specialize (H0 x).
  destruct H0 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  exists (avmap vs x (n - start vs x)).
  rewrite X5. lia.
Qed.

Lemma vs_avs_bij_l : forall vs avs dim, avs_prop vs avs dim -> vars_anti_same vs -> vars_sparse vs ->
           exp_com_WF vs dim -> (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i).
Proof.
  intros. 
  bdestruct (avs (find_pos vs i) ==? i). easy.
  unfold avs_prop in H0.
  specialize (H0 (find_pos vs i)).
  assert (find_pos vs i < dim ).
  apply H3. easy.
  specialize (H0 H6).
  bdestruct (avs (find_pos vs i) ==? i). easy.
  destruct (avs (find_pos vs i)) eqn:eq1. destruct i eqn:eq2.
  bdestruct (v =? v0). subst.
  assert (n <> n0). intros R. subst. contradiction.
  destruct H0 as [V1 [ V2 V3]]. simpl in V3.
  assert ((start vs v0 + vmap vs v0 n0 - start vs v0) = vmap vs v0 n0) by lia. rewrite H0 in V3.
  unfold vars_anti_same in H1.
  destruct (H1 v0) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite X6 in V3. subst. lia.
  specialize (var_not_over_lap (avs (find_pos vs (v0, n0))) (v0, n0) vs H2 H1 H4) as eq3.
  rewrite eq1 in eq3. simpl in eq3.
  apply eq3 in H8.
  destruct H8. destruct H0.
  unfold find_pos in H0. simpl in H0. lia.
  destruct H0 as [V1 [V2 V3]].
  unfold find_pos in V2. simpl in V2. lia.
Qed.

Lemma vs_avs_bij_r : forall vs avs dim, avs_prop vs avs dim -> vars_anti_same vs ->
           (forall i, i < dim -> find_pos vs (avs i) = i).
Proof.
  intros. 
  bdestruct (find_pos vs (avs i) =? i). easy.
  unfold avs_prop in H0.
  specialize (H0 i H2).
  unfold find_pos in H3.
  destruct (avs i) eqn:eq1. simpl in H0.
  destruct H0 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  assert (vmap vs v (avmap vs v (i - start vs v)) = vmap vs v n).
  rewrite V3. easy.
  rewrite X5 in H0.
  rewrite <- H0 in H3. lia. 
Qed.


Lemma vs_avs_size : forall vs avs dim, avs_prop vs avs dim -> vars_anti_same vs ->
             (forall i, i < dim -> snd (avs i) < vsize vs (fst (avs i))).
Proof.
  intros. 
  unfold avs_prop in H0.
  specialize (H0 i H2).
  destruct H0 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 (fst (avs i))) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  apply X3. easy.
Qed.

Lemma lshift_avs_lshift_same : forall vs avs dim rmax f x,
          vars_sparse vs -> vars_anti_same vs -> avs_prop vs avs dim -> exp_com_WF vs dim
         -> exp_com_gt vs avs dim -> 0 < vsize vs x
            -> (trans_state avs rmax f) = ((trans_state (lshift_avs dim vs avs x) rmax (lshift f x (vsize vs x)))).
Proof.
  intros. unfold trans_state.
  apply functional_extensionality.
  intros.
  unfold lshift_avs,trans_lshift. 
  destruct (vs x) eqn:eq1.
  destruct p. destruct p.
  bdestruct (x0 <? dim).
  bdestruct ((start vs x <=? x0)).
  bdestruct ((x0 - start vs x <? vsize vs x)). simpl.
  unfold avmap. bdestruct (x =? x). simpl.
  unfold lshift.
  unfold start,vsize. rewrite eq1. simpl.
  assert (fst (avs x0) = x).
  apply var_over_lap_1 with (vs := vs); try assumption.
  apply vs_avs_size with (dim := dim); try assumption.
  unfold avs_prop in H2. specialize (H2 x0 H6). 
  unfold find_pos. destruct (avs x0). simpl in H2.
  destruct H2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia.
  unfold avs_prop in H2. specialize (H2 x0 H6). 
  unfold find_pos. destruct (avs x0). simpl in H2.
  destruct H2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia.
  destruct (avs x0) eqn:eq2. simpl in H10. subst.
  unfold ashift_fun.
  bdestruct (x0 - n1 <? n2).
  unfold avs_prop in H2.
  specialize (H2 x0 H6). rewrite eq2 in H2. simpl in H2.
  destruct H2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  unfold avmap,start in V3. rewrite eq1 in V3. simpl in V3.
  rewrite V3.
  bdestruct (n3 =? n2 -1 ). rewrite H2.
  assert ((n2 - 1 + 1) = n2) by lia.
  rewrite H11.
  rewrite Nat.mod_same by lia.
  rewrite lshift'_0 by lia. easy.
  unfold start,vsize in V2. rewrite eq1 in V2. simpl in V2. 
  specialize (X3 (x0 - n1)).
  unfold vsize,avmap in X3. rewrite eq1 in X3. simpl in X3.
  apply X3 in V2. rewrite V3 in V2.
  rewrite Nat.mod_small by lia.
  assert (n3 + 1 = S n3) by lia. rewrite H11.
  rewrite lshift'_le by lia. easy.
  unfold start,vsize in H8. rewrite eq1 in H8. simpl in H8. lia. lia.
  unfold avs_prop in H2. specialize (H2 x0 H6).
  simpl.
  bdestruct (fst (avs x0) =? x).
  rewrite H9 in H2.
  destruct H2 as [V1 [V2 V3]]. lia.
  unfold lshift.
  rewrite lshift'_irrelevant by assumption. easy.
  simpl.
  unfold avs_prop in H2. specialize (H2 x0 H6).
  simpl.
  bdestruct (fst (avs x0) =? x).
  rewrite H8 in H2.
  destruct H2 as [V1 [V2 V3]]. lia.
  unfold lshift.
  rewrite lshift'_irrelevant by assumption. easy.
  apply H4 in H6.
  bdestruct (fst (avs x0) =? x).
  rewrite H7 in H6. lia.
  simpl.
  unfold lshift.
  rewrite lshift'_irrelevant by assumption. easy.
Qed.

Lemma rshift_avs_rshift_same : forall vs avs dim rmax f x,
          vars_sparse vs -> vars_anti_same vs -> avs_prop vs avs dim -> exp_com_WF vs dim
         -> exp_com_gt vs avs dim -> 0 < vsize vs x
            -> (trans_state avs rmax f) = ((trans_state (rshift_avs dim vs avs x) rmax (rshift f x (vsize vs x)))).
Proof.
  intros. unfold trans_state.
  apply functional_extensionality.
  intros.
  unfold rshift_avs,trans_rshift. 
  destruct (vs x) as [p ag] eqn:eq1.
  destruct p as [p g]. destruct p as [st size].
  bdestruct (x0 <? dim).
  bdestruct ((start vs x <=? x0)).
  bdestruct ((x0 - start vs x <? vsize vs x)). simpl.
  unfold avmap. bdestruct (x =? x). simpl.
  unfold ashift_fun,vsize. rewrite eq1. simpl.
  unfold vsize in H8. rewrite eq1 in H8. simpl in H8.
  specialize (H2 x0 H6) as eq2.
  bdestruct (x0 - start vs x <? size).
  assert (fst (avs x0) = x).
  apply var_over_lap_1 with (vs := vs); try assumption.
  apply vs_avs_size with (dim := dim); try assumption.
  unfold find_pos. destruct (avs x0). simpl in eq2.
  destruct eq2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia.
  unfold find_pos. destruct (avs x0). simpl in eq2.
  destruct eq2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. unfold vsize. rewrite eq1. simpl. lia.
  unfold rshift.
  destruct (avs x0) eqn:eq3. simpl in H11. subst. simpl in *.
  destruct eq2 as [V1 [V2 V3]].
  unfold avmap in V3. rewrite eq1 in V3. simpl in V3.
  rewrite V3. 
  destruct n eqn:eq4. rewrite plus_0_l.
  rewrite Nat.mod_small by lia.
  rewrite rshift'_0 by lia. easy.
  assert ( (S n0 + (size - 1)) = n0 + size) by lia. rewrite H11.
  rewrite Nat.add_mod by lia.
  destruct (H1 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  apply X3 in V2.
  unfold avmap,vsize in V2. rewrite eq1 in V2. simpl in V2.
  rewrite V3 in V2.
  rewrite (Nat.mod_small n0) by lia.
  rewrite Nat.mod_same by lia. rewrite plus_0_r.
  rewrite Nat.mod_small by lia.
  rewrite rshift'_le by lia. easy. lia. lia.
  simpl.
  unfold avs_prop in H2. specialize (H2 x0 H6).
  bdestruct (fst (avs x0) =? x).
  rewrite H9 in H2.
  destruct H2 as [V1 [V2 V3]]. lia.
  unfold rshift.
  rewrite rshift'_irrelevant by lia. easy.
  unfold avs_prop in H2. specialize (H2 x0 H6).
  simpl.
  bdestruct (fst (avs x0) =? x).
  rewrite H8 in H2.
  destruct H2 as [V1 [V2 V3]]. lia.
  unfold rshift.
  rewrite rshift'_irrelevant by assumption. easy.
  apply H4 in H6.
  bdestruct (fst (avs x0) =? x).
  rewrite H7 in H6. lia.
  simpl.
  unfold rshift.
  rewrite rshift'_irrelevant by assumption. easy.
Qed.

Lemma rev_avs_rev_same : forall vs avs dim rmax f x,
          vars_sparse vs -> vars_anti_same vs -> avs_prop vs avs dim -> exp_com_WF vs dim
         -> exp_com_gt vs avs dim -> 0 < vsize vs x
            -> trans_state avs rmax f
                   = trans_state (rev_avs dim vs avs x) rmax (reverse f x (vsize vs x)).
Proof.
  intros. unfold trans_state.
  apply functional_extensionality.
  intros.
  unfold rev_avs,reverse,trans_rev,afbrev. 
  bdestruct (x0 <? dim).
  bdestruct ((start vs x <=? x0)).
  bdestruct ((x0 - start vs x <? vsize vs x)). simpl.
  destruct (vs x) as [p ag] eqn:eq1.
  destruct p as [p g]. destruct p as [st size].
  unfold avmap. bdestruct (x =? x). simpl.
  bdestruct ( x0 - start vs x <? size).
  bdestruct (size - 1 - ag (x0 - start vs x) <? vsize vs x).
  assert (fst (avs x0) = x).
  apply var_over_lap_1 with (vs := vs); try assumption.
  apply vs_avs_size with (dim := dim); try assumption.
  unfold avs_prop in H2. specialize (H2 x0 H6). 
  unfold find_pos. destruct (avs x0). simpl in H2.
  destruct H2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia.
  unfold avs_prop in H2. specialize (H2 x0 H6). 
  unfold find_pos. destruct (avs x0). simpl in H2.
  destruct H2 as [V1 [V2 V3]]. 
  unfold vars_anti_same in H1.
  destruct (H1 v) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite <- V3.
  rewrite X5. lia. 
  unfold avs_prop in H2. specialize (H2 x0 H6).
  rewrite H12 in H2. simpl in H2. 
  destruct H2 as [V1 [V2 V3]].
  unfold vsize. rewrite eq1. simpl.
  destruct (H1 x) as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  apply X3 in V2.
  unfold avmap,vsize in V2. rewrite eq1 in V2. simpl in V2.
  assert (size - 1 - (size - 1 -
      ag (x0 - start vs x)) = ag (x0 - start vs x)) by lia.
  rewrite H2.
  destruct (avs x0). simpl in H12. subst.
  unfold avmap in V3. rewrite eq1 in V3. simpl in V3.
  rewrite V3. easy. unfold vsize in H11. rewrite eq1 in H11. simpl in H11. lia.
  unfold vsize in H8. rewrite eq1 in H8. simpl in H8. lia. lia.
  simpl.
  bdestruct ((fst (avs x0) =? x)).
  specialize (H2 x0 H6). rewrite H9 in H2. 
  destruct H2 as [V1 [V2 V3]].  lia. simpl. easy.
  simpl.
  bdestruct ((fst (avs x0) =? x)).
  specialize (H2 x0 H6). rewrite H8 in H2. 
  destruct H2 as [V1 [V2 V3]].  lia. simpl. easy.
  simpl.
  apply H4 in H6.
  bdestruct ((fst (avs x0) =? x)).
  rewrite H7 in H6. lia.
  simpl. easy.
Qed.

Lemma vsize_vs_same: forall e dim vs vs' avs p,
         vs' = (snd (fst (trans_exp vs dim e avs))) -> vsize vs' p = vsize vs p.
Proof.
 induction e; intros;subst; try easy.
 specialize (trans_exp_cu vs avs dim p e) as eq1.
 destruct eq1. destruct H0. destruct H0. subst. rewrite H1. simpl. easy.
 rewrite H0. simpl. easy.
 simpl.
 unfold trans_lshift, vsize.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 unfold trans_rshift, vsize.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 unfold trans_rev, vsize.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p0.
 destruct (trans_exp v dim e2 p1) eqn:eq2. destruct p0.
 simpl.
 specialize (IHe1 dim vs v avs p).
 rewrite eq1 in IHe1. simpl in IHe1.
 rewrite <- IHe1.
 rewrite (IHe2 dim v v0 p1). easy.
 rewrite eq2. easy. easy.
Qed.

Lemma size_env_vs_same : forall vs vs' e dim avs,
         vs' = (snd (fst (trans_exp vs dim e avs))) -> size_env vs' = size_env vs.
Proof.
 intros. unfold size_env.
  apply functional_extensionality.
  intros.
  erewrite vsize_vs_same. reflexivity. apply H0.
Qed.

Lemma start_vs_same: forall e dim vs vs' avs p, vs' = (snd (fst (trans_exp vs dim e avs))) -> start vs' p = start vs p.
Proof.
 induction e; intros;subst; try easy.
 specialize (trans_exp_cu vs avs dim p e) as eq1.
 destruct eq1. destruct H0. destruct H0. subst. rewrite H1. simpl. easy.
 rewrite H0. simpl. easy.
 simpl.
 unfold trans_lshift, start.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 unfold trans_rshift, start.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 unfold trans_rev, start.
 destruct (vs x) eqn:eq1.
 destruct p0 eqn:eq2.
 destruct p1 eqn:eq3.
 bdestruct (p =? x). subst.
 rewrite eq1. simpl. easy.
 easy.
 simpl.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p0.
 destruct (trans_exp v dim e2 p1) eqn:eq2. destruct p0.
 simpl.
 specialize (IHe1 dim vs v avs p).
 rewrite eq1 in IHe1. simpl in IHe1.
 rewrite <- IHe1.
 rewrite (IHe2 dim v v0 p1). easy.
 rewrite eq2. easy. easy.
Qed.

Lemma vars_start_diff_vs_same : forall vs vs' e dim avs, vs' = (snd (fst (trans_exp vs dim e avs)))
                    -> vars_start_diff vs -> vars_start_diff vs'.
Proof.
  intros.
  unfold vars_start_diff in *.
  intros.
  rewrite (start_vs_same e dim vs vs' avs).
  rewrite (start_vs_same e dim vs vs' avs).
  apply H1. easy. easy. easy.
Qed.



Lemma shift_fun_lt : forall g off size, (forall i, i < size -> g i < size)
               -> (forall i, i < size -> shift_fun g off size i < size). 
Proof.
  intros. unfold shift_fun.
  bdestruct (i <? size).
  apply H0. apply Nat.mod_bound_pos. 
  lia. lia. lia.
Qed.

Lemma fbrev_lt : forall g size, (forall i, i < size -> g i < size)
               -> (forall i, i < size -> fbrev size g i < size). 
Proof.
  intros. unfold fbrev.
  bdestruct (i <? size).
  apply H0. lia. 
  lia.
Qed.

Lemma vars_fun_lt : forall e dim vs vs' avs x, vs' = (snd (fst (trans_exp vs dim e avs)))
          -> (forall i, i < vsize vs x -> vmap vs x i < vsize vs x)
          -> (forall i, i < vsize vs x -> vmap vs' x i < vsize vs x).
Proof.
  induction e; intros.
  1-2:subst; simpl; apply H1; easy.
  specialize (trans_exp_cu vs avs dim p e) as eq1.
  destruct eq1. destruct H3. destruct H3. subst. rewrite H4. simpl. apply H1. easy.
  subst. rewrite H3. simpl. apply H1. easy.
  1-5:subst; simpl; apply H1; easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_lshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (shift_fun_lt n0 (n2 - 1) n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H1. rewrite eq1 in H2. simpl in *.
  apply H1. easy. rewrite eq1 in H2. simpl in *. easy.
  apply H1. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_rshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (shift_fun_lt n0 1 n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H1. rewrite eq1 in H2. simpl in *.
  apply H1. easy. rewrite eq1 in H2. simpl in *. easy.
  apply H1. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_rev in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (fbrev_lt n0 n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H1. rewrite eq1 in H2. simpl in *.
  apply H1. easy. rewrite eq1 in H2. simpl in *. easy.
  apply H1. easy.
  simpl in H0.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
  simpl in *. subst.
  assert (v = snd (fst (trans_exp vs dim e1 avs))). rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H0 H1).
  assert (v0 = snd (fst (trans_exp v dim e2 p0))). rewrite eq2. easy.
  specialize (IHe2 dim v v0 p0 x H3).
  assert ((forall i : nat,
        i < vsize v x -> vmap v x i < vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs v avs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v avs). assumption. easy. easy.
  specialize (IHe2 H4).
  rewrite <- (vsize_vs_same e1 dim vs v avs).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v avs). easy.
  easy. easy.
Qed.


Lemma ashift_fun_lt : forall g off size, (forall i, i < size -> g i < size)
               -> (forall i, i < size -> ashift_fun g off size i < size). 
Proof.
  intros. unfold ashift_fun.
  bdestruct (i <? size).
  apply Nat.mod_bound_pos. 
  lia. lia. apply H0. lia.
Qed.


Lemma afbrev_lt : forall g size, (forall i, i < size -> g i < size)
               -> (forall i, i < size -> afbrev g size i < size). 
Proof.
  intros. unfold afbrev.
  bdestruct (i <? size). lia. lia.
Qed.


Lemma vars_afun_lt : forall e dim vs vs' avs x, vs' = (snd (fst (trans_exp vs dim e avs)))
          -> (forall i, i < vsize vs x -> avmap vs x i < vsize vs x)
          -> (forall i, i < vsize vs x -> avmap vs' x i < vsize vs x).
Proof.
  induction e; intros.
  1-2:subst; simpl; apply H1; easy.
  specialize (trans_exp_cu vs avs dim p e) as eq1.
  destruct eq1. destruct H3. destruct H3. subst. rewrite H4. simpl. apply H1. easy.
  subst. rewrite H3. simpl. apply H1. easy.
  1-5:subst; simpl; apply H1; easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_lshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (ashift_fun_lt n 1 n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H1. rewrite eq1 in H2. simpl in *.
  apply H1. easy. rewrite eq1 in H2. simpl in *. easy.
  apply H1. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_rshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (ashift_fun_lt n (n2-1) n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H1. rewrite eq1 in H2. simpl in *.
  apply H1. easy. rewrite eq1 in H2. simpl in *. easy.
  apply H1. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_rev in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  specialize (afbrev_lt n n2) as eq2.
  apply eq2. intros.
  rewrite eq1 in H1. rewrite eq1 in H2. simpl in *.
  apply H1. easy. rewrite eq1 in H2. simpl in *. easy.
  apply H1. easy.
  simpl in H0.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p. simpl in *. subst.
  assert (v = snd (fst (trans_exp vs dim e1 avs))). rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H0 H1).
  assert (v0 = snd (fst (trans_exp v dim e2 p0))). rewrite eq2. easy.
  specialize (IHe2 dim v v0 p0 x H3).
  assert ((forall i : nat,
        i < vsize v x -> avmap v x i < vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs v avs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v avs). assumption. easy. easy.
  specialize (IHe2 H4).
  rewrite <- (vsize_vs_same e1 dim vs v avs). 
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v avs). easy. easy. easy.
Qed.

Lemma shift_fun_twice : forall f g off size, off <= size -> 
           (forall x, x < size -> (f x) < size) ->
           (forall x, x < size -> (g x) < size) ->
           (forall x, x < size -> g (f x) = x) ->
           (forall x, x < size -> ashift_fun g (size - off) size (shift_fun f off size x) = x).
Proof.
  intros.
  unfold shift_fun,ashift_fun.
  bdestruct (x <? size).
  bdestruct ( off =? size). subst.
  bdestruct (f ((x + size) mod size) <? size).
  assert ((size - size) = 0) by lia. rewrite H7.
  rewrite plus_0_r.
  rewrite H3.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small x) by lia. easy.
  apply Nat.mod_bound_pos. lia. lia.
  rewrite H3.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small) by lia.
  easy.
  apply Nat.mod_bound_pos. lia. lia.
  bdestruct (off =? 0). subst.
  assert (size - 0 = size) by lia. rewrite H7.
  rewrite plus_0_r.
  bdestruct (f (x mod size) <? size).
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite H3.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small by lia. easy.
  apply Nat.mod_bound_pos. lia. lia.
  rewrite H3. 
  rewrite Nat.mod_small by lia. easy.
  apply Nat.mod_bound_pos. lia. lia.
  bdestruct (f ((x + off) mod size) <? size).
  rewrite H3.
  assert (size - off < size) by lia.
  rewrite <- (Nat.mod_small (size - off) size) by lia.
  rewrite <- Nat.add_mod by lia.
  assert ((x + off + (size - off)) = x + size) by lia.
  rewrite H10.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small x) by lia. easy.
  apply Nat.mod_bound_pos. lia. lia.
  assert (f ((x + off) mod size) < size).
  apply H1. 
  apply Nat.mod_bound_pos. lia. lia. lia. lia.
Qed.

Lemma ashift_fun_twice : forall f g off size, off <= size -> 
           (forall x, x < size -> (f x) < size) ->
           (forall x, x < size -> (g x) < size) ->
           (forall x, x < size -> f (g x) = x) ->
           (forall x, x < size -> (shift_fun f off size (ashift_fun g (size - off) size x)) = x).
Proof.
  intros.
  unfold shift_fun,ashift_fun.
  bdestruct (x <? size).
  bdestruct ( off =? size). subst.
  bdestruct ((g x + (size - size)) mod size <? size).
  assert ((size - size) = 0) by lia. rewrite H7.
  rewrite plus_0_r.
  rewrite (Nat.mod_small (g x)).
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small (g x)).
  rewrite H3. easy. easy.
  apply H2. easy. apply H2. easy.
  assert ((g x + (size - size)) mod size < size). 
  apply Nat.mod_bound_pos. lia. lia.
  lia.
  bdestruct ((g x + (size - off)) mod size <? size).
  rewrite <- (Nat.mod_small off size) by lia.
  rewrite <- Nat.add_mod by lia.
  rewrite (Nat.mod_small off) by lia.
  assert ((g x + (size - off) + off) = g x + size) by lia.
  rewrite H8.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite (Nat.mod_small (g x)).
  rewrite H3. easy. easy. apply H2. lia.
  assert ((g x + (size - off)) mod size < size).
  apply Nat.mod_bound_pos. lia. lia. lia. lia.
Qed.

Lemma afbrev_back_lt : forall f g size,
           (forall x, x < size -> (f x) < size) ->
           (forall x, x < size -> (g x) < size) ->
           (forall x, x < size -> f (g x) = x) ->
          (forall i, i < size -> afbrev f size (fbrev size g i) = i).
Proof.
  intros.
  unfold afbrev,fbrev.
  bdestruct (i <? size).
  bdestruct (g (size - 1 - i) <? size).
  rewrite H2. lia. lia.
  assert (size - 1 - i < size) by lia.
  apply H1 in H6. lia. lia.
Qed.

Lemma fbrev_back_lt : forall f g size,
           (forall x, x < size -> (f x) < size) ->
           (forall x, x < size -> (g x) < size) ->
           (forall x, x < size -> f (g x) = x) ->
          (forall i, i < size -> fbrev size f (afbrev g size i) = i).
Proof.
  intros.
  unfold afbrev,fbrev.
  bdestruct (i <? size).
  bdestruct (size - 1 - g i <? size).
  assert (g i < size). apply H1. easy.
  assert ((size - 1 - (size - 1 - g i)) = g i) by lia.
  rewrite H7. rewrite H2. lia. lia. lia. lia.
Qed.

Definition exists_fun_bij (vs:vars) (x:var) := exists g : nat -> nat,
  (forall y : nat, y < vsize vs x -> g y < vsize vs x) /\
  (forall x0 : nat,
   x0 < vsize vs x -> g (vmap vs x x0) = x0) /\
  (forall y : nat, y < vsize vs x -> vmap vs x (g y) = y).

Lemma trans_same_bij:  forall e dim vs vs' avs x, 
    (forall i, i < vsize vs x -> vmap vs x i < vsize vs x) ->
      vs' = (snd (fst (trans_exp vs dim e avs)))
       -> 0 < vsize vs x ->
       exists_fun_bij vs x -> exists_fun_bij vs' x.
Proof.
  induction e; intros; subst; try easy.
- specialize (trans_exp_cu vs avs dim p e) as eq1.
  destruct eq1. destruct H1. destruct H1. subst. rewrite H4. simpl. easy.
  rewrite H1. simpl. easy.
- unfold exists_fun_bij in *.
  rewrite (vsize_vs_same (Lshift x) dim vs) with (avs := avs).
  simpl in *.
  destruct H3 as [g [Ht [Hf Hb]]].
  bdestruct (x =? x0). subst.
  unfold trans_lshift.
  destruct (vs x0) eqn:eq1.
  destruct p. destruct p.
  exists (ashift_fun g 1 n2).
  split. intros.
  unfold vsize. rewrite eq1. simpl.
  Check shift_fun_lt.
  specialize (ashift_fun_lt g 1 n2) as eq2.
  apply eq2. intros.
  unfold vsize in Ht. 
  rewrite eq1 in Ht. simpl in Ht.
  apply Ht. easy. 
  unfold vsize in H1.
  rewrite eq1 in H1. simpl in H1.
  easy.
  unfold vsize,vmap in H0.
  rewrite eq1 in H0. simpl in H0.
  unfold vsize in Ht. rewrite eq1 in Ht. simpl in Ht.
  unfold vsize,vmap in Hf. rewrite eq1 in Hf. simpl in Hf.
  unfold vsize,vmap in Hb. rewrite eq1 in Hb. simpl in Hb.
  split.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  assert (n2 - 1 <= n2).
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. lia.
  specialize (shift_fun_twice n0 g (n2 - 1) n2 H3 H0 Ht Hf x1) as eq2.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1.
  assert (n2 - (n2 -1) = 1) by lia. rewrite H4 in eq2.
  rewrite eq2. easy. assumption. lia.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  assert ((n2 - 1) <= n2).
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. lia.
  Check ashift_fun_twice.
  specialize (ashift_fun_twice n0 g (n2 - 1) n2 H3 H0 Ht Hb) as eq2.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. 
  assert ((n2 - (n2 - 1)) = 1) by lia. rewrite H4 in eq2.
  rewrite eq2. easy. easy.
  lia.
  exists g. split. easy.
  split.
  unfold vmap,trans_lshift. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert ((snd (fst (vs x0)) x1) = vmap vs x0 x1) by easy.
  rewrite H5. rewrite Hf. easy. assumption.
  unfold vmap,trans_lshift. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert (snd (fst (vs x0)) (g y) = vmap vs x0 (g y)) by easy.
  rewrite H5. rewrite Hb. easy. assumption. easy.
- unfold exists_fun_bij in *.
  rewrite (vsize_vs_same (Rshift x) dim vs) with (avs := avs).
  simpl in *.
  destruct H3 as [g [Ht [Hf Hb]]].
  bdestruct (x =? x0). subst.
  unfold trans_rshift.
  destruct (vs x0) eqn:eq1.
  destruct p. destruct p.
  exists (ashift_fun g (n2 - 1) n2).
  split. intros.
  unfold vsize. rewrite eq1. simpl.
  Check shift_fun_lt.
  specialize (ashift_fun_lt g (n2 - 1) n2) as eq2.
  apply eq2. intros.
  unfold vsize in Ht. 
  rewrite eq1 in Ht. simpl in Ht.
  apply Ht. easy. 
  unfold vsize in H1.
  rewrite eq1 in H1. simpl in H1.
  easy.
  unfold vsize,vmap in H0.
  rewrite eq1 in H0. simpl in H0.
  unfold vsize in Ht. rewrite eq1 in Ht. simpl in Ht.
  unfold vsize,vmap in Hf. rewrite eq1 in Hf. simpl in Hf.
  unfold vsize,vmap in Hb. rewrite eq1 in Hb. simpl in Hb.
  split.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1.
  assert (1 <= n2) by lia.
  specialize (shift_fun_twice n0 g 1 n2 H3 H0 Ht Hf) as eq2.
  rewrite eq2. easy. easy. lia.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1.
  assert (1 <= n2) by lia.
  Check ashift_fun_twice.
  specialize (ashift_fun_twice n0 g 1 n2 H3 H0 Ht Hb) as eq2.
  rewrite eq2. easy.
  easy.
  lia.
  exists g. split. easy.
  split.
  unfold vmap,trans_rshift. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert ((snd (fst (vs x0)) x1) = vmap vs x0 x1) by easy.
  rewrite H5. rewrite Hf. easy. assumption.
  unfold vmap,trans_rshift. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert (snd (fst (vs x0)) (g y) = vmap vs x0 (g y)) by easy.
  rewrite H5. rewrite Hb. easy. assumption. easy.
- unfold exists_fun_bij in *.
  rewrite (vsize_vs_same (Rev x) dim vs) with (avs := avs).
  simpl in *.
  destruct H3 as [g [Ht [Hf Hb]]].
  bdestruct (x =? x0). subst.
  unfold trans_rev.
  destruct (vs x0) eqn:eq1.
  destruct p. destruct p.
  exists (afbrev g n2).
  split. intros.
  unfold vsize. rewrite eq1. simpl.
  Check afbrev_lt.
  specialize (afbrev_lt g n2) as eq2.
  apply eq2. intros.
  unfold vsize in Ht. 
  rewrite eq1 in Ht. simpl in Ht.
  apply Ht. easy. 
  unfold vsize in H1.
  rewrite eq1 in H1. simpl in H1.
  easy.
  unfold vsize,vmap in H0.
  rewrite eq1 in H0. simpl in H0.
  unfold vsize in Ht. rewrite eq1 in Ht. simpl in Ht.
  unfold vsize,vmap in Hf. rewrite eq1 in Hf. simpl in Hf.
  unfold vsize,vmap in Hb. rewrite eq1 in Hb. simpl in Hb.
  split.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1.
  Check afbrev_back_lt.
  specialize (afbrev_back_lt g n0 n2 Ht H0 Hf) as eq2.
  rewrite eq2. easy. easy. lia.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1.
  Check fbrev_back_lt.
  specialize (fbrev_back_lt n0 g n2 H0 Ht Hb) as eq2.
  rewrite eq2. easy.
  easy.
  lia.
  exists g. split. easy.
  split.
  unfold vmap,trans_rev. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert ((snd (fst (vs x0)) x1) = vmap vs x0 x1) by easy.
  rewrite H5. rewrite Hf. easy. assumption.
  unfold vmap,trans_rev. intros.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x0 =? x). lia.
  assert (snd (fst (vs x0)) (g y) = vmap vs x0 (g y)) by easy.
  rewrite H5. rewrite Hb. easy. assumption. easy.
- simpl in *.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
  simpl in *.
  assert (v = (snd (fst (trans_exp vs dim e1 avs)))).
  rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H0 H1 H2 H3).
  assert ((forall i : nat, i < vsize v x -> vmap v x i < vsize v x) ).
  intros.
  rewrite (vsize_vs_same e1 dim vs v avs).
  rewrite (vsize_vs_same e1 dim vs v avs) in H4.
  apply (vars_fun_lt e1 dim) with (avs := avs). easy. apply H0. easy. easy. easy.
  assert (v0 = snd (fst (trans_exp v dim e2 p0))).
  rewrite eq2. easy.
  assert (0 < vsize v x).
  rewrite (vsize_vs_same e1 dim vs) with (avs := avs). easy. rewrite eq1. easy.
  specialize (IHe2 dim v v0 p0 x H4 H5 H6 IHe1). easy.
Qed.

Lemma vars_finite_bij_vs_same : forall e dim vs vs' avs, vs' = (snd (fst (trans_exp vs dim e avs)))
                    -> vars_finite_bij vs -> vars_finite_bij vs'.
Proof.
  intros. unfold vars_finite_bij in *.
  intros.
  unfold weak_finite_bijection in *.
  split.
  intros. specialize (H1 x).
  destruct H1.
  rewrite (vsize_vs_same e dim vs vs' avs).
  apply (vars_fun_lt e dim vs vs' avs). assumption. easy.
  rewrite <- (vsize_vs_same e dim vs vs' avs). easy. easy. easy.
  specialize (H1 x). destruct H1.
  bdestruct (vsize vs x =? 0).
  assert (vsize vs' x = 0).
  rewrite (vsize_vs_same e dim vs vs' avs). easy. easy.
  destruct H2. exists x0.
  split. intros. lia.
  split. intros. lia.
  intros. lia.
  assert (0 < vsize vs x) by lia.
  specialize (trans_same_bij e dim vs vs' avs x H1 H0 H4 H2) as eq1. easy.
Qed.

Lemma vars_sparse_vs_same : forall e dim vs vs' avs, vs' = (snd (fst (trans_exp vs dim e avs)))
                    -> vars_sparse vs -> vars_sparse vs'.
Proof.
  intros.
  unfold vars_sparse in *.
  intros.
  repeat rewrite (start_vs_same e dim vs vs' avs) by easy.
  rewrite (vsize_vs_same e dim vs vs' avs) in H3 by easy.
  rewrite (vsize_vs_same e dim vs vs' avs) in H4 by easy.
  apply H1; easy.
Qed.

Lemma vars_fun_ge : forall e dim vs vs' avs x, vs' = (snd (fst (trans_exp vs dim e avs)))
          -> (forall i, i >= vsize vs x -> vmap vs x i >= vsize vs x)
          -> (forall i, i >= vsize vs x -> vmap vs' x i >= vsize vs x).
Proof.
  induction e; intros.
  1-2:subst; simpl; apply H1; easy.
  specialize (trans_exp_cu vs avs dim p e) as eq1.
  destruct eq1. destruct H3. destruct H3. subst. rewrite H4. simpl. apply H1. easy.
  subst. rewrite H3. simpl. apply H1. easy.
  1-5:subst; simpl; apply H1; easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_lshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H2. simpl in H2.
  unfold shift_fun.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H1. simpl in H1. apply H1. easy.
  apply H1. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_rshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H2. simpl in H2.
  unfold shift_fun.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H1. simpl in H1. apply H1. easy.
  apply H1. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_rev in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H2. simpl in H2.
  unfold fbrev.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H1. simpl in H1. apply H1. easy.
  apply H1. easy.
  subst. simpl.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p. simpl.
  assert (v = snd (fst (trans_exp vs dim e1 avs))). rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H0 H1).
  assert (v0 = snd (fst (trans_exp v dim e2 p0))). rewrite eq2. easy.
  specialize (IHe2 dim v v0 p0 x H3).
  assert ((forall i : nat,
        i >= vsize v x -> vmap v x i >= vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs) with (avs := avs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v avs). assumption. easy. easy.
  specialize (IHe2 H4).
  rewrite <- (vsize_vs_same e1 dim vs v avs).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v avs). easy.
  easy. easy.
Qed.

Lemma vars_afun_ge : forall e dim vs vs' avs x, vs' = (snd (fst (trans_exp vs dim e avs)))
          -> (forall i, i >= vsize vs x -> avmap vs x i >= vsize vs x)
          -> (forall i, i >= vsize vs x -> avmap vs' x i >= vsize vs x).
Proof.
  induction e; intros.
  1-2:subst; simpl; apply H1; easy.
  specialize (trans_exp_cu vs avs dim p e) as eq1.
  destruct eq1. destruct H3. destruct H3. subst. rewrite H4. simpl. apply H1. easy.
  subst. rewrite H3. simpl. apply H1. easy.
  1-5:subst; simpl; apply H1; easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_lshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H2. simpl in H2.
  unfold ashift_fun.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H1. simpl in H1. apply H1. easy.
  apply H1. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_rshift in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H2. simpl in H2.
  unfold ashift_fun.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H1. simpl in H1. apply H1. easy.
  apply H1. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_rev in H0.
  destruct (vs x) eqn:eq1.
  destruct p eqn:eq2.
  destruct p0 eqn:eq3.
  rewrite H0.
  bdestruct (x0 =? x). subst. rewrite eq1. simpl in *.
  rewrite eq1 in H2. simpl in H2.
  unfold afbrev.
  bdestruct (i <? n2). lia.
  rewrite eq1 in H1. simpl in H1. apply H1. easy.
  apply H1. easy.
  subst. simpl.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p. simpl.
  assert (v = snd (fst (trans_exp vs dim e1 avs))). rewrite eq1. easy.
  specialize (IHe1 dim vs v avs x H0 H1).
  assert (v0 = snd (fst (trans_exp v dim e2 p0))). rewrite eq2. easy.
  specialize (IHe2 dim v v0 p0 x H3).
  assert ((forall i : nat,
        i >= vsize v x -> avmap v x i >= vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs v avs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v avs). assumption. easy. easy.
  specialize (IHe2 H4).
  rewrite <- (vsize_vs_same e1 dim vs v avs).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v avs). easy.
  easy. easy.
Qed.

Lemma vars_vs_anti_bij :
    forall e dim vs vs' avs x, vs' = (snd (fst (trans_exp vs dim e avs))) ->
     (forall i : nat, i < vsize vs x -> vmap vs x i < vsize vs x) ->
     (forall i : nat, i >= vsize vs x -> vmap vs x i >= vsize vs x) ->
    (forall i : nat, i < vsize vs x -> avmap vs x i < vsize vs x) ->
       (forall i : nat, i >= vsize vs x -> avmap vs x i >= vsize vs x) ->
      (forall i : nat, vmap vs x (avmap vs x i) = i) -> 
       (forall i : nat, avmap vs x (vmap vs x i) = i) ->
      (forall i : nat, vmap vs' x (avmap vs' x i) = i) /\ (forall i : nat, avmap vs' x (vmap vs' x i) = i).
Proof.
 induction e; intros.
 1-2:subst; simpl; easy.
 specialize (trans_exp_cu vs avs dim p e) as eq1.
 destruct eq1. destruct H7. destruct H7. subst. rewrite H8. simpl. easy.
 subst. rewrite H7. simpl. easy.
 1-5:subst; simpl; easy.
-
 subst. simpl. split. intros.
 unfold trans_lshift.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 bdestruct (0 <? n2).
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite shift_fun_back_1 ; try easy.
 unfold shift_fun,ashift_fun.
 bdestruct (i <? n2). lia.
 bdestruct (n i <? n2).
 unfold vsize,avmap in H4. rewrite eq1 in H4. simpl in H4.
 apply H4 in H7. lia.
 unfold vmap,avmap in H5. rewrite eq1 in H5. simpl in H5.
 rewrite H5. easy.
 unfold vmap,avmap in H5.
 rewrite H5. easy.
 intros.
 unfold trans_lshift.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 bdestruct (0 <? n2).
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite shift_fun_back ; try easy.
 unfold shift_fun,ashift_fun.
 bdestruct (i <? n2). lia.
 bdestruct (n0 i <? n2).
 unfold vsize,avmap in H2. rewrite eq1 in H2. simpl in H2.
 apply H2 in H7. lia.
 unfold vmap,avmap in H6. rewrite eq1 in H6. simpl in H6.
 rewrite H6. easy.
 unfold vmap,avmap in H6.
 rewrite H6. easy.
- subst. simpl.
 split. intros.
 unfold trans_rshift.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 bdestruct (0 <? n2).
 assert (shift_fun n0 1 n2 (ashift_fun n (n2 - 1) n2 i) 
           = shift_fun n0 (n2 - (n2 - 1)) n2 (ashift_fun n (n2 - 1) n2 i)).
 assert (n2 - (n2 -1) = 1) by lia.
 rewrite H7. easy.
 rewrite H7.
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite shift_fun_back_1 ; try easy. lia.
 unfold shift_fun,ashift_fun.
 bdestruct (i <? n2). lia.
 bdestruct (n i <? n2).
 unfold vsize,avmap in H4. rewrite eq1 in H4. simpl in H4.
 apply H4 in H7. lia.
 unfold vmap,avmap in H5. rewrite eq1 in H5. simpl in H5.
 rewrite H5. easy.
 unfold vmap,avmap in H5.
 rewrite H5. easy.
 intros.
 unfold trans_rshift.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 bdestruct (0 <? n2).
 assert (ashift_fun n (n2 - 1) n2 (shift_fun n0 1 n2 i) 
           = ashift_fun n (n2 - 1) n2 (shift_fun n0 (n2 - (n2 -1)) n2 i)).
 assert (n2 - (n2 -1) = 1) by lia.
 rewrite H7. easy.
 rewrite H7.
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite shift_fun_back ; try easy. lia.
 unfold shift_fun,ashift_fun.
 bdestruct (i <? n2). lia.
 bdestruct (n0 i <? n2).
 unfold vsize,avmap in H2. rewrite eq1 in H2. simpl in H2.
 apply H2 in H7. lia.
 unfold vmap,avmap in H6. rewrite eq1 in H6. simpl in H6.
 rewrite H6. easy.
 unfold vmap,avmap in H6.
 rewrite H6. easy.
-
 subst. simpl. split. intros.
 unfold trans_rev.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite afbrev_back ; try easy.
 unfold vmap,avmap in H5. rewrite H5. easy.
 intros.
 unfold trans_rev.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2.
 destruct p0 eqn:eq3.
 unfold vmap,avmap.
 bdestruct (x0 =? x).
 subst. simpl.
 unfold vsize in *. unfold vmap,avmap in *.
 rewrite eq1 in *. simpl in *.
 rewrite fbrev_back ; try easy.
 unfold vmap,avmap in H6. rewrite H6. easy.
-
 subst. simpl.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p. simpl.
 specialize (IHe1 dim vs v avs x).
 rewrite eq1 in IHe1.
 assert (v = snd (fst (b, v, p0))) by easy.
 specialize (IHe1 H0 H1 H2 H3 H4 H5 H6).
 specialize (IHe2 dim v v0 p0 x).
 rewrite eq2 in IHe2.
 assert (v0 = snd (fst (b0, v0, p1))) by easy.
 apply IHe2 in H7. easy.
 rewrite (vsize_vs_same e1 dim vs v avs).
 apply (vars_fun_lt e1 dim) with (avs := avs). rewrite eq1. easy. easy.
 rewrite eq1. easy.
 rewrite (vsize_vs_same e1 dim vs v avs).
 apply (vars_fun_ge e1 dim) with (avs := avs). rewrite eq1. easy. easy.
 rewrite eq1. easy.
 rewrite (vsize_vs_same e1 dim vs v avs).
 apply (vars_afun_lt e1 dim) with (avs := avs). rewrite eq1. easy. easy.
 rewrite eq1. easy.
 rewrite (vsize_vs_same e1 dim vs v avs).
 apply (vars_afun_ge e1 dim) with (avs := avs). rewrite eq1. easy. easy.
 rewrite eq1. easy. easy. easy.
Qed.

Lemma vars_anti_vs_same: forall e dim vs vs' avs, vs' = (snd (fst (trans_exp vs dim e avs)))
                    -> vars_anti_same vs -> vars_anti_same vs'.
Proof.
  intros.
  unfold vars_anti_same in *.
  intro x. specialize (H1 x).
  destruct H1.
  split.
  rewrite (vsize_vs_same e dim vs vs' avs) by assumption.
  apply (vars_fun_lt e dim vs vs' avs). easy. assumption.
  split.
  rewrite (vsize_vs_same e dim vs vs' avs) by assumption.
  apply (vars_fun_ge e dim vs) with (avs := avs) ; easy.
  split.
  rewrite (vsize_vs_same e dim vs vs' avs) by assumption.
  apply (vars_afun_lt e dim vs vs' avs). easy. easy.
  split.
  rewrite (vsize_vs_same e dim vs vs' avs) by assumption.
  apply (vars_afun_ge e dim vs vs' avs) ; easy.
  destruct H2 as [H2 [H3 [H4 [H5 H6]]]].
  specialize (vars_vs_anti_bij e dim vs vs' avs x H0 H1 H2 H3 H4 H5 H6) as eq1.
  destruct eq1. easy.
Qed.


Lemma wf_vs_same: forall e1 e2 avs dim vs vs', exp_WF vs e1 -> 
                vs' = (snd (fst (trans_exp vs dim e2 avs))) -> exp_WF vs' e1.
Proof.
  intros.
  induction H0. constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  apply IHexp_WF. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  apply IHexp_WF1. easy.
  apply IHexp_WF2. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs vs' avs). easy. easy.
Qed.


Lemma exists_same_vs_var : forall e dim x n avs vs vs', vs' = (snd (fst (trans_exp vs dim e avs)))->
                  n < vsize vs x -> 
                 (exists n', n' < vsize vs x /\ find_pos vs' (x,n) = find_pos vs (x,n')).
Proof.
 induction e; intros.
 1-2:subst; exists n; easy.
 specialize (trans_exp_cu vs avs dim p e) as eq1.
 destruct eq1. destruct H2. destruct H2. subst. rewrite H3. simpl.
 exists n. easy.
 subst. rewrite H2. exists n. simpl. easy.
 1-5:subst; exists n; easy.
- 
 specialize (start_vs_same (Lshift x) dim vs vs' avs x0 H0) as eq1.
 specialize (vsize_vs_same (Lshift x) dim vs vs' avs x0 H0) as eq2.
 simpl.
 rewrite eq1. 
 bdestruct (x =? x0). subst.
 unfold vmap. simpl.
 simpl in eq2.
 unfold trans_lshift in *.
 destruct (vs x0) eqn:eq3.
 destruct p. destruct p.
 unfold vsize in eq2. 
 bdestruct (x0 =? x0). simpl in *.
 unfold vsize in *. rewrite <- eq2 in *.
 unfold shift_fun.
 bdestruct (n <? n3).
 exists (((n + (n3 - 1)) mod n3)).
 split.
 apply Nat.mod_bound_pos. lia. lia. easy. lia. lia.
 exists n. 
 rewrite H0. simpl.
 unfold trans_lshift,vmap.
 destruct (vs x) eqn:eq3. destruct p. destruct p.
 bdestruct (x0 =? x). lia.
 easy.
-
 specialize (start_vs_same (Rshift x) dim vs vs' avs x0 H0) as eq1.
 specialize (vsize_vs_same (Rshift x) dim vs vs' avs x0 H0) as eq2.
 simpl.
 rewrite eq1. 
 bdestruct (x =? x0). subst.
 unfold vmap. simpl.
 simpl in eq2.
 unfold trans_rshift in *.
 destruct (vs x0) eqn:eq3.
 destruct p. destruct p.
 unfold vsize in eq2. 
 bdestruct (x0 =? x0). simpl in *.
 unfold vsize in *. rewrite <- eq2 in *.
 unfold shift_fun.
 bdestruct (n <? n3).
 exists (((n + 1) mod n3)).
 split.
 apply Nat.mod_bound_pos. lia. lia. easy. lia.
 exists n. 
 rewrite eq3. simpl. easy.
 exists n.
 split. easy.
 rewrite H0. simpl.
 unfold trans_rshift,vmap.
 destruct (vs x) eqn:eq3. destruct p. destruct p.
 bdestruct (x0 =? x). lia.
 easy.
- 
 specialize (start_vs_same (Rev x) dim vs vs' avs x0 H0) as eq1.
 specialize (vsize_vs_same (Rev x) dim vs vs' avs x0 H0) as eq2.
 simpl.
 rewrite eq1. 
 bdestruct (x =? x0). subst.
 unfold vmap. simpl.
 simpl in eq2.
 unfold trans_rev in *.
 destruct (vs x0) eqn:eq3.
 destruct p. destruct p.
 unfold vsize in eq2. 
 bdestruct (x0 =? x0). simpl in *.
 unfold vsize in *. rewrite <- eq2 in *.
 unfold fbrev.
 bdestruct (n <? n3).
 exists ((n3 - 1 - n)).
 split. lia. easy. lia. lia. 
 exists n.
 split. easy.
 rewrite H0. simpl.
 unfold trans_rev,vmap.
 destruct (vs x) eqn:eq3. destruct p. destruct p.
 bdestruct (x0 =? x). lia.
 easy.
- 
 simpl in H0.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_exp v dim e2 p0 ) eqn:eq2. destruct p.
 simpl in H0. subst.
 specialize (IHe2 dim x n p0 v v0).
 rewrite eq2 in IHe2.
 assert (v0 = snd (fst (b0, v0, p1))) by easy.
 apply IHe2 in H0. destruct H0. destruct H0.
 specialize (IHe1 dim x x0 avs vs v).
 rewrite eq1 in IHe1. assert (v = snd (fst (b, v, p0))) by easy.
 apply IHe1 in H3. destruct H3.
 destruct H3.
 exists x1.
 split. assumption. 
 rewrite H2. easy.
 erewrite <- vsize_vs_same.
 apply H0. rewrite eq1. easy.
 erewrite vsize_vs_same.
 apply H1.
 rewrite eq1. easy.
Qed.

Lemma exp_com_WF_vs_same : forall e dim avs vs vs', vs' = (snd (fst (trans_exp vs dim e avs)))
          -> exp_com_WF vs dim -> exp_com_WF vs' dim.
Proof.
 induction e; intros.
 1-2:subst; easy.
 specialize (trans_exp_cu vs avs dim p e) as eq1.
 destruct eq1. destruct H2. destruct H2. subst. easy.
 subst. rewrite H2. easy.
 1-5:subst; easy.
 unfold exp_com_WF in *.
 intros.
 specialize (vsize_vs_same (Lshift x) dim vs vs' avs (fst p) H0) as eq1.
 rewrite eq1 in H2.
 specialize (exists_same_vs_var (Lshift x) dim (fst p) (snd p) avs vs vs' H0 H2) as eq5.
 destruct eq5. destruct H3.
 assert ((fst p, snd p) = p). destruct p. simpl. easy.
 rewrite H5 in H4. rewrite H4.
 apply H1. simpl. easy.
 unfold exp_com_WF in *.
 intros.
 specialize (vsize_vs_same (Rshift x) dim vs vs' avs (fst p) H0) as eq1.
 rewrite eq1 in H2.
 specialize (exists_same_vs_var (Rshift x) dim (fst p) (snd p) avs vs vs' H0 H2) as eq5.
 destruct eq5. destruct H3.
 assert ((fst p, snd p) = p). destruct p. simpl. easy.
 rewrite H5 in H4. rewrite H4.
 apply H1. simpl. easy.
 unfold exp_com_WF in *.
 intros.
 specialize (vsize_vs_same (Rev x) dim vs vs' avs (fst p) H0) as eq1.
 rewrite eq1 in H2.
 specialize (exists_same_vs_var (Rev x) dim (fst p) (snd p) avs vs vs' H0 H2) as eq5.
 destruct eq5. destruct H3.
 assert ((fst p, snd p) = p). destruct p. simpl. easy.
 rewrite H5 in H4. rewrite H4.
 apply H1. simpl. easy.
 rewrite H0. simpl in *.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
 specialize (IHe1 dim avs vs v).
 specialize (IHe2 dim p0 v v0).
 subst.
 apply IHe2. rewrite eq2. easy.
 apply IHe1. rewrite eq1. easy.
 assumption. 
Qed.

Lemma exp_com_gt_vs_same :
    forall e dim vs vs' avs avs', vs' = (snd (fst (trans_exp vs dim e avs)))
      -> avs' = snd (trans_exp vs dim e avs)
          -> exp_com_gt vs avs dim -> exp_com_gt vs' avs' dim.
Proof.
 induction e; intros.
 1-2:subst; easy.
 specialize (trans_exp_cu vs avs dim p e) as eq1.
 destruct eq1. destruct H3. destruct H3. subst. easy.
 subst. rewrite H3. easy.
 1-5:subst; easy.
 unfold exp_com_gt in *. intros.
 rewrite (vsize_vs_same (Lshift x) dim vs vs' avs) by try assumption.
 rewrite H1. simpl. unfold lshift_avs.
 bdestruct ((i <? dim)). lia. simpl. apply H2. easy.
 unfold exp_com_gt in *. intros.
 rewrite (vsize_vs_same (Rshift x) dim vs vs' avs) by try assumption.
 rewrite H1. simpl. unfold rshift_avs.
 bdestruct ((i <? dim)). lia. simpl. apply H2. easy.
 unfold exp_com_gt in *. intros.
 rewrite (vsize_vs_same (Rev x) dim vs vs' avs) by try assumption.
 rewrite H1. simpl. unfold rev_avs.
 bdestruct ((i <? dim)). lia. simpl. apply H2. easy.
 rewrite H1. rewrite H0. simpl in *.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p. simpl in *.
 specialize (IHe1 dim vs v avs p0).
 rewrite eq1 in IHe1. simpl in IHe1.
 apply IHe1 in H2.
 apply (IHe2 dim v v0 p0 p1). rewrite eq2. easy. rewrite eq2. easy.
 1-3:easy.
Qed.

Lemma avs_prop_vs_same : forall e dim vs vs' avs avs', vs' = (snd (fst (trans_exp vs dim e avs)))
      -> avs' = snd (trans_exp vs dim e avs) -> vars_anti_same vs -> vars_sparse vs
          -> avs_prop vs avs dim -> avs_prop vs' avs' dim.
Proof.
 induction e; intros.
 1-2:subst; easy.
 specialize (trans_exp_cu vs avs dim p e) as eq1.
 destruct eq1. destruct H5. destruct H5. subst. easy.
 subst. rewrite H5. easy.
 1-5:subst; easy.
-
 specialize (vs_avs_bij_r vs avs dim H4 H2) as Q1.
 specialize (vs_avs_size vs avs dim H4 H2) as Q2.
 unfold avs_prop. intros.
 subst.
 simpl. unfold trans_lshift,lshift_avs.
 destruct (vs x) as [p ag] eqn:eq1.
 destruct p as [p g]. destruct p as [st size].
 bdestruct (i <? dim).
 bdestruct ((start vs x <=? i)).
 bdestruct ((i - start vs x <? vsize vs x)). simpl.
 split.
 unfold start. bdestruct (x =? x). simpl.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H8 in H4.
 destruct H4 as [V1 [V2 V3]]. unfold start in V1. rewrite eq1 in V1. simpl in V1. easy.
 specialize (var_not_over_lap_1 x (avs i) vs H3 H2) as eq2.
 apply eq2 in H8. destruct H8. rewrite Q1 in H8. lia. easy.
 rewrite Q1 in H8. lia. easy. apply Q2. easy. rewrite eq1. simpl.
 unfold start in H1. rewrite eq1 in H1. simpl in H1. easy. 
 split. unfold start,vsize. simpl.
 bdestruct (x =? x). simpl. unfold start,vsize in H6. rewrite eq1 in H6. simpl in H6. lia. lia.
 unfold avmap,start,trans_lshift.
 rewrite eq1. bdestruct (x =? x). simpl. easy. lia.
 simpl.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H7 in H4.
 destruct H4 as [V1 [V2 V3]]. unfold start in V2. rewrite eq1 in V2. simpl in V2.
 unfold start in H6. rewrite eq1 in H6. simpl in H6. lia. 
 unfold start,vsize,avmap.
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H4. easy.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H6 in H4.
 destruct H4 as [V1 [V2 V3]]. lia. simpl.
 unfold start,vsize,avmap. 
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H4. easy. lia.
-
 specialize (vs_avs_bij_r vs avs dim H4 H2) as Q1.
 specialize (vs_avs_size vs avs dim H4 H2) as Q2.
 unfold avs_prop. intros.
 subst.
 simpl. unfold trans_rshift,rshift_avs.
 destruct (vs x) as [p ag] eqn:eq1.
 destruct p as [p g]. destruct p as [st size].
 bdestruct (i <? dim).
 bdestruct ((start vs x <=? i)).
 bdestruct ((i - start vs x <? vsize vs x)). simpl.
 split.
 unfold start. bdestruct (x =? x). simpl.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H8 in H4.
 destruct H4 as [V1 [V2 V3]]. unfold start in V1. rewrite eq1 in V1. simpl in V1. easy.
 specialize (var_not_over_lap_1 x (avs i) vs H3 H2) as eq2.
 apply eq2 in H8. destruct H8. rewrite Q1 in H8. lia. easy.
 rewrite Q1 in H8. lia. easy. apply Q2. easy. rewrite eq1. simpl.
 unfold start in H1. rewrite eq1 in H1. simpl in H1. easy. 
 split. unfold start,vsize. simpl.
 bdestruct (x =? x). simpl. unfold start,vsize in H6. rewrite eq1 in H6. simpl in H6. lia. lia.
 unfold avmap,start,trans_rshift.
 rewrite eq1. bdestruct (x =? x). simpl. easy. lia.
 simpl.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H7 in H4.
 destruct H4 as [V1 [V2 V3]]. unfold start in V2. rewrite eq1 in V2. simpl in V2.
 unfold start in H6. rewrite eq1 in H6. simpl in H6. lia. 
 unfold start,vsize,avmap.
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H4. easy.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H6 in H4.
 destruct H4 as [V1 [V2 V3]]. lia. simpl.
 unfold start,vsize,avmap. 
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H4. easy. lia.
-
 specialize (vs_avs_bij_r vs avs dim H4 H2) as Q1.
 specialize (vs_avs_size vs avs dim H4 H2) as Q2.
 unfold avs_prop. intros.
 subst.
 simpl. unfold trans_rev,rev_avs.
 destruct (vs x) as [p ag] eqn:eq1.
 destruct p as [p g]. destruct p as [st size].
 bdestruct (i <? dim).
 bdestruct ((start vs x <=? i)).
 bdestruct ((i - start vs x <? vsize vs x)). simpl.
 split.
 unfold start. bdestruct (x =? x). simpl.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H8 in H4.
 destruct H4 as [V1 [V2 V3]]. unfold start in V1. rewrite eq1 in V1. simpl in V1. easy.
 specialize (var_not_over_lap_1 x (avs i) vs H3 H2) as eq2.
 apply eq2 in H8. destruct H8. rewrite Q1 in H8. lia. easy.
 rewrite Q1 in H8. lia. easy. apply Q2. easy. rewrite eq1. simpl.
 unfold start in H1. rewrite eq1 in H1. simpl in H1. easy. 
 split. unfold start,vsize. simpl.
 bdestruct (x =? x). simpl. unfold start,vsize in H6. rewrite eq1 in H6. simpl in H6. lia. lia.
 unfold avmap,start,trans_rev.
 rewrite eq1. bdestruct (x =? x). simpl. easy. lia.
 simpl.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H7 in H4.
 destruct H4 as [V1 [V2 V3]]. unfold start in V2. rewrite eq1 in V2. simpl in V2.
 unfold start in H6. rewrite eq1 in H6. simpl in H6. lia. 
 unfold start,vsize,avmap.
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H4. easy.
 specialize (H4 i H5).
 bdestruct (fst (avs i) =? x). rewrite H6 in H4.
 destruct H4 as [V1 [V2 V3]]. lia. simpl.
 unfold start,vsize,avmap. 
 bdestruct (fst (avs i) =? x). lia.
 unfold start,vsize,avmap in H4. easy. lia.
-
 subst. simpl.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
 destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
 simpl.
 specialize (IHe1 dim vs v avs p0).
 rewrite eq1 in IHe1. simpl in IHe1.
 assert (v = v) by easy. assert (p0 = p0) by easy.
 specialize (IHe1 H0 H1 H2 H3 H4).
 apply (vars_anti_vs_same e1 dim vs v avs) in H2.
 apply (vars_sparse_vs_same e1 dim vs v avs) in H3.
 apply (IHe2 dim v v0 p0 p1). rewrite eq2. easy.
 rewrite eq2. easy. easy. easy. easy. rewrite eq1. easy.
 rewrite eq1. easy.
Qed.

Lemma efresh_trans_same: forall e dim vs vs' avs p, exp_fresh (size_env vs) p e -> 
                vs' = (snd (fst (trans_exp vs dim e avs))) ->
                 find_pos vs p = find_pos vs' p.
Proof.
 induction e; intros; subst; try easy.
 specialize (trans_exp_cu vs avs dim p e) as eq1.
 destruct eq1. destruct H1. destruct H1. subst. easy.
 rewrite H1. easy.
 inv H0. simpl. unfold or_not_eq in H3. destruct H3.
 unfold find_pos,trans_lshift,shift_fun.
 destruct p.
 destruct (vs x) eqn:eq1. destruct p. destruct p.
 unfold start,vmap.
 bdestruct (v =? x). simpl in *. lia. easy.
 unfold find_pos,trans_lshift,shift_fun, size_env in *.
 destruct p.
 destruct (vs x) eqn:eq1. destruct p. destruct p.
 unfold start,vmap,vsize in *.
 rewrite eq1 in *.
 bdestruct (v =? x). subst. simpl in *.
 bdestruct (n <? n3). lia. rewrite eq1 in *. simpl in *. easy. easy.
 inv H0. simpl. unfold or_not_eq in H3. destruct H3.
 unfold find_pos,trans_rshift,shift_fun.
 destruct p.
 destruct (vs x) eqn:eq1. destruct p. destruct p.
 unfold start,vmap.
 bdestruct (v =? x). simpl in *. lia. easy.
 unfold find_pos,trans_rshift,shift_fun, size_env in *.
 destruct p.
 destruct (vs x) eqn:eq1. destruct p. destruct p.
 unfold start,vmap,vsize in *.
 rewrite eq1 in *.
 bdestruct (v =? x). subst. simpl in *.
 bdestruct (n <? n3). lia. rewrite eq1 in *. simpl in *. easy. easy.
 inv H0. simpl. unfold or_not_eq in H3. destruct H3.
 unfold find_pos,trans_rev,shift_fun.
 destruct p.
 destruct (vs x) eqn:eq1. destruct p. destruct p.
 unfold start,vmap.
 bdestruct (v =? x). simpl in *. lia. easy.
 unfold find_pos,trans_rev,shift_fun, size_env in *.
 destruct p.
 destruct (vs x) eqn:eq1. destruct p. destruct p.
 unfold start,vmap,vsize in *.
 rewrite eq1 in *.
 bdestruct (v =? x). subst. simpl in *.
 rewrite eq1. simpl.
 unfold fbrev.
 bdestruct (n <? n3). lia. easy. easy.
 inv H0. simpl.
 destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p0.
 destruct (trans_exp v dim e2 p1) eqn:eq2. destruct p0. simpl.
 specialize (IHe1 dim vs v avs p H4).
 rewrite IHe1.
 apply (IHe2 dim) with (avs := p1); try assumption.
 assert (size_env v = size_env vs).
 unfold size_env.
 apply functional_extensionality; intro.
 erewrite vsize_vs_same. easy.
 rewrite eq1. easy. rewrite H0. easy.
 rewrite eq2. easy.
 rewrite eq1. easy.
Qed.

Check trans_exp.

Lemma list_neq {A:Type} : forall (l :list A) a, l <> (a :: l).
Proof.
  induction l; intros.
  easy.
  intros R. inv R. specialize (IHl a0). contradiction.
Qed.

Lemma neu_trans_state : forall e l vs dim avs, exp_neu l e l -> snd (trans_exp vs dim e avs) = avs.
Proof.
  induction e; intros; try easy.
  specialize (trans_exp_cu vs avs dim p e) as eq1.
  destruct eq1. destruct H1. destruct H1. subst. rewrite H2. easy.
  rewrite H1. easy.
  inv H0. unfold insert_ls in H5. destruct (l x) eqn:eq1.
  assert (l x <> (update l x (Some (Ls :: l0))) x).
  rewrite update_index_eq. rewrite eq1. intros R. inv R.
  specialize (list_neq l0 Ls) as eq2. contradiction.
  rewrite <- H5 in H0. contradiction.
  assert (l x <> update l x (Some ([Ls])) x).
  rewrite update_index_eq. rewrite eq1. easy.
  rewrite <- H5 in H0. contradiction.
Admitted.


Local Transparent SQIR.ID SQIR.CNOT SQIR.X SQIR.Rz. 

Lemma vkron_fun_gt : forall i m (f : nat -> Vector 2) v, i <= m -> vkron i (update f m v) = vkron i f.
Proof.
  intros. induction i.
  simpl. easy.
  simpl.
  rewrite IHi by lia.
  rewrite update_index_neq. easy. lia.
Qed.

Lemma vkron_shift_gt : forall i m j (f : nat -> Vector 2) v, j < m ->
                vkron i (shift (update f j v) m) = vkron i (shift f m).
Proof.
  intros. induction i.
  simpl. easy.
  simpl.
  rewrite IHi by lia.
  assert (shift (update f j v) m i = shift f m i).
  unfold shift.
  rewrite update_index_neq. easy. lia.
  rewrite H1. easy.
Qed.


Lemma vkron_split_up : forall n i (f : nat -> Vector 2) v,
  (forall j, WF_Matrix (f j)) -> WF_Matrix v ->
(*  (forall j, j < n -> WF_Matrix (f j)) -> Maybe necessary? *)
  i < n ->
  vkron n (update f i v) = (vkron i f) ⊗ v ⊗ (vkron (n - (i + 1)) (shift f (i + 1))).
Proof.
  intros.
  rewrite (vkron_split n i).
  rewrite vkron_fun_gt by lia.
  assert ((n - 1 - i) = n - (i + 1)) by lia. rewrite H3.
  rewrite vkron_shift_gt.
  rewrite update_index_eq. easy. lia.
  intros.
  bdestruct (i =? j). subst.
  rewrite update_index_eq. assumption.
  rewrite update_index_neq.
  apply H0. lia. lia.
Qed.



Lemma denote_ID_1 : forall dim n, n < dim -> uc_eval (ID n) = I (2 ^ dim).
Proof.
  intros.
  rewrite denote_ID. unfold pad.
  bdestruct (n+1<=? dim).
  gridify. easy. lia.
Qed.

Lemma vkron_X : forall (n i : nat) (f : nat -> Vector 2),
  i < n ->
  (forall j, WF_Matrix (f j))  ->
  (uc_eval (SQIR.X i)) × (vkron n f) 
      = vkron i f ⊗ (σx × (f i)) ⊗ vkron (n - (i + 1)) (shift f (i + 1)).
Proof.
  intros.
  autorewrite with eval_db.
  rewrite (vkron_split n i f H1 H0). 
  simpl; replace (n - 1 - i) with (n - (i + 1)) by lia.
  repad. 
  Msimpl. easy.
Qed.

Lemma vkron_Rz : forall (n i : nat) q (f : nat -> Vector 2),
  i < n ->
  (forall j, WF_Matrix (f j))  ->
  (uc_eval (SQIR.Rz q i)) × (vkron n f) 
      = vkron i f ⊗ (phase_shift q × f i) ⊗ vkron (n - (i + 1)) (shift f (i + 1)).
Proof.
  intros.
  autorewrite with eval_db.
  rewrite (vkron_split n i f H1 H0). 
  simpl; replace (n - 1 - i) with (n - (i + 1)) by lia.
  repad. 
  Msimpl. easy.
Qed.

Lemma is_fresh_sr_gates : forall m n size x dim vs, 0 < n -> m <= n -> m <= size
       -> n < vsize vs x -> vars_finite_bij vs
       -> is_fresh (find_pos vs (x,n)) (gen_sr_gate' vs dim x m size).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  specialize (finite_bij_inj vs x H4 0 n) as eq1.
  assert (0 < vsize vs x) by lia.
  specialize (eq1 H5 H3). lia.
  constructor.
  apply IHm; try lia. easy.
  apply fresh_app1.  
  specialize (finite_bij_inj vs x H4 m n) as eq1.
  assert (m < vsize vs x) by lia.
  specialize (eq1 H5 H3). lia.
Qed.


Lemma is_fresh_sr_gate_start : forall m n size x y dim vs, m <= size -> x <> y
       -> n < vsize vs x -> m < vsize vs y -> vars_finite_bij vs -> vars_sparse vs
       -> is_fresh (find_pos vs (x,n)) (gen_sr_gate' vs dim y m size).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  unfold vars_sparse in *.
  specialize (finite_bij_lt vs H4 x n H2) as eq1.
  specialize (finite_bij_lt vs H4 y 0 H3) as eq2.
  apply H5; try lia.
  constructor.
  apply IHm; try lia. easy. easy.
  apply fresh_app1.  
  specialize (finite_bij_lt vs H4 x n H2) as eq1.
  assert (m < vsize vs y) by lia.
  specialize (finite_bij_lt vs H4 y m H6) as eq2.
  apply H5; try lia.
Qed.

Lemma is_fresh_srr_gates : forall m n size x dim vs, 0 < n -> m <= n -> m <= size
       -> n < vsize vs x -> vars_finite_bij vs
       -> is_fresh (find_pos vs (x,n)) (gen_srr_gate' vs dim x m size).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  specialize (finite_bij_inj vs x H4 0 n) as eq1.
  assert (0 < vsize vs x) by lia.
  specialize (eq1 H5 H3). lia.
  constructor.
  apply IHm; try lia. easy.
  apply fresh_app1.  
  specialize (finite_bij_inj vs x H4 m n) as eq1.
  assert (m < vsize vs x) by lia.
  specialize (eq1 H5 H3). lia.
Qed.

Lemma is_fresh_srr_gate_start : forall m n size x y dim vs, m <= size -> x <> y
       -> n < vsize vs x -> m < vsize vs y -> vars_finite_bij vs -> vars_sparse vs
       -> is_fresh (find_pos vs (x,n)) (gen_srr_gate' vs dim y m size).
Proof.
  induction m; intros; simpl.
  apply fresh_app1.
  unfold vars_sparse in *.
  specialize (finite_bij_lt vs H4 x n H2) as eq1.
  specialize (finite_bij_lt vs H4 y 0 H3) as eq2.
  apply H5; try lia.
  constructor.
  apply IHm; try lia. easy. easy.
  apply fresh_app1.  
  specialize (finite_bij_lt vs H4 x n H2) as eq1.
  assert (m < vsize vs y) by lia.
  specialize (finite_bij_lt vs H4 y m H6) as eq2.
  apply H5; try lia.
Qed.

Lemma fresh_is_fresh :
  forall p e vs (dim:nat) avs,
    exp_fresh (size_env vs) p e -> exp_WF vs e ->
    snd p < vsize vs (fst p) ->
    vars_start_diff vs -> vars_finite_bij vs ->
    vars_sparse vs ->
      @is_fresh _ dim (find_pos vs p) (fst (fst (trans_exp vs dim e avs))).
Proof.
  intros.
  remember (find_pos vs p) as q.
  generalize dependent vs.
  generalize dependent avs.
  induction e; intros.
  subst.
  apply fresh_app1.
  inv H0. inv H1.
  apply find_pos_prop; try assumption.
  subst.
  apply fresh_app1.
  inv H0. inv H1.
  apply find_pos_prop; try assumption.
  specialize (trans_exp_cu vs avs dim p0 e) as eq1.
  destruct eq1. destruct H6. destruct H6.
  subst. rewrite H7. simpl.
  apply fresh_app2.
  inv H0. inv H1. inv H12.
  apply find_pos_prop; try assumption.
  apply find_pos_prop; try assumption.
  inv H1. inv H11. assumption.
  inv H0. inv H11. assumption.
  rewrite H6. rewrite Heqq.
  inv H1. inv H0.
  apply fresh_control. split.
  apply find_pos_prop; try assumption. 
  apply IHe; try assumption. easy.
  subst. inv H0. inv H1.
  simpl.
  apply fresh_app1.
  apply find_pos_prop; try assumption.
  subst. inv H0. inv H1.
  simpl.
  apply fresh_app1.
  apply find_pos_prop; try assumption.
  subst. inv H0. inv H1.
  simpl. unfold gen_sr_gate.
  unfold or_not_r in *.
  bdestruct (x =? fst p). subst. destruct H8. lia.
  specialize (is_fresh_sr_gates (S q0) (snd p) (S q0) (fst p) dim vs) as eq1.
  destruct p.
  simpl in *. unfold find_pos. apply eq1; try lia. easy.
  destruct p.
  specialize (is_fresh_sr_gate_start (S q0) n (S q0) v x dim vs) as eq1.
  apply eq1; try lia. iner_p. iner_p. easy. easy.
  subst. inv H0. inv H1.
  simpl. unfold gen_sr_gate.
  unfold or_not_r in *.
  bdestruct (x =? fst p). subst. destruct H8. lia.
  specialize (is_fresh_srr_gates (S q0) (snd p) (S q0) (fst p) dim vs) as eq1.
  destruct p.
  simpl in *. unfold find_pos. apply eq1; try lia. easy.
  destruct p.
  specialize (is_fresh_srr_gate_start (S q0) n (S q0) v x dim vs) as eq1.
  apply eq1; try lia. iner_p. iner_p. easy. easy.
  simpl.
  apply fresh_app2.
  inv H0. inv H1.
  apply find_pos_prop; try assumption. subst.
  apply find_pos_prop; try assumption.
  inv H1. easy.
  inv H0. easy.
  inv H0. simpl. inv H1.
  apply fresh_app1.
  assert (start vs x + vmap vs x 0 = find_pos vs (x,0)).
  unfold find_pos. easy. rewrite H0.
  unfold or_not_eq in H8.
  destruct H8.
  apply find_pos_prop; try assumption.
  destruct p. iner_p.
  unfold size_env in H1. destruct p. simpl in H2. simpl in H1.
  bdestruct (x =? v). subst.
  apply find_pos_prop; try assumption. iner_p.
  apply find_pos_prop; try assumption. iner_p.
  inv H0. simpl. inv H1.
  apply fresh_app1.
  assert (start vs x + vmap vs x 0 = find_pos vs (x,0)).
  unfold find_pos. easy. rewrite H0.
  unfold or_not_eq in H8.
  destruct H8.
  apply find_pos_prop; try assumption.
  destruct p. iner_p.
  unfold size_env in H1. destruct p. simpl in H2. simpl in H1.
  bdestruct (x =? v). subst.
  apply find_pos_prop; try assumption. iner_p.
  apply find_pos_prop; try assumption. iner_p.
  inv H0. simpl. inv H1.
  apply fresh_app1.
  assert (start vs x + vmap vs x 0 = find_pos vs (x,0)).
  unfold find_pos. easy. rewrite H0.
  unfold or_not_eq in H8.
  destruct H8.
  apply find_pos_prop; try assumption.
  destruct p. iner_p.
  unfold size_env in H1. destruct p. simpl in H2. simpl in H1.
  bdestruct (x =? v). subst.
  apply find_pos_prop; try assumption. iner_p.
  apply find_pos_prop; try assumption. iner_p.
  simpl.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p0.
  destruct (trans_exp v dim e2 p1) eqn:eq2. destruct p0. simpl.
  apply fresh_seq; try assumption.
  inv H1. inv H0.
  assert (b = (fst (fst (trans_exp vs dim e1 avs)))). rewrite eq1. easy.
  rewrite H0.
  apply IHe1; try assumption. easy.
  inv H1. inv H0.
  assert (b0 = (fst (fst (trans_exp v dim e2 p1)))). rewrite eq2. easy. subst.
  apply IHe2; try assumption.
  erewrite size_env_vs_same. apply H11. rewrite eq1. easy.
  apply (wf_vs_same e2 e1 avs dim vs v). easy. rewrite eq1. easy.
  rewrite (vsize_vs_same e1 dim vs v avs); try easy. rewrite eq1. easy.
  eapply vars_start_diff_vs_same. rewrite eq1. easy. easy.
  eapply vars_finite_bij_vs_same. rewrite eq1. easy. easy.
  eapply vars_sparse_vs_same. rewrite eq1. easy. easy.
  rewrite (efresh_trans_same e1 dim vs v avs p); try easy.
  rewrite eq1. easy.
Qed.

Lemma gen_sr_gate_uc_well_typed : forall n size x dim vs, n <= size ->
     n < vsize vs x -> exp_com_WF vs dim -> uc_well_typed (gen_sr_gate' vs dim x n size).
Proof.
  induction n; intros; simpl.
  constructor. unfold exp_com_WF in H2.
  specialize (H2 (x,0)). apply H2. iner_p.
  constructor. apply IHn; try lia. easy.
  constructor.
  specialize (H2 (x,n)). apply H2. simpl. lia.
Qed.

Lemma gen_srr_gate_uc_well_typed : forall n size x dim vs, n <= size ->
     n < vsize vs x -> exp_com_WF vs dim -> uc_well_typed (gen_srr_gate' vs dim x n size).
Proof.
  induction n; intros; simpl.
  constructor. unfold exp_com_WF in H2.
  specialize (H2 (x,0)). apply H2. iner_p.
  constructor. apply IHn; try lia. easy.
  constructor.
  specialize (H2 (x,n)). apply H2. simpl. lia.
Qed.

Lemma trans_exp_uc_well_typed : forall e dim vs avs,     
     vars_start_diff vs -> vars_finite_bij vs ->
       vars_sparse vs -> exp_fwf (size_env vs) e -> exp_WF vs e ->
            exp_com_WF vs dim ->  @uc_well_typed _ dim (fst (fst (trans_exp vs dim e avs))).
Proof.
  induction e; intros.
  1-2:constructor; apply H5; inv H4; easy.
  specialize (trans_exp_cu vs avs dim p e) as eq1.
  destruct eq1. destruct H6. destruct H6. subst. rewrite H7. inv H4. inv H11.
  constructor. apply H5. easy. apply H5. easy.
  apply find_pos_prop; try assumption. inv H3. inv H9. easy.
  rewrite H6. simpl. inv H4. inv H3.
  apply uc_well_typed_control. split. apply H5.  easy.
  split.
  apply fresh_is_fresh; try assumption.
  apply IHe; try easy.
  1-2:constructor; apply H5; inv H4; easy.
  simpl. unfold gen_sr_gate.
  apply gen_sr_gate_uc_well_typed; try easy.
  inv H4. easy.
  simpl. unfold gen_srr_gate.
  apply gen_srr_gate_uc_well_typed; try easy.
  inv H4. easy.
  simpl. inv H4.
  constructor. apply H5. easy.
  apply H5. easy.
  apply find_pos_prop; try assumption.
  inv H3. easy.
  simpl. constructor.
  assert (start vs x + vmap vs x 0 = find_pos vs (x,0)). easy.
  rewrite H6. apply H5. inv H4. easy.
  simpl. constructor.
  assert (start vs x + vmap vs x 0 = find_pos vs (x,0)). easy.
  rewrite H6. apply H5. inv H4. easy.
  simpl. constructor.
  assert (start vs x + vmap vs x 0 = find_pos vs (x,0)). easy.
  rewrite H6. apply H5. inv H4. easy.
  simpl.
  inv H3. inv H4.
  destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
  destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p.
  constructor.
  assert ((fst (fst (trans_exp vs dim e1 avs))) = b). rewrite eq1. easy.
  rewrite <- H3.
  apply IHe1; try easy.
  assert ((fst (fst (trans_exp v dim e2 p0))) = b0). rewrite eq2. easy.
  rewrite <- H3.
  apply IHe2; try easy.
  eapply vars_start_diff_vs_same. rewrite eq1. easy. easy.
  eapply vars_finite_bij_vs_same. rewrite eq1. easy. easy.
  eapply vars_sparse_vs_same. rewrite eq1. easy. easy.
  erewrite size_env_vs_same. apply H9. rewrite eq1. easy.
  eapply wf_vs_same. apply H11. rewrite eq1. easy.
  eapply exp_com_WF_vs_same. rewrite eq1. easy. easy.
Qed.

Lemma two_n_kron_n: forall {m p} n i (A : Matrix m p),
  WF_Matrix A -> (i + n) ⨂ A = (n ⨂ A) ⊗ (i ⨂ A).
Proof.
  intros.
  induction n.
  simpl.
  Msimpl. rewrite plus_0_r.
  reflexivity.
  rewrite kron_n_assoc by assumption.
  restore_dims.
  rewrite kron_assoc.
  rewrite <- IHn.
  assert ((m ^ n * m ^ i) = m ^ (i + n)).
  rewrite Nat.pow_add_r. lia.
  rewrite H1. clear H1.
  assert ((p ^ n * p ^ i) = p ^ (i + n)).
  rewrite Nat.pow_add_r. lia.
  rewrite H1. clear H1.
  rewrite <- kron_n_assoc by assumption.
  assert ((i + S n) =  S (i + n)) by lia.
  rewrite H1. easy.
  assumption.
  auto with wf_db.
  auto with wf_db.
Qed.

Lemma uc_cnot_control : forall (n i j : nat),
  i < n -> j < n -> i <> j ->
  (@uc_eval n (SQIR.CNOT i j)) = (uc_eval (control i (SQIR.X j))).
Proof.
  intros.
  rewrite control_correct.
  autorewrite with eval_db.
  bdestruct ( i <? j).
  assert ((i + (1 + (j - i - 1) + 1)) = j + 1) by lia.
  rewrite H4. 
  bdestruct (j + 1 <=? n).
  unfold proj,pad.
  bdestruct (i + 1 <=? n).
  simpl.
  autorewrite with ket_db.
  rewrite Mplus_comm.
  restore_dims.
  rewrite kron_plus_distr_l.
  rewrite kron_plus_distr_r.
  rewrite kron_assoc.
  rewrite kron_assoc.
  assert ((I 2 ⊗ I (2 ^ (n - (j + 1)))) = I (2^ S (n - (j + 1)))).
  rewrite <- kron_n_I.
  rewrite <- kron_n_assoc.
  rewrite kron_n_I. easy.
  auto with wf_db.
  rewrite H7.
  rewrite kron_assoc.
  assert ((I (2 ^ (j - i - 1)) ⊗ I (2 ^ S (n - (j + 1)))) = I (2 ^ (n - (i + 1)))).
  Check @kron_n_I.
  Check two_n_kron_n.
  rewrite <- kron_n_I.
  rewrite <- kron_n_I.
  rewrite <- two_n_kron_n.
  rewrite kron_n_I.
  assert ((S (n - (j + 1)) + (j - i - 1)) = (n - (i + 1))) by lia.
  rewrite H8. easy. 
  auto with wf_db.
  restore_dims.
  rewrite H8.
  gridify. easy.
  1-9:auto with wf_db.
  lia. lia.
  bdestruct (j <? i).
  assert (j + (1 + (i - j - 1) + 1) = i + 1) by lia.
  rewrite H5. 
  unfold proj,pad.
  bdestruct (i + 1 <=? n).
  bdestruct (j + 1 <=? n).
  simpl.
  autorewrite with ket_db.
  rewrite Mplus_comm.
  restore_dims.
  rewrite kron_plus_distr_l.
  gridify. easy. lia. lia. lia.
  constructor. easy.
  constructor. easy.
Qed.

Lemma vkron_proj_eq : forall f q n r b,
  (forall j : nat, WF_Matrix (f j)) ->
  q < n -> f q = r .* ket (Nat.b2n b) -> 
  proj q n b × (vkron n f) = vkron n f.
Proof.
  intros f q n r b ? ? ?.
  rewrite (vkron_split n q) by (try assumption; try lia). 
  replace (n - 1 - q)%nat with (n - (q + 1))%nat by lia.
  unfold proj, pad.
  gridify. 
  do 2 (apply f_equal2; try reflexivity). 
  rewrite H2. destruct b; solve_matrix.
Qed.

Lemma vkron_proj_neq : forall f q n r b b',
  (forall j : nat, WF_Matrix (f j)) ->
  q < n -> f q = r .* ket (Nat.b2n b) -> b <> b' ->
  proj q n b' × (vkron n f) = Zero.
Proof.
  intros f q n r b b' ? ? H ?.
  rewrite (vkron_split n q) by (try assumption; try lia). 
  replace (n - 1 - q)%nat with (n - (q + 1))%nat by lia.
  unfold proj, pad.
  gridify. rewrite H.
  destruct b. destruct b'. contradiction. lma.
  destruct b'.  lma. contradiction.
Qed.


Local Opaque SQIR.ID SQIR.CNOT SQIR.X SQIR.Rz. 

Lemma trans_exp_cu_eval : forall vs avs dim p e, 
          vars_start_diff vs -> vars_finite_bij vs -> vars_sparse vs ->
                 exp_fwf (size_env vs) (CU p e) ->
                 exp_WF vs (CU p e) -> exp_com_WF vs dim ->
                 (uc_eval (fst (fst (trans_exp vs dim (CU p e) avs)))) = 
                    (uc_eval (control (find_pos vs p) (fst (fst (trans_exp vs dim e avs))))).
Proof.
  intros.
  specialize (trans_exp_cu vs avs dim p e) as eq1.
  destruct eq1.
  destruct H6. destruct H6. subst. rewrite H7.
  simpl.
  rewrite uc_cnot_control. easy.
  inv H4. apply H5. easy.
  inv H4. inv H11. apply H5. easy.
  inv H3. inv H9. inv H4. inv H12. 
  apply find_pos_prop; try assumption.
  rewrite H6. easy.
Qed.

Lemma turn_angle_add_same : forall n r q, q < n ->
       (2 * PI * turn_angle r n + rz_ang q)%R = (2 * PI *  turn_angle (rotate r q) n)%R.
Proof.

Admitted.

Lemma turn_angle_add_r_same : forall n r q, q < n -> 
          (2 * PI * turn_angle r n + rrz_ang q)%R = (2 * PI *  turn_angle (r_rotate r q) n)%R.
Proof.

Admitted.

Lemma Z_0_bit : σz × ∣0⟩ = ∣0⟩.
Proof.
  solve_matrix.
Qed.

Lemma Z_1_bit : σz × ∣1⟩ = (-1)%R .* ∣1⟩.
Proof.
  solve_matrix.
Qed.

Lemma rz_ang_trans_sem : forall vs dim avs tenv q rmax f p size, 
    exp_com_WF vs dim -> snd p < vsize vs (fst p) -> q < rmax ->
    right_mode_env (size_env vs) tenv f -> Env.MapsTo (fst p) (Phi size) tenv ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
           (phase_shift (rz_ang q) × trans_state avs rmax f (find_pos vs p))
                = compile_val (times_rotate (f p) q) rmax.
Proof.
      intros.
      unfold trans_state.
      rewrite H5 by assumption.
      apply (H3 (Phi size)) in H1; try easy. inv H1. 
      unfold times_rotate.
      unfold compile_val.
      distribute_scale.
      rewrite Mmult_plus_distr_l.
      distribute_scale.
      assert (∣0⟩ = ket (Nat.b2n false)).
      autorewrite with ket_db. easy. rewrite H1.
      rewrite phase_shift_on_basis_state.
      simpl. rewrite Rmult_0_l. simpl. rewrite Cexp_0. Msimpl.
      assert (∣1⟩ = ket (Nat.b2n true)).
      autorewrite with ket_db. easy. rewrite H6.
      rewrite phase_shift_on_basis_state. simpl.
      distribute_scale.
      rewrite <- Cexp_add. rewrite Rmult_1_l.
      rewrite turn_angle_add_same. easy. easy.
Qed.

Lemma rrz_ang_trans_sem : forall vs dim avs tenv q rmax f p size, 
    exp_com_WF vs dim -> snd p < vsize vs (fst p) -> q < rmax ->
    right_mode_env (size_env vs) tenv f -> Env.MapsTo (fst p) (Phi size) tenv ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
           (phase_shift (rrz_ang q) × trans_state avs rmax f (find_pos vs p))
                = compile_val (times_r_rotate (f p) q) rmax.
Proof.
      intros.
      unfold trans_state.
      rewrite H5 by assumption.
      apply (H3 (Phi size)) in H1; try easy. inv H1. 
      unfold times_rotate.
      unfold compile_val.
      distribute_scale.
      rewrite Mmult_plus_distr_l.
      distribute_scale.
      assert (∣0⟩ = ket (Nat.b2n false)).
      autorewrite with ket_db. easy. rewrite H1.
      rewrite phase_shift_on_basis_state.
      simpl. rewrite Rmult_0_l. simpl. rewrite Cexp_0. Msimpl.
      assert (∣1⟩ = ket (Nat.b2n true)).
      autorewrite with ket_db. easy. rewrite H6.
      rewrite phase_shift_on_basis_state. simpl.
      distribute_scale.
      rewrite <- Cexp_add. rewrite Rmult_1_l.
      rewrite turn_angle_add_r_same. easy. easy.
Qed.

Lemma gen_sr_gate_eval : forall n size asize tenv f vs avs dim rmax x, n <= size <= asize ->
    exp_com_WF vs dim -> n < vsize vs x -> size < rmax -> Env.MapsTo x (Phi asize) tenv ->
    right_mode_env (size_env vs) tenv f ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
    (forall i, i < dim -> find_pos vs (avs i) = i) ->
    uc_eval (gen_sr_gate' vs dim x n size) × vkron dim (trans_state avs rmax f)
    = vkron dim (trans_state avs rmax (sr_rotate' f x n size)).
Proof.
  induction n; intros; simpl.
  rewrite denote_ID.
  assert (find_pos vs (x,0) < dim).
  apply H1. easy. unfold find_pos in H6.
  unfold pad.
  bdestruct (start vs x + vmap vs x 0 + 1 <=? dim).
  repeat rewrite id_kron.
  assert (2 ^ (start vs x + vmap vs x 0) * 2 = 2 ^ (start vs x + vmap vs x 0) * (2^1)).
  rewrite Nat.pow_1_r. easy. rewrite H10.
  repeat rewrite <- Nat.pow_add_r. Msimpl. easy.
  unfold find_pos in H8. lia.
  rewrite Mmult_assoc.
  rewrite IHn with (asize := asize) (tenv := tenv); (try lia; try easy).
  rewrite vkron_Rz. 
  assert (vkron dim (trans_state avs rmax ((sr_rotate' f x n size) [(x, n)
                      |-> times_rotate (f (x, n)) (size - n)])) = 
          vkron dim (update (trans_state avs rmax (sr_rotate' f x n size))
                        (find_pos vs (x, n)) (compile_val (times_rotate (f (x, n)) (size - n)) rmax))).
  erewrite vkron_eq. reflexivity. intros.
  apply (trans_state_update dim). simpl. lia. easy. assumption. assumption.
  rewrite H8.
  rewrite vkron_split_up.
  Check rz_ang_trans_sem.
  replace ((start vs x + vmap vs x n)) with (find_pos vs (x,n)) by easy.
  rewrite (rz_ang_trans_sem vs dim avs tenv (size - n) rmax 
      (sr_rotate' f x n size) (x,n) asize); (try lia; try easy).
  rewrite sr_rotate'_ge; try easy.
  simpl. lia.
  unfold right_mode_env in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  bdestruct (n0 <? n). 
  rewrite sr_rotate'_lt_1; try lia.
  simpl in H10.
  apply mapsto_always_same with (v1:=(Phi asize)) in H10; try easy.
  specialize (H5 (Phi asize) (v,n0) H9). simpl in H5. apply H5 in H4.
  inv H4. unfold times_rotate. constructor.
  rewrite sr_rotate'_ge ; try lia. apply H5; try easy. simpl. lia.
  rewrite sr_rotate'_irrelevant; try easy.
  apply H5; try easy. simpl. lia.
  auto with wf_db. auto with wf_db.
  apply H1. simpl. lia.
  replace ((start vs x + vmap vs x n)) with (find_pos vs (x,n)) by easy.
  apply H1. simpl. lia.
  auto with wf_db. 
Qed.

Lemma gen_srr_gate_eval : forall n size asize tenv f vs avs dim rmax x, n <= size <= asize ->
    exp_com_WF vs dim -> n < vsize vs x -> size < rmax -> Env.MapsTo x (Phi asize) tenv ->
    right_mode_env (size_env vs) tenv f ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
    (forall i, i < dim -> find_pos vs (avs i) = i) ->
    uc_eval (gen_srr_gate' vs dim x n size) × vkron dim (trans_state avs rmax f)
    = vkron dim (trans_state avs rmax (srr_rotate' f x n size)).
Proof.
  induction n; intros; simpl.
  rewrite denote_ID.
  assert (find_pos vs (x,0) < dim).
  apply H1. easy. unfold find_pos in H6.
  unfold pad.
  bdestruct (start vs x + vmap vs x 0 + 1 <=? dim).
  repeat rewrite id_kron.
  assert (2 ^ (start vs x + vmap vs x 0) * 2 = 2 ^ (start vs x + vmap vs x 0) * (2^1)).
  rewrite Nat.pow_1_r. easy. rewrite H10.
  repeat rewrite <- Nat.pow_add_r. Msimpl. easy.
  unfold find_pos in H8. lia.
  rewrite Mmult_assoc.
  rewrite IHn with (asize := asize) (tenv := tenv); (try lia; try easy).
  rewrite vkron_Rz. 
  assert (vkron dim (trans_state avs rmax ((srr_rotate' f x n size) [(x, n)
                      |-> times_r_rotate (f (x, n)) (size - n)])) = 
          vkron dim (update (trans_state avs rmax (srr_rotate' f x n size))
                        (find_pos vs (x, n)) (compile_val (times_r_rotate (f (x, n)) (size - n)) rmax))).
  erewrite vkron_eq. reflexivity. intros.
  apply (trans_state_update dim). simpl. lia. easy. assumption. assumption.
  rewrite H8.
  rewrite vkron_split_up.
  replace ((start vs x + vmap vs x n)) with (find_pos vs (x,n)) by easy.
  rewrite (rrz_ang_trans_sem vs dim avs tenv (size - n) rmax 
      (srr_rotate' f x n size) (x,n) asize); (try lia; try easy).
  rewrite srr_rotate'_ge; try easy.
  simpl. lia.
  unfold right_mode_env in *. intros.
  destruct p.
  bdestruct (x =? v). subst.
  bdestruct (n0 <? n). 
  rewrite srr_rotate'_lt_1; try lia.
  simpl in H10.
  apply mapsto_always_same with (v1:=(Phi asize)) in H10; try easy.
  specialize (H5 (Phi asize) (v,n0) H9). simpl in H5. apply H5 in H4.
  inv H4. unfold times_r_rotate. constructor.
  rewrite srr_rotate'_ge ; try lia. apply H5; try easy. simpl. lia.
  rewrite srr_rotate'_irrelevant; try easy.
  apply H5; try easy. simpl. lia.
  auto with wf_db. auto with wf_db.
  apply H1. simpl. lia.
  replace ((start vs x + vmap vs x n)) with (find_pos vs (x,n)) by easy.
  apply H1. simpl. lia.
  auto with wf_db. 
Qed.

Lemma trans_exp_sem :
  forall dim e f tenv rmax vs (avs : nat -> posi) l l',
    vars_start_diff vs ->
    vars_finite_bij vs ->
    vars_sparse vs ->
    vars_anti_same vs ->
    exp_fwf (size_env vs) e ->
    exp_WF vs e ->
    exp_com_WF vs dim ->
    exp_com_gt vs avs dim ->
    well_typed_exp tenv e ->
    right_mode_env (size_env vs) tenv f ->
    avs_prop vs avs dim -> 
    exp_rmax rmax e ->
    exp_neu l e l' ->
    dim > 0 ->
    (uc_eval (fst (fst (trans_exp vs dim e avs)))) × (vkron dim (trans_state avs rmax f)) 
                =  vkron dim (trans_state (snd (trans_exp vs dim e avs)) rmax (exp_sem (size_env vs) e f)).
Proof.
  intros dim e. induction e; intros.
  - simpl. rewrite denote_ID_1. Msimpl. easy.
    apply H6. inv H5. easy.
  - simpl.
    rewrite vkron_X. 
    assert (vkron dim (trans_state avs rmax (f [p |-> exchange (f p)])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p) (compile_val (exchange (f p)) rmax))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). inv H5. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy. easy.
    rewrite H14.  rewrite vkron_split_up.
    assert ((σx × trans_state avs rmax f (find_pos vs p))
                 = compile_val (exchange (f p)) rmax).
    { unfold trans_state.
      inv H5. rewrite vs_avs_bij_l with (dim := dim); try easy.
      inv H8. unfold right_mode_env in H9.
      apply (H9 Nor) in H17. inv H17.
      unfold exchange. 
      unfold compile_val.
      distribute_scale.
      destruct b. simpl.
      autorewrite with ket_db. easy.
      simpl.
      autorewrite with ket_db. easy. easy.
      apply (H9 Had) in H17.
      inv H17. 
      unfold exchange.
      unfold compile_val.
      distribute_scale.
      autorewrite with ket_db.
      rewrite Mplus_comm. easy. easy.
      }
    rewrite H15. easy.
    intros.
    auto with wf_db.
    auto with wf_db.
    apply H6. inv H5. assumption.
    apply H6. inv H5. assumption.
    auto with wf_db.
  - rewrite trans_exp_cu_eval by assumption.
    assert ((snd (trans_exp vs dim (CU p e) avs)) = avs).
    specialize (trans_exp_cu vs avs dim p e) as eq1. destruct eq1.
    destruct H14. destruct H14. rewrite H15. easy. rewrite H14. easy.
    rewrite H14. clear H14.
    rewrite control_correct.
    simpl. 
    assert (exists r', (trans_state avs rmax f) (find_pos vs p) = r' .* (ket (Nat.b2n (get_cua (f p))))).
    inv H4. inv H5.
    unfold trans_state. 
    rewrite vs_avs_bij_l with (dim := dim); try easy.
    inv H8. apply (H9 Nor) in H18; try easy. inv H18.
    unfold compile_val,get_cua.
    exists (Cexp (2 * PI * turn_angle r rmax)). 
    easy.
    destruct H14.
    assert ((snd (trans_exp vs dim e avs)) = avs) as eq3.
    inv H12. rewrite neu_trans_state with (l := l') ; try easy. 
    rewrite Mmult_plus_distr_r.
    rewrite Mmult_assoc.
    specialize (IHe f tenv rmax vs avs).
    inv H4. inv H5. inv H8. apply (H9 Nor) in H19 as eq1.
    rewrite IHe with (l := l) (l' := l') ; try easy.
    destruct (get_cua (f p)) eqn:eq2.
    erewrite vkron_proj_neq.
    rewrite vkron_proj_eq with (r := x). rewrite eq3.
    Msimpl. easy. auto with wf_db. apply H6. easy. rewrite eq3.
    unfold trans_state in *. rewrite efresh_exp_sem_irrelevant. easy.
    rewrite vs_avs_bij_l with (dim := dim); try easy.
    auto with wf_db.
    apply H6; easy. rewrite H14. reflexivity. easy.
    rewrite vkron_proj_eq with (r := x).
    rewrite vkron_proj_neq with (r := x) (b := false). Msimpl. easy.
    auto with wf_db.
    apply H6. easy. rewrite eq3.
    unfold trans_state in *. rewrite efresh_exp_sem_irrelevant. easy.
    rewrite vs_avs_bij_l with (dim := dim); try easy. easy.
    auto with wf_db.
    apply H6; easy. rewrite H14. reflexivity. inv H11. easy.
    inv H12. easy. easy.
    apply fresh_is_fresh; try easy.
    inv H4. easy. inv H5. easy. inv H5. easy.
    apply trans_exp_uc_well_typed; try easy. inv H4. easy. inv H5. easy.
  - simpl.
    rewrite vkron_Rz. 
    assert (vkron dim (trans_state avs rmax (f [p |-> times_rotate (f p) q])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p) (compile_val (times_rotate (f p) q) rmax))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). inv H5. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy. easy.
    rewrite H14.  rewrite vkron_split_up.
    assert ((phase_shift (rz_ang q) × trans_state avs rmax f (find_pos vs p))
                 = compile_val (times_rotate (f p) q) rmax).
    { unfold trans_state.
      inv H5.
      rewrite vs_avs_bij_l with (dim := dim); try easy.
      inv H8. apply (H9 Nor) in H17; try easy. inv H17. 
      unfold times_rotate. destruct b.
      unfold compile_val.
      distribute_scale.
      rewrite phase_shift_on_basis_state.
      distribute_scale.
      rewrite <- Cexp_add. simpl. rewrite Rmult_1_l.
      inv H11. rewrite turn_angle_add_same. easy. easy.
      unfold compile_val.
      distribute_scale.
      rewrite phase_shift_on_basis_state.
      distribute_scale. simpl. 
      rewrite <- Cexp_add. simpl.
      autorewrite with R_db. easy.
      apply (H9 Had) in H17. inv H17. 
      unfold compile_val,times_rotate. unfold rz_ang,z_phase.
      assert ((2 * PI / 2 ^ 1)%R = PI) by lra. rewrite H15.
      rewrite phase_pi. destruct b1. destruct b2.
      distribute_scale. gridify.
      rewrite Z_0_bit. rewrite Z_1_bit. easy.
      simpl. distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit.
      rewrite Mscale_assoc.
      assert (((-1)%R * (-1)%R)%C = C1) by lca.
      rewrite H17. Msimpl. easy.
      destruct b2.
      distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit. easy.
      simpl.
      distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit. 
      rewrite Mscale_assoc.
      assert (((-1)%R * (-1)%R)%C = C1) by lca.
      rewrite H17. Msimpl. easy. easy.
      }
    rewrite H15. easy.
    intros.
    auto with wf_db.
    auto with wf_db.
    apply H6. inv H5. assumption.
    apply H6. inv H5. assumption.
    auto with wf_db.
  - simpl.
    rewrite vkron_Rz. 
    assert (vkron dim (trans_state avs rmax (f [p |-> times_r_rotate (f p) q])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p) (compile_val (times_r_rotate (f p) q) rmax))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). inv H5. easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy. easy.
    rewrite H14.  rewrite vkron_split_up.
    assert ((phase_shift (rrz_ang q) × trans_state avs rmax f (find_pos vs p))
                 = compile_val (times_r_rotate (f p) q) rmax).
    { unfold trans_state.
      inv H5.
      rewrite vs_avs_bij_l with (dim := dim); try easy.
      inv H8. apply (H9 Nor) in H17.
      inv H17.
      unfold times_r_rotate. destruct b. 
      unfold compile_val.
      distribute_scale.
      rewrite phase_shift_on_basis_state.
      distribute_scale.
      rewrite <- Cexp_add. simpl. rewrite Rmult_1_l.
      inv H11. rewrite turn_angle_add_r_same. easy. easy.
      unfold compile_val.
      distribute_scale.
      rewrite phase_shift_on_basis_state.
      distribute_scale. simpl. 
      rewrite <- Cexp_add. simpl.
      autorewrite with R_db. easy. easy.
      apply (H9 Had) in H17. inv H17.
      unfold compile_val,times_r_rotate. unfold rrz_ang,z_phase.
      assert ((2 * PI - 2 * PI / 2 ^ 1)%R = PI) by lra. rewrite H15.
      rewrite phase_pi. destruct b1. destruct b2.
      distribute_scale. gridify.
      rewrite Z_0_bit. rewrite Z_1_bit. easy.
      simpl. distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit.
      rewrite Mscale_assoc.
      assert (((-1)%R * (-1)%R)%C = C1) by lca.
      rewrite H17. Msimpl. easy.
      destruct b2.
      distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit. easy.
      simpl.
      distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit. 
      rewrite Mscale_assoc.
      assert (((-1)%R * (-1)%R)%C = C1) by lca.
      rewrite H17. Msimpl. easy. easy.
      }
    rewrite H15. easy.
    intros.
    auto with wf_db.
    auto with wf_db.
    apply H6. inv H5. assumption.
    apply H6. inv H5. assumption.
    auto with wf_db.
  - Local Opaque gen_sr_gate. simpl.
    Local Transparent gen_sr_gate. unfold gen_sr_gate,sr_rotate.
    inv H8. inv H5. inv H4. inv H11.
    rewrite gen_sr_gate_eval with (asize := n) (tenv := tenv); try easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy.
  - Local Opaque gen_srr_gate. simpl.
    Local Transparent gen_srr_gate. unfold gen_srr_gate,srr_rotate.
    inv H8. inv H5. inv H4. inv H11.
    rewrite gen_srr_gate_eval with (asize := n) (tenv := tenv); try easy.
    apply vs_avs_bij_l with (dim := dim); try easy.
    apply vs_avs_bij_r with (dim := dim); try easy.
  - 
(*
simpl. inv H4. inv H5.
    rewrite uc_cnot_control; try easy.
    rewrite control_correct. inv H6.
    apply (H7 Had) in H16 as eq1.
    apply (H7 Had) in H17 as eq2. inv eq1. inv eq2.
    unfold hexchange.
    rewrite Mmult_plus_distr_r.
    rewrite Mmult_assoc.
    assert ((uc_eval (SQIR.X (find_pos vs p2))
      × vkron dim (trans_state avs rmax f))
      = (vkron dim (trans_state avs rmax (f[p2 |-> exchange (f p2)])))).
    rewrite vkron_X. 
    assert (vkron dim (trans_state avs rmax (f [p2 |-> exchange (f p2)])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p2) (compile_val (exchange (f p2)) rmax))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). easy. assumption. assumption. lia.
    rewrite H19.  rewrite vkron_split_up.
    assert ((σx × trans_state avs rmax f (find_pos vs p2))
                 = compile_val (exchange (f p2)) rmax).
    { unfold trans_state.
      rewrite H8 by assumption.
      unfold exchange.
      rewrite <- H6. 
      unfold compile_val.
      distribute_scale.
      autorewrite with ket_db. rewrite Mplus_comm. easy.
      }
    rewrite H20. easy.
    auto with wf_db.
    auto with wf_db.
    apply H5. assumption.
    apply H5. assumption.
    auto with wf_db.
    rewrite H19. clear H19.
    destruct (eqb b0 b3) eqn:eq1.
    apply Bool.eqb_prop in eq1.
    rewrite <- H6. unfold exchange. subst.
    rewrite H6. rewrite H3.
    rewrite eupdate_same by easy.
    rewrite eupdate_same by easy.
    rewrite <- Mmult_plus_distr_r.
    rewrite Mplus_comm.
    rewrite proj_sum.
    Msimpl. easy.
    apply H5. easy.
    apply eqb_false_iff in eq1.
    rewrite <- H6. unfold exchange.
    rewrite (vkron_split dim (find_pos vs p1)).
    assert (trans_state avs rmax f (find_pos vs p1) = Cexp ((turn_angle r rmax)) .*
                              ((RtoC ((z_phase b1))) .* ∣0⟩ .+ (RtoC ((z_phase b2))) .* ∣1⟩)).
    unfold trans_state,compile_val. rewrite H8; try easy. rewrite <- H3. easy.
    rewrite H19.
    distribute_scale.
    distribute_plus.
    distribute_scale.
    assert (@Mmult (2 ^ dim) (2 ^ dim) 1 
            (proj (find_pos vs p1) dim false)
            (vkron (find_pos vs p1) (trans_state avs rmax f) ⊗ ∣1⟩
              ⊗ vkron (dim - 1 - find_pos vs p1)
                  (shift (trans_state avs rmax f) (find_pos vs p1 + 1))) = Zero).
    replace ((dim - 1 - find_pos vs p1)) with (dim - (1 + find_pos vs p1)) by lia.
    unfold proj,pad.
    assert (∣1⟩ = ket (Nat.b2n true)). autorewrite with ket_db. simpl. easy. rewrite H20.
    gridify.
    assert ((find_pos vs p1 + 1 + d - S (find_pos vs p1)) = d) by lia. rewrite H16.
    autorewrite with ket_db. easy.
    rewrite H20. clear H20. Msimpl.
    rewrite (vkron_split dim (find_pos vs p1) (trans_state avs rmax (f [p2 |-> hval b3 b0 r0]))).
    assert (trans_state avs rmax (f [p2 |-> hval b3 b0 r0]) (find_pos vs p1) = Cexp ((turn_angle r rmax)) .*
                              ((RtoC ((z_phase b1))) .* ∣0⟩ .+ (RtoC ((z_phase b2))) .* ∣1⟩)).
    unfold trans_state,compile_val. rewrite H8; try easy.
    rewrite eupdate_index_neq by iner_p. rewrite <- H3. easy.
    rewrite H20. clear H20.
    distribute_scale.
    distribute_plus.
    distribute_scale.
    assert (@Mmult (2 ^ dim) (2 ^ dim) 1 
            (proj (find_pos vs p1) dim true)
            (vkron (find_pos vs p1)
                (trans_state avs rmax (f [p2 |-> hval b3 b0 r0])) ⊗ ∣0⟩
              ⊗ vkron (dim - 1 - find_pos vs p1)
                  (shift
                     (trans_state avs rmax (f [p2 |-> hval b3 b0 r0]))
                     (find_pos vs p1 + 1))) = Zero).
    replace ((dim - 1 - find_pos vs p1)) with (dim - (1 + find_pos vs p1)) by lia.
    unfold proj,pad.
    assert (∣0⟩ = ket (Nat.b2n false)). autorewrite with ket_db. simpl. easy. rewrite H20.
    gridify.
    assert ((find_pos vs p1 + 1 + d - S (find_pos vs p1)) = d) by lia. rewrite H16.
    autorewrite with ket_db. easy.
    rewrite H20. clear H20. Msimpl.

    admit.
    auto with wf_db.
    apply H5. easy.
    auto with wf_db.
    apply H5. easy.
    1-2:easy.
    assert (SQIR.X (find_pos vs p2) = trans_exp vs dim (X p2)) by easy.
    rewrite H3.
    apply fresh_is_fresh; try easy. constructor. easy. constructor. easy.
    assert (SQIR.X (find_pos vs p2) = trans_exp vs dim (X p2)) by easy. rewrite H3.
    apply trans_exp_uc_well_typed; try easy. constructor. constructor. easy.
    apply H5. easy. apply H5. easy.
    apply find_pos_prop; try easy.
*) admit.
  - simpl. rewrite denote_ID_1. Msimpl. unfold size_env. 
    rewrite <- lshift_avs_lshift_same; try easy.
    inv H5. easy. unfold exp_com_WF,find_pos in H6.
    specialize (H6 (x,0)). simpl in H6. apply H6. inv H5. easy.
  - simpl. rewrite denote_ID_1. Msimpl. unfold size_env. rewrite <- rshift_avs_rshift_same; try easy.
    inv H5. easy. unfold exp_com_WF,find_pos in H6.
    specialize (H6 (x,0)). simpl in H6. apply H6. inv H5. easy.
  - simpl. rewrite denote_ID_1. Msimpl. unfold size_env. rewrite <- rev_avs_rev_same; try easy.
    inv H5. easy. unfold exp_com_WF,find_pos in H6.
    specialize (H6 (x,0)). simpl in H6. apply H6. inv H5. easy.
  - simpl.
    destruct (trans_exp vs dim e1 avs) eqn:eq1. destruct p.
    destruct (trans_exp v dim e2 p0) eqn:eq2. destruct p. simpl. inv H4. inv H5. inv H8. inv H11.
    rewrite Mmult_assoc.
    assert (b = fst (fst (trans_exp vs dim e1 avs))). rewrite eq1. easy.
    rewrite H4. inv H12.
    rewrite (IHe1 f tenv) with (l := l) (l' := l'0); try easy.
    assert (b0 = fst (fst (trans_exp v dim e2 p0))). rewrite eq2. easy.
    rewrite H4. rewrite eq1. simpl.
    rewrite (IHe2 (exp_sem (size_env vs) e1 f) tenv) with (l := l'0) (l' := l'); try easy.
    rewrite eq2. simpl.
    rewrite (size_env_vs_same vs v e1 dim avs). easy.
    rewrite eq1. easy.
    apply (vars_start_diff_vs_same vs v e1 dim avs).
    rewrite eq1. easy. easy.
    apply (vars_finite_bij_vs_same e1 dim vs v avs).
    rewrite eq1. easy. easy.
    apply (vars_sparse_vs_same e1 dim vs v avs).
    rewrite eq1. easy. easy.
    apply (vars_anti_vs_same e1 dim vs v avs).
    rewrite eq1. easy. easy.
    erewrite size_env_vs_same with (vs := vs); try easy.
    rewrite eq1. easy.
    apply (wf_vs_same e2 e1 avs dim vs v). easy.
    rewrite eq1. easy.
    apply (exp_com_WF_vs_same e1 dim avs vs v).
    rewrite eq1. easy. easy.
    apply (exp_com_gt_vs_same e1 dim vs v avs p0).
    rewrite eq1. easy. rewrite eq1. easy. easy.
    rewrite (size_env_vs_same vs v e1 dim avs); try easy.
    apply well_typed_right_mode_exp; try easy.
    rewrite eq1. easy.
    apply (avs_prop_vs_same e1 dim vs v avs p0).
    rewrite eq1. easy. rewrite eq1. easy. easy.
    easy. easy.
Admitted.

(* generalized Controlled rotation cascade on n qubits. *)

(* SQIR.Rz (rz_ang q) (find_pos f p) *)

Fixpoint controlled_rotations_gen (f : vars) (dim:nat) (x:var) (n : nat) (i:nat) : base_ucom dim :=
  match n with
  | 0 | 1 => SQIR.ID (find_pos f (x,i))
  | S m  => SQIR.useq (controlled_rotations_gen f dim x m i)
                 (control (find_pos f (x,m+i)) (SQIR.Rz (rz_ang n) (find_pos f (x,i))))
  end.

(* generalized Quantum Fourier transform on n qubits. 
   We use the definition below (with cast and map_qubits) for proof convenience.
   For a more standard functional definition of QFT see Quipper:
   https://www.mathstat.dal.ca/~selinger/quipper/doc/src/Quipper/Libraries/QFT.html *)

Fixpoint QFT_gen (f : vars) (dim:nat) (x:var) (n : nat) (size:nat) : base_ucom dim :=
  match n with
  | 0    => SQIR.ID (find_pos f (x,0))
  | S m => SQIR.useq  (QFT_gen f dim x m size)
             (SQIR.useq (SQIR.H (find_pos f (x,m))) ((controlled_rotations_gen f dim x (size-m) m)))
  end.

Definition trans_qft (f:vars) (dim:nat) (x:var) : base_ucom dim :=
          QFT_gen f dim x (vsize f x) (vsize f x).

(*
Fixpoint controlled_rotations_gen_r (f : vars) (dim:nat) (x:var) (n : nat) (i:nat) : base_ucom dim :=
  match n with
  | 0 | 1 => SQIR.ID (find_pos f (x,i))
  | S m  => SQIR.useq (control (find_pos f (x,m+i)) (SQIR.Rz (rrz_ang n) (find_pos f (x,i))))
                  (controlled_rotations_gen_r f dim x m i)
  end.

Fixpoint QFT_gen_r (f : vars) (dim:nat) (x:var) (n : nat) (size:nat) : base_ucom dim :=
  match n with
  | 0    => SQIR.ID (find_pos f (x,0))
  | S m => SQIR.useq (controlled_rotations_gen_r f dim x (size-m) m)
            (SQIR.useq (SQIR.H (find_pos f (x,m))) (QFT_gen_r f dim x m size))
  end.
*)

Definition trans_rqft (f:vars) (dim:nat) (x:var) : base_ucom dim :=
          invert (QFT_gen f dim x (vsize f x) (vsize f x)).

Fixpoint nH (f : vars) (dim:nat) (x:var) (n:nat) : base_ucom dim :=
     match n with 0 => SQIR.ID (find_pos f (x,0))
               | S m => SQIR.useq (SQIR.H (find_pos f (x,m))) (nH f dim x m)
     end.

Definition trans_h (f : vars) (dim:nat) (x:var) : base_ucom dim := nH f dim x (vsize f x).
        

(*
Inductive pexp := SExp (s:sexp) | QFT (x:var) | RQFT (x:var)
               | H (x:var) | PSeq (p1:pexp) (p2:pexp).
(f : vars) (dim:nat) (exp:sexp) (avs: nat -> posi) :
*)

Fixpoint trans_pexp (vs:vars) (dim:nat) (exp:pexp) (avs: nat -> posi) :=
     match exp with Exp s => (trans_exp vs dim s avs)
                 | QFT x => (trans_qft vs dim x, vs, avs)
                 | RQFT x => (trans_rqft vs dim x, vs, avs)
                 | H x => (trans_h vs dim x, vs, avs)
                 | PCU p e1 => match trans_pexp vs dim e1 avs with (e1', vs',avs')
                              => (control (find_pos vs p) e1', vs, avs) end
                 | PSeq e1 e2 =>  
                         match trans_pexp vs dim e1 avs with (e1',vs',avs') => 
                             match trans_pexp vs' dim e2 avs' with (e2',vs'',avs'') => 
                                        (SQIR.useq e1' e2', vs'', avs'')
                             end
                            end
     end.



Inductive pexp_WF : vars -> nat -> pexp -> Prop :=
      | qft_wf : forall vs rs x, 0 < vsize vs x -> pexp_WF vs rs (QFT x)
      | rqft_wf : forall vs rs x, 0 < vsize vs x -> pexp_WF vs rs (RQFT x)
      | h_wf : forall vs rs x, 0 < vsize vs x -> pexp_WF vs rs (H x)
      | sexp_wf : forall vs rs e, exp_WF vs e -> exp_rmax rs e -> pexp_WF vs rs (Exp e)
      | fseq_wf : forall vs rs e1 e2, pexp_WF vs rs e1 -> pexp_WF vs rs e2 -> pexp_WF vs rs (PSeq e1 e2).

Lemma trans_pexp_sem :
  forall dim (e:pexp) f env env' rmax vs (avs : nat -> posi) l l',
    vars_start_diff vs ->
    vars_finite_bij vs ->
    vars_sparse vs ->
    vars_anti_same vs ->
    pexp_WF vs rmax e ->
    exp_com_WF vs dim ->
    exp_com_gt vs avs dim ->
    well_typed_pexp (size_env vs) l env e l' env' ->
    right_mode_env (size_env vs) env f ->
    avs_prop vs avs dim ->
    dim > 0 ->
    (uc_eval (fst (fst (trans_pexp vs dim e avs)))) × (vkron dim (trans_state avs rmax f)) 
         = vkron dim (trans_state (snd (trans_pexp vs dim e avs)) rmax (prog_sem (size_env vs) e f)).
Proof.
  intros dim e. induction e; intros; simpl.
Admitted.

(* some useful gates. *)
Definition CNOT (x y : posi) := CU x (X y).
Definition SWAP (x y : posi) := if (x ==? y) then (SKIP x) else (CNOT x y; CNOT y x; CNOT x y).
Definition CCX (x y z : posi) := CU x (CNOT y z).

Lemma cnot_fwf : forall x y aenv, x<> y -> exp_fwf aenv (CNOT x y).
Proof.
  intros.
  unfold CNOT. constructor.
  constructor. easy.
  constructor.
Qed.

Lemma swap_fwf : forall x y aenv, exp_fwf aenv (SWAP x y).
Proof.
  intros.
  unfold SWAP.
  bdestruct (x ==? y).
  constructor.
  constructor.
  constructor. apply cnot_fwf. easy.
  apply cnot_fwf. nor_sym.
  constructor. constructor. easy.
  constructor.
Qed.

Lemma ccx_fwf : forall x y z aenv, x <> y -> y <> z -> z <> x -> exp_fwf aenv (CCX x y z).
Proof.
  intros.
  unfold CCX.
  constructor. constructor. easy.
  constructor. nor_sym.
  constructor. constructor.
  easy.
  constructor.
Qed.


(* Proofs of semantics. *)
Lemma cnot_sem : forall f x y aenv, nor_mode f x -> nor_mode f y -> 
              exp_sem aenv (CNOT x y) f = (f[y |-> put_cu (f y) (get_cua (f x) ⊕ get_cua (f y))]).
Proof.
 intros.
 unfold CNOT.
 assert (eq1 := H0).
 apply nor_mode_nval in H0.
 destruct H0. destruct H0.
 simpl.
 destruct (get_cua (f x)).
 bt_simpl.
 unfold exchange.
 destruct (f y) eqn:eq2.
 simpl. easy.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
 destruct (f y) eqn:eq2.
 simpl. destruct b.
 rewrite <- eq2. rewrite eupdate_same. easy.
 easy.
 rewrite <- eq2. rewrite eupdate_same. easy. easy.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
 simpl.
 assert (get_cua (f x) = false). unfold get_cua. rewrite H0. easy.
 rewrite H2.
 destruct (f y) eqn:eq2.
 simpl. destruct b.
 rewrite <- eq2. rewrite eupdate_same. easy. easy.
 rewrite <- eq2. rewrite eupdate_same. easy. easy.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
 unfold nor_mode in H1.
 rewrite eq2 in H1. inv H1.
Qed.

Lemma cnot_nor : forall f x y v aenv, nor_mode f x -> nor_mode f y -> 
          put_cu (f y) (get_cua (f x) ⊕ get_cua (f y)) = v
           -> exp_sem aenv (CNOT x y) f = (f[y |-> v]).
Proof.
  intros. subst. apply cnot_sem; assumption.
Qed.

Lemma cnot_nor_1 : forall f f' x y v aenv, nor_mode f x -> nor_mode f y -> 
          put_cu (f y) (get_cua (f x) ⊕ get_cua (f y)) = v
           -> f[y|-> v] = f'
           -> exp_sem aenv (CNOT x y) f = f'.
Proof.
  intros. subst. apply cnot_sem; assumption.
Qed.

Lemma ccx_sem : forall f x y z aenv, nor_mode f x -> nor_mode f y -> nor_mode f z
                     -> x <> y -> y <> z -> x <> z -> 
                    exp_sem aenv (CCX x y z) f = (f[z |-> put_cu (f z) (get_cua (f z) ⊕ (get_cua (f y) && get_cua (f x)))]).
Proof.
 intros. 
 assert (eq1 := H0).
 unfold CCX. apply nor_mode_nval in H0.
 destruct H0. destruct H0.
 simpl. rewrite H0. simpl.
 destruct (f z) eqn:eq2.
 unfold exchange.
 simpl.
 destruct (get_cua (f y)) eqn:eq3.
 simpl. easy.
 simpl. rewrite eupdate_same. easy. rewrite eq2.
 bt_simpl. easy.
 unfold nor_mode in H2.
 rewrite eq2 in H2. inv H2.
 unfold nor_mode in H2.
 rewrite eq2 in H2. inv H2.
 simpl.
 rewrite H0. simpl. bt_simpl.
 rewrite put_get_cu. rewrite eupdate_same. easy. easy. assumption.
Qed.

Lemma ccx_nor : forall f f' x y z v aenv, nor_mode f x -> nor_mode f y -> nor_mode f z
                     -> x <> y -> y <> z -> x <> z -> 
                       put_cu (f z) (get_cua (f z) ⊕ (get_cua (f y) && get_cua (f x))) = v ->
                       f = f' ->
                    exp_sem aenv (CCX x y z) f = (f'[z |-> v]).
Proof.
 intros. subst. apply ccx_sem. 1 - 6: assumption. 
Qed.


Definition id_nat := fun i :nat => i.
Definition avs_for_arith (size:nat) := fun x => (x/size, x mod size).
Fixpoint gen_vars' (size:nat) (l : list var) (start:nat) :=
      match l with [] => (fun _ => (0,0,id_nat,id_nat))
             | (x::xl) => (fun y => if x =? y then (start,size,id_nat,id_nat) else 
                                gen_vars' size xl (start+size) y)
      end.
Definition gen_vars (size:nat) (l:list var) := gen_vars' size l 0.

Fixpoint findnum' (size:nat) (x:nat) (y:nat) (i:nat) := 
       match size with 0 => i
              | S n => if y <=? x then i else findnum' n (2 * x) y (i+1)
       end.

(* find a number that is great-equal than 2^(n-1), assume that the number is less than 2^n *)
Definition findnum (x:nat) (n:nat) := findnum' n x (2^(n-1)) 0.


Fixpoint copyto (x y:var) size := match size with 0 => SKIP (x,0) 
                  | S m => CNOT (x,m) (y,m) ; copyto x y m
    end.

Definition div_two_spec (f:nat->bool) := fun i => f (i+1).
