Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat.
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

Declare Scope exp_scope.
Delimit Scope exp_scope with exp.
Local Open Scope exp_scope.
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


Definition rz_val : Type := (nat -> bool).

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


Notation "f '[' i '|->' x ']'" := (eupdate f i x) (at level 10).


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

(* Adds an equality in the context *)
Ltac ctx e1 e2 :=
  let H := fresh "HCtx" in
  assert (e1 = e2) as H by reflexivity.

(* Standard inversion/subst/clear abbrev. *)
Tactic Notation "inv" hyp(H) := inversion H; subst; clear H.
Tactic Notation "inv" hyp(H) "as" simple_intropattern(p) :=
  inversion H as p; subst; clear H.

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

(* irrelavent vars. *)
Definition vars_neq (l:list var) := forall n m x y, nth_error l m = Some x ->  nth_error l n = Some y -> n <> m -> x <> y.


Inductive exp := SKIP (p:posi) | X (p:posi) | CU (p:posi) (e:exp)
        | RZ (q:nat) (p:posi) (* 2 * PI * i / 2^q *)
        | RRZ (q:nat) (p:posi) 
        | Seq (s1:exp) (s2:exp).

Notation "p1 ; p2" := (Seq p1 p2) (at level 50) : exp_scope.


Inductive sexp :=  | Lshift (x:var) | Rshift (x:var) 
                   | Rev (x:var)  (* move the positions in x to be upside-down. *)
                 (*  | Reset (x:var) *)
                   | Exp (s:exp) | SSeq (s1:sexp) (s2:sexp).

Coercion Exp : exp >-> sexp.

Notation "p1 ;; p2" := (SSeq p1 p2) (at level 49) : exp_scope.

Inductive pexp := SExp (s:sexp) | QFT (x:var) | RQFT (x:var)
               | H (x:var) | FSeq (p1:pexp) (p2:pexp).

Coercion SExp : sexp >-> pexp.

Notation "p1 ;;; p2" := (FSeq p1 p2) (at level 48) : exp_scope.

Inductive type := Had | Phi | Nor.

Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Module Env := FMapList.Make Nat_as_OT.

Definition env := Env.t type.

Inductive exp_fresh : posi -> exp -> Prop :=
      | skip_fresh : forall p p1, p <> p1 -> exp_fresh p (SKIP p1)
      | x_fresh : forall p p' , p <> p' -> exp_fresh p (X p')
      | cu_fresh : forall p p' e, p <> p' -> exp_fresh p e -> exp_fresh p (CU p' e)
      | rz_fresh : forall p p' q, p <> p' -> exp_fresh p (RZ q p')
      | rrz_fresh : forall p p' q, p <> p' -> exp_fresh p (RRZ q p')
      | seq_fresh : forall p e1 e2, exp_fresh p e1 -> exp_fresh p e2 -> exp_fresh p (Seq e1 e2).

Inductive exp_fwf : exp -> Prop :=
      | skip_fwf : forall p, exp_fwf (SKIP p)
      | x_fwf : forall p,  exp_fwf (X p)
      | cu_fwf : forall p e, exp_fresh p e -> exp_fwf e -> exp_fwf (CU p e)
      | rz_fwf : forall p q, exp_fwf (RZ q p)
      | rrz_fwf : forall p q, exp_fwf (RRZ q p)
      | seq_fwf : forall e1 e2, exp_fwf e1 -> exp_fwf e2 -> exp_fwf (Seq e1 e2).

Inductive well_typed_exp : env -> exp -> Prop :=
    | skip_refl : forall env, forall p, well_typed_exp env (SKIP p)
    | x_refl : forall env a b, Env.MapsTo a Nor env -> well_typed_exp env (X (a,b))
    | x_had : forall env a b, Env.MapsTo a Had env -> well_typed_exp env (X (a,b))
    | cu_refl : forall env a b e, Env.MapsTo a Nor env -> well_typed_exp env e -> well_typed_exp env (CU (a,b) e)
    | rz_refl :forall env q a b, Env.MapsTo a Nor env -> well_typed_exp env (RZ q (a,b))
    | rz_had : forall env a b, Env.MapsTo a Had env -> well_typed_exp env (RZ 1 (a,b))
    | rz_qft : forall env q a b, Env.MapsTo a Phi env -> well_typed_exp env (RZ q (a,b))
    | rrz_refl :forall env q a b, Env.MapsTo a Nor env -> well_typed_exp env (RRZ q (a,b))
    | rrz_had : forall env a b, Env.MapsTo a Had env -> well_typed_exp env (RRZ 1 (a,b))
    | rrz_qft : forall env q a b, Env.MapsTo a Phi env -> well_typed_exp env (RRZ q (a,b))
    | e_seq : forall env p1 p2, well_typed_exp env p1 -> well_typed_exp env p2 -> well_typed_exp env (p1 ; p2).


Inductive well_typed_sexp : env -> sexp -> Prop :=
    | lshift_refl : forall env x, well_typed_sexp env (Lshift x)
    | rshift_refl : forall env x, well_typed_sexp env (Rshift x)
    | rev_refl : forall env x, well_typed_sexp env (Rev x)
    | exp_refl : forall env e, exp_fwf e -> well_typed_exp env e -> well_typed_sexp env (Exp e)
    | se_seq : forall env e1 e2, well_typed_sexp env e1 -> well_typed_sexp env e2 -> well_typed_sexp env (e1 ;; e2).


Inductive well_typed_pexp : env -> pexp -> env -> Prop :=
    | sexp_refl : forall env e, well_typed_sexp env e -> well_typed_pexp env (SExp e) env
    | qft_nor :  forall env env' x, Env.MapsTo x Nor env -> Env.Equal env' (Env.add x Phi env)
                   -> well_typed_pexp env (QFT x) env'
    | rqft_phi :  forall env env' x, Env.MapsTo x Phi env ->  Env.Equal env' (Env.add x Nor env) -> 
                 well_typed_pexp env (RQFT x) env'
    | h_nor : forall env env' x, Env.MapsTo x Nor env -> Env.Equal env' (Env.add x Had env) ->  
                  well_typed_pexp env (H x) env'
    | h_had : forall env env' x, Env.MapsTo x Had env -> Env.Equal env' (Env.add x Nor env) ->  
                                   well_typed_pexp env (H x) env'
    | fe_seq : forall env env' env'' e1 e2, well_typed_pexp env e1 env' -> 
                 well_typed_pexp env' e2 env'' -> well_typed_pexp env (e1 ;;; e2) env''.


Inductive right_mode_val : type -> val -> Prop :=
    | right_nor: forall b r, right_mode_val Nor (nval b r)
    | right_had: forall b1 b2 r, r 0 = false -> right_mode_val Had (hval b1 b2 r)
    | right_phi: forall r, right_mode_val Phi (qval r).

Definition right_mode_vals (f:posi -> val) (x:var) (t:type) : Prop :=
    forall i, right_mode_val t (f (x,i)).

Inductive right_mode_exp : env -> (posi -> val) -> exp -> Prop :=
    | skip_right : forall env f, forall p, right_mode_exp env f (SKIP p)
    | x_right : forall env f a b t, Env.MapsTo a t env -> right_mode_val t (f (a,b)) -> right_mode_exp env f (X (a,b))
    | cu_right : forall env f a b t e, Env.MapsTo a t env -> right_mode_val t (f (a,b))
                      -> right_mode_exp env f e -> right_mode_exp env f (CU (a,b) e)
    | rz_right : forall env f a b t q,  Env.MapsTo a t env -> right_mode_val t (f (a,b)) -> right_mode_exp env f (RZ q (a,b))
    | rrz_right : forall env f a b t q,  Env.MapsTo a t env -> right_mode_val t (f (a,b)) -> right_mode_exp env f (RRZ q (a,b))
    | seq_right : forall env f e1 e2, right_mode_exp env f e1 -> right_mode_exp env f e2 -> right_mode_exp env f (e1 ; e2).

Inductive right_mode_sexp : env -> (posi -> val) -> sexp -> Prop :=
    | lshift_right : forall env f a t, Env.MapsTo a t env -> right_mode_vals f a t -> right_mode_sexp env f (Lshift a) 
    | rshift_right : forall env f a t, Env.MapsTo a t env -> right_mode_vals f a t -> right_mode_sexp env f (Rshift a)
    | rev_right : forall env f a t, Env.MapsTo a t env -> right_mode_vals f a t -> right_mode_sexp env f (Rev a)
    | exp_right : forall env f e, right_mode_exp env f e -> right_mode_sexp env f (Exp e)
    | sseq_right : forall env f e1 e2, right_mode_sexp env f e1 -> right_mode_sexp env f e2 -> right_mode_sexp env f (e1 ;; e2).


Inductive right_mode_pexp : env -> (posi -> val) -> pexp -> env -> Prop :=
    | qft_right : forall env env' f a t, Env.MapsTo a t env -> right_mode_vals f a t ->
             well_typed_pexp env (QFT a) env' -> right_mode_pexp env f (QFT a) env'
    | rqft_right : forall env env' f a t, Env.MapsTo a t env -> right_mode_vals f a t -> 
                        well_typed_pexp env (RQFT a) env' -> right_mode_pexp env f (RQFT a) env'
    | h_right : forall env env' f a t, Env.MapsTo a t env -> right_mode_vals f a t ->
                     well_typed_pexp env (H a) env' -> right_mode_pexp env f (H a) env'
    | sexp_right : forall env f e, right_mode_sexp env f e -> right_mode_pexp env f (SExp e) env
    | pseq_right : forall env env' env'' f e1 e2, right_mode_pexp env f e1 env'
                     -> right_mode_pexp env' f e2 env'' -> right_mode_pexp env f (e1 ;;; e2) env''.

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


Lemma right_mode_cu : forall env f x i e, well_typed_exp env (CU (x,i) e)
                          -> right_mode_exp env f (CU (x,i) e) -> (exists b r, (f (x,i)) = nval b r).
Proof.
  intros. inv H0. inv H1. apply (mapsto_always_same x Nor t env0) in H8. subst.
  inv H9. exists b. exists r. easy.
  assumption.
Qed.


(* Here we defined the specification of carry value for each bit. *)
(* fb_push is to take a qubit and then push it to the zero position 
        in the bool function representation of a number. *)
Definition allfalse := fun (_:nat) => false.

Definition majb a b c := (a && b) ⊕ (b && c) ⊕ (a && c).

Definition fb_push b f : nat -> bool :=
  fun x => match x with
        | O => b
        | S n => f n
        end.

Lemma fb_push_right:
  forall n b f, 0 < n -> fb_push b f n = f (n-1).
Proof.
  intros. induction n. lia.
  simpl. assert ((n - 0) = n) by lia.
  rewrite H1. reflexivity.
Qed.

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

Definition nat2fb n := N2fb (N.of_nat n).

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

Definition negatem i (f : nat -> bool) := fun (x : nat) => if (x <? i) then ¬ (f x) else f x.

Lemma sumfb_correct_carry0 :
  forall x y,
    sumfb false (nat2fb x) (nat2fb y) = nat2fb (x + y).
Proof.
  intros. unfold nat2fb. rewrite Nnat.Nat2N.inj_add.
  apply functional_extensionality. intros. unfold sumfb. rewrite carry_add_eq_carry0. easy.
Qed.

Lemma sumfb_correct_carry1 :
  forall x y,
    sumfb true (nat2fb x) (nat2fb y) = nat2fb (x + y + 1).
Proof.
  intros. unfold nat2fb. do 2 rewrite Nnat.Nat2N.inj_add.
  apply functional_extensionality. intros. unfold sumfb. rewrite carry_add_eq_carry1. easy.
Qed.

Lemma sumfb_correct_N_carry0 :
  forall x y,
    sumfb false (N2fb x) (N2fb y) = N2fb (x + y).
Proof.
  intros. apply functional_extensionality. intros. unfold sumfb. rewrite carry_add_eq_carry0. easy.
Qed.

Lemma pos2fb_Postestbit :
  forall n i,
    (pos2fb n) i = Pos.testbit n (N.of_nat i).
Proof.
  induction n; intros.
  - destruct i; simpl. easy. rewrite IHn. destruct i; simpl. easy. rewrite Pos.pred_N_succ. easy.
  - destruct i; simpl. easy. rewrite IHn. destruct i; simpl. easy. rewrite Pos.pred_N_succ. easy.
  - destruct i; simpl. easy. easy.
Qed.

Lemma N2fb_Ntestbit :
  forall n i,
    (N2fb n) i = N.testbit n (N.of_nat i).
Proof.
  intros. destruct n. easy.
  simpl. apply pos2fb_Postestbit.
Qed.

Lemma Z2N_Nat2Z_Nat2N :
  forall x,
    Z.to_N (Z.of_nat x) = N.of_nat x.
Proof.
  destruct x; easy.
Qed.

Lemma Nofnat_mod :
  forall x y,
    y <> 0 ->
    N.of_nat (x mod y) = ((N.of_nat x) mod (N.of_nat y))%N.
Proof.
  intros. specialize (Zdiv.mod_Zmod x y H0) as G.
  repeat rewrite <- Z2N_Nat2Z_Nat2N. rewrite G. rewrite Z2N.inj_mod; lia.
Qed.

Lemma Nofnat_pow :
  forall x y,
    N.of_nat (x ^ y) = ((N.of_nat x) ^ (N.of_nat y))%N.
Proof.
  intros. induction y. easy.
  Local Opaque N.pow. replace (N.of_nat (S y)) with ((N.of_nat y) + 1)%N by lia.
 simpl. rewrite N.pow_add_r. rewrite N.pow_1_r. rewrite Nnat.Nat2N.inj_mul. rewrite IHy. lia.
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


(* Here, we define the addto / addto_n functions for angle rotation. *)
Definition cut_n (f:nat -> bool) (n:nat) := fun i => if i <? n then f i else allfalse i.
 
Definition fbrev' i n (f : nat -> bool) := fun (x : nat) => 
            if (x <=? i) then f (n - 1 - x) else if (x <? n - 1 - i) 
                         then f x else if (x <? n) then f (n - 1 - x) else f x.
Definition fbrev n (f : nat -> bool) := fun (x : nat) => if (x <? n) then f (n - 1 - x) else f x.

Lemma fbrev'_fbrev :
  forall n f,
    0 < n ->
    fbrev n f = fbrev' ((n - 1) / 2) n f.
Proof.
  intros. unfold fbrev, fbrev'. apply functional_extensionality; intro.
  assert ((n - 1) / 2 < n) by (apply Nat.div_lt_upper_bound; lia).
  assert (2 * ((n - 1) / 2) <= n - 1) by (apply Nat.mul_div_le; easy).
  assert (n - 1 - (n - 1) / 2 <= (n - 1) / 2 + 1).
  { assert (n - 1 <= 2 * ((n - 1) / 2) + 1).
    { assert (2 <> 0) by easy.
      specialize (Nat.mul_succ_div_gt (n - 1) 2 H3) as G.
      lia.
    }
    lia.
  }
  IfExpSimpl; easy.
Qed.

Lemma allfalse_0 : forall n, cut_n allfalse n = nat2fb 0.
Proof.
  intros. unfold nat2fb. simpl.
  unfold cut_n.
  apply functional_extensionality; intro.
  bdestruct (x <? n).
  easy. easy.
Qed.

Lemma f_num_aux_0: forall n f x, cut_n f n = nat2fb x 
                -> f n = false -> cut_n f (S n) = nat2fb x.
Proof.
  intros.
  rewrite <- H0.
  unfold cut_n.
  apply functional_extensionality.
  intros.
  bdestruct (x0 <? n).
  bdestruct (x0 <? S n).
  easy.
  lia.
  bdestruct (x0 <? S n).
  assert (x0 = n) by lia.
  subst. rewrite H1. easy.
  easy.
Qed.

Definition twoton_fun (n:nat) := fun i => if i <? n then false else if i=? n then true else false.


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
  assert ((fb_push false (fb_push true (pos2fb p))) x = (fb_push true (pos2fb p)) (x - 1)).
  rewrite fb_push_right.
  reflexivity. lia.
  rewrite H1.
  reflexivity.
  simpl.
  rewrite (fb_push_right x).
  reflexivity. lia.
  simpl.
  rewrite (fb_push_right x).
  reflexivity. lia.
Qed.

Lemma times_two_correct:
   forall x, (times_two_spec (nat2fb x)) = (nat2fb (2*x)).
Proof.
  intros.
  unfold times_two_spec.
  apply functional_extensionality; intros.
  unfold nat2fb.
  bdestruct (x0 =? 0).
  rewrite H0.
  specialize (nat2fb_even_0 x) as H3.
  unfold nat2fb in H3.
  rewrite H3.
  reflexivity.
  rewrite Nat2N.inj_double.
  unfold N.double,N2fb.
  destruct (N.of_nat x).
  unfold allfalse.
  reflexivity.
  rewrite pos2fb_times_two_eq.
  reflexivity. lia.
Qed.


Lemma f_twoton_eq : forall n, twoton_fun n = nat2fb (2^n).
Proof.
  intros.
  induction n.
  simpl.
  unfold twoton_fun.
  apply functional_extensionality.
  intros. 
  IfExpSimpl.
  unfold fb_push. destruct x. easy. lia.
  unfold fb_push. destruct x. lia. easy.
  assert ((2 ^ S n) = 2 * (2^n)). simpl. lia.
  rewrite H0.
  rewrite <- times_two_correct.
  rewrite <- IHn.
  unfold twoton_fun,times_two_spec.
  apply functional_extensionality; intros.
  bdestruct (x =? 0).
  subst.
  bdestruct (0 <? S n).
  easy. lia.
  bdestruct (x <? S n).
  bdestruct (x - 1 <? n).
  easy. lia.
  bdestruct (x =? S n).
  bdestruct (x - 1 <? n). lia.
  bdestruct (x - 1 =? n). easy.
  lia.
  bdestruct (x-1<? n). easy.
  bdestruct (x-1 =? n). lia.
  easy.
Qed.

Local Transparent carry.

Lemma carry_cut_n_false : forall i n f, carry false i (cut_n f n) (twoton_fun n) = false.
Proof.
  intros.
  induction i.
  simpl. easy.
  simpl. rewrite IHi.
  unfold cut_n,twoton_fun.
  IfExpSimpl. btauto.
  simpl.
  btauto.
  simpl. easy.
Qed.

Local Opaque carry.

Lemma sumfb_cut_n : forall n f, f n = true -> sumfb false (cut_n f n) (twoton_fun n)  = cut_n f (S n).
Proof.
  intros.
  unfold sumfb.
  apply functional_extensionality; intros.
  rewrite carry_cut_n_false.
  unfold cut_n, twoton_fun.
  IfExpSimpl. btauto.
  subst. rewrite H0. simpl.  easy.
  simpl. easy.
Qed.

Lemma f_num_aux_1: forall n f x, cut_n f n = nat2fb x -> f n = true 
                  -> cut_n f (S n) = nat2fb (x + 2^n).
Proof.
  intros.
  rewrite <- sumfb_correct_carry0.
  rewrite <- H0.
  rewrite <- f_twoton_eq.
  rewrite sumfb_cut_n.
  easy. easy.
Qed.

Lemma f_num_0 : forall f n, (exists x, cut_n f n = nat2fb x).
Proof.
  intros.
  induction n.
  exists 0.
  rewrite <- (allfalse_0 0).
  unfold cut_n.
  apply functional_extensionality.
  intros.
  bdestruct (x <? 0).
  inv H0. easy.
  destruct (bool_dec (f n) true).
  destruct IHn.
  exists (x + 2^n).
  rewrite (f_num_aux_1 n f x).
  easy. easy. easy.
  destruct IHn.
  exists x. rewrite (f_num_aux_0 n f x).
  easy. easy.
  apply not_true_is_false in n0. easy.
Qed.

Lemma f_num_small : forall f n x, cut_n f n = nat2fb x -> x < 2^n.
Proof.
  intros.
Admitted.

Definition addto (r : nat -> bool) (n:nat) : nat -> bool := fun i => if i <? n 
                    then (cut_n (fbrev n (sumfb false (cut_n (fbrev n r) n) (nat2fb 1))) n) i else r i.

Definition addto_n (r:nat -> bool) n := fun i => if i <? n
                        then (cut_n (fbrev n (sumfb false 
                  (cut_n (fbrev n r) n) (sumfb false (nat2fb 1) (negatem n (nat2fb 1))))) n) i else r i.

Lemma addto_n_0 : forall r, addto_n r 0 = r.
Proof.
  intros.
  unfold addto_n.
  apply functional_extensionality.
  intros.
  IfExpSimpl. easy.
Qed.

Lemma addto_0 : forall r, addto r 0 = r.
Proof.
  intros.
  unfold addto.
  apply functional_extensionality.
  intros.
  IfExpSimpl. easy.
Qed.

Lemma cut_n_fbrev_flip : forall n f, cut_n (fbrev n f) n = fbrev n (cut_n f n).
Proof.
  intros.
  unfold cut_n, fbrev.
  apply functional_extensionality.
  intros.
  bdestruct (x <? n).
  bdestruct (n - 1 - x <? n).
  easy. lia. easy.
Qed.

Lemma cut_n_if_cut : forall n f g, cut_n (fun i => if i <? n then f i else g i) n = cut_n f n.
Proof.
  intros.
  unfold cut_n.
  apply functional_extensionality; intros.
  bdestruct (x <? n).
  easy. easy.
Qed.

Lemma fbrev_twice_same: forall n f, fbrev n (fbrev n f) = f.
Proof.
  intros.
  unfold fbrev.
  apply functional_extensionality.
  intros.
  bdestruct (x <? n).
  bdestruct (n - 1 - x <? n).
  assert ((n - 1 - (n - 1 - x)) = x) by lia.
  rewrite H2. easy.
  lia. easy.
Qed.

Lemma cut_n_mod : forall n x, cut_n (nat2fb x) n = (nat2fb (x mod 2^n)).
Proof.
  intros.
  unfold nat2fb.
Admitted.

Lemma add_to_r_same : forall q r, addto (addto_n r q) q = r.
Proof.
  intros.
  destruct q eqn:eq1.
  rewrite addto_n_0.
  rewrite addto_0. easy.
  unfold addto_n.
  specialize (f_num_0 (fbrev (S n) r) (S n)) as eq2.
  destruct eq2.
  rewrite negatem_arith.
  rewrite sumfb_correct_carry0.
  assert (1 < 2 ^ (S n)).
  apply Nat.pow_gt_1. lia. lia.
  assert ((1 + (2 ^ S n - 1 - 1)) = 2^ S n -1) by lia.
  rewrite H2.
  rewrite H0.
  rewrite sumfb_correct_carry0.
  unfold addto.
  rewrite (cut_n_fbrev_flip (S n) (fun i0 : nat =>
                 if i0 <? S n
                 then
                  cut_n
                    (fbrev (S n)
                       (nat2fb
                          (x + (2 ^ S n - 1))))
                    (S n) i0
                 else r i0)).
  rewrite cut_n_if_cut.
  rewrite (cut_n_fbrev_flip (S n)
                      (nat2fb
                         (x + (2 ^ S n - 1)))).
  rewrite cut_n_mod.
  rewrite <- cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  rewrite cut_n_mod.
  rewrite Nat.mod_mod by lia.
  rewrite sumfb_correct_carry0.
  assert (((x + (2 ^ S n - 1)) mod 2 ^ S n + 1) = ((x + (2 ^ S n - 1)) mod 2 ^ S n + (1 mod 2^ S n))).
  assert (1 mod 2^ S n = 1).
  rewrite Nat.mod_small. easy. easy.
  rewrite H3. easy.
  rewrite H3.
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_mod.
  rewrite <- Nat.add_mod by lia.
  assert ((x + (2 ^ S n - 1) + 1) = x + 2 ^ S n) by lia.
  rewrite H4.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  assert (x mod 2 ^ S n = x).
  rewrite Nat.mod_small. easy.
  apply (f_num_small (fbrev (S n) r)). easy.
  rewrite H5.
  rewrite plus_0_r.
  rewrite H5.
  rewrite <- H0.
  rewrite <- cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  apply functional_extensionality.
  intros.
  bdestruct (x0 <? S n).
  unfold cut_n.
  bdestruct (x0 <? S n).
  easy. lia. easy.
  apply Nat.pow_gt_1. lia. lia.
Qed.

Lemma add_to_same : forall q r, addto_n (addto r q) q = r.
Proof.
  intros.
  destruct q eqn:eq1.
  rewrite addto_n_0.
  rewrite addto_0. easy.
  unfold addto.
  specialize (f_num_0 (fbrev (S n) r) (S n)) as eq2.
  destruct eq2.
  rewrite H0.
  rewrite sumfb_correct_carry0.
  unfold addto_n.
  rewrite negatem_arith.
  rewrite sumfb_correct_carry0.
  assert (1 < 2 ^ (S n)).
  apply Nat.pow_gt_1. lia. lia.
  assert ((1 + (2 ^ S n - 1 - 1)) = 2^ S n -1) by lia.
  rewrite H2.
  rewrite (cut_n_fbrev_flip (S n) (fun i0 : nat =>
                 if i0 <? S n
                 then
                  cut_n
                    (fbrev (S n)
                       (nat2fb (x + 1))) 
                    (S n) i0
                 else r i0)).
  rewrite cut_n_if_cut.
  rewrite (cut_n_fbrev_flip (S n)
                      (nat2fb (x+1))).
  rewrite cut_n_mod.
  rewrite <- cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  rewrite cut_n_mod.
  rewrite Nat.mod_mod by lia.
  assert ((2 ^ S n - 1) = (2 ^ S n - 1) mod (2^ S n)).
  rewrite Nat.mod_small by lia.
  easy.
  rewrite H3.
  rewrite sumfb_correct_carry0.
  rewrite cut_n_fbrev_flip.
  rewrite cut_n_mod.
  rewrite <- Nat.add_mod by lia.
  assert ((x + 1 + (2 ^ S n - 1))  = x + 2 ^ S n) by lia.
  rewrite H4.
  rewrite Nat.add_mod by lia.
  rewrite Nat.mod_same by lia.
  rewrite plus_0_r.
  rewrite Nat.mod_mod by lia.
  rewrite Nat.mod_small.
  rewrite <- H0.
  rewrite cut_n_fbrev_flip.
  rewrite fbrev_twice_same.
  apply functional_extensionality.
  intros.
  bdestruct (x0 <? S n).
  unfold cut_n.
  bdestruct (x0 <? S n).
  easy. lia. easy.
  apply (f_num_small (fbrev (S n) r)). easy.
  apply Nat.pow_gt_1. lia. lia.
Qed.


Lemma posi_neq_f : forall (p p' : posi), p <> p' -> fst p <> fst p' \/ snd p <> snd p'.
Proof.
 intros. destruct p. destruct p'.
 simpl in *.
 bdestruct (v =? v0).
 subst. right.
 intros R. subst. contradiction.
 bdestruct (n =? n0).
 subst.
 left.
 intros R. subst. contradiction.
 left. lia.
Qed.

Lemma posi_neq_b : forall (p p' : posi), fst p <> fst p' \/ snd p <> snd p' -> p <> p'.
Proof.
 intros. destruct p. destruct p'.
 simpl in *.
 intros R. inv R.
 destruct H0.
 lia.
 lia.
Qed.


(* helper functions/lemmas for NOR states. *)
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



Definition put_cu (v:val) (b:bool) :=
    match v with nval x r => nval b r | a => a end.

Definition get_cua (v:val) := 
    match v with nval x r => x | a => false end.

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


Fixpoint init_v (n:nat) (x:var) (M: nat -> bool) :=
      match n with 0 => (SKIP (x,0))
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



Definition get_cu (v : val) :=
    match v with nval b r => Some b 
                 | hval b1 b2 r => Some b1
                 | _ => None
    end.


Lemma get_cu_good : forall tenv f p e, well_typed_exp tenv (CU p e) 
            -> right_mode_exp tenv f (CU p e) -> (exists b, get_cu (f p) = Some b).
Proof.
  intros. 
  unfold get_cu.
  inv H0. inv H1. 
  apply (mapsto_always_same a Nor t tenv) in H8. subst.
  inv H9.
  exists b0. easy. easy.
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

Notation "p1 '[⊕]' p2" := (vxor p1 p2) (at level 50) : exp_scope.

Notation "p1 '[&&]' p2" := (vand p1 p2) (at level 50) : exp_scope.

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


(*A function to get the rotation angle of a state. *)
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
                  | qval r =>  qval (rotate r q)
     end.

Definition r_rotate (r :rz_val) (q:nat) := addto_n r q.

Definition times_r_rotate (v : val) (q:nat) := 
     match v with nval b r =>  if b then nval b (r_rotate r q) else nval b r
                  | hval b1 b2 r => hval b1 (¬ b2) r
                  | qval r =>  qval (r_rotate r q)
     end.


Definition exchange (v: val) :=
     match v with nval b r => nval (¬ b) r
                  | hval b1 b2 r => hval b2 b1 r
                  | a => a
     end.

Fixpoint lshift' (n:nat) (size:nat) (f:posi -> val) (x:var) := 
   match n with 0 => f[(x,0) |-> f(x,size)]
             | S m => ((lshift' m size f x)[ (x,n) |-> f(x,m)])
   end.
Definition lshift (f:posi -> val) (x:var) (n:nat) := lshift' n n f x.

Fixpoint rshift' (n:nat) (size:nat) (f:posi -> val) (x:var) := 
   match n with 0 => f[(x,size) |-> f(x,0)]
             | S m => ((rshift' m size f x)[(x,m) |-> f (x,n)])
   end.
Definition rshift (f:posi -> val) (x:var) (n:nat) := rshift' n n f x.

(*
Inductive varType := SType (n1:nat) (n2:nat).

Definition inter_env (enva: var -> nat) (x:var) :=
             match  (enva x) with SType n1 n2 => n1 + n2 end.
*)

(* This is the semantics for basic gate set of the language. *)
Fixpoint exp_sem (env: var -> nat) (e:exp) (st: posi -> val) : (posi -> val) :=
   match e with (SKIP p) => st
              | X p => (st[p |-> (exchange (st p))])
              | CU p e' => if get_cua (st p) then exp_sem env e' st else st
              | RZ q p => (st[p |-> times_rotate (st p) q])
              | RRZ q p => (st[p |-> times_r_rotate (st p) q])
              | e1 ; e2 => exp_sem env e2 (exp_sem env e1 st)
    end.

Definition reverse (f:posi -> val) (x:var) (n:nat) := fun a =>
             if ((fst a) =? x) && ((snd a) <? n) then f (x, (n-1) - (snd a)) else f a.


Lemma x_nor : forall env f x v, nor_mode f x -> put_cu (f x) (¬ (get_cua (f x))) = v ->
                            exp_sem env (X x) f = (f[x |-> v]).
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

Lemma efresh_exp_sem_irrelevant :
  forall e env p f,
    exp_fresh p e ->
    exp_sem env e f p = f p.
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
  simpl.
  apply (IHe1 env0) with (f := f) in H4.
  apply (IHe2 env0) with (f := (exp_sem env0 e1 f)) in H5.
  rewrite H5. rewrite H4. easy.
Qed.


Lemma two_cu_same : forall env f p e1 e2, get_cua (f p) = true ->
                     exp_fwf (CU p e1) -> exp_sem env (e1 ; e2) f = exp_sem env (CU p e1; CU p e2) f. 
Proof.
  intros.
  inv H1.
  simpl.
  destruct (get_cua (f p)) eqn:eq1.
  rewrite (efresh_exp_sem_irrelevant e1 env0 p f) by assumption.
  destruct (get_cua (f p)). easy.
  inv eq1. inv H0.
Qed.

(* This is the semantics for shifting/virtual qubit states. *)
Fixpoint sexp_sem (env: var -> nat) (e:sexp) (st: posi -> val) : (posi -> val) :=
   match e with | Lshift x => (lshift st x (env x))
                | Rshift x => (rshift st x (env x))
                | Rev x => (reverse st x (env x))
              | Exp e => exp_sem env e st
              | e1 ;; e2 => sexp_sem env e2 (sexp_sem env e1 st)
    end.


(* This is the semantics for switching qubit representation states. *)
Definition h_case (v : val) :=
    match v with nval b r => if r 0 then hval false b (rotate r 1) else hval true (¬ b) r
               | hval true true r => nval false r
               | hval true false r => nval true r
               | hval false true r => nval true (rotate r 1)
               | hval false false r => nval false (rotate r 1)
               | a => a
    end.

Lemma fbrev_1_same : forall f, fbrev 1 f = f.
Proof.
  intros.
  unfold fbrev.
  apply functional_extensionality. intros.
  bdestruct (x<?1).
  assert (1 - 1 - x = x) by lia.
  rewrite H1. easy. easy. 
Qed.
 
Lemma cut_n_1_1: forall (r:rz_val), r 0 = true -> cut_n r 1 = nat2fb 1.
Proof.
  intros. unfold cut_n.
  apply functional_extensionality. intros.
  bdestruct (x <? 1).
  assert (x = 0) by lia. subst.
  unfold nat2fb. simpl. rewrite H0. easy.
  unfold nat2fb. simpl. 
  rewrite fb_push_right. easy. lia.
Qed.

Lemma cut_n_1_0: forall (r:rz_val), r 0 = false -> cut_n r 1 = nat2fb 0.
Proof.
  intros. unfold cut_n.
  apply functional_extensionality. intros.
  bdestruct (x <? 1).
  assert (x = 0) by lia. subst.
  unfold nat2fb. simpl. rewrite H0. easy.
  unfold nat2fb. simpl. easy.
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

Fixpoint h_sem (f:posi -> val) (x:var) (n : nat) := 
    match n with 0 => f
              | S m => h_sem (f[(x,m) |-> h_case (f (x,m))]) x m
    end.

Definition seq_val (v:val) :=
  match v with nval b r => b
             | _ => false
  end.

Fixpoint get_seq (f:posi -> val) (x:var) (base:nat) (n:nat) : (nat -> bool) :=
     match n with 0 => allfalse
              | S m => fun (i:nat) => if i =? (base + m) then seq_val (f (x,base+m)) else ((get_seq f x base m) i)
     end.

Definition up_qft (v:val) (f:nat -> bool) :=
   match v with nval b r => qval f
              | a => a
   end.

Fixpoint qft_val' (f:posi -> val) (x:var) (n:nat) (base:nat) :=
    match n with 0 => f
              | S m => qft_val' (f[(x,base) |-> up_qft (f (x,base)) (get_seq f x base n)]) x m (base +1)
    end.

Definition qft_val (f:posi -> val) (x:var) (n:nat) := qft_val' f x n 0.

Definition no_rot (f:posi -> val) (x:var) :=
    forall n, (exists b r, (f (x,n)) = nval b r /\ r = allfalse).

Definition all_qft (f:posi -> val) (x:var) := forall n, (exists r, f (x,n) = qval r).

Fixpoint prog_sem (env:var -> nat) (e:pexp) (st:posi-> val) : (posi -> val) :=
    match e with SExp e => sexp_sem env e st
               | H x => h_sem st x (env x)
               | QFT x => qft_val st x (env x)
               | RQFT x => qft_val st x (env x)
               | e1 ;;; e2 => prog_sem env e2 (prog_sem env e1 st)
    end.


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
  bdestruct (( f x - 1 - n0 <? f x)).
  simpl.
  assert ( f x - 1 - ( f x - 1 - n0)= n0) by lia.
  rewrite H3. easy.
  simpl. lia.
  lia. simpl. easy.
  simpl. easy.
Qed.

(*
  The following defines the inverse function of a given RCIRplus circuit. 
*)

Fixpoint inv_exp p :=
  match p with
  | SKIP a => SKIP a
  | X n => X n
  | CU n p => CU n (inv_exp p)
  | Seq p1 p2 => inv_exp p2; inv_exp p1
  | RZ q p1 => RRZ q p1
  | RRZ q p1 => RZ q p1
  end.

Lemma inv_exp_involutive :
  forall p,
    inv_exp (inv_exp p) = p.
Proof.
  induction p; simpl; try easy.
  - rewrite IHp. easy.
  - rewrite IHp1, IHp2. easy.
Qed.

Fixpoint inv_sexp p :=
  match p with 
  | Exp e => Exp (inv_exp e)
  | Lshift x => Rshift x
  | Rshift x => Lshift x
  | Rev x => Rev x
  | p1 ;; p2 => inv_sexp p2 ;; inv_sexp p1
  end.

Lemma inv_sexp_involutive :
  forall p,
    inv_sexp (inv_sexp p) = p.
Proof.
  induction p; simpl; try easy.
  - rewrite inv_exp_involutive. easy.
  - rewrite IHp1, IHp2. easy.
Qed.


Fixpoint inv_pexp p :=
   match p with 
    | SExp s => SExp (inv_sexp s)
    | QFT x => RQFT x
    | RQFT x => QFT x
    | H x => H x
    | FSeq p1 p2 => FSeq (inv_pexp p2) (inv_pexp p1)
   end.

Lemma inv_pexp_involutive :
  forall p,
    inv_pexp (inv_pexp p) = p.
Proof.
  induction p; simpl; try easy.
  - rewrite inv_sexp_involutive. easy.
  - rewrite IHp1, IHp2. easy.
Qed.


Lemma fresh_inv_exp :
  forall p e,
    exp_fresh p e ->
    exp_fresh p (inv_exp e).
Proof.
  intros. induction H0; simpl; try constructor; try assumption.
Qed.

Lemma fwf_inv_exp :
  forall p,
    exp_fwf p ->
    exp_fwf (inv_exp p).
Proof.
  intros. induction H0; simpl; try constructor; try assumption.
  apply fresh_inv_exp. assumption.
Qed.

Lemma typed_inv_exp :
  forall tenv p,
    well_typed_exp tenv p ->
    well_typed_exp tenv (inv_exp p).
Proof.
  intros. induction p; simpl; try assumption.
  inv H0. constructor. assumption.
  apply IHp. assumption.
  inv H0. constructor. assumption.
  apply rrz_had. assumption.
  apply rrz_qft. assumption.
  inv H0. constructor. assumption.
  apply rz_had. assumption.
  apply rz_qft. assumption.
  inv H0.
  constructor.
  apply IHp2. assumption.
  apply IHp1. assumption.
Qed.

Lemma typed_inv_sexp :
  forall tenv p,
    well_typed_sexp tenv p ->
    well_typed_sexp tenv (inv_sexp p).
Proof.
  intros. induction p; simpl; try assumption.
  constructor. constructor.
  inv H0.
  constructor. apply fwf_inv_exp. easy.
  apply typed_inv_exp. easy.
  inv H0.
  constructor.
  apply IHp2. assumption.
  apply IHp1. assumption.
Qed.

Lemma right_mode_inv_exp :
  forall tenv f p,
    right_mode_exp tenv f p ->
    right_mode_exp tenv f (inv_exp p).
Proof.
  intros. induction p; simpl; try assumption.
  inv H0. 
  eapply cu_right. apply H3.
  assumption. apply IHp. assumption.
  inv H0.
  econstructor.
  apply H5. assumption.
  inv H0.
  econstructor.
  apply H5. assumption.
  inv H0.
  constructor.
  apply IHp2. assumption.
  apply IHp1. assumption.
Qed.

Lemma right_mode_inv_sexp :
  forall tenv f p,
    right_mode_sexp tenv f p ->
    right_mode_sexp tenv f (inv_sexp p).
Proof.
  intros. induction p; simpl; try assumption.
  inv H0.
  eapply rshift_right. apply H2. easy.
  inv H0. econstructor. apply H2. easy.
  inv H0.
  constructor. apply right_mode_inv_exp. easy.
  inv H0.
  constructor.
  apply IHp2. assumption.
  apply IHp1. assumption.
Qed.


Lemma right_mode_not_change_exp :
    forall env tenv f f' e1 e2,
     right_mode_exp tenv f e1 ->
     exp_sem env e2 f = f' -> 
     right_mode_exp tenv f' e1.
Proof.
  intros. 
  induction e2; simpl in *. subst.
  assumption.
  unfold exchange in *.
Admitted.

Lemma right_mode_not_change_sexp :
    forall env tenv f f' e1 e2,
     right_mode_sexp tenv f e1 ->
     sexp_sem env e2 f = f' -> 
     right_mode_sexp tenv f' e1.
Proof.
  intros. 
  induction e2; simpl in *. subst.
Admitted.


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
  bdestruct (S n0 <=? n).
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
  bdestruct (n0 =? n). subst.
  rewrite rshift'_0.
  rewrite lshift'_0. easy. easy. easy.
  bdestruct (n0 <? n).
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
     right_mode_vals f x t ->
    h_sem (h_sem f x n) x n = f.
Proof.
  induction n; intros.
  simpl. easy.
  simpl.
  rewrite h_sem_gt with (f:= f) by lia.
  rewrite eupdate_index_eq.
  rewrite eupdate_twice_eq by lia.
  rewrite h_sem_gt by lia.
  rewrite IHn with (t := t) by assumption.
  rewrite h_case_twice_same with (t := t).
  rewrite eupdate_same. easy. easy. apply H0.
Qed.

Lemma exp_sem_assoc : forall env f e1 e2 e3, 
               exp_sem env (e1 ; e2 ; e3) f = exp_sem env (e1 ; (e2 ; e3)) f.
Proof.
  intros. simpl. easy.
Qed.

Lemma inv_exp_correct :
  forall tenv env e f,
    exp_fwf e -> well_typed_exp tenv e -> right_mode_exp tenv f e ->
    exp_sem env (inv_exp e; e) f = f.
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
    rewrite H3. easy.
  - specialize (typed_inv_exp tenv (CU p e) H1) as eq1. simpl in eq1.
    specialize (right_mode_inv_exp tenv f (CU p e) H2) as eq2. simpl in eq2.
    assert (inv_exp (CU p e) = CU p (inv_exp e)). simpl. easy.
    rewrite H3.
    destruct (get_cua (f p)) eqn:eq3.
    rewrite <- two_cu_same.
    apply IHe. inv H0. assumption.
    inv H1. assumption. inv H2. assumption.
    assumption. rewrite <- H3.
    apply fwf_inv_exp. assumption.
    simpl. rewrite eq3. rewrite eq3. easy.
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
    rewrite H3. easy.
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
    rewrite H3. easy.
 - assert (inv_exp (e1; e2) = inv_exp e2; inv_exp e1). simpl. easy.
   rewrite H3.
   rewrite exp_sem_assoc.
   assert (exp_sem env0 (inv_exp e2; (inv_exp e1; (e1; e2))) f 
             = exp_sem env0 (inv_exp e1 ; (e1 ; e2)) (exp_sem env0 (inv_exp e2) f)).
   simpl. easy.
   rewrite H4.
   rewrite <- exp_sem_assoc.
   assert ( forall f', exp_sem env0 ((inv_exp e1; e1); e2) f' = exp_sem env0 e2 (exp_sem env0 ((inv_exp e1; e1)) f')).
   intros. simpl. easy.
   rewrite H5.
   rewrite IHe1.
   assert (exp_sem env0 e2 (exp_sem env0 (inv_exp e2) f) = exp_sem env0 (inv_exp e2 ; e2) f).
   simpl. easy.
   rewrite H6.
   rewrite IHe2. easy.
   inv H0. easy.
   inv H1. easy.
   inv H2. easy.
   inv H0. easy.
   inv H1. easy.
   inv H2. eapply right_mode_not_change_exp. apply H10. reflexivity.
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



Lemma typed_inv_pexp :
  forall p tenv tenv',
    well_typed_pexp tenv p tenv' ->
    well_typed_pexp tenv' (inv_pexp p) tenv.
Proof.
  induction p; intros; simpl; try assumption.
  simpl. inv H0.
  apply sexp_refl.
  apply typed_inv_sexp. easy.
  inv H0.
  econstructor. unfold Env.Equal in H4.
  specialize (H4 x).
  rewrite map_find_add in H4.
  apply Env.find_2 in H4. easy.
  unfold Env.Equal in *.
  intros.
  bdestruct (x =? y). subst.
  rewrite map_find_add.
  apply Env.find_1. assumption.
  rewrite map_find_neq.
  rewrite H4.
  rewrite map_find_neq. easy. lia. lia.
  inv H0.
  econstructor. unfold Env.Equal in H4.
  specialize (H4 x).
  rewrite map_find_add in H4.
  apply Env.find_2 in H4. easy.
  unfold Env.Equal in *.
  intros.
  bdestruct (x =? y). subst.
  rewrite map_find_add.
  apply Env.find_1. assumption.
  rewrite map_find_neq.
  rewrite H4.
  rewrite map_find_neq. easy. lia. lia.
  inv H0. apply h_had.
  unfold Env.Equal in H4.
  specialize (H4 x).
  rewrite map_find_add in H4.
  apply Env.find_2 in H4. easy.
  unfold Env.Equal in *.
  intros.
  bdestruct (x =? y). subst.
  rewrite map_find_add.
  apply Env.find_1. assumption.
  rewrite map_find_neq.
  rewrite H4.
  rewrite map_find_neq. easy. lia. lia.
  apply h_nor.
  unfold Env.Equal in H4.
  specialize (H4 x).
  rewrite map_find_add in H4.
  apply Env.find_2 in H4. easy.
  unfold Env.Equal in *.
  intros.
  bdestruct (x =? y). subst.
  rewrite map_find_add.
  apply Env.find_1. assumption.
  rewrite map_find_neq.
  rewrite H4.
  rewrite map_find_neq. easy. lia. lia.
  inv H0.
  econstructor.
  specialize (IHp2 env' tenv').
  apply IHp2. assumption.
  apply IHp1. easy.
Qed.

Lemma right_mode_inv_pexp :
  forall p tenv tenv' f,
    right_mode_pexp tenv f p tenv' ->
    right_mode_pexp tenv' f (inv_pexp p) tenv.
Proof.
  induction p; intros; simpl; try assumption.
  inv H0. constructor. 
  apply right_mode_inv_sexp. easy.
  inv H0. inv H6.
  eapply rqft_right. 
Admitted.

Lemma inv_exp_correct_rev :
  forall tenv env e f,
    exp_fwf e -> well_typed_exp tenv e -> right_mode_exp tenv f e ->
    exp_sem env (e; inv_exp e) f = f.
Proof.
  intros. apply fwf_inv_exp in H0.
  assert ((e; inv_exp e) = inv_exp (inv_exp e) ; inv_exp e).
  rewrite inv_exp_involutive. easy.
  rewrite H3.
  apply (inv_exp_correct tenv). assumption.
  apply typed_inv_exp. assumption.
  apply right_mode_inv_exp. assumption.
Qed.

Lemma sexp_sem_assoc : forall env f e1 e2 e3, 
               sexp_sem env (e1 ;; e2 ;; e3) f = sexp_sem env (e1 ;; (e2 ;; e3)) f.
Proof.
  intros. simpl. easy.
Qed.


Lemma inv_sexp_correct :
  forall tenv env e f,
    well_typed_sexp tenv e -> right_mode_sexp tenv f e ->
    sexp_sem env (inv_sexp e ;; e) f = f.
Proof.
  induction e; intros.
 - simpl.
   rewrite lr_shift_same. easy. 
 - simpl.
   rewrite rl_shift_same. easy. 
 - simpl.
   rewrite rev_twice_same. easy.
  - simpl. inv H0. inv H1.
    Check inv_exp_correct.
    specialize (inv_exp_correct tenv env0 s f H3 H5 H6) as eq1.
    simpl in eq1. easy.
 - assert (inv_sexp (e1;; e2) = inv_sexp e2;; inv_sexp e1). simpl. easy.
   rewrite H2.
   rewrite sexp_sem_assoc.
   assert (sexp_sem env0 (inv_sexp e2;; (inv_sexp e1;; (e1;; e2))) f
             = sexp_sem env0 (inv_sexp e1 ;; (e1 ;; e2)) (sexp_sem env0 (inv_sexp e2) f)).
   simpl. easy.
   rewrite H3.
   rewrite <- sexp_sem_assoc.
   assert ( forall f', sexp_sem env0 ((inv_sexp e1;; e1);; e2) f' = sexp_sem env0 e2 (sexp_sem env0 ((inv_sexp e1;; e1)) f')).
   intros. simpl. easy.
   rewrite H4.
   rewrite IHe1.
   assert (sexp_sem env0 e2 (sexp_sem env0 (inv_sexp e2) f) = sexp_sem env0 (inv_sexp e2 ;; e2) f).
   simpl. easy.
   rewrite H5.
   rewrite IHe2. easy.
   inv H0. easy.
   inv H1. easy.
   inv H0. easy.
   inv H1. eapply right_mode_not_change_sexp. apply H9. reflexivity.
Qed.

Lemma inv_sexp_correct_rev :
  forall tenv env e f,
    well_typed_sexp tenv e -> right_mode_sexp tenv f e ->
    sexp_sem env (e;; inv_sexp e) f = f.
Proof.
  intros.
  assert ((e;; inv_sexp e) = inv_sexp (inv_sexp e) ;; inv_sexp e).
  rewrite inv_sexp_involutive. easy.
  rewrite H2.
  apply (inv_sexp_correct tenv).
  apply typed_inv_sexp. easy.
  apply right_mode_inv_sexp. assumption.
Qed.

Lemma pexp_sem_assoc : forall env f e1 e2 e3, 
               prog_sem env (e1 ;;; e2 ;;; e3) f = prog_sem env (e1 ;;; (e2 ;;; e3)) f.
Proof.
  intros. simpl. easy.
Qed.

Lemma well_typed_right_mode :
       forall e tenv tenv' tenv'' f, well_typed_pexp tenv e tenv'
              -> right_mode_pexp tenv f e tenv'' -> tenv' = tenv''.
Proof.
  induction e;intros. 
(*
  inv H0. inv H1. easy.
  inv H0. inv H1. inv H7. easy.
  inv H0. inv H1. inv H7. easy.
  inv H0. inv H1. inv H7. easy.
  apply mapsto_always_same with (v1 := Nor) in H5. inv H5. easy.
  inv H1. inv H7.
  apply mapsto_always_same with (v1 := Nor) in H4. inv H4. easy. easy.
  inv H0. inv H1.
  specialize (IHe1 tenv env' env'0 f H5 H6).
  subst.
  apply (IHe2 env'0) with (f := f).
  easy. easy.
*)
Admitted.

Lemma right_mode_pexp_sem : forall e1 e2 tenv tenv' tenv'' f env,
     right_mode_pexp tenv f e1 tenv' -> right_mode_pexp tenv' f e2 tenv'' ->
       right_mode_pexp tenv' (prog_sem env e1 f) e2 tenv''.
Proof.
  induction e1; intros.
  simpl in *. inv H0. admit.
  simpl. inv H0. inv H7.
Admitted.


Lemma inv_pexp_correct_rev :
  forall e tenv tenv' env f,
    well_typed_pexp tenv e tenv' -> right_mode_pexp tenv f e tenv' ->
    prog_sem env (e;;; inv_pexp e) f = f.
Proof. 
  induction e; intros.
 - simpl. inv H0. inv H1.
    specialize (inv_sexp_correct_rev tenv' env0 s f H4 H5) as eq1.
    simpl in eq1. easy.
 - simpl. admit.
 - simpl. admit.
 - simpl. inv H1.
   erewrite had_twice_same. easy. apply H4.
 - assert (inv_pexp (e1;;; e2) = inv_pexp e2;;; inv_pexp e1). simpl. easy.
   rewrite H2.
   rewrite pexp_sem_assoc.
   assert (prog_sem env0 (e1;;; (e2;;; (inv_pexp e2;;; inv_pexp e1))) f
             = prog_sem env0 (e2 ;;; (inv_pexp e2 ;;; inv_pexp e1)) (prog_sem env0 (e1) f)).
   simpl. easy.
   rewrite H3.
   rewrite <- pexp_sem_assoc.
   assert ( forall f', prog_sem env0 ((e2;;; inv_pexp e2);;; inv_pexp e1) f'
            = prog_sem env0 (inv_pexp e1) (prog_sem env0 ((e2;;; inv_pexp e2)) f')).
   intros. simpl. easy.
   rewrite H4.
   inv H0. inv H1.
   rewrite (IHe2 env' tenv').
   assert (prog_sem env0 (inv_pexp e1) (prog_sem env0 e1 f) = prog_sem env0 (e1 ;;; inv_pexp e1) f).
   simpl. easy.
   rewrite H0.
   rewrite (IHe1 tenv env'). easy. easy.
   assert (env' = env'0). eapply well_typed_right_mode.
   apply H8. apply H9. subst. easy. easy.
   assert (env' = env'0). eapply well_typed_right_mode.
   apply H8. apply H9. subst.
   apply (right_mode_pexp_sem e1 e2 tenv). assumption. assumption.
Admitted.

Lemma inv_pexp_correct :
  forall e tenv tenv' env f,
    well_typed_pexp tenv e tenv' -> right_mode_pexp tenv f e tenv' ->
    prog_sem env (inv_pexp e ;;; e) f = f.
Proof. 
  intros.
  assert ((inv_pexp e;;; e) = (inv_pexp e;;; inv_pexp (inv_pexp e))).
  rewrite inv_pexp_involutive. easy.
  rewrite H2.
  eapply (inv_pexp_correct_rev (inv_pexp e) tenv' tenv).
  apply typed_inv_pexp. easy.
  apply right_mode_inv_pexp. easy.
Qed.


Lemma exp_sem_same_out:
   forall env0 e f g1 g2, exp_sem env0 e f = g1 -> exp_sem env0 e f = g2 -> g1 = g2.
Proof.
 intros env0 e.
 induction e;simpl; intros; subst; try easy.
Qed.

Lemma inv_exp_reverse :
  forall (tenv:env) (env0: var -> nat) e f g,
    exp_fwf e -> well_typed_exp tenv e -> right_mode_exp tenv f e ->
    exp_sem env0 e f = g ->
    exp_sem env0 (inv_exp e) g = f.
Proof.
  intros. specialize (inv_exp_correct_rev tenv env0 e f H0 H1 H2) as G.
  simpl in G.
  subst. easy.
Qed.

(*  Compilation to bcom. *)
(* Controlled rotation cascade on n qubits. *)


(* States that is useful in compiling RCIR+ to SQIR. *)
Definition id_fun := fun (i:nat) => i.


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

(*
Definition inter_num (size:nat) (t : varType) :=
   match t with NType => size
              | SType => size+1
   end.
*)

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


(* the compilation state properties with lemmas. *)
Definition vars_start_diff (vs: vars) :=
        forall x y,  x <> y -> start vs x <> start vs y.

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
Inductive exp_WF : vars -> exp -> Prop :=
      | skip_wf : forall vs p, snd p < vsize vs (fst p) -> exp_WF vs (SKIP p)
      | x_wf : forall vs p, snd p < vsize vs (fst p) -> exp_WF vs (X p)
      | cu_wf : forall vs p e, snd p < vsize vs (fst p) -> exp_WF vs e -> exp_WF vs (CU p e)
      | rz_wf : forall vs p q, snd p < vsize vs (fst p) -> exp_WF vs (RZ q p)
      | rrz_wf : forall vs p q, snd p < vsize vs (fst p) -> exp_WF vs (RRZ q p)
      | seq_wf : forall vs e1 e2, exp_WF vs e1 -> exp_WF vs e2 -> exp_WF vs (Seq e1 e2).


Fixpoint trans_exp (f : vars) (dim:nat) (exp:exp) : base_ucom dim :=
  match exp with SKIP p => SQIR.ID (find_pos f p)
              | X p => SQIR.X (find_pos f p)
              | RZ q p => SQIR.Rz (rz_ang q) (find_pos f p)
              | RRZ q p => SQIR.Rz (rrz_ang q) (find_pos f p)
              | CU p1 (X p2) => SQIR.CNOT (find_pos f p1) (find_pos f p2)
              | CU p e1 => control (find_pos f p) (trans_exp f dim e1)
              | e1 ; e2 => SQIR.useq (trans_exp f dim e1) (trans_exp f dim e2)
  end.

Definition exp_com_WF (vs:vars) (dim:nat) :=
    forall p, snd p < vsize vs (fst p) -> find_pos vs p < dim.

Fixpoint turn_angle (rval : nat -> bool) (n : nat) : R :=
  match n with 0 => (0:R)
            | S m => ((1/ (2^(Nat.b2n(rval m))))%R + turn_angle rval m)%R
  end.

Definition z_phase (b:bool) : R := if b then 1%R else (-1)%R.

Definition compile_val (v:val) (r_max : nat) : Vector 2 := 
   match v with nval b r => Cexp ((turn_angle r r_max)) .* ∣ Nat.b2n b ⟩
             | hval b1 b2 r => Cexp ((turn_angle r r_max)) .*
                              ((RtoC ((z_phase b1))) .* ∣0⟩ .+ (RtoC ((z_phase b2))) .* ∣1⟩)
             | qval r => (∣0⟩ .+ (Cexp ((turn_angle r r_max))) .* ∣1⟩)
  end.

Lemma WF_compile_val : forall v r, WF_Matrix (compile_val v r).
Proof.
  intros. unfold compile_val.
  destruct v;auto with wf_db.
Qed.

Hint Resolve WF_compile_val : wf_db.

Definition trans_state (avs : nat -> posi) (rmax : posi -> nat) (f : posi -> val) : (nat -> Vector 2) :=
        fun i => compile_val (f (avs i)) (rmax (avs i)).

Lemma WF_trans_state : forall avs r f i, WF_Matrix (trans_state avs r f i).
Proof.
  intros. unfold trans_state. auto with wf_db.
Qed.

Hint Resolve WF_trans_state : wf_db.

Lemma trans_exp_cu : forall vs dim p e, 
       (exists p1, e = X p1 /\ 
             trans_exp vs dim (CU p e) = SQIR.CNOT (find_pos vs p) (find_pos vs p1))
    \/ (trans_exp vs dim (CU p e) = ((control (find_pos vs p) (trans_exp vs dim e)))).
Proof.
  intros.
  simpl in *.
  destruct e. right. easy.
  left.
  exists p0. easy.
  right. easy.
  right. easy. right. easy. right. easy.
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
            = update (trans_state avs rmax f) (find_pos vs p) (compile_val v (rmax p)) x).
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

Definition size_env (vs : vars):= fun i => vsize vs i.

Lemma fresh_is_fresh :
  forall p e vs (dim:nat),
    exp_fresh p e -> exp_WF vs e ->
    snd p < vsize vs (fst p) ->
    vars_start_diff vs -> vars_finite_bij vs ->
    vars_sparse vs ->
      @is_fresh _ dim (find_pos vs p) ((trans_exp vs dim e)).
Proof.
  intros.
  remember (find_pos vs p) as q.
  generalize dependent vs.
  induction e; intros.
  subst.
  apply fresh_app1.
  inv H0. inv H1.
  apply find_pos_prop; try assumption.
  subst.
  apply fresh_app1.
  inv H0. inv H1.
  apply find_pos_prop; try assumption.
  specialize (trans_exp_cu vs dim p0 e) as eq1.
  destruct eq1. destruct H6. destruct H6.
  subst. rewrite H7.
  apply fresh_app2.
  inv H0. inv H1. inv H12.
  apply find_pos_prop; try assumption.
  apply find_pos_prop; try assumption.
  inv H1. inv H11. assumption.
  inv H0. inv H11. assumption.
  rewrite H6. rewrite Heqq.
  inv H1. inv H0.
  apply fresh_control.
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
  simpl.
  apply fresh_seq; try assumption.
  inv H1. inv H0.
  apply IHe1; try assumption. easy.
  inv H1. inv H0.
  apply IHe2; try assumption. easy. 
Qed.

Lemma trans_exp_uc_well_typed : forall e dim vs,     
     vars_start_diff vs -> vars_finite_bij vs ->
       vars_sparse vs -> exp_fwf e -> exp_WF vs e ->
            exp_com_WF vs dim ->  @uc_well_typed _ dim (((trans_exp vs dim e))).
Proof.
  induction e; intros.
  simpl. inv H4. constructor. apply H5. easy. 
  simpl. inv H4. constructor. apply H5. easy. 
  specialize (trans_exp_cu vs dim p e) as eq1.
  destruct eq1. destruct H6. destruct H6. subst. simpl.
  inv H4. constructor. apply H5. easy. 
  apply H5. inv H11. assumption.
  inv H3. inv H8.
  inv H11.
  apply find_pos_prop; try assumption.
  rewrite H6. 
  apply uc_well_typed_control.
  inv H3. inv H4.
  apply H5. easy.
  inv H3. inv H4.
  apply fresh_is_fresh; try assumption.
  inv H3. inv H4.
  apply IHe; try assumption.
  inv H4.
  simpl. constructor.
  apply H5. easy.
  inv H4.
  simpl. constructor.
  apply H5. easy.
  simpl. inv H3. inv H4.
  constructor.
  apply IHe1; try assumption.
  apply IHe2; try assumption.
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

Lemma trans_exp_cu_eval : forall vs dim p e, 
          vars_start_diff vs -> vars_finite_bij vs -> vars_sparse vs ->
                 exp_fwf (CU p e) ->
                 exp_WF vs (CU p e) -> exp_com_WF vs dim ->
                 (uc_eval ( (trans_exp vs dim (CU p e)))) = 
                    (uc_eval (control (find_pos vs p) ( (trans_exp vs dim e)))).
Proof.
  intros.
  specialize (trans_exp_cu vs dim p e) as eq1.
  destruct eq1.
  destruct H6. destruct H6. subst.
  simpl.
  rewrite uc_cnot_control. easy.
  inv H4. apply H5. easy.
  inv H4. inv H11. apply H5. easy.
  inv H3. inv H9. inv H4. inv H12. 
  apply find_pos_prop; try assumption.
  rewrite H6. easy.
Qed.

Inductive exp_rmax : (posi -> nat) -> exp -> Prop :=
      | skip_rmax : forall rs p, exp_rmax rs (SKIP p)
      | x_rmax : forall rs p, exp_rmax rs (X p)
      | cu_rmax : forall vs p e, exp_rmax vs e -> exp_rmax vs (CU p e)
      | rz_rmax : forall rs p q, q < rs p -> exp_rmax rs (RZ q p)
      | rrz_rmax : forall rs p q, q < rs p -> exp_rmax rs (RRZ q p)
      | seq_rmax : forall rs e1 e2, exp_rmax rs e1 -> exp_rmax rs e2 -> exp_rmax rs (Seq e1 e2).

Lemma turn_angle_add_same : forall n r q, q < n -> (turn_angle r n + rz_ang q)%R = (turn_angle (rotate r q) n)%R.
Proof.

Admitted.

Lemma turn_angle_add_r_same : forall n r q, q < n -> (turn_angle r n + rrz_ang q)%R = (turn_angle (r_rotate r q) n)%R.
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

Lemma trans_exp_sem :
  forall dim e f env rmax vs (avs : nat -> posi),
    vars_start_diff vs ->
    vars_finite_bij vs ->
    vars_sparse vs ->
    exp_fwf e ->
    exp_WF vs e ->
    exp_com_WF vs dim ->
    well_typed_exp env e ->
    right_mode_exp env f e ->
         (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
         (forall i, i < dim -> find_pos vs (avs i) = i) ->
         (forall i, i < dim -> snd (avs i) < vsize vs (fst (avs i))) ->
    exp_rmax rmax e ->
    dim > 0 ->
    (uc_eval ((trans_exp vs dim e))) × (vkron dim (trans_state avs rmax f)) 
                =  vkron dim (trans_state avs rmax (exp_sem (size_env vs) e f)).
Proof.
  intros dim e. induction e; intros.
  - simpl. rewrite denote_ID_1. Msimpl. easy.
    apply H5. inv H4. easy.
  - simpl.
    rewrite vkron_X. 
    assert (vkron dim (trans_state avs rmax (f [p |-> exchange (f p)])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p) (compile_val (exchange (f p)) (rmax p)))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). inv H4. easy. assumption. assumption. lia.
    rewrite H13.  rewrite vkron_split_up.
    assert ((σx × trans_state avs rmax f (find_pos vs p))
                 = compile_val (exchange (f p)) (rmax p)).
    { unfold trans_state.
      inv H4.
      rewrite H8 by assumption.
      inv H6. inv H7. inv H19.
      unfold exchange. 
      unfold compile_val.
      distribute_scale.
      destruct b0. simpl.
      autorewrite with ket_db. easy.
      simpl.
      autorewrite with ket_db. easy.
      apply (mapsto_always_same a Nor Had) in H15. inv H15. assumption.
      apply (mapsto_always_same a Nor Phi) in H15. inv H15. assumption.
      inv H7. inv H19.
      apply (mapsto_always_same a Nor Had) in H15. inv H15. assumption.
      unfold exchange.
      unfold compile_val.
      distribute_scale.
      autorewrite with ket_db.
      rewrite Mplus_comm. easy.
      apply (mapsto_always_same a Had Phi) in H15. inv H15. assumption.
      }
    rewrite H14. easy.
    intros.
    auto with wf_db.
    auto with wf_db.
    apply H5. inv H4. assumption.
    apply H5. inv H4. assumption.
    auto with wf_db.
  - rewrite trans_exp_cu_eval by assumption.
    rewrite control_correct.
    simpl. 
    assert (exists r', (trans_state avs rmax f) (find_pos vs p) = r' .* (ket (Nat.b2n (get_cua (f p))))).
    inv H3. inv H4.
    unfold trans_state. 
    rewrite H8 by assumption.
    inv H6. inv H7.
    apply (mapsto_always_same a Nor t) in H21. rewrite <- H21 in H22. 
    inv H22. unfold compile_val,get_cua.
    exists (Cexp (turn_angle r (rmax (a, b)))). easy. easy.
    destruct H13.
    rewrite Mmult_plus_distr_r.
    rewrite Mmult_assoc.
    specialize (IHe f env0 rmax vs avs).
    inv H3. inv H4. inv H6. inv H7.
    rewrite IHe; try easy.
    destruct (get_cua (f (a,b))) eqn:eq1.
    erewrite vkron_proj_neq.
    rewrite vkron_proj_eq with (r := x).
    Msimpl. easy. auto with wf_db. apply H5. easy.
    unfold trans_state in *. rewrite efresh_exp_sem_irrelevant. easy.
    rewrite H8; try easy.
    auto with wf_db.
    apply H5; easy. rewrite H13. reflexivity. easy.
    rewrite vkron_proj_eq with (r := x).
    rewrite vkron_proj_neq with (r := x) (b := false). Msimpl. easy.
    auto with wf_db.
    apply H5. easy.
    unfold trans_state in *. rewrite efresh_exp_sem_irrelevant. easy.
    rewrite H8; try easy. easy.
    auto with wf_db.
    apply H5; easy. rewrite H13. reflexivity. inv H11. easy.
    inv H3. inv H4.
    apply fresh_is_fresh; try easy.
    inv H3. inv H4.
    apply trans_exp_uc_well_typed; try easy.
  - simpl.
    rewrite vkron_Rz. 
    assert (vkron dim (trans_state avs rmax (f [p |-> times_rotate (f p) q])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p) (compile_val (times_rotate (f p) q) (rmax p)))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). inv H4. easy. assumption. assumption. lia.
    rewrite H13.  rewrite vkron_split_up.
    assert ((phase_shift (rz_ang q) × trans_state avs rmax f (find_pos vs p))
                 = compile_val (times_rotate (f p) q) (rmax p)).
    { unfold trans_state.
      inv H4.
      rewrite H8 by assumption.
      inv H6. inv H7. 
      apply (mapsto_always_same a t Nor) in H15. subst. inv H20.
      unfold times_rotate. destruct b0. 
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
      autorewrite with R_db. easy. easy.
      inv H7. 
      apply (mapsto_always_same a t Had) in H15. subst. inv H20.
      unfold compile_val,times_rotate. unfold rz_ang,z_phase.
      assert ((2 * PI / 2 ^ 1)%R = PI) by lra. rewrite H7.
      rewrite phase_pi. destruct b1. destruct b2.
      distribute_scale. gridify.
      rewrite Z_0_bit. rewrite Z_1_bit. easy.
      simpl. distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit.
      rewrite Mscale_assoc.
      assert (((-1)%R * (-1)%R)%C = C1) by lca.
      rewrite H15. Msimpl. easy.
      destruct b2.
      distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit. easy.
      simpl.
      distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit. 
      rewrite Mscale_assoc.
      assert (((-1)%R * (-1)%R)%C = C1) by lca.
      rewrite H15. Msimpl. easy. easy.
      inv H7.
      apply (mapsto_always_same a t Phi) in H15. subst. inv H20.
      unfold times_rotate,compile_val.
      distribute_scale. distribute_plus. distribute_scale.
      rewrite ket0_phase. rewrite ket1_phase.
      rewrite Mscale_assoc.
      rewrite <- Cexp_add.
      inv H11. rewrite turn_angle_add_same by easy. gridify.
      easy.
      }
    rewrite H14. easy.
    intros.
    auto with wf_db.
    auto with wf_db.
    apply H5. inv H4. assumption.
    apply H5. inv H4. assumption.
    auto with wf_db.
  - simpl.
    rewrite vkron_Rz. 
    assert (vkron dim (trans_state avs rmax (f [p |-> times_r_rotate (f p) q])) = 
                   vkron dim (update (trans_state avs rmax f)
                        (find_pos vs p) (compile_val (times_r_rotate (f p) q) (rmax p)))).
    erewrite vkron_eq. reflexivity. intros.
    apply (trans_state_update dim). inv H4. easy. assumption. assumption. lia.
    rewrite H13.  rewrite vkron_split_up.
    assert ((phase_shift (rrz_ang q) × trans_state avs rmax f (find_pos vs p))
                 = compile_val (times_r_rotate (f p) q) (rmax p)).
    { unfold trans_state.
      inv H4.
      rewrite H8 by assumption.
      inv H6. inv H7. 
      apply (mapsto_always_same a t Nor) in H15. subst. inv H20.
      unfold times_r_rotate. destruct b0. 
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
      inv H7. 
      apply (mapsto_always_same a t Had) in H15. subst. inv H20.
      unfold compile_val,times_r_rotate. unfold rrz_ang,z_phase.
      assert ((2 * PI - 2 * PI / 2 ^ 1)%R = PI) by lra. rewrite H7.
      rewrite phase_pi. destruct b1. destruct b2.
      distribute_scale. gridify.
      rewrite Z_0_bit. rewrite Z_1_bit. easy.
      simpl. distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit.
      rewrite Mscale_assoc.
      assert (((-1)%R * (-1)%R)%C = C1) by lca.
      rewrite H15. Msimpl. easy.
      destruct b2.
      distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit. easy.
      simpl.
      distribute_scale. gridify. distribute_scale.
      rewrite Z_0_bit. rewrite Z_1_bit. 
      rewrite Mscale_assoc.
      assert (((-1)%R * (-1)%R)%C = C1) by lca.
      rewrite H15. Msimpl. easy. easy.
      inv H7.
      apply (mapsto_always_same a t Phi) in H15. subst. inv H20.
      unfold times_r_rotate,compile_val.
      distribute_scale. distribute_plus. distribute_scale.
      rewrite ket0_phase. rewrite ket1_phase.
      rewrite Mscale_assoc.
      rewrite <- Cexp_add.
      inv H11. rewrite turn_angle_add_r_same by easy. gridify.
      easy.
      }
    rewrite H14. easy.
    intros.
    auto with wf_db.
    auto with wf_db.
    apply H5. inv H4. assumption.
    apply H5. inv H4. assumption.
    auto with wf_db.
  - simpl. inv H3. inv H4. inv H6. inv H7. inv H11.
    rewrite Mmult_assoc. rewrite (IHe1 f env0); try easy.
    rewrite (IHe2 (exp_sem (size_env vs) e1 f) env0); try easy.
    eapply right_mode_not_change_exp. apply H21. easy.
Qed.


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

Definition trans_lshift (f:vars) (x:var) :=
     match f x with (start, size,g,ag) => 
              fun i => if i =? x then (start, size,
                              shift_fun g 1 size,ashift_fun ag (size - 1) size) else f i
     end.

Definition trans_rshift (f:vars) (x:var) :=
     match f x with (start, size,g,ag) => 
              fun i => if i =? x then (start, size, 
               shift_fun g (size - 1) size,ashift_fun ag 1 size) else f i
     end.



Definition vars_anti_same (vs:vars) :=
     forall x, (forall i, i < vsize vs x -> vmap vs x i < vsize vs x) /\
     (forall i, i >= vsize vs x -> vmap vs x i >= vsize vs x) /\
     (forall i, i < vsize vs x -> avmap vs x i < vsize vs x) /\
     (forall i, i >= vsize vs x -> avmap vs x i >= vsize vs x) /\
     (forall i, vmap vs x (avmap vs x i) = i) /\ (forall i, avmap vs x (vmap vs x i) = i).









Inductive vars_WF : (list (var * nat)) -> Prop :=
    vars_WF_empty : vars_WF (List.nil)
    | vars_WF_many : forall x y xl, 0 < y -> vars_WF xl -> vars_WF ((x,y)::xl).

Fixpoint avars (l: list (var * nat)) (dim:nat) : (nat -> posi) :=
    match l with [] => fun i => (dim,dim)
              | (x,n):: l' => fun i => if (dim <? i) && (i - dim <? n) then (x, i - dim)
                                       else avars l' (dim + n) i
    end.
                                                                                   
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


Fixpoint trans_avs (f : vars) (dim:nat) (exp:exp) (avs: nat -> posi) : (vars  * (nat -> posi)) :=
  match exp with SKIP p => (f,avs)
              | X p => (f,avs)
              | RZ q p => (f,avs)
              | RRZ q p => (f,avs)
              | Lshift x => (trans_lshift f x,
                                   (fun i => if (start f x <=? i) && (i - start f x  <? vsize f x)
                                       then (x, avmap (trans_lshift f x) x (i - start f x)) else avs i))

              | Rshift x => (trans_rshift f x,
                                   (fun i => if (start f x <=? i) && (i - start f x <? vsize f x)
                            then (x,avmap (trans_rshift f x) x (i - start f x)) else avs i))
              | CU p e1 => trans_avs f dim e1 avs
              | e1 ; e2 => match trans_avs f dim e1 avs with (f',avs') => trans_avs f' dim e2 avs' end
  end.

Lemma trans_exp_avs_same : forall e f dim avs, snd (trans_exp f dim e) = fst (trans_avs f dim e avs).
Proof.
  induction e;intros.
  simpl. easy.
  simpl. easy.
  specialize (trans_exp_cu f dim p e) as eq1.
  destruct eq1. destruct H0. destruct H0. subst. simpl. easy.
  destruct (trans_exp f dim e) eqn:eq1.
  rewrite H0. simpl. rewrite <- IHe. rewrite eq1. easy.
  simpl. easy. simpl. easy.
  simpl. destruct (f x) eqn:eq1.
  destruct p eqn:eq2. simpl. easy.
  simpl. destruct (f x) eqn:eq1.
  destruct p eqn:eq2. simpl. easy.
  simpl.
  destruct (trans_exp f dim e1) eqn:eq1.
  destruct (trans_exp v dim e2) eqn:eq2.
  destruct (trans_avs f dim e1 avs) eqn:eq3.
  simpl in *. 
  specialize (IHe1 f dim avs).
  rewrite eq1 in IHe1. simpl in IHe1.
  rewrite eq3 in IHe1. simpl in IHe1. subst.
  specialize (IHe2 v1 dim p).
  rewrite eq2 in IHe2. simpl in IHe2.
  easy.
Qed.



(* Definition of the adder and the modmult in the language. *)
Definition CNOT (x y : posi) := CU x (X y).
Definition SWAP (x y : posi) := if (x ==? y) then (SKIP x) else (CNOT x y; CNOT y x; CNOT x y).
Definition CCX (x y z : posi) := CU x (CNOT y z).

Lemma cnot_fwf : forall x y, x<> y -> exp_fwf (CNOT x y).
Proof.
  intros.
  unfold CNOT. constructor.
  constructor. easy.
  constructor.
Qed.

Lemma swap_fwf : forall x y, exp_fwf (SWAP x y).
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

Lemma ccx_fwf : forall x y z, x <> y -> y <> z -> z <> x -> exp_fwf (CCX x y z).
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
Lemma cnot_sem : forall env f x y, nor_mode f x -> nor_mode f y -> 
              exp_sem env (CNOT x y) f = (f[y |-> put_cu (f y) (get_cua (f x) ⊕ get_cua (f y))]).
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

Lemma cnot_nor : forall env f x y v, nor_mode f x -> nor_mode f y -> 
          put_cu (f y) (get_cua (f x) ⊕ get_cua (f y)) = v
           -> exp_sem env (CNOT x y) f = (f[y |-> v]).
Proof.
  intros. subst. apply cnot_sem; assumption.
Qed.

Lemma cnot_nor_1 : forall env f f' x y v, nor_mode f x -> nor_mode f y -> 
          put_cu (f y) (get_cua (f x) ⊕ get_cua (f y)) = v
           -> f[y|-> v] = f'
           -> exp_sem env (CNOT x y) f = f'.
Proof.
  intros. subst. apply cnot_sem; assumption.
Qed.

Lemma ccx_sem : forall env f x y z, nor_mode f x -> nor_mode f y -> nor_mode f z
                     -> x <> y -> y <> z -> x <> z -> 
                    exp_sem env (CCX x y z) f = (f[z |-> put_cu (f z) (get_cua (f z) ⊕ (get_cua (f y) && get_cua (f x)))]).
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

Lemma ccx_nor : forall env f f' x y z v, nor_mode f x -> nor_mode f y -> nor_mode f z
                     -> x <> y -> y <> z -> x <> z -> 
                       put_cu (f z) (get_cua (f z) ⊕ (get_cua (f y) && get_cua (f x))) = v ->
                       f = f' ->
                    exp_sem env (CCX x y z) f = (f'[z |-> v]).
Proof.
 intros. subst. apply ccx_sem. 1 - 6: assumption. 
Qed.


Local Opaque CNOT. Local Opaque CCX.

Definition MAJ a b c := CNOT c b ; CNOT c a ; CCX a b c.
Definition UMA a b c := CCX a b c ; CNOT c a ; CNOT a b.

Lemma maj_fwf : forall x y z, x <> y -> y <> z -> z <> x -> exp_fwf (MAJ x y z).
Proof.
  intros.
  unfold MAJ.
  constructor.
  constructor. 
  apply cnot_fwf. nor_sym.
  apply cnot_fwf. easy.
  apply ccx_fwf; easy. 
Qed.

Lemma uma_fwf : forall x y z, x <> y -> y <> z -> z <> x -> exp_fwf (UMA x y z).
Proof.
  intros.
  unfold UMA.
  constructor.
  constructor. 
  apply ccx_fwf; easy. 
  apply cnot_fwf. easy.
  apply cnot_fwf. easy.
Qed.

Lemma MAJ_correct :
  forall a b c env f,
    nor_mode f a -> nor_mode f b -> nor_mode f c ->
    a <> b -> b <> c -> a <> c ->
    exp_sem env (MAJ c b a) f = (((f[a |-> put_cu (f a) (majb (get_cua (f a)) (get_cua (f b)) (get_cua (f c)))])
                              [b |-> put_cu (f b) (get_cua (f b) ⊕ get_cua (f a))])
                              [c |-> put_cu (f c) (get_cua (f c) ⊕ (get_cua (f a)))]).
(*Admitted. 
(* The following proof works, but too slow. Admitted when debugging. *)*)
Proof.
  intros ? ? ? ? ? HNa HNb HNc Hab' Hbc' Hac'.
  unfold MAJ.
  simpl.
  rewrite cnot_sem.
  rewrite cnot_sem.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite ccx_sem.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite get_put_cu by assumption.
  rewrite get_put_cu by assumption.
  apply functional_extensionality.
  intros.
  bdestruct (c ==? x).
  subst.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite xorb_comm. easy.
  bdestruct (x ==? a).
  subst.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  assert ((get_cua (f a)
   ⊕ (get_cua (f a) ⊕ get_cua (f b) && get_cua (f a) ⊕ get_cua (f c)))
    = (majb (get_cua (f a)) (get_cua (f b)) (get_cua (f c)))).
  unfold majb. btauto.
  rewrite H1. easy.
  bdestruct (x ==? b).
  subst.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite xorb_comm. easy.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  easy.
  rewrite eupdate_twice_neq by nor_sym.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up ; nor_sym.
  1-3:nor_sym. 1-2:assumption.
  rewrite cnot_sem by assumption.
  apply nor_mode_up ; nor_sym.
  rewrite cnot_sem by assumption.
  apply nor_mode_up ; nor_sym.
Qed.

(*
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
*)

Lemma UMA_correct_partial :
  forall a b c env f' fa fb fc,
    nor_mode f' a -> nor_mode f' b -> nor_mode f' c ->
    a <> b -> b <> c -> a <> c ->
    get_cua (f' a) = majb fa fb fc ->
    get_cua (f' b) = (fb ⊕ fa) -> get_cua (f' c) = (fc ⊕ fa) ->
    exp_sem env (UMA c b a) f' = (((f'[a |-> put_cu (f' a) fa])
                  [b |-> put_cu (f' b) (fa ⊕ fb ⊕ fc)])[c |-> put_cu (f' c) fc]).
(* Admitted.
(* The following proof works, but too slow. Admitted when debugging. *) *)
Proof.
  unfold majb. intros.
  unfold UMA.
  simpl.
  rewrite ccx_sem by (try assumption; try nor_sym).
  rewrite cnot_sem.
  rewrite cnot_sem.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite get_put_cu by assumption.
  rewrite get_put_cu by assumption.
  apply functional_extensionality.
  intros.
  bdestruct (x ==? c).
  subst.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  assert (((get_cua (f' a) ⊕ (get_cua (f' b) && get_cua (f' c))) ⊕ get_cua (f' c)) = fc).
  rewrite H6. rewrite H7. rewrite H8.
  btauto.
  rewrite H9. easy.
  bdestruct (x ==? b).
  subst.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  assert ((((get_cua (f' a) ⊕ (get_cua (f' b) && get_cua (f' c))) ⊕ get_cua (f' c))
   ⊕ get_cua (f' b)) = ((fa ⊕ fb) ⊕ fc)).
  rewrite H6. rewrite H7. rewrite H8.
  btauto.
  rewrite H10. easy.
  bdestruct (x ==? a).
  subst.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_eq.
  assert ((get_cua (f' a) ⊕ (get_cua (f' b) && get_cua (f' c))) = fa).
  rewrite H6. rewrite H7. rewrite H8.
  btauto.
  rewrite H11. easy.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  rewrite eupdate_index_neq by nor_sym.
  easy.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
  rewrite cnot_sem.
  apply nor_mode_up_1.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
  rewrite cnot_sem.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up ; nor_sym.
  apply nor_mode_up_1. assumption.
  apply nor_mode_up ; nor_sym.
Qed.

Local Transparent CNOT. Local Transparent CCX.

(*
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
*)

(* The following defines n-bits MAJ and UMA circuit. 
   Eventually, MAJ;UMA circuit takes [x][y] and produce [x][(x+y) % 2 ^ n] *)
Fixpoint MAJseq' n x y c : exp :=
  match n with
  | 0 => MAJ c (y,0) (x,0)
  | S m => MAJseq' m x y c; MAJ (x, m) (y, n) (x, n)
  end.
Definition MAJseq n x y c := MAJseq' (n - 1) x y c.

Lemma majseq'_fwf : forall n x y c,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf (MAJseq' n x y c).
Proof.
  intros.
  induction n. simpl.
  apply maj_fwf.
  iner_p. iner_p. iner_p.
  simpl.
  constructor.
  apply IHn.
  apply maj_fwf.
  1-3:iner_p.
Qed.

Lemma majseq_fwf : forall n x y c,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf (MAJseq n x y c).
Proof.
  intros. unfold MAJseq.
  apply majseq'_fwf; assumption.
Qed.

Fixpoint UMAseq' n x y c : exp :=
  match n with
  | 0 => UMA c (y,0) (x,0)
  | S m => UMA (x, m) (y,n) (x, n); UMAseq' m x y c
  end.
Definition UMAseq n x y c := UMAseq' (n - 1) x y c.

Lemma umaseq'_fwf : forall n x y c,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf (UMAseq' n x y c).
Proof.
  intros.
  induction n. simpl.
  apply uma_fwf.
  iner_p. iner_p. iner_p.
  simpl.
  constructor.
  apply uma_fwf.   1-3:iner_p.
  apply IHn.
Qed.

Lemma umaseq_fwf : forall n x y c,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf (UMAseq n x y c).
Proof.
  intros. unfold UMAseq.
  apply umaseq'_fwf; assumption.
Qed.


Definition adder01 n x y c: exp := MAJseq n x y c; UMAseq n x y c.

Lemma adder_fwf : forall n x y c,
       x <> fst c -> y <> fst c -> x <> y -> exp_fwf (adder01 n x y c).
Proof.
  intros. unfold adder01. constructor.
  apply majseq_fwf; assumption.
  apply umaseq_fwf; assumption.
Qed.

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

Lemma msma_0 : forall f x b g n, 0 < n -> nor_modes f x n -> put_cus f x (msma 0 b (get_cus n f x) g) n =
                     f[(x,0) |-> put_cu (f (x,0)) (carry b (S 0) (get_cus n f x) g)].
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
  unfold nor_modes in *. apply H1. lia. lia.
  intros R. inv R. contradiction.
  rewrite eupdate_index_neq. easy.
  intros R. inv R. lia.
  rewrite eupdate_index_neq. easy.
  apply iner_neq. lia.
Qed.

Lemma msmb_0 : forall S f b y n, 0 < n -> nor_modes S y n -> put_cus S y (msmb 0 b f (get_cus n S y)) n =
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
  rewrite eupdate_index_eq.
  rewrite get_cus_cua. easy. lia.
  rewrite eupdate_index_neq.
  rewrite get_cus_cua.
  rewrite put_get_cu. easy.
  unfold nor_modes in *. apply H1. lia. lia.
  intros R. inv R. lia.
  rewrite eupdate_index_neq. easy.
  intros R. inv R. lia.
  rewrite eupdate_index_neq. easy.
  apply iner_neq. lia.
Qed.

Local Opaque MAJ.

Local Opaque UMA.

Lemma MAJseq'_correct :
  forall i n env S x y c,
    0 < n -> i < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem env (MAJseq' i x y c) S = 
     (put_cus 
        (put_cus (S[c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x,0)))])
                   x (msma i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n)
          y (msmb i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n).
Proof.
  induction i; intros.
  - simpl. rewrite MAJ_correct.
    apply functional_extensionality.
    intros.
    bdestruct (x0 ==? c).
    subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_neq_1 by assumption.
    rewrite put_cus_neq_1 by assumption.
    rewrite eupdate_index_eq. easy.
    rewrite eupdate_index_neq by nor_sym.
    destruct x0.
    bdestruct (v =? y).
    subst.
    bdestruct (n0 <? n).
    rewrite put_cus_eq by assumption.
    rewrite put_cus_neq by assumption.
    unfold msmb.
    bdestruct (n0 =? 0).
    subst.
    rewrite eupdate_index_eq.
    bdestruct (0 <=? 0).
    rewrite eupdate_index_neq by nor_sym.
    rewrite get_cus_cua by lia.
    rewrite get_cus_cua by lia.
    rewrite xorb_comm. easy.
    lia.
    bdestruct (n0 <=? 0). lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by nor_sym.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu. easy.
    apply H3. easy.
    rewrite put_cus_out by lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    bdestruct (v =? x). subst.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_1 by nor_sym.
    bdestruct (n0 <? n).
    rewrite put_cus_eq by assumption.
    unfold msma.
    bdestruct (n0 =? 0).
    subst.
    rewrite eupdate_index_eq.
    bdestruct (0 <? 0). lia.
    rewrite eupdate_index_neq by nor_sym.
    rewrite carry_1.
    rewrite get_cus_cua by lia.
    rewrite get_cus_cua by lia. easy.
    bdestruct (n0 <? 0). lia.
    rewrite get_cus_cua by lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by nor_sym.
    rewrite put_get_cu. easy.
    apply H2. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_out by nor_sym.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    apply H2. lia.
    apply H3. lia.
    assumption.
    tuple_eq. destruct c. simpl in *.
    tuple_eq. destruct c. simpl in *. tuple_eq.
  - simpl. rewrite (IHi n).
    rewrite MAJ_correct.
    rewrite cus_get_eq.
    rewrite cus_get_neq by lia.
    rewrite cus_get_eq.
    rewrite cus_get_neq by lia.
    rewrite cus_get_eq.
    apply functional_extensionality.
    intros.
    destruct x0.
    bdestruct (n0 <? n). 
    bdestruct (v =? x). subst.
    bdestruct (n0 =? i).
    subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_neq by lia.
    rewrite (put_cus_neq (put_cus (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))]) x
     (msma (Datatypes.S i) (get_cua (S c)) (get_cus n S x) (get_cus n S y))
     n)) by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_eq by lia.
    rewrite <- (msm_eq1 n).
    rewrite put_cu_twice_eq.
    easy. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    bdestruct (n0 =? Datatypes.S i).
    subst. rewrite eupdate_index_eq.
    rewrite put_cus_neq by lia.
    rewrite (put_cus_neq (put_cus (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))]) x
     (msma (Datatypes.S i) (get_cua (S c)) (get_cus n S x) (get_cus n S y))
     n)) by lia.
    rewrite (put_cus_eq (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))])).
    rewrite (msm_eq3 n).
    rewrite put_cu_twice_eq.
    rewrite put_cus_eq by lia. easy.
    lia. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    unfold msma.
    bdestruct (n0 <? i).
    bdestruct (n0 <? Datatypes.S i).
    easy. lia.
    bdestruct (n0 =? i). lia.
    bdestruct (n0 <? Datatypes.S i). lia.
    bdestruct (n0 =? Datatypes.S i). lia.
    easy.
    rewrite eupdate_index_neq by tuple_eq.
    bdestruct (v =? y). subst.
    bdestruct (n0 =? Datatypes.S i). subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite (msm_eq2 n). easy. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    unfold msmb.
    bdestruct (n0 <=? i).
    bdestruct (n0 <=? Datatypes.S i). easy.
    lia.
    bdestruct (n0 <=? Datatypes.S i). lia. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia. easy. lia.
    unfold nor_modes. intros.
    apply nor_mode_up. 
    destruct c. simpl in *. tuple_eq.
    apply H2. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_up. 
    destruct c. simpl in *. tuple_eq.
    apply H2. lia. lia.
    unfold nor_modes. intros.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1. easy. 
    apply H3. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1. easy. 
    apply H2. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1. easy. 
    apply H3. lia.
    apply nor_mode_cus_eq.
    apply nor_mode_cus_eq.
    apply nor_mode_up.
    apply iner_neq_1. easy. 
    apply H2. lia.
    tuple_eq. tuple_eq. tuple_eq.
    lia. lia.
    unfold nor_modes. intros.
    apply H2. lia.
    unfold nor_modes. intros.
    apply H3. lia.
    apply H4. lia. lia. lia.
Qed.




Local Transparent carry.

Lemma UMAseq'_correct :
  forall i n env S x y c,
    0 < n -> i < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem env (UMAseq' i x y c) (put_cus 
        (put_cus (S[c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x,0)))])
                   x (msma i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n)
          y (msmc i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n) = 
         (put_cus S y (sumfb (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n).
Proof.
  induction i; intros. 
  - simpl.
    rewrite UMA_correct_partial with (fa := (get_cus n S x) 0) (fb := (get_cus n S y) 0)
                   (fc := carry (get_cua (S c)) 0 (get_cus n S x) (get_cus n S y)).
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite eupdate_index_neq.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq.
    simpl. 
    rewrite put_cus_neq_1 by nor_sym. 
    rewrite put_cus_neq_1 by nor_sym. 
    rewrite eupdate_index_eq.
    rewrite put_cu_twice_eq_1.
    apply functional_extensionality.
    intros.
    bdestruct (x0 ==? c). subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_neq_1 by lia.
    rewrite put_get_cu. easy.  assumption.
    rewrite eupdate_index_neq by nor_sym.
    destruct x0.
    bdestruct (v =? y).
    subst.
    bdestruct (n0 <? n).
    rewrite put_cus_eq by lia.
    bdestruct (n0 =? 0). subst.
    rewrite eupdate_index_eq.
    unfold sumfb. simpl.
    assert (((get_cus n S x 0 ⊕ get_cus n S y 0) ⊕ get_cua (S c)) 
          = ((get_cua (S c) ⊕ get_cus n S x 0) ⊕ get_cus n S y 0)) by btauto.
    rewrite H10. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    unfold sumfb.
    unfold msmc.
    bdestruct (n0 <=? 0). lia. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite eupdate_index_neq by nor_sym.
    rewrite put_cus_neq_2 by lia. easy.
    bdestruct (v =? x).
    subst.
    bdestruct (n0 <? n).
    rewrite put_cus_neq by lia.
    bdestruct (n0 =? 0). subst.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_eq.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu. easy. apply H2. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by nor_sym.
    rewrite put_cus_eq by lia.
    rewrite eupdate_index_neq by nor_sym.
    unfold msma.
    bdestruct ( n0 <? 0). lia.
    bdestruct (n0 =? 0). lia.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu. easy. apply H2. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite eupdate_index_neq by nor_sym.
    easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym. easy.
    destruct c. simpl in *. tuple_eq.
    destruct c. simpl in *. tuple_eq.
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
    simpl. rewrite get_cus_cua. easy. lia.
    assumption.
  - simpl.
    rewrite UMA_correct_partial with (fa := (get_cus n S x) (Datatypes.S i)) (fb := (get_cus n S y) (Datatypes.S i))
                   (fc := carry (get_cua (S c)) (Datatypes.S i) (get_cus n S x) (get_cus n S y)).
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite eupdate_index_neq.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cu_twice_eq.
    rewrite eupdate_index_neq.
    rewrite <- (IHi n env0).
    assert (((((put_cus
        (put_cus
           (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))]) x
           (msma (Datatypes.S i) (get_cua (S c)) 
              (get_cus n S x) (get_cus n S y)) n) y
        (msmc (Datatypes.S i) (get_cua (S c)) (get_cus n S x)
           (get_cus n S y)) n) [(x, Datatypes.S i)
     |-> S (x, Datatypes.S i)]) [(y, Datatypes.S i)
    |-> put_cu (S (y, Datatypes.S i))
          ((get_cua (S (x, Datatypes.S i)) ⊕ get_cus n S y (Datatypes.S i))
           ⊕ carry (get_cua (S c)) (Datatypes.S i) 
               (get_cus n S x) (get_cus n S y))]) [
   (x, i)
   |-> put_cu (S (x, i))
         (carry (get_cua (S c)) (Datatypes.S i) (get_cus n S x)
            (get_cus n S y))])
     = (put_cus
     (put_cus (S [c |-> put_cu (S c) (get_cua (S c) ⊕ get_cua (S (x, 0)))])
        x (msma i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n) y
     (msmc i (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n)).
    apply functional_extensionality.
    intros.
    bdestruct (x0 ==? c). subst.
    rewrite put_cus_neq_1 by nor_sym.
    rewrite put_cus_neq_1 by nor_sym.
    rewrite eupdate_index_neq.
    rewrite eupdate_index_neq.
    rewrite eupdate_index_neq.
    rewrite put_cus_neq_1 by nor_sym.
    rewrite put_cus_neq_1 by nor_sym.
    rewrite eupdate_index_eq. easy.
    1-3:apply iner_neq_1; lia.
    destruct x0.
    bdestruct (n0 <? n).
    bdestruct (v =? x). subst.
    rewrite put_cus_neq by lia.
    bdestruct (n0 =? i). subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_eq by lia.
    rewrite eupdate_index_neq by nor_sym.
    unfold msma.
    bdestruct (i <? i). lia.
    bdestruct (i =? i). easy. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_eq by lia.
    bdestruct (n0 =? Datatypes.S i).
    subst.
    rewrite eupdate_index_eq.
    rewrite eupdate_index_neq by nor_sym.
    unfold msma.
    bdestruct (Datatypes.S i <? i). lia.
    bdestruct (Datatypes.S i =? i). lia.
    rewrite get_cus_cua by lia.
    rewrite put_get_cu. easy.
    apply H2. lia.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    unfold msma.
    bdestruct (n0 <? i).
    bdestruct (n0 <? Datatypes.S i). easy. lia.
    bdestruct (n0 <? Datatypes.S i). lia.
    bdestruct (n0 =? i). lia.
    bdestruct (n0 =? Datatypes.S i). lia.
    easy.
    bdestruct (v =? y). subst.
    rewrite eupdate_index_neq by tuple_eq.
    bdestruct (n0 =? Datatypes.S i). subst.
    rewrite eupdate_index_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite eupdate_index_neq by nor_sym.
    unfold msmc.
    bdestruct (Datatypes.S i <=? i). lia.
    assert (((get_cua (S (x, Datatypes.S i)) ⊕ get_cus n S y (Datatypes.S i))
       ⊕ carry (get_cua (S c)) (Datatypes.S i) (get_cus n S x) (get_cus n S y))
     = ((carry (get_cua (S c)) (Datatypes.S i) (get_cus n S x) (get_cus n S y)
    ⊕ get_cus n S x (Datatypes.S i)) ⊕ get_cus n S y (Datatypes.S i))).
    rewrite <- (get_cus_cua n). btauto. lia.
    rewrite H12. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_eq by lia.
    rewrite put_cus_eq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    unfold msmc.
    bdestruct (n0 <=? i).
    bdestruct (n0 <=? Datatypes.S i). easy.
    lia. bdestruct (n0 <=? Datatypes.S i). lia. easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_neq by lia.
    easy.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite eupdate_index_neq by tuple_eq.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    rewrite put_cus_neq_2 by lia.
    easy.
    rewrite H8. rewrite IHi. easy.
    lia. lia.
    1-7:easy.
    lia.
    1-6:easy.
    apply neq_sym.
    apply iner_neq_1. assumption.
    apply neq_sym.
    apply iner_neq_1.
    assumption.
    apply H2. lia.
    apply neq_sym.
    apply iner_neq_1. assumption.
    apply nor_mode_cus_eq. 
    apply nor_mode_cus_eq. 
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H2. lia.
    apply nor_mode_cus_eq. 
    apply nor_mode_cus_eq. 
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H3. lia.
    apply nor_mode_cus_eq. 
    apply nor_mode_cus_eq. 
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H2. lia.
    1-3:tuple_eq.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite get_put_cu.
    unfold msma.
    bdestruct (Datatypes.S i <? Datatypes.S i). lia.
    bdestruct (Datatypes.S i =? Datatypes.S i).
    unfold majb.
    simpl. btauto. lia.
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H2. lia.
    rewrite put_cus_eq by lia.
    rewrite get_put_cu.
    unfold msmc.
    bdestruct (Datatypes.S i <=? Datatypes.S i).
    btauto.
    lia.
    apply nor_mode_cus_eq. 
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H3. lia.
    rewrite put_cus_neq by lia.
    rewrite put_cus_eq by lia.
    rewrite get_put_cu.
    unfold msma.
    bdestruct (i <? Datatypes.S i). easy. lia.
    apply nor_mode_up. apply iner_neq_1; assumption.
    apply H2. lia.
Qed.

(* adder correctness proofs. *)
Lemma adder01_correct_fb :
  forall n env S x y c,
    0 < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem env (adder01 n x y c) S = (put_cus S y (sumfb (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n).
Proof.
  intros. unfold adder01. unfold MAJseq, UMAseq.
  simpl.
  rewrite MAJseq'_correct with (n := n). 
  assert (forall S', put_cus S' y (msmb (n - 1) (get_cua (S c)) 
        (get_cus n S x) (get_cus n S y)) n = put_cus S' y (msmc (n - 1) (get_cua (S c)) 
        (get_cus n S x) (get_cus n S y)) n).
  intros. apply put_cus_sem_eq. intros.
  unfold msmb,msmc.
  bdestruct (m <=? n - 1). easy. lia.
  rewrite H7.
  apply UMAseq'_correct. assumption. lia. 1 - 6: assumption.
  apply H0. lia. 1 - 6 : assumption.
Qed.




Lemma efresh_trans_same: forall e dim vs vs' p, exp_fresh p e -> 
                vs' = (snd (trans_exp vs dim e)) ->
                 find_pos vs p = find_pos vs' p.
Proof.
 induction e; intros; subst.
 eauto. eauto.
 specialize (trans_exp_cu vs dim p e) as eq1.
 destruct eq1. destruct H1.
 destruct H1. subst. rewrite H2 in *.
 simpl in *. easy.
 destruct (trans_exp vs dim e) eqn:eq1.
 rewrite H1. simpl.
 apply (IHe dim). inv H0. easy.
 rewrite eq1. easy.
 inv H0. simpl. easy.
 inv H0. simpl. easy.
 inv H0. simpl.
 unfold find_pos,trans_lshift,shift_fun.
 destruct p.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2. 
 destruct p0 eqn:eq3.
 unfold start,vmap.
 bdestruct (v =? x). simpl in *. lia. easy.
 inv H0. simpl.
 unfold find_pos,trans_rshift,shift_fun.
 destruct p.
 destruct (vs x) eqn:eq1.
 destruct p eqn:eq2. 
 destruct p0 eqn:eq3. 
 unfold start,vmap.
 bdestruct (v =? x). simpl in *. lia. easy.
 inv H0. simpl.
 destruct (trans_exp vs dim e1) eqn:eq1.
 destruct (trans_exp v dim e2) eqn:eq2. simpl.
 specialize (IHe1 dim vs v p H4).
 rewrite IHe1.
 apply (IHe2 dim); try assumption.
 rewrite eq2. easy.
 rewrite eq1. easy.
Qed.

Lemma trans_exp_cu_snd_same : forall vs dim p e, 
         snd (trans_exp vs dim (CU p e)) = snd (trans_exp vs dim e).
Proof.
  intros.
  specialize (trans_exp_cu vs dim p e) as eq1.
  destruct eq1. destruct H0.
  destruct H0. subst.
  rewrite H1. simpl. easy.
  destruct (trans_exp vs dim e) eqn:eq1.
  rewrite H0. easy.
Qed.

Lemma vsize_vs_same: forall e dim vs vs' p, vs' = (snd (trans_exp vs dim e)) -> vsize vs' p = vsize vs p.
Proof.
 induction e; intros;subst; try easy.
 apply (IHe dim).
 rewrite trans_exp_cu_snd_same. easy.
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
 destruct (trans_exp vs dim e1) eqn:eq1.
 destruct (trans_exp v dim e2) eqn:eq2.
 simpl.
 specialize (IHe1 dim vs v p).
 rewrite eq1 in IHe1. simpl in IHe1.
 rewrite <- IHe1.
 rewrite (IHe2 dim v v0). easy.
 rewrite eq2. easy. easy.
Qed.

Lemma start_vs_same: forall e dim vs vs' p, vs' = (snd (trans_exp vs dim e)) -> start vs' p = start vs p.
Proof.
 induction e; intros;subst; try easy.
 apply (IHe dim).
 rewrite trans_exp_cu_snd_same. easy.
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
 destruct (trans_exp vs dim e1) eqn:eq1.
 destruct (trans_exp v dim e2) eqn:eq2.
 simpl.
 specialize (IHe1 dim vs v p).
 rewrite eq1 in IHe1. simpl in IHe1.
 rewrite <- IHe1.
 rewrite (IHe2 dim v v0). easy.
 rewrite eq2. easy. easy.
Qed.

Lemma wf_vs_same: forall e1 e2 dim vs vs', exp_WF vs e1 -> 
                vs' = (snd (trans_exp vs dim e2)) -> exp_WF vs' e1.
Proof.
  intros.
  induction H0. constructor.
  rewrite (vsize_vs_same e2 dim vs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs). easy. easy.
  apply IHexp_WF. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs). easy. easy.
  constructor.
  rewrite (vsize_vs_same e2 dim vs). easy. easy.
  constructor.
  apply IHexp_WF1. easy.
  apply IHexp_WF2. easy.
Qed.


Lemma vars_start_diff_vs_same : forall e dim vs vs', vs' = (snd (trans_exp vs dim e)) 
                    -> vars_start_diff vs -> vars_start_diff vs'.
Proof.
  intros.
  unfold vars_start_diff in *.
  intros.
  rewrite (start_vs_same e dim vs vs').
  rewrite (start_vs_same e dim vs vs').
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

Lemma vars_fun_lt : forall e dim vs vs' x, vs' = (snd (trans_exp vs dim e))
          -> (forall i, i < vsize vs x -> vmap vs x i < vsize vs x)
          -> (forall i, i < vsize vs x -> vmap vs' x i < vsize vs x).
Proof.
  induction e; intros.
  simpl in *. subst. apply H1. easy.
  simpl in *. subst. apply H1. easy.
  rewrite trans_exp_cu_snd_same in H0.
  specialize (IHe dim vs vs' x H0 H1).
  apply IHe. easy.
  simpl in *. subst. apply H1. easy.
  simpl in *. subst. apply H1. easy.
  simpl in *.
  unfold vmap,vsize in *.
  unfold trans_lshift in H0.
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
  unfold trans_rshift in H0.
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
  subst. simpl.
  destruct (trans_exp vs dim e1) eqn:eq1.
  destruct (trans_exp v dim e2) eqn:eq2. simpl.
  assert (v = snd (trans_exp vs dim e1)). rewrite eq1. easy.
  specialize (IHe1 dim vs v x H0 H1).
  assert (v0 = snd (trans_exp v dim e2)). rewrite eq2. easy.
  specialize (IHe2 dim v v0 x H3).
  assert ((forall i : nat,
        i < vsize v x -> vmap v x i < vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v). assumption. easy. easy.
  specialize (IHe2 H4).
  rewrite <- (vsize_vs_same e1 dim vs v).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v). easy.
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

Lemma vars_afun_lt : forall e dim vs vs' x, vs' = (snd (trans_exp vs dim e))
          -> (forall i, i < vsize vs x -> avmap vs x i < vsize vs x)
          -> (forall i, i < vsize vs x -> avmap vs' x i < vsize vs x).
Proof.
  induction e; intros.
  simpl in *. subst. apply H1. easy.
  simpl in *. subst. apply H1. easy.
  rewrite trans_exp_cu_snd_same in H0.
  specialize (IHe dim vs vs' x H0 H1).
  apply IHe. easy.
  simpl in *. subst. apply H1. easy.
  simpl in *. subst. apply H1. easy.
  simpl in *.
  unfold avmap,vsize in *.
  unfold trans_lshift in H0.
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
  unfold trans_rshift in H0.
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
  subst. simpl.
  destruct (trans_exp vs dim e1) eqn:eq1.
  destruct (trans_exp v dim e2) eqn:eq2. simpl.
  assert (v = snd (trans_exp vs dim e1)). rewrite eq1. easy.
  specialize (IHe1 dim vs v x H0 H1).
  assert (v0 = snd (trans_exp v dim e2)). rewrite eq2. easy.
  specialize (IHe2 dim v v0 x H3).
  assert ((forall i : nat,
        i < vsize v x -> avmap v x i < vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v). assumption. easy. easy.
  specialize (IHe2 H4).
  rewrite <- (vsize_vs_same e1 dim vs v).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v). easy.
  easy. easy.
Qed.

Lemma vars_fun_ge : forall e dim vs vs' x, vs' = (snd (trans_exp vs dim e))
          -> (forall i, i >= vsize vs x -> vmap vs x i >= vsize vs x)
          -> (forall i, i >= vsize vs x -> vmap vs' x i >= vsize vs x).
Proof.
  induction e; intros.
  simpl in *. subst. apply H1. easy.
  simpl in *. subst. apply H1. easy.
  rewrite trans_exp_cu_snd_same in H0.
  specialize (IHe dim vs vs' x H0 H1).
  apply IHe. easy.
  simpl in *. subst. apply H1. easy.
  simpl in *. subst. apply H1. easy.
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
  subst. simpl.
  destruct (trans_exp vs dim e1) eqn:eq1.
  destruct (trans_exp v dim e2) eqn:eq2. simpl.
  assert (v = snd (trans_exp vs dim e1)). rewrite eq1. easy.
  specialize (IHe1 dim vs v x H0 H1).
  assert (v0 = snd (trans_exp v dim e2)). rewrite eq2. easy.
  specialize (IHe2 dim v v0 x H3).
  assert ((forall i : nat,
        i >= vsize v x -> vmap v x i >= vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v). assumption. easy. easy.
  specialize (IHe2 H4).
  rewrite <- (vsize_vs_same e1 dim vs v).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v). easy.
  easy. easy.
Qed.

Lemma vars_afun_ge : forall e dim vs vs' x, vs' = (snd (trans_exp vs dim e))
          -> (forall i, i >= vsize vs x -> avmap vs x i >= vsize vs x)
          -> (forall i, i >= vsize vs x -> avmap vs' x i >= vsize vs x).
Proof.
  induction e; intros.
  simpl in *. subst. apply H1. easy.
  simpl in *. subst. apply H1. easy.
  rewrite trans_exp_cu_snd_same in H0.
  specialize (IHe dim vs vs' x H0 H1).
  apply IHe. easy.
  simpl in *. subst. apply H1. easy.
  simpl in *. subst. apply H1. easy.
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
  subst. simpl.
  destruct (trans_exp vs dim e1) eqn:eq1.
  destruct (trans_exp v dim e2) eqn:eq2. simpl.
  assert (v = snd (trans_exp vs dim e1)). rewrite eq1. easy.
  specialize (IHe1 dim vs v x H0 H1).
  assert (v0 = snd (trans_exp v dim e2)). rewrite eq2. easy.
  specialize (IHe2 dim v v0 x H3).
  assert ((forall i : nat,
        i >= vsize v x -> avmap v x i >= vsize v x)).
  intros.
  rewrite (vsize_vs_same e1 dim vs). apply IHe1.
  rewrite <- (vsize_vs_same e1 dim vs v). assumption. easy. easy.
  specialize (IHe2 H4).
  rewrite <- (vsize_vs_same e1 dim vs v).
  apply IHe2.
  rewrite (vsize_vs_same e1 dim vs v). easy.
  easy. easy.
Qed.


Definition exists_fun_bij (vs:vars) (x:var) := exists g : nat -> nat,
  (forall y : nat, y < vsize vs x -> g y < vsize vs x) /\
  (forall x0 : nat,
   x0 < vsize vs x -> g (vmap vs x x0) = x0) /\
  (forall y : nat, y < vsize vs x -> vmap vs x (g y) = y).


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

Lemma trans_same_bij:  forall e dim vs vs' x, 
    (forall i, i < vsize vs x -> vmap vs x i < vsize vs x) ->
      vs' = (snd (trans_exp vs dim e)) 
       -> 0 < vsize vs x ->
       exists_fun_bij vs x -> exists_fun_bij vs' x.
Proof.
  induction e; intros; subst.
  simpl in *. easy.
  simpl in *. easy.
  rewrite trans_exp_cu_snd_same.
  apply (IHe dim vs). easy. easy. assumption. easy.
  simpl in *. easy.
  simpl in *. easy.
  unfold exists_fun_bij in *.
  rewrite (vsize_vs_same (Lshift x) dim vs).
  simpl in *.
  destruct H3 as [g [Ht [Hf Hb]]].
  bdestruct (x =? x0). subst.
  unfold trans_lshift.
  destruct (vs x0) eqn:eq1.
  destruct p. destruct p.
  exists (ashift_fun g (n2 - 1) n2).
  split. intros.
  unfold vsize. rewrite eq1. simpl.
  Check shift_fun_lt.
  specialize (ashift_fun_lt g (n2-1) n2) as eq2.
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
  assert (1 <= n2).
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. lia.
  specialize (shift_fun_twice n0 g 1 n2 H3 H0 Ht Hf) as eq2.
  rewrite eq2. easy.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. easy. lia.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  assert (1 <= n2).
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. lia.
  Check ashift_fun_twice.
  specialize (ashift_fun_twice n0 g 1 n2 H3 H0 Ht Hb) as eq2.
  rewrite eq2. easy.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. easy.
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
  unfold exists_fun_bij in *.
  rewrite (vsize_vs_same (Rshift x) dim vs).
  simpl in *.
  destruct H3 as [g [Ht [Hf Hb]]].
  bdestruct (x =? x0). subst.
  unfold trans_rshift.
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
  assert (n2-1 <= n2) by lia.
  assert (ashift_fun g (n2 - (n2 - 1)) n2 (shift_fun n0 (n2 - 1) n2 x1) = 
            ashift_fun g 1 n2 (shift_fun n0 (n2 - 1) n2 x1)).
  assert (0 < n2).
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. lia.
  assert (n2 - (n2 - 1) = 1) by lia.
  rewrite H5. easy.
  rewrite <- H4.
  specialize (shift_fun_twice n0 g (n2-1) n2 H3 H0 Ht Hf) as eq2.
  rewrite eq2. easy.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. easy. lia.
  intros.
  unfold vmap.
  bdestruct (x0 =? x0). clear H3. simpl.
  assert (n2-1 <= n2) by lia.
  assert (shift_fun n0 (n2 - 1) n2 (ashift_fun g (n2-(n2 - 1)) n2 y) = 
            shift_fun n0 (n2 - 1) n2 (ashift_fun g 1 n2 y)).
  assert (0 < n2).
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. lia.
  assert (n2 - (n2 - 1) = 1) by lia.
  rewrite H5. easy.
  rewrite <- H4.
  Check ashift_fun_twice.
  specialize (ashift_fun_twice n0 g (n2-1) n2 H3 H0 Ht Hb) as eq2.
  rewrite eq2. easy.
  unfold vsize in H1. rewrite eq1 in H1. simpl in H1. easy.
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
  simpl in *.
  destruct (trans_exp vs dim e1) eqn:eq1.
  destruct (trans_exp v dim e2) eqn:eq2.
  simpl in *.
  assert (v = (snd (trans_exp vs dim e1))).
  rewrite eq1. easy.
  specialize (IHe1 dim vs v x H0 H1 H2 H3).
  assert ((forall i : nat, i < vsize v x -> vmap v x i < vsize v x) ).
  intros.
  rewrite (vsize_vs_same e1 dim vs).
  rewrite (vsize_vs_same e1 dim vs) in H4.
  apply (vars_fun_lt e1 dim). easy. apply H0. easy. easy. easy.
  assert (v0 = snd (trans_exp v dim e2)).
  rewrite eq2. easy.
  assert (0 < vsize v x).
  rewrite (vsize_vs_same e1 dim vs). easy. rewrite eq1. easy.
  specialize (IHe2 dim v v0 x H4 H5 H6 IHe1). easy.
Qed.

Lemma vars_finite_bij_vs_same : forall e dim vs vs', vs' = (snd (trans_exp vs dim e)) 
                    -> vars_finite_bij vs -> vars_finite_bij vs'.
Proof.
  intros. unfold vars_finite_bij in *.
  intros.
  unfold weak_finite_bijection in *.
  split.
  intros. specialize (H1 x).
  destruct H1.
  rewrite (vsize_vs_same e dim vs vs').
  apply (vars_fun_lt e dim vs). assumption. easy.
  rewrite <- (vsize_vs_same e dim vs vs'). easy. easy. easy.
  specialize (H1 x). destruct H1.
  bdestruct (vsize vs x =? 0).
  assert (vsize vs' x = 0).
  rewrite (vsize_vs_same e dim vs). easy. easy.
  destruct H2. exists x0.
  split. intros. lia.
  split. intros. lia.
  intros. lia.
  assert (0 < vsize vs x) by lia.
  specialize (trans_same_bij e dim vs vs' x H1 H0 H4 H2) as eq1. easy.
Qed.


Lemma vars_sparse_vs_same : forall e dim vs vs', vs' = (snd (trans_exp vs dim e)) 
                    -> vars_sparse vs -> vars_sparse vs'.
Proof.
  intros.
  unfold vars_sparse in *.
  intros.
  repeat rewrite (start_vs_same e dim vs vs') by easy.
  rewrite (vsize_vs_same e dim vs vs') in H3 by easy.
  rewrite (vsize_vs_same e dim vs vs') in H4 by easy.
  apply H1; easy.
Qed.

Lemma vars_vs_anti_bij :
    forall e dim vs vs' x, vs' = (snd (trans_exp vs dim e)) ->
     (forall i : nat, i < vsize vs x -> vmap vs x i < vsize vs x) ->
     (forall i : nat, i >= vsize vs x -> vmap vs x i >= vsize vs x) ->
    (forall i : nat, i < vsize vs x -> avmap vs x i < vsize vs x) ->
       (forall i : nat, i >= vsize vs x -> avmap vs x i >= vsize vs x) ->
      (forall i : nat, vmap vs x (avmap vs x i) = i) -> 
       (forall i : nat, avmap vs x (vmap vs x i) = i) ->
      (forall i : nat, vmap vs' x (avmap vs' x i) = i) /\ (forall i : nat, avmap vs' x (vmap vs' x i) = i).
Proof.
 induction e; intros.
 subst. simpl. easy.
 subst. simpl. easy.
 rewrite trans_exp_cu_snd_same in H0.
 apply (IHe dim vs vs' x) ; try easy.
 subst. simpl. easy.
 subst. simpl. easy.
 subst. simpl.
 split. intros.
 unfold trans_lshift.
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
 unfold trans_lshift.
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
 subst. simpl. split. intros.
 unfold trans_rshift.
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
 unfold trans_rshift.
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
 subst. simpl.
 destruct (trans_exp vs dim e1) eqn:eq1.
 destruct (trans_exp v dim e2) eqn:eq2. simpl.
 specialize (IHe1 dim vs v x).
 rewrite eq1 in IHe1.
 assert (v = snd (b, v)) by easy.
 specialize (IHe1 H0 H1 H2 H3 H4 H5 H6).
 specialize (IHe2 dim v v0 x).
 rewrite eq2 in IHe2.
 assert (v0 = snd (b0, v0)) by easy.
 apply IHe2 in H7. easy.
 rewrite (vsize_vs_same e1 dim vs).
 apply (vars_fun_lt e1 dim). rewrite eq1. easy. easy.
 rewrite eq1. easy.
 rewrite (vsize_vs_same e1 dim vs).
 apply (vars_fun_ge e1 dim). rewrite eq1. easy. easy.
 rewrite eq1. easy.
 rewrite (vsize_vs_same e1 dim vs).
 apply (vars_afun_lt e1 dim). rewrite eq1. easy. easy.
 rewrite eq1. easy.
 rewrite (vsize_vs_same e1 dim vs).
 apply (vars_afun_ge e1 dim). rewrite eq1. easy. easy.
 rewrite eq1. easy. easy. easy.
Qed.


Lemma vars_anti_vs_same: forall e dim vs vs', vs' = (snd (trans_exp vs dim e)) 
                    -> vars_anti_same vs -> vars_anti_same vs'.
Proof.
  intros.
  unfold vars_anti_same in *.
  intro x. specialize (H1 x).
  destruct H1.
  split.
  rewrite (vsize_vs_same e dim vs) by assumption.
  apply (vars_fun_lt e dim vs). easy. assumption.
  split.
  rewrite (vsize_vs_same e dim vs) by assumption.
  apply (vars_fun_ge e dim vs) ; easy.
  split.
  rewrite (vsize_vs_same e dim vs) by assumption.
  apply (vars_afun_lt e dim vs). easy. easy.
  split.
  rewrite (vsize_vs_same e dim vs) by assumption.
  apply (vars_afun_ge e dim vs) ; easy.
  destruct H2 as [H2 [H3 [H4 [H5 H6]]]].
  specialize (vars_vs_anti_bij e dim vs vs' x H0 H1 H2 H3 H4 H5 H6) as eq1.
  destruct eq1. easy.
Qed.



Check trans_exp.

Lemma exists_same_vs_var : forall e dim x n vs vs', vs' = (snd (trans_exp vs dim e)) ->
                  n < vsize vs x -> 
                 (exists n', n' < vsize vs x /\ find_pos vs' (x,n) = find_pos vs (x,n')).
Proof.
 induction e; intros.
 simpl in H0. subst.  exists n. easy.
 simpl in H0. subst.  exists n. easy.
 specialize (trans_exp_cu vs dim (x,n) e) as eq1.
 destruct eq1. destruct H2. destruct H2. subst.
 simpl. exists n. easy.
 rewrite trans_exp_cu_snd_same in H0.
 specialize (IHe dim x n vs vs' H0 H1). easy.
 simpl in H0. subst.  exists n. easy.
 simpl in H0. subst.  exists n. easy.
 specialize (start_vs_same (Lshift x) dim vs vs' x0 H0) as eq1.
 specialize (vsize_vs_same (Lshift x) dim vs vs' x0 H0) as eq2.
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
 exists (((n + 1) mod n3)).
 split.
 apply Nat.mod_bound_pos. lia. lia. easy. lia.
 exists n. 
 rewrite eq3. simpl. easy.
 exists n.
 split. easy.
 rewrite H0. simpl.
 unfold trans_lshift,vmap.
 destruct (vs x) eqn:eq3. destruct p. destruct p.
 bdestruct (x0 =? x). lia.
 easy.
 specialize (start_vs_same (Rshift x) dim vs vs' x0 H0) as eq1.
 specialize (vsize_vs_same (Rshift x) dim vs vs' x0 H0) as eq2.
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
 exists (((n + (n3 - 1)) mod n3)).
 split.
 apply Nat.mod_bound_pos. lia. lia. easy. lia. lia.
 exists n. 
 rewrite H0. simpl.
 unfold trans_rshift,vmap.
 destruct (vs x) eqn:eq3. destruct p. destruct p.
 bdestruct (x0 =? x). lia.
 easy.
 simpl in H0.
 destruct (trans_exp vs dim e1) eqn:eq1.
 destruct (trans_exp v dim e2) eqn:eq2.
 simpl in H0. subst.
 specialize (IHe2 dim x n v v0).
 rewrite eq2 in IHe2.
 assert (v0 = snd (b0, v0)) by easy.
 apply IHe2 in H0. destruct H0. destruct H0.
 specialize (IHe1 dim x x0 vs v).
 rewrite eq1 in IHe1. assert (v = snd (b,v)) by easy.
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

Lemma exp_com_WF_vs_same : forall e dim vs vs', vs' = (snd (trans_exp vs dim e)) 
          -> exp_com_WF vs dim -> exp_com_WF vs' dim.
Proof.
 induction e; intros.
 simpl in H0. subst. easy.
 simpl in H0. subst. easy.
 specialize (trans_exp_cu vs dim p e) as eq1.
 destruct eq1. destruct H2. destruct H2. subst.
 simpl. easy.
 apply (IHe dim vs). 
 rewrite trans_exp_cu_snd_same in H0. easy. easy.
 simpl in H0. subst. easy.
 simpl in H0. subst. easy.
 unfold exp_com_WF in *.
 intros.
 specialize (vsize_vs_same (Lshift x) dim vs vs' (fst p) H0) as eq1.
 rewrite eq1 in H2.
 specialize (exists_same_vs_var (Lshift x) dim (fst p) (snd p) vs vs' H0 H2) as eq5.
 destruct eq5. destruct H3.
 assert ((fst p, snd p) = p). destruct p. simpl. easy.
 rewrite H5 in H4. rewrite H4.
 apply H1. simpl. easy.
 unfold exp_com_WF in *.
 intros.
 specialize (vsize_vs_same (Rshift x) dim vs vs' (fst p) H0) as eq1.
 rewrite eq1 in H2.
 specialize (exists_same_vs_var (Rshift x) dim (fst p) (snd p) vs vs' H0 H2) as eq5.
 destruct eq5. destruct H3.
 assert ((fst p, snd p) = p). destruct p. simpl. easy.
 rewrite H5 in H4. rewrite H4.
 apply H1. simpl. easy.
 simpl in H0.
 destruct (trans_exp vs dim e1) eqn:eq1.
 destruct ( trans_exp v dim e2) eqn:eq2.
 simpl in H0.
 specialize (IHe1 dim vs v).
 specialize (IHe2 dim v v0).
 subst.
 apply IHe2. rewrite eq2. easy.
 apply IHe1. rewrite eq1. easy.
 assumption. 
Qed.


Lemma avs_bij_aux: forall e dim vs vs' avs avs', 
           vs' = fst (trans_avs vs dim e avs) -> 
           avs' = snd (trans_avs vs dim e avs) ->
          vars_anti_same vs ->
        (forall i, i < dim -> snd (avs i) < vsize vs (fst (avs i))) ->
         (forall i, i < dim -> snd (avs' i) < vsize vs (fst (avs' i))).
Proof.
  induction e; intros.
  simpl in *. subst. apply H3. easy.
  simpl in *. subst. apply H3. easy.
  simpl in H0. simpl in H1.
  apply (IHe dim vs vs' avs avs'); try assumption.
  simpl in *. subst. apply H3. easy.
  simpl in *. subst. apply H3. easy.
  rewrite <- trans_exp_avs_same in H0.
  apply (vars_anti_vs_same (Lshift x) dim vs vs') in H2.
  unfold vars_anti_same in H2.
  rewrite trans_exp_avs_same with (avs := avs) in H0.
  rewrite H1. simpl.
  bdestruct ((start vs x <=? i)).
  bdestruct ((i - start vs x <? vsize vs x)).
  simpl.
  destruct (H2 x) as [X1 [X2 [X3 [X4]]]].
  specialize (X3 ((i - start vs x))).
  rewrite <- trans_exp_avs_same in H0.
  rewrite (vsize_vs_same (Lshift x) dim vs vs') in X3.
  rewrite H0 in X3. simpl in X3. apply X3. lia. easy.
  simpl. apply H3. easy.
  simpl. apply H3. easy.
  easy.
  rewrite <- trans_exp_avs_same in H0.
  apply (vars_anti_vs_same (Rshift x) dim vs vs') in H2.
  unfold vars_anti_same in H2.
  rewrite trans_exp_avs_same with (avs := avs) in H0.
  rewrite H1. simpl.
  bdestruct ((start vs x <=? i)).
  bdestruct ((i - start vs x <? vsize vs x)).
  simpl.
  destruct (H2 x) as [X1 [X2 [X3 [X4]]]].
  specialize (X3 ((i - start vs x))).
  rewrite <- trans_exp_avs_same in H0.
  rewrite (vsize_vs_same (Rshift x) dim vs vs') in X3.
  rewrite H0 in X3. simpl in X3. apply X3. lia. easy.
  simpl. apply H3. easy.
  simpl. apply H3. easy.
  easy.
  simpl in H0. simpl in H1.
  destruct (trans_avs vs dim e1 avs) eqn:eq1.
  specialize (IHe1 dim vs v avs p).
  rewrite eq1 in IHe1.
  assert (v = fst (v,p)) by easy.
  assert (p = snd (v,p)) by easy.
  specialize (IHe1 H5 H6 H2 H3).
  apply (vars_anti_vs_same e1 dim vs v) in H2.
  specialize (IHe2 dim v vs' p avs').
  rewrite <- H0 in IHe2.
  rewrite <- H1 in IHe2.
  assert (vs' = vs') by easy. assert (avs' = avs') by easy.
  assert ((forall i : nat, i < dim -> snd (p i) < vsize v (fst (p i)))).
  intros. rewrite (vsize_vs_same e1 dim vs v). apply IHe1. easy.
  rewrite trans_exp_avs_same with (avs := avs). rewrite eq1. easy.
  specialize (IHe2 H7 H8 H2 H9).
  rewrite <- (vsize_vs_same e1 dim vs v). apply IHe2. easy.
  rewrite trans_exp_avs_same with (avs := avs). rewrite eq1. easy.
  rewrite trans_exp_avs_same with (avs := avs). rewrite eq1. easy.
Qed.

Lemma avs_bij : forall e dim vs vs' avs avs', 
           vs' = fst (trans_avs vs dim e avs) -> 
           avs' = snd (trans_avs vs dim e avs) ->
        vars_finite_bij vs -> vars_sparse vs -> vars_anti_same vs ->
         (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
         (forall i, i < dim -> find_pos vs (avs i) = i) ->
         (forall i, i < dim -> snd (avs i) < vsize vs (fst (avs i))) ->
         (forall i, snd i < vsize vs (fst i) -> avs' (find_pos vs' i) = i)
        /\ (forall i, i < dim -> find_pos vs' (avs' i) = i).
Proof.
  induction e; intros.
  simpl in H1. subst. easy.
  simpl in H1. subst. easy.
  simpl in H1.
  apply (IHe dim vs vs' avs avs') ; try assumption.
  simpl in H1. subst. easy.
  simpl in H1. subst. easy.
  split. intros.
  simpl in H1.
  rewrite H1.
  rewrite <- trans_exp_avs_same in H0.
  rewrite <- (start_vs_same (Lshift x) dim vs vs') by assumption.
  bdestruct ((start vs' x <=? find_pos vs' i)).
  bdestruct ((find_pos vs' i - start vs' x <? vsize vs x)). simpl.
  destruct i.
  bdestruct (x =? v). rewrite H11.
  unfold find_pos.
  assert ((start vs' v + vmap vs' v n - start vs' v) = vmap vs' v n) by lia.
  rewrite H12.
  rewrite H0.
  simpl. unfold trans_lshift.
  rewrite H11.
  destruct (vs v) eqn:eq1.
  destruct p. destruct p.
  unfold avmap,vmap.
  bdestruct (v =? v). simpl.
  unfold vars_anti_same in H4.
  specialize (H4 v).
  destruct H4 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite shift_fun_twice. easy.
  unfold vsize in H8. simpl in H8.
  rewrite eq1 in H8. simpl in H8. lia.
  unfold vmap,vsize in X1.
  rewrite eq1 in X1. simpl in X1. easy.
  unfold avmap,vsize in X3.
  rewrite eq1 in X3. simpl in X3. easy.
  unfold avmap,vmap in X6.
  rewrite eq1 in X6. simpl in X6. intros. easy.
  unfold vsize in H8. simpl in H8. rewrite eq1 in H8. easy. lia. 
  apply (vars_sparse_vs_same (Lshift x) dim vs vs' H0) in H3.
  unfold vars_sparse in H3.
  specialize (H3 x v H11).
  rewrite (vsize_vs_same (Lshift x) dim vs vs') in H3.
  rewrite (vsize_vs_same (Lshift x) dim vs vs') in H3.
  simpl in H8.
  unfold vars_anti_same in H4.
  specialize (H4 v).
  destruct H4 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  specialize (vars_fun_lt (Lshift x) dim vs vs' v H0 X1) as eq1.
  apply eq1 in H8.
  specialize (H3 (find_pos vs' (v, n) - start vs' x) (vmap vs' v n) H10 H8).
  assert (start vs' x + (find_pos vs' (v, n) - start vs' x) = find_pos vs' (v, n)) by lia.
  rewrite H4 in H3.
  unfold find_pos in H3. contradiction. easy. easy.
  simpl.
  assert (fst i <> x).
  intros R.
  unfold find_pos in H10.
  unfold find_pos in H9.
  destruct i. simpl in R.
  rewrite R in *.
  assert (start vs' x + vmap vs' x n - start vs' x  = vmap vs' x n) by lia.
  rewrite H11 in H10. simpl in H8.
  apply (vars_anti_vs_same (Lshift x) dim vs vs' H0) in H4.
  specialize (H4 x).
  destruct H4 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite (vsize_vs_same (Lshift x) dim vs) in X1.
  apply X1 in H8. lia. easy.
  subst. unfold find_pos.
  destruct i. simpl.
  unfold trans_lshift,start,vmap.
  destruct (vs x) eqn:eq1.
  destruct p. destruct p. 
  bdestruct (v =? x). simpl in H11. lia. simpl.
  assert (fst (fst (fst (vs v))) + snd (fst (vs v)) n = find_pos vs (v,n)).
  unfold find_pos,start,vmap. easy.
  rewrite H1. rewrite H5. easy. lia.
  simpl.
  assert (fst i <> x).
  intros R.
  unfold find_pos in H9.
  destruct i. simpl in R. subst. lia.
  subst. unfold find_pos.
  destruct i. simpl.
  unfold trans_lshift,start,vmap.
  destruct (vs x) eqn:eq1.
  destruct p. destruct p. 
  bdestruct (v =? x). simpl in H10. lia. simpl.
  assert (fst (fst (fst (vs v))) + snd (fst (vs v)) n = find_pos vs (v,n)).
  unfold find_pos,start,vmap. easy.
  rewrite H1. rewrite H5. easy. lia.
  intros.
  simpl in H1.
  rewrite H1.
  bdestruct (((start vs x <=? i))).
  bdestruct ((i - start vs x <? vsize vs x)). simpl.
  rewrite (start_vs_same (Lshift x) dim vs vs') by assumption.
  rewrite H0.
  simpl.
  unfold vmap,avmap,trans_lshift.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x =? x). simpl.
  assert (eq2 := H10).
  unfold vsize in eq2. rewrite eq1 in eq2. simpl in eq2.
  assert (shift_fun n0 1 n2 (ashift_fun n (n2 - 1) n2 (i - start vs x)) 
         = shift_fun n0 (n2 - (n2 -1)) n2 (ashift_fun n (n2 - 1) n2 (i - start vs x))).
  assert (n2 - (n2 -1) = 1) by lia. rewrite H12. easy.
  rewrite H12.
  unfold vars_anti_same in H4.
  specialize (H4 x).
  unfold vsize,vmap,avmap in H4.
  rewrite eq1 in H4. simpl in H4.
  rewrite (shift_fun_back_1); try easy.
  lia. lia. lia. 
  simpl.
  assert (x <> fst (avs i)).
  intros R.
  rewrite R in H9. rewrite R in H10.
  unfold find_pos in H6.
  specialize (H6 i H8).
  destruct (avs i) eqn:eq1.
  simpl in H9. simpl in H10.
  assert ( i - start vs v = vmap vs v n) by lia.
  rewrite H11 in H10.
  specialize (H7 i H8).
  rewrite eq1 in H7. simpl in H7.
  unfold vars_anti_same in H4.
  specialize (H4 v). destruct H4.
  apply H4 in H7. lia.
  rewrite H0. simpl.
  unfold trans_lshift,find_pos,start,vmap.
  destruct (avs i) eqn:eq1.
  destruct (vs x) eqn:eq2.
  destruct p. destruct p.
  bdestruct (v =? x). simpl in H11. lia.
  assert (fst (fst (fst (vs v))) + snd (fst (vs v)) n = find_pos vs (avs i)).
  rewrite eq1. unfold find_pos,start,vmap. easy.
  rewrite H13. rewrite H6. easy. lia. 
  simpl.
  assert (x <> fst (avs i)).
  intros R.
  specialize (H6 i H8).
  unfold find_pos in H6.
  destruct (avs i) eqn:eq1.
  simpl in R. rewrite R in H9. lia.
  rewrite H0. simpl.
  unfold trans_lshift,find_pos,start,vmap.
  destruct (avs i) eqn:eq1.
  destruct (vs x) eqn:eq2.
  destruct p. destruct p.
  bdestruct (v =? x). simpl in H10. lia.
  assert (fst (fst (fst (vs v))) + snd (fst (vs v)) n = find_pos vs (avs i)).
  rewrite eq1. unfold find_pos,start,vmap. easy.
  rewrite H12. rewrite H6. easy. lia. 
  split. intros.
  simpl in H1.
  rewrite H1.
  rewrite <- trans_exp_avs_same in H0.
  rewrite <- (start_vs_same (Rshift x) dim vs vs') by assumption.
  bdestruct ((start vs' x <=? find_pos vs' i)).
  bdestruct ((find_pos vs' i - start vs' x <? vsize vs x)). simpl.
  destruct i.
  bdestruct (x =? v). rewrite H11.
  unfold find_pos.
  assert ((start vs' v + vmap vs' v n - start vs' v) = vmap vs' v n) by lia.
  rewrite H12.
  rewrite H0.
  simpl. unfold trans_rshift.
  rewrite H11.
  destruct (vs v) eqn:eq1.
  destruct p. destruct p.
  unfold avmap,vmap.
  bdestruct (v =? v). simpl.
  unfold vars_anti_same in H4.
  specialize (H4 v).
  unfold vsize,vmap,avmap in H4. rewrite eq1 in H4. simpl in H4.
  destruct H4 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite shift_fun_back; try easy.
  unfold vsize in H8. simpl in H8.
  rewrite eq1 in H8. simpl in H8. lia.
  lia. 
  apply (vars_sparse_vs_same (Rshift x) dim vs vs' H0) in H3.
  unfold vars_sparse in H3.
  specialize (H3 x v H11).
  rewrite (vsize_vs_same (Rshift x) dim vs vs') in H3.
  rewrite (vsize_vs_same (Rshift x) dim vs vs') in H3.
  simpl in H8.
  unfold vars_anti_same in H4.
  specialize (H4 v).
  destruct H4 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  specialize (vars_fun_lt (Rshift x) dim vs vs' v H0 X1) as eq1.
  apply eq1 in H8.
  specialize (H3 (find_pos vs' (v, n) - start vs' x) (vmap vs' v n) H10 H8).
  assert (start vs' x + (find_pos vs' (v, n) - start vs' x) = find_pos vs' (v, n)) by lia.
  rewrite H4 in H3.
  unfold find_pos in H3. contradiction. easy. easy.
  simpl.
  assert (fst i <> x).
  intros R.
  unfold find_pos in H10.
  unfold find_pos in H9.
  destruct i. simpl in R.
  rewrite R in *.
  assert (start vs' x + vmap vs' x n - start vs' x  = vmap vs' x n) by lia.
  rewrite H11 in H10. simpl in H8.
  apply (vars_anti_vs_same (Rshift x) dim vs vs' H0) in H4.
  specialize (H4 x).
  destruct H4 as [X1 [X2 [X3 [X4 [X5 X6]]]]].
  rewrite (vsize_vs_same (Rshift x) dim vs) in X1.
  apply X1 in H8. lia. easy.
  subst. unfold find_pos.
  destruct i. simpl.
  unfold trans_rshift,start,vmap.
  destruct (vs x) eqn:eq1.
  destruct p. destruct p. 
  bdestruct (v =? x). simpl in H11. lia. simpl.
  assert (fst (fst (fst (vs v))) + snd (fst (vs v)) n = find_pos vs (v,n)).
  unfold find_pos,start,vmap. easy.
  rewrite H1. rewrite H5. easy. lia.
  simpl.
  assert (fst i <> x).
  intros R.
  unfold find_pos in H9.
  destruct i. simpl in R. subst. lia.
  subst. unfold find_pos.
  destruct i. simpl.
  unfold trans_rshift,start,vmap.
  destruct (vs x) eqn:eq1.
  destruct p. destruct p. 
  bdestruct (v =? x). simpl in H10. lia. simpl.
  assert (fst (fst (fst (vs v))) + snd (fst (vs v)) n = find_pos vs (v,n)).
  unfold find_pos,start,vmap. easy.
  rewrite H1. rewrite H5. easy. lia.
  intros.
  simpl in H1.
  rewrite H1.
  bdestruct (((start vs x <=? i))).
  bdestruct ((i - start vs x <? vsize vs x)). simpl.
  rewrite (start_vs_same (Rshift x) dim vs vs') by assumption.
  rewrite H0.
  simpl.
  unfold vmap,avmap,trans_rshift.
  destruct (vs x) eqn:eq1. destruct p. destruct p.
  bdestruct (x =? x). simpl.
  assert (eq2 := H10).
  unfold vsize in eq2. rewrite eq1 in eq2. simpl in eq2.
  unfold vars_anti_same in H4.
  specialize (H4 x).
  unfold vsize,vmap,avmap in H4.
  rewrite eq1 in H4. simpl in H4.
  rewrite (shift_fun_back_1); try easy.
  lia. lia. lia. 
  simpl.
  assert (x <> fst (avs i)).
  intros R.
  rewrite R in H9. rewrite R in H10.
  unfold find_pos in H6.
  specialize (H6 i H8).
  destruct (avs i) eqn:eq1.
  simpl in H9. simpl in H10.
  assert ( i - start vs v = vmap vs v n) by lia.
  rewrite H11 in H10.
  specialize (H7 i H8).
  rewrite eq1 in H7. simpl in H7.
  unfold vars_anti_same in H4.
  specialize (H4 v). destruct H4.
  apply H4 in H7. lia.
  rewrite H0. simpl.
  unfold trans_rshift,find_pos,start,vmap.
  destruct (avs i) eqn:eq1.
  destruct (vs x) eqn:eq2.
  destruct p. destruct p.
  bdestruct (v =? x). simpl in H11. lia.
  assert (fst (fst (fst (vs v))) + snd (fst (vs v)) n = find_pos vs (avs i)).
  rewrite eq1. unfold find_pos,start,vmap. easy.
  rewrite H13. rewrite H6. easy. lia. 
  simpl.
  assert (x <> fst (avs i)).
  intros R.
  specialize (H6 i H8).
  unfold find_pos in H6.
  destruct (avs i) eqn:eq1.
  simpl in R. rewrite R in H9. lia.
  rewrite H0. simpl.
  unfold trans_rshift,find_pos,start,vmap.
  destruct (avs i) eqn:eq1.
  destruct (vs x) eqn:eq2.
  destruct p. destruct p.
  bdestruct (v =? x). simpl in H10. lia.
  assert (fst (fst (fst (vs v))) + snd (fst (vs v)) n = find_pos vs (avs i)).
  rewrite eq1. unfold find_pos,start,vmap. easy.
  rewrite H12. rewrite H6. easy. lia.
  simpl in H0. simpl in H1. 
  destruct (trans_avs vs dim e1 avs) eqn:eq1.
  specialize (IHe1 dim vs v avs p).
  rewrite eq1 in IHe1.
  assert (v = fst (v, p)) by easy.
  assert (p = snd (v, p)) by easy.
  specialize (IHe1 H8 H9 H2 H3 H4 H5 H6 H7).
  destruct IHe1.
  specialize (IHe2 dim v vs' p avs').
  rewrite <- H0 in IHe2. rewrite <- H1 in IHe2.
  assert (vs' = vs') by easy.
  assert (avs' = avs') by easy.
  assert (v = snd (trans_exp vs dim e1)).
  erewrite trans_exp_avs_same. rewrite eq1. easy.
  specialize (avs_bij_aux e1 dim vs v avs p) as eq2.
  rewrite eq1 in eq2.
  specialize (eq2 H8 H9 H4 H7).
  apply (vars_finite_bij_vs_same e1 dim vs v H14) in H2.
  apply (vars_sparse_vs_same e1 dim vs v H14) in H3.
  apply (vars_anti_vs_same e1 dim vs v H14) in H4.
  assert ((forall i : var * nat,
        snd i < vsize v (fst i) -> p (find_pos v i) = i)).
  intros. apply H10.
  rewrite <- (vsize_vs_same e1 dim vs v). easy. easy.
  assert ((forall i : nat, i < dim -> snd (p i) < vsize v (fst (p i)))).
  intros.
  rewrite (vsize_vs_same e1 dim vs v). apply eq2. easy.
  rewrite trans_exp_avs_same with (avs := avs). rewrite eq1. easy.
  specialize (IHe2 H12 H13 H2 H3 H4 H15 H11 H16).
  split. intros. destruct IHe2. apply H18.
  rewrite (vsize_vs_same e1 dim vs v). easy.
  rewrite trans_exp_avs_same with (avs := avs). rewrite eq1. easy.
  easy.
Qed.

   
(*   
Lemma finite_bij_lt : forall vs, vars_finite_bij vs 
         -> (forall x i, i < vsize vs x -> vmap vs x i < vsize vs x).
Proof.
  intros. unfold vars_finite_bij in H0.
  unfold weak_finite_bijection in H0.
  destruct (H0 x).
  apply H2. easy.
Qed.

    vs' = snd ((trans_exp vs dim e)) ->
    (forall i, snd i < vsize vs (fst i) -> avs (find_pos vs i) = i) ->
    (forall i, i < dim -> find_pos vs (avs i) = i) ->
*)

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

Lemma efresh_trans_avs_same: forall e f dim vs avs avs' rmax p, 
    vars_sparse vs -> vars_anti_same vs -> 
       exp_fresh p e -> (snd p < vsize vs (fst p)) ->
                avs' = (snd (trans_avs vs dim e avs)) ->
                 (trans_state avs' rmax f) (find_pos vs p)
                        = (trans_state avs rmax f) (find_pos vs p).
Proof.
 induction e; intros; subst.
 simpl. eauto. simpl. easy.
 simpl. rewrite (IHe f dim vs avs). easy. inv H2. easy. easy.
 inv H2. easy. assumption. easy.
 simpl. eauto. simpl. eauto.
 inv H2. simpl.
 unfold trans_state.
 specialize (var_not_over_lap_1 x p vs H0 H1 H3 H6) as eq1. 
 bdestruct ((start vs x <=? find_pos vs p)). 
 bdestruct ((find_pos vs p - start vs x <? vsize vs x)). lia.
 simpl. easy.
 simpl. easy.
 inv H2. simpl.
 unfold trans_state.
 specialize (var_not_over_lap_1 x p vs H0 H1 H3 H6) as eq1. 
 bdestruct ((start vs x <=? find_pos vs p)). 
 bdestruct ((find_pos vs p - start vs x <? vsize vs x)). lia.
 simpl. easy.
 simpl. easy.
 simpl.
 inv H2.
 destruct (trans_avs vs dim e1 avs) eqn:eq1.
 specialize (IHe1 f dim vs avs p0 rmax p H0 H1 H7 H3).
 rewrite eq1 in IHe1. assert (p0 = snd (v, p0)) by easy.
 specialize (IHe1 H2).
 remember ((snd (trans_avs v dim e2 p0))) as avs'.
 specialize (IHe2 f dim v p0 avs' rmax p).
 assert (v = fst (trans_avs vs dim e1 avs)). rewrite eq1. easy.
 rewrite <- trans_exp_avs_same in H4.
 apply (vars_sparse_vs_same e1 dim vs v H4) in H0.
 apply (vars_anti_vs_same e1 dim vs v H4) in H1.
 rewrite <- (vsize_vs_same e1 dim vs v) in H3.
 specialize (IHe2 H0 H1 H8 H3 Heqavs').
 rewrite <- IHe1.
 rewrite (efresh_trans_same e1 dim vs v).
 1-4: easy. 
Qed.






(* here, backs to mod-multiplier proofs. *)

Lemma adder01_nor_fb :
  forall n env S S' x y c,
    0 < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    S' = (put_cus S y (sumfb (get_cua (S c)) (get_cus n S x) (get_cus n S y)) n) ->
    exp_sem env S (adder01 n x y c) S'.
Proof.
  intros.
  subst. apply adder01_correct_fb. 1-7:assumption.
Qed.

Check put_cus.

Definition reg_push (f : posi -> val)  (x : var) (v:nat) (n : nat) : posi -> val := put_cus f x (nat2fb v) n.


Lemma reg_push_exceed :
  forall n x v f,
    reg_push f x v n = reg_push f x (v mod 2^n) n.
Proof.
  intros. unfold reg_push. unfold nat2fb.
  apply put_cus_sem_eq. intros.
  rewrite Nofnat_mod. 2: apply Nat.pow_nonzero; lia.
  rewrite Nofnat_pow. simpl.
  do 2 rewrite N2fb_Ntestbit. rewrite N.mod_pow2_bits_low. easy. lia.
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


Lemma pos2fb_bound : forall n p m , (Pos.to_nat p) < 2 ^ n -> n <= m -> pos2fb p m = false.
Proof.
intros n p.
induction p.
intros. simpl.
Admitted.

Lemma N2fb_bound :
    forall n x m, x < 2 ^ n -> n <= m -> (nat2fb x) m = false.
Proof.
 intros.
 unfold nat2fb.
 unfold N2fb.
 destruct (N.of_nat x) eqn:eq.
 unfold allfalse. reflexivity.
 eapply (pos2fb_bound n). lia. lia.
Qed.

Check put_cus.

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
  rewrite (N2fb_bound n). easy. assumption. lia.
Qed.

(* The following two lemmas show the correctness of the adder implementation based on MAJ;UMA circuit. 
   The usage of the adder is based on the carry0 lemma. *)
Lemma adder01_correct_carry0 :
  forall n env (S S' S'' : posi -> val) x y c v1 v2,
    0 < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    v1 < 2^n -> v2 < 2^n ->
    S' = reg_push (reg_push (S[c |-> put_cu (S c) false]) x v1 n) y v2 n ->
    S'' = reg_push (reg_push (S[c |-> put_cu (S c) false]) x v1 n) y (v1+v2) n ->
    exp_sem env S' (adder01 n x y c) S''.
Proof.
  intros. unfold reg_push in *. apply adder01_nor_fb. assumption.
  subst. 
  unfold nor_modes. intros. 
  apply nor_mode_cus_eq. apply nor_mode_cus_eq.
  apply nor_mode_up. apply iner_neq_1; assumption.
  apply H1. lia. 
  subst.
  unfold nor_modes. intros. 
  apply nor_mode_cus_eq. apply nor_mode_cus_eq.
  apply nor_mode_up. apply iner_neq_1; assumption.
  apply H2. lia. 
  subst.
  unfold nor_modes. intros. destruct c.
  apply nor_mode_cus_eq. apply nor_mode_cus_eq.
  apply nor_mode_ups. easy. assumption. assumption.
  assumption. assumption.
  subst.
  destruct c. simpl in *.
  rewrite cus_get_neq by lia.
  rewrite cus_get_neq by lia.
  rewrite eupdate_index_eq.
  rewrite get_put_cu by assumption.
  rewrite put_cus_twice_eq.
  rewrite get_cus_put_neq by lia.
  rewrite get_cus_put_eq.
  rewrite get_cus_put_eq.
  rewrite sumfb_correct_carry0. easy.
  assumption.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_up. apply iner_neq. lia.
  apply H2. lia. assumption.
  unfold nor_modes. intros.
  apply nor_mode_up. apply iner_neq. lia.
  apply H1. lia.
Qed.

Lemma adder01_correct_carry1 :
  forall n env (S S' S'' : posi -> val) x y c v1 v2,
    0 < n -> nor_modes S x n -> nor_modes S y n -> nor_mode S c ->
    x <> y -> x <> fst c -> y <> fst c ->
    v1 < 2^n -> v2 < 2^n ->
    S' = reg_push (reg_push (S[c |-> put_cu (S c) true]) x v1 n) y v2 n ->
    S'' = reg_push (reg_push (S[c |-> put_cu (S c) true]) x v1 n) y (v1+v2+1) n ->
    exp_sem env S' (adder01 n x y c) S''.
Proof.
  intros. unfold reg_push in *. apply adder01_nor_fb. assumption.
  subst. 
  unfold nor_modes. intros. 
  apply nor_mode_cus_eq. apply nor_mode_cus_eq.
  apply nor_mode_up. apply iner_neq_1; assumption.
  apply H1. lia. 
  subst.
  unfold nor_modes. intros. 
  apply nor_mode_cus_eq. apply nor_mode_cus_eq.
  apply nor_mode_up. apply iner_neq_1; assumption.
  apply H2. lia. 
  subst.
  unfold nor_modes. intros. destruct c.
  apply nor_mode_cus_eq. apply nor_mode_cus_eq.
  apply nor_mode_ups. easy. assumption. assumption.
  assumption. assumption.
  subst.
  destruct c. simpl in *.
  rewrite cus_get_neq by lia.
  rewrite cus_get_neq by lia.
  rewrite eupdate_index_eq.
  rewrite get_put_cu by assumption.
  rewrite put_cus_twice_eq.
  rewrite get_cus_put_neq by lia.
  rewrite get_cus_put_eq.
  rewrite get_cus_put_eq.
  rewrite sumfb_correct_carry1. easy.
  assumption.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq.
  apply nor_mode_up. apply iner_neq. lia.
  apply H2. lia. assumption.
  unfold nor_modes. intros.
  apply nor_mode_up. apply iner_neq. lia.
  apply H1. lia.
Qed.

(* The following will do the negation of the first input value in the qubit sequence 00[x][y][z].
   THe actual effect is to make the sequence to be 00[-x][y][z]. *)
Fixpoint negator0 i x : exp :=
  match i with
  | 0 => SKIP
  | S i' => negator0 i' x; X (x, i')
  end.



Lemma negatem_put_get : forall i n f x, S i <= n ->
       put_cus f x (negatem (S i) (get_cus n f x)) n =
              (put_cus f x (negatem i (get_cus n f x)) n)[(x,i) |-> put_cu (f (x,i)) (¬ (get_cua (f (x,i))))].
Proof.
  intros.
  unfold negatem.
  apply functional_extensionality. intros.
  destruct x0.
  bdestruct (x =? v).
  bdestruct (n0 =? i).
  subst.
  rewrite eupdate_index_eq.
  unfold put_cus. simpl.
  bdestruct (v =? v).
  bdestruct (i <? n).
  bdestruct (i <? S i).
  rewrite get_cus_cua. easy. lia.
  lia. lia. lia.
  rewrite eupdate_index_neq.
  unfold put_cus. simpl.
  bdestruct (v =? x).
  bdestruct (n0 <? n).
  bdestruct (n0 <? S i).
  bdestruct (n0 <? i). easy.
  lia.
  bdestruct (n0 <? i). lia. easy.
  easy. easy.
  intros R. inv R. lia.
  rewrite put_cus_neq.
  rewrite eupdate_index_neq.
  rewrite put_cus_neq.
  easy. 
  lia.
  intros R. inv R. lia. lia.
Qed.

Lemma negator0_correct :
  forall i n env f x,
    0 < n ->
    i <= n ->
    nor_modes f x n ->
    exp_sem env f (negator0 i x) (put_cus f x (negatem i (get_cus n f x)) n).
Proof.
 induction i; intros.
 simpl.
 assert ((negatem 0 (get_cus n f x)) = get_cus n f x).
  apply functional_extensionality. intros.
 unfold negatem. bdestruct (x0 <? 0).
 lia. easy.
 rewrite H3.
 rewrite put_get_cus_eq. constructor. assumption.
 simpl. econstructor.
 apply IHi. apply H0. lia. assumption.
 rewrite negatem_put_get.
 apply x_nor.
 apply nor_mode_cus_eq. apply H2. lia.
 assert ((¬ (get_cua
        (put_cus f x (negatem i (get_cus n f x)) n (x, i))))
         = (¬ (get_cua (f (x, i))))).
 unfold put_cus, get_cua, negatem, put_cu,get_cus. simpl.
 bdestruct (x =? x).
 bdestruct (i <? n).
 unfold nor_modes in H2.
 specialize (H2 i H4). unfold nor_mode in H2.
 destruct (f (x,i)).
 bdestruct (i <? i). lia. easy. easy. easy.
 easy. lia.
 rewrite H3.
 assert ((put_cus f x (negatem i (get_cus n f x)) n (x, i)) = f (x,i)).
 unfold put_cus,put_cu,negatem,get_cus. simpl.
 bdestruct (x =? x).
 bdestruct (i <? n).
 unfold nor_modes in H2.
 specialize (H2 i H5). unfold nor_mode in H2.
 destruct (f (x,i)).
 bdestruct (i <? i). lia. easy. easy. easy.
 easy. easy.
 rewrite H4. easy. lia.
Qed.

Lemma negator0_nor :
  forall i n env f f' x,
    0 < n ->
    i <= n ->
    nor_modes f x n ->
    f' = (put_cus f x (negatem i (get_cus n f x)) n) ->
    exp_sem env f (negator0 i x) f'.
Proof.
 intros. subst. apply negator0_correct. 1 - 3: assumption.
Qed.

(* The correctness represents the actual effect of flip all bits for the number x.
   The effect is to make the x number positions to store the value  2^n - 1 - x. *)
Lemma negator0_sem :
  forall n env x v f f' f'',
    0 < n ->
    v < 2^n -> nor_modes f x n ->
    f' =  (reg_push f x v n) ->
    f'' = reg_push f x (2^n - 1 - v) n ->
    exp_sem env f' (negator0 n x) f''.
Proof.
  intros. unfold reg_push in *.
  apply (negator0_nor n n). assumption. lia.
  subst.
  unfold nor_modes. intros.
  apply nor_mode_cus_eq. apply H2. lia.
  subst. rewrite get_cus_put_eq.
  rewrite negatem_arith.
  rewrite put_cus_twice_eq. easy.
  1-3:assumption.
Qed.

(* The following implements an comparator. 
   THe first step is to adjust the adder circuit above to be
    MAJ;high_bit_manipulate;UMA.
    This is based on a binary number circuit observation that:
    To compare if x < y, we just need to do x - y, and see the high bit of the binary
    format of x - y. If the high_bit is zero, that means that x >= y;
    otherwise x < y. *)


Definition highb01 n x y c1 c2: exp := MAJseq n x y c1; CNOT (x,n) c2; inv_exp (MAJseq n x y c1).

Definition no_equal (x y:var) (c1 c2 : posi) : Prop := x <> y /\ x <> fst c1 /\  x <> fst c2 
                   /\ y <> fst c1 /\ y <> fst c2 /\ fst c1 <> fst c2.


Lemma highb01_correct :
  forall n env f f' x y c1 c2,
    0 < n -> no_equal x y c1 c2 ->
    nor_mode f c2 -> nor_mode f c1 -> nor_modes f x n -> nor_modes f y n -> 
    get_cua (f c2) = false ->
    f' = f[c2 |-> put_cu (f c2) (carry (get_cua (f c1)) n (get_cus n f x) (get_cus n f y))] ->
    exp_sem env f (highb01 n x y c1 c2) f'.
Proof.
  intros. unfold highb01. unfold no_equal in H1.
  simpl. unfold MAJseq. econstructor. 
  econstructor. apply MAJseq'_correct. apply H0. lia.
  1-3:assumption. 1-3:easy.
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

(* The actual comparator implementation. 
    We first flip the x positions, then use the high-bit comparator above. 
    Then, we use an inverse circuit of flipping x positions to turn the
    low bits back to store the value x.
    The actual implementation in the comparator is to do (x' + y)' as x - y,
    and then, the high-bit actually stores the boolean result of x - y < 0.  *)
Definition comparator01 n x y c1 c2 := (X c1; negator0 n x); highb01 n x y c1 c2; inv_exp (X c1; negator0 n x).

(* The implementation of a subtractor. It takes two values [x][y], and the produces
    the result of [x][y + 2^n - x]. *)
Definition substractor01 n x y c1:= (X c1; negator0 n x); adder01 n x y c1; inv_exp (X c1; negator0 n x).


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
Definition modmult_half n M x y c1 c2 s C := modsummer n M x y c1 c2 s C; (inv_exp (modsummer n M x y c1 c2 s 0)).

Definition modmult_full C Cinv n M x y c1 c2 s := modmult_half n M x y c1 c2 s C; inv_exp (modmult_half n M x y c1 c2 s Cinv).

Definition modmult M C Cinv n x y z s c1 c2 := init_v n z M; modmult_full C Cinv n z x y c1 c2 s; inv_exp (init_v n z M).

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

Fixpoint trans_pexp (f:vars) (dim:nat) (exp:pexp) : (base_ucom dim * vars) :=
     match exp with Exp s => trans_exp f dim s
                 | QFT x => (trans_qft f x, f)
                 | RQFT x => (trans_qft f x, f)
                 | H x => (trans_h f x, f)
                 | FSeq e1 e2 =>  
                         match trans_pexp f dim e1 with (e1',f') => 
                             match trans_pexp f' dim e2 with (e2',f'') => 
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

Definition csplit (p : exp) :=
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

Fixpoint csplit_pexp (p : pexp) :=
  match p with
  | Exp s => Exp (csplit s)
  | FSeq e1 e2 => FSeq (csplit_pexp e1) (csplit_pexp e2)
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

Fixpoint bcelim_pexp p :=
   match p with 
     | Exp s => Exp (bcelim s)
     | FSeq e1 e2 => match bcelim_pexp e1, bcelim_pexp e2 with
                           |  Exp SKIP, e2' => e2'
                           | e1', Exp SKIP => e1'
                           | e1',e2' => e1' ;; e2'
                     end
     | e => e
   end.

Definition modmult_vars (n:nat) := cons (x,n,SType) (cons (y,n,NType) (cons (z,n,NType)
                               (cons (s,n,NType) (cons (c1,1,NType) (cons (c2,1,NType) []))))).

Definition modmult_var_fun (n:nat) := compile_var (modmult_vars n).

Definition modmult_sqir M C Cinv n := trans_pexp (modmult_var_fun n)
            (get_dim (modmult_vars n)) (csplit_pexp (bcelim_pexp(modmult_rev (nat2fb M) C Cinv n x y z s (c1,0) (c2,0)))).

Definition f_modmult_circuit a ainv N n := fun i => modmult_sqir N (a^(2^i) mod N) (ainv^(2^i) mod N) n.

Definition rz_mod_vars (n:nat) := cons (x,n,NType) (cons (y,n,NType) (cons (c1,1,NType) [])).

Definition rz_var_fun (n:nat) := compile_var (rz_mod_vars n).

Definition rz_mod_sqir M C Cinv n := trans_pexp (rz_var_fun n)
            (get_dim (rz_mod_vars n)) (csplit_pexp (bcelim_pexp (rz_modmult_full x y n (c1,0) (nat2fb C) (nat2fb Cinv) (nat2fb M)))).

Definition rz_f_modmult_circuit a ainv N n := fun i => 
                            rz_mod_sqir N (a^(2^i) mod N) (ainv^(2^i) mod N) n.


