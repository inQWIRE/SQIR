Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import VSQIR.
Require Import CLArith.
Require Import RZArith.

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monads.

(* The definition of QSSA. *)
Local Open Scope exp_scope.
Local Open Scope nat_scope.

Definition fvar := nat.

Inductive qvar := G (v:var) | L (v:var).

Definition qty_eq  (t1 t2:qvar) : bool := 
   match t1 with G x => match t2 with G y  => (x =? y)
                            | _ => false
                        end
               | L x => match t2 with L y => (x =? y)
                           | _ => false
                        end
   end.

Notation "i '=q=' j" := (qty_eq i j) (at level 50).

Lemma qty_eqb_eq : forall a b, a =q= b = true -> a = b.
Proof.
 intros. unfold qty_eq in H.
 destruct a. destruct b.
 apply Nat.eqb_eq in H. subst. easy. inv H.
 destruct b. inv H. 
 apply Nat.eqb_eq in H. subst. easy.
Qed.

Lemma qty_eqb_neq : forall a b, a =q= b = false -> a <> b.
Proof.
 intros. unfold qty_eq in H.
 destruct a. destruct b.
 apply Nat.eqb_neq in H.
 intros R. inv R. contradiction.
 intros R. inv R.
 destruct b. 
 intros R. inv R.
 apply Nat.eqb_neq in H.
 intros R. inv R. contradiction.
Qed.

Lemma qty_eq_reflect : forall r1 r2, reflect (r1 = r2) (qty_eq r1 r2). 
Proof.
  intros.
  destruct (r1 =q= r2) eqn:eq1.
  apply  ReflectT.
  apply qty_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply qty_eqb_neq in eq1.
  assumption. 
Qed.

(*  a type for const values that cannot appear in a quantum circuit,
   and register values that can appear in a guantum circuit. *)
Inductive btype := Nat : btype | Flt : btype | Bl : btype.


Definition bty_eq  (t1 t2:btype) : bool := 
   match t1 with Nat => match t2 with Nat  => true
                            | _ => false
                        end
               | Flt => match t2 with Flt => true
                           | _ => false
                        end
                | Bl => match t2 with Bl => true
                           | _ => false
                        end
   end.


(*
Definition bty_eq  (t1 t2:btype) : bool := 
   match t1 with TPtr b1 n => match t2 with TPtr b2 m  => bty_eq' b1 b2 && (n =? m) 
                            | _ => false
                        end
               | TNor b1 => match t2 with TNor b2 => bty_eq' b1 b2 
                           | _ => false
                        end
   end.
*)

Notation "i '=b=' j" := (bty_eq i j) (at level 50).

Lemma bty_eqb_eq : forall a b, a =b= b = true -> a = b.
Proof.
 intros. unfold bty_eq in H.
 destruct a. destruct b. 1-3:easy.
 destruct b. 1-3:easy.
 destruct b. 1-3:easy.
Qed.

Lemma bty_eqb_neq : forall a b, a =b= b = false -> a <> b.
Proof.
 intros. unfold bty_eq in H.
 destruct a. destruct b. 1-3:easy.
 destruct b. 1-3:easy.
 destruct b. 1-3:easy.
Qed.

Lemma bty_eq_reflect : forall r1 r2, reflect (r1 = r2) (bty_eq r1 r2). 
Proof.
  intros.
  destruct (r1 =b= r2) eqn:eq1.
  apply  ReflectT.
  apply bty_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply bty_eqb_neq in eq1.
  assumption. 
Qed.

Inductive atype := C : atype | Q : atype.


Definition aty_eq  (t1 t2:atype) : bool := 
   match t1 with C => match t2 with C  => true
                            | _ => false
                        end
               | Q => match t2 with Q => true
                           | _ => false
                        end
   end.

Notation "i '=a=' j" := (aty_eq i j) (at level 50).

Lemma aty_eqb_eq : forall a b, a =a= b = true -> a = b.
Proof.
 intros. unfold aty_eq in H.
 destruct a. destruct b. 1-2:easy.
 destruct b. 1-2:easy.
Qed.

Lemma aty_eqb_neq : forall a b, a =a= b = false -> a <> b.
Proof.
 intros. unfold aty_eq in H.
 destruct a. destruct b. easy.
 easy.
 destruct b. easy. easy.
Qed.

Lemma aty_eq_reflect : forall r1 r2, reflect (r1 = r2) (aty_eq r1 r2). 
Proof.
  intros.
  destruct (r1 =a= r2) eqn:eq1.
  apply  ReflectT.
  apply aty_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply aty_eqb_neq in eq1.
  assumption. 
Qed.

Definition typ :Type := (atype * btype).


Definition typ_eq  (t1 t2:typ) : bool := 
   match t1 with (c1,b1) => match t2 with (c2,b2)  => (c1 =a= c2) && (b1 =b= b2)
                        end
   end.

Notation "i '=t=' j" := (typ_eq i j) (at level 50).

Lemma typ_eqb_eq : forall a b, a =t= b = true -> a = b.
Proof.
 intros. unfold typ_eq in H.
 destruct a. destruct b.
 apply andb_true_iff in H.
 destruct H.
 apply aty_eqb_eq in H.
 apply bty_eqb_eq in H0. subst. easy.
Qed.

Lemma typ_eqb_neq : forall a b, a =t= b = false -> a <> b.
Proof.
 intros. unfold typ_eq in H.
 destruct a. destruct b.
 apply andb_false_iff in H.
 destruct H.
 apply aty_eqb_neq in H. intros R. inv R. easy.
 apply bty_eqb_neq in H. intros R. inv R. easy.
Qed.

Lemma typ_eq_reflect : forall r1 r2, reflect (r1 = r2) (typ_eq r1 r2). 
Proof.
  intros.
  destruct (r1 =t= r2) eqn:eq1.
  apply  ReflectT.
  apply typ_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply typ_eqb_neq in eq1.
  assumption. 
Qed.

Hint Resolve aty_eq_reflect qty_eq_reflect bty_eq_reflect typ_eq_reflect : bdestruct.

Inductive ttyp := TPtr (t:typ) (n:nat) | TNor (t:typ).

Module QvarType <: OrderedType.

 Definition t := qvar.

 Definition eq := @eq t.

 Definition lt (x y : qvar) := match x with
                                 L u => 
                                       match y with L v => (u < v)
                                                  | G v => True
                                       end
                                | G u =>
                                     match y with G v => (u < v)
                                                | L v => False
                                     end
                      end.

  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.


 Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
 Proof.
 intros. 
 unfold lt in *.
 destruct x. destruct y. destruct z. lia. lia. lia.
 destruct y. destruct z. lia. lia. destruct z. lia. lia.
 Qed.

 Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
 Proof.
 intros. 
 unfold lt,eq in *.
 destruct x. destruct y. intros R. inv R. lia.
 easy.
 destruct y.
 easy. intros R. inv R. lia.
 Qed.

 Definition compare : forall x y : t, Compare lt eq x y.
 Proof.
 intros.
 destruct x. destruct y.
 bdestruct (v <? v0).
 apply LT. unfold lt. easy.
 bdestruct (v =? v0).
 apply EQ; unfold eq;auto.
 apply GT;unfold lt. lia.
 apply GT;unfold lt. lia.
 destruct y.
 apply LT. unfold lt. easy.
 bdestruct (v <? v0).
 apply LT. unfold lt. easy.
 bdestruct (v =? v0).
 apply EQ; unfold eq;auto.
 apply GT;unfold lt. lia.
 Defined.

 Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
 Proof.
 intros; elim (compare x y); intro H; [ right | left | right ]; auto.
 auto using lt_not_eq.
 assert (~ eq y x); auto using lt_not_eq.
 unfold eq in *. intros R. subst. contradiction.
 Defined.

End QvarType.



Inductive factor := Var (v:qvar)
                 | Num (n:nat -> bool).
     (* the first m in Num represents the number of bits.
      a value is represented as a natural number x. it means x / 2^m where m is the number of denominator. *)

Inductive cfac := Ptr (x:var) (v:factor) | Nor (v:factor).

Inductive flag := QFTA | Classic.

(* the SSA form is to restrict non-loop instructions. x = y op z, 
    where we compute y op z and then we store the value into x, so if x is freshly defined, then x = y op z. 
    if one wants to use instructions in a loop, then use the qadd/qsub/qmul. 
Inductive iexp := eplus (f:flag) (x : factor) (y: factor)
      | eminus (f:flag) (x:factor) (y:factor)
      | emult (f:flag) (x:factor) (y:factor)
      | ediv (f:flag) (x:factor) (y:factor)
      | emod (f:flag) (x:factor) (y:factor)
      | eload (v:var).
*)


(* qadd/qsub/qmul has the property as x = y op x, which is corresponding to
   [y][x] -> [y][y op x] structure.
   for qadd/qsub, x and y are both float numbers. For mult, x is a natural number while y is a float.
   for comparator operations, both are floats. *)

Inductive cexp := clt (f:flag) (b:btype) (x:cfac) (y:cfac)
                  | ceq (f:flag) (b:btype) (x:cfac) (y:cfac)
                  | iseven (x:cfac).

Inductive qexp := skip
                | init (b:btype) (x:cfac) (v:cfac)  
                | nadd (f:flag) (v:cfac) (x:cfac) 
                | nsub (f:flag) (v:cfac) (x:cfac)
                | nmul (f:flag) (v:cfac) (x:cfac)
                | nqmul (f:flag) (v1:cfac) (v2:cfac) (z:cfac)
                | fadd (f:flag) (v:cfac) (x:cfac) 
                | fsub (f:flag) (v:cfac) (x:cfac)
                | fmul (f:flag) (v1:cfac) (v2:cfac) (z:cfac)
                | qxor (b:btype) (v:cfac) (x:cfac)
                | nfac (x:cfac) (v:cfac)
                | fdiv (x:cfac) (v:cfac) (* x := x / n where n is a natural number. *)
                | fnmul (x:cfac) (v:cfac) (* x := x * n where n is a natural number. *)
                | fndiv (x:cfac) (v:cfac) (z:cfac)(* z = x/v where x and v are natural numbers, z is float
                           x and v are both integers, but the final result in z must be a float < 1 *)
                | qinv (e:qexp)
                | call (f:fvar) (v: cfac)
                | qif (c:cexp) (e1:qexp) (e2:qexp)
                | qwhile (x:var) (n:nat) (e:qexp)
                | qseq (q1:qexp) (q2:qexp).

(*functions will do automatic inverse computation after a function is returned.
  for each ret statement, there is a list of pairs of vars, and the left one is the global variables to return,
   while the left one is the local variables. after a function call is returned,
    it will store all the local variables to their correponding global variables, and then reverse the computation.  *)

Notation "p1 ;;; p2" := (qseq p1 p2) (at level 50) : exp_scope.

Definition func : Type := ( fvar * list (btype * var * nat) * qexp * qvar).
    (* a function is a fun name, a starting block label, and a list of blocks, and the returned variable. *)

Definition prog : Type := (nat * nat * list (btype * var * (nat -> bool)) * list func * fvar * var). 
   (* a program is a nat representing the stack size,
       and a number of bits in Flt and Nat
          and a list of global vars, and a list of functions.
     and the main function to call, and the final global var to write to. *)


(* Define the well-formedness of exp. It is SSA + variable-dominance, as well as type match. *)
(* The following relation defines the SSA + variable dominance for expressions and instructions. 
Inductive ssa_factor : list var -> factor -> Prop :=
   | ssa_jfactor : forall r x, In x r -> ssa_factor r (Var x)
   | ssa_cfactor_num : forall r n m t, ssa_factor r (Num n m t).

Inductive ssa_exp : list var -> iexp -> Prop := 
  | eplus_ssa : forall f r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (eplus f x y)
  | eminus_ssa : forall f r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (eminus f x y)
  | emult_ssa : forall f r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (emult f x y)
  | ediv_ssa : forall f r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (ediv f x y)
  | emod_ssa : forall f r x y , ssa_factor r x -> ssa_factor r y -> ssa_exp r (emod f x y)
  | eload_ssa : forall r x, In x r -> ssa_exp r (eload x).

Inductive ssa_comexp : list var -> comexp -> Prop :=
     | ssa_clt : forall r f x y, ssa_factor r x -> ssa_factor r y -> ssa_comexp r (clt f x y)
     | ssa_ceq : forall r f x y, ssa_factor r x -> ssa_factor r y -> ssa_comexp r (ceq f x y).

Inductive ssa_inst : list var -> qexp -> list var -> Prop :=
   | ssa_assign : forall r x n t e, ~ In x r -> ssa_exp r e -> ssa_inst r (inst x n t e) (x::r)
   | ssa_add : forall r f x y, ssa_factor r x -> ssa_factor r y -> ssa_inst r (qadd f x y) r
   | ssa_sub : forall r f x y, ssa_factor r x -> ssa_factor r y -> ssa_inst r (qsub f x y) r
   | ssa_mul : forall r f x y, ssa_factor r x -> ssa_factor r y -> ssa_inst r (qmul f x y) r
   | ssa_if : forall r r' r'' c e1 e2, ssa_comexp r c ->
                 ssa_inst r e1 r' -> ssa_inst r' e2 r'' -> ssa_inst r (qif c e1 e2) r''
   | ssa_while : forall r r' c e, ssa_comexp r c -> ssa_inst r e r' -> ssa_inst r (qwhile c e) r'
   | ssa_ret : forall r l, (forall a b, In (a,b) l -> In a r /\ In b r) -> ssa_inst r (ret l) r
   | ssa_call : forall r f, ssa_inst r (call f) r
   | ssa_seq : forall r r' r'' e1 e2, ssa_inst r e1 r' -> ssa_inst r' e2 r'' -> ssa_inst r (qseq e1 e2) r''.

Inductive ssa_funs : list var -> list func -> list var -> Prop :=
   ssa_fun_empty : forall r, ssa_funs r [] r
  | ssa_fun_many : forall r r' r'' f e fs, ssa_inst r e r' -> ssa_funs r' fs r'' -> ssa_funs r ((f,e)::fs) r''.


Inductive ssa_prog : prog -> Prop :=
  | ssa_top : forall n m i l l' fs, ssa_funs (fst (split l)) fs l' -> ssa_prog (n,m,i,l,fs).
*)

(* The following relation defines the type system for expressions and instructions and functions. *)
(* Defining matching shifting stack. *)

Definition benv : Type := (qvar -> option ttyp).

Definition qupdate {A} (f : qvar -> A) (i : qvar) (x : A) :=
  fun j => if j =q= i then x else f j.

Lemma qupdate_index_eq : forall {A} (f : qvar -> A) i b, (qupdate f i b) i = b.
Proof.
  intros. 
  unfold qupdate.
  bdestruct (i =q= i). easy. easy.
Qed.

Lemma qupdate_index_neq : forall {A} (f : qvar -> A) i j b, i <> j -> (qupdate f i b) j = f j.
Proof.
  intros. 
  unfold qupdate.
  bdestruct (j =q= i). subst. easy. easy.
Qed.

Lemma qupdate_same : forall {A} (f : qvar -> A) i b,
  b = f i -> qupdate f i b = f.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold qupdate.
  bdestruct (x =q= i); subst; reflexivity.
Qed.

Lemma qupdate_twice_eq : forall {A} (f : qvar -> A) i b b',
  qupdate (qupdate f i b) i b' = qupdate f i b'.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold qupdate.
  bdestruct (x =q= i); subst; reflexivity.
Qed.  

Lemma qupdate_twice_neq : forall {A} (f : qvar -> A) i j b b',
  i <> j -> qupdate (qupdate f i b) j b' = qupdate (qupdate f j b') i b.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold qupdate.
  bdestruct (x =q= i); bdestruct (x =q= j); subst; easy.
Qed.

Definition fenv : Type := (var -> option (list (btype * var * nat) * qexp * benv * qvar)).

Notation "'do' X '<-' A '@' B" := (bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).


Definition typ_factor (benv:benv) (t:btype) (fc:factor) :=
   match fc with Var x => do re <- benv x @
    match re with TPtr x y => None
            | TNor t' => if snd t' =b= t then Some t' else None
   end
            | Num n => Some (C,t)
  end.

Definition type_factor (benv:benv) (t:btype) (fc:cfac) :=
   match fc with Ptr x ic => do re <- benv (L x) @ 
             match re with TPtr (a,b) n =>
                       do ta <- typ_factor benv Nat ic @
                          if (fst ta =a= C) && (b =b= t) then Some (a,b) else None

                    | TNor ta => None
             end
               | Nor c => typ_factor benv t c
   end.


Definition meet_type (t1 t2 : typ) := match t1 with (Q,b) => (Q,b)
                   | (C,b) => match t2 with (Q,b2) => (Q,b) | _ => (C,b) end end.


Definition type_cexp (benv:benv) (c:cexp) := 
   match c with clt f b x y => 
             do re1 <- type_factor benv b x @
                do re2 <- type_factor benv b y @ ret (meet_type re1 re2)
            | ceq f b x y => 
             do re1 <- type_factor benv b x @
                do re2 <- type_factor benv b y @ ret (meet_type re1 re2)
            | iseven x => match type_factor benv Nat x with Some (C,Nat) => Some (C, Nat) | _ => None end
          
   end.
(*
Definition var_raw (t:qvar) := match t with G x => x | L x => x end.
*)
Fixpoint a_nat2fb (f:nat->bool) (n:nat) :=
             match n with 0 => 0
                       | S m => (Nat.b2n (f m)) + a_nat2fb f m
             end.  


Definition allow_inv (e:qexp) : bool :=
   match e with skip | init _ _ _ | nadd _ _ _ | nsub _ _ _
              | nmul _ _ _ | nqmul _ _ _ _ | fadd _ _ _ | fsub _ _ _ | fmul _ _ _ _ | qxor _ _ _ => true
             | _ => false
   end.

Definition is_q (t:typ) : bool := match t with (Q,c) => true | _ => false end.

Definition get_var (c:cfac) : option qvar :=
   match c with Nor (Var x) => Some x
             | Nor (Num x) => None
             | Ptr x y => Some (L x)
   end.

Definition put_shell (c:ttyp) (t:typ) :=
   match c with TNor t' => TNor t
              | TPtr t' n => TPtr t n
   end.

Definition get_core (c:ttyp) :=
   match c with TNor t' => t'
              | TPtr t' n => t'
   end.

Fixpoint type_qexp (fv:fenv) (benv:benv) (e:qexp) :=
   match e with skip => Some benv
             | init b x v => 
               do re <- type_factor benv b x @
                 do core <- get_var x @ 
                  do old <- benv core @
                          ret (qupdate benv core (Some (put_shell old (Q,b))))

             | nadd f x y => 
             do re1 <- type_factor benv Nat x @
                do re2 <- type_factor benv Nat y @ 
                   do core <- get_var y @
                    do old <- benv core @
                       ret (qupdate benv core (Some (put_shell old (meet_type re1 re2))))

             | nsub f x y => 
             do re1 <- type_factor benv Nat x @
                do re2 <- type_factor benv Nat y @ 
                   do core <- get_var y @
                    do old <- benv core @
                       ret (qupdate benv core (Some (put_shell old (meet_type re1 re2))))

             | nmul f x y => 
             do re1 <- type_factor benv Nat x @
                do re2 <- type_factor benv Nat y @ 
                   do core <- get_var y @
                    do old <- benv core @ 
                        if is_q re1 then None else 
                            ret (qupdate benv core (Some (put_shell old (meet_type re1 re2))))

             | nqmul f x y z => 
             do re1 <- type_factor benv Nat x @
                do re2 <- type_factor benv Nat y @ 
                 do re3 <- type_factor benv Nat z @
                   do core <- get_var z @
                    do old <- benv core @ 
                          if (is_q re1) && (is_q re2)
                                     then ret (qupdate benv core (Some (put_shell old re1))) else None

             | fadd f x y => 
             do re1 <- type_factor benv Flt x @
                do re2 <- type_factor benv Flt y @ 
                   do core <- get_var y @
                    do old <- benv core @
                       ret (qupdate benv core (Some (put_shell old (meet_type re1 re2))))

             | fsub f x y => 
             do re1 <- type_factor benv Flt x @
                do re2 <- type_factor benv Flt y @ 
                   do core <- get_var y @
                    do old <- benv core @
                       ret (qupdate benv core (Some (put_shell old (meet_type re1 re2))))

             | fmul f x y z => 
             do re1 <- type_factor benv Flt x @
                do re2 <- type_factor benv Flt y @ 
                 do re3 <- type_factor benv Flt z @
                   do core <- get_var z @
                    do old <- benv core @ 
                          if (is_q re2)
                            then ret (qupdate benv core (Some (put_shell old re2))) else None

             | qxor b x y => 
             do re1 <- type_factor benv b x @
                do re2 <- type_factor benv b y @ 
                   do core <- get_var y @
                    do old <- benv core @
                       ret (qupdate benv core (Some (put_shell old (meet_type re1 re2))))

             | qinv e => if allow_inv e then type_qexp fv benv e else None

             | nfac x y => 
             do re1 <- type_factor benv Nat x @
                do re2 <- type_factor benv Nat y @ 
                       if is_q re1 || is_q re2 then None else ret benv

             | fdiv x y => 
             do re1 <- type_factor benv Flt x @
                do re2 <- type_factor benv Nat y @ 
                       if is_q re1 || is_q re2 then None else ret benv

             | fndiv x y z => 
             do re1 <- type_factor benv Nat x @
                do re2 <- type_factor benv Nat y @ 
                  do re3 <- type_factor benv Flt z @ 
                       if is_q re1 || is_q re2 || is_q re3 then None else ret benv

             | fnmul x y => 
             do re1 <- type_factor benv Flt x @
                do re2 <- type_factor benv Nat y @ 
                       if is_q re1 || is_q re2 then None else ret benv

              | call f x => 
                 do ref <- fv f @
                   match ref with (tvl,e,fbenv, rx) =>
                        do re1 <- fbenv rx @
                              do core <- get_var x @
                           do old <- benv core @
                                ret (qupdate benv core (Some (put_shell old (meet_type (get_core re1) (get_core old)))))
                   end

              | qif ce e1 e2 => 
                 do rce <- type_cexp benv ce @
                   do benv' <- type_qexp fv benv e1 @
                       type_qexp fv benv' e2

              | qwhile x n e => 
                 do re <- type_factor benv Nat (Nor (Var (L x))) @
                     if is_q re then None else type_qexp fv benv e

              | qseq e1 e2 => 
                 do benv' <- type_qexp fv benv e1 @ type_qexp fv benv' e2

   end.


Fixpoint gen_env (l:list (btype * var * nat)) (bv:benv) : option benv := 
   match l with [] => Some bv
             | ((t,x,n)::xl) => 
                  do new_env <- gen_env xl bv @
                     if n =? 1 then Some (qupdate new_env (L x) (Some (TNor (C,t))))
                       else if n =? 0 then None
                       else Some (qupdate new_env (L x) (Some (TPtr (C,t) n)))
   end.

Fixpoint type_funs (benv:benv) (fv:fenv) (l:list func) : option fenv :=
     match l with [] => Some fv
              | ((f,l,e,rx)::fs) => 
               do benv' <- gen_env l benv @
                 do benv'' <- type_qexp fv benv' e @
                    do rxv <- benv'' rx @
                     type_funs benv (update fv f (Some (l,e,benv',rx))) fs
     end.

Fixpoint gen_genv (l:list (btype * var * (nat->bool))) : benv := 
   match l with [] => (fun _ => None)
             | ((t,x,v)::xl) => qupdate (gen_genv xl) (G x) (Some (TNor (Q,t)))
   end.

(* ( fvar * list var * qexp ). *)
Definition type_prog (p:prog) : option fenv :=
   match p with (si,n,l,fl,main,rx) => 
      do fv <- type_funs (gen_genv l) (fun _ => None) fl @
            do block <- fv main @ ret fv
   end.

(*define example hash_function as the oracle for grover's search. *)
Definition hash_qr (b:qvar) (a:qvar) := nadd QFTA (Nor (Var b)) (Nor (Var a));;;
             qxor Nat (Nor (Var a)) (Nor (Var b));;;nadd QFTA (Nor (Var b)) (Nor (Var a))
                   ;;; qxor Nat (Nor (Var a)) (Nor (Var b)).

Definition g :var := 1.
Definition x :var := 7.
Definition a :var := 3.
Definition b :var := 4.
Definition c :var := 6.
Definition d :var := 100.
Definition f :var := 8.
Definition result :var := 9.

Definition hash_oracle (key:nat) (sndk:nat) :=
     (f, ((Bl,g,1)::(Nat,x,1)::(Nat,a,1)::(Nat,b,1)::(Nat,c,1)::(Nat,d,1)::[]),
      init Nat (Nor (Var (L d))) (Nor (Num (nat2fb 1)));;;
      qwhile x 10
           (hash_qr (L a) (L c);;; hash_qr (L b) (L d) ;;; hash_qr (L a) (L d)
                ;;; hash_qr (L b) (L c);;; nadd Classic (Nor (Num (nat2fb 1))) (Nor (Var (L x))));;;
      qif (ceq QFTA Nat (Nor (Var (L c))) (Nor (Num (nat2fb key))))
                (qif (ceq QFTA Nat (Nor (Var (L d))) (Nor (Num (nat2fb sndk))))
                    (init Bl (Nor (Var (L g))) (Nor (Num (nat2fb 1)))) (skip)) (skip), L g).

Definition hash_prog (s_size:nat) (size:nat) (key:nat) (sndk:nat) : prog := 
         (s_size, size,[(Bl,result,nat2fb 0)],[hash_oracle key sndk],f,result).


(* define sin/cos. a = x^2, b = x^1/3/5/...., d is the result
    the input of sin/cos function is x/2 (not x) range from [0,pi/2) *)


Definition x2 := 6.
Definition x3 := 0.
(*
Definition x5 := 1.
Definition x7 := 2.
Definition x9 := 3.
Definition x11 := 4.
*)
Definition n : var := 10. 
Definition e : var := 15. 
Definition rc : var := 11. 
Definition re : var := 14. 
Definition fac : var := 12. 
Definition xc : var := 13. 

Definition taylor_sin : func := 
     (f, ((Flt,x3,5)::(Flt,x2,1)::(Flt,e,1)::
              (Nat,g,1)::(Nat,n,1)::(Nat, xc,1)::(Nat,fac,1)::(Flt,rc,1)::(Flt,re,1)::[]),
                         fmul QFTA (Nor (Var (G x))) (Nor (Var (G x))) (Nor (Var (L x2)));;;
                         fmul QFTA (Nor (Var (G x))) (Nor (Var (L x2))) (Ptr x3 (Num (nat2fb 0)));;;
                         fmul QFTA (Nor (Var (L x2))) (Ptr x3 (Num (nat2fb 0))) (Ptr x3 (Num (nat2fb 1)));;;
                         fmul QFTA (Nor (Var (L x2))) (Ptr x3 (Num (nat2fb 1))) (Ptr x3 (Num (nat2fb 2)));;;
                         fmul QFTA (Nor (Var (L x2))) (Ptr x3 (Num (nat2fb 2))) (Ptr x3 (Num (nat2fb 3)));;;
                         fmul QFTA (Nor (Var (L x2))) (Ptr x3 (Num (nat2fb 3))) (Ptr x3 (Num (nat2fb 4)));;;
                         init Flt (Nor (Var (L re))) (Nor (Var (G x)));;;
                         nadd QFTA (Nor (Num (nat2fb 1))) (Nor (Var (L n)));;;
                         nadd QFTA (Nor (Num (nat2fb 1))) (Nor (Var  (L xc)));;;
         qwhile g 5 
             (qif (iseven (Nor (Var (L g)))) 
                      (nadd QFTA (Nor (Num (nat2fb 2))) (Nor (Var ((L n))));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       nmul QFTA (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L xc))) (Nor (Var (L fac))) (Nor (Var (L rc)));;;
                       fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e)));;;
                       fsub QFTA (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv (fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e))));;;
                       nadd QFTA (Nor (Num (nat2fb 1))) (Nor (Var ((L g)))))
                      (nadd QFTA (Nor (Num (nat2fb 2))) (Nor (Var ((L n))));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       nmul QFTA (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L xc))) (Nor (Var (L fac))) (Nor (Var (L rc)));;;
                       fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e)));;;
                       fadd QFTA (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv (fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e))));;;
                       nadd QFTA (Nor (Num (nat2fb 1))) (Nor (Var ((L g))))))
             ,L re).

Definition sin_prog (s_size:nat) (size:nat) (v:nat->bool) : prog := 
         (s_size, size,[(Flt,result,v)],[taylor_sin],f,result).

Parameter Pi_4 : nat -> bool. (*a binary representation of PI/4 *)

Definition taylor_cos : func := 
     (f, ((Flt,x3,5)::(Flt,x2,1)::(Flt,e,1)::
              (Nat,g,1)::(Nat,n,1)::(Nat, xc,1)::(Nat,fac,1)::(Flt,rc,1)::(Flt,re,1)::[]),
                         fsub QFTA (Nor (Num Pi_4)) (Nor (Var (G x)));;;
                         fmul QFTA (Nor (Var (G x))) (Nor (Var (G x))) (Nor (Var (L x2)));;;
                         fmul QFTA (Nor (Var (G x))) (Nor (Var (L x2))) (Ptr x3 (Num (nat2fb 0)));;;
                         fmul QFTA (Nor (Var (L x2))) (Ptr x3 (Num (nat2fb 0))) (Ptr x3 (Num (nat2fb 1)));;;
                         fmul QFTA (Nor (Var (L x2))) (Ptr x3 (Num (nat2fb 1))) (Ptr x3 (Num (nat2fb 2)));;;
                         fmul QFTA (Nor (Var (L x2))) (Ptr x3 (Num (nat2fb 2))) (Ptr x3 (Num (nat2fb 3)));;;
                         fmul QFTA (Nor (Var (L x2))) (Ptr x3 (Num (nat2fb 3))) (Ptr x3 (Num (nat2fb 4)));;;
                         init Flt (Nor (Var (L re))) (Nor (Var (G x)));;;
                         nadd QFTA (Nor (Num (nat2fb 1))) (Nor (Var (L n)));;;
                         nadd QFTA (Nor (Num (nat2fb 1))) (Nor (Var  (L xc)));;;
         qwhile g 5 
             (qif (iseven (Nor (Var (L g)))) 
                      (nadd QFTA (Nor (Num (nat2fb 2))) (Nor (Var ((L n))));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       nmul QFTA (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L xc))) (Nor (Var (L fac))) (Nor (Var (L rc)));;;
                       fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e)));;;
                       fsub QFTA (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv (fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e))));;;
                       nadd QFTA (Nor (Num (nat2fb 1))) (Nor (Var ((L g)))))
                      (nadd QFTA (Nor (Num (nat2fb 2))) (Nor (Var ((L n))));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       nmul QFTA (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L xc))) (Nor (Var (L fac))) (Nor (Var (L rc)));;;
                       fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e)));;;
                       fadd QFTA (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv (fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e))));;;
                       nadd QFTA (Nor (Num (nat2fb 1))) (Nor (Var ((L g))))))
             ,L re).

Definition cos_prog (s_size:nat) (size:nat) (v:nat->bool) : prog := 
         (s_size, size,[(Flt,result,v)],[taylor_cos],f,result).

(*The semantics of QLLVM. *)

Definition reg : Type := (qvar -> (nat -> bool)).

Definition empty_reg : (qvar -> (nat -> bool)) := fun _ => allfalse.

Definition sem_factor (size:nat) (reg:reg) (b:btype) (fc:factor) := 
   match fc with Var x => reg x
            | Num n => match b with Bl => cut_n n 1
                                 | Nat => cut_n n size
                                 | Flt => cut_n n size
                       end
   end.

Definition sem_cexp (sl_size sn size:nat) (reg:reg) (ce:cexp) : option (nat * bool) :=
   if sn <? sl_size then
          match ce with clt f b x y => 
              match b with Bl => Some (S sn,a_nat2fb (sem_factor size reg Bl x) 1 <? a_nat2fb ((sem_factor size reg Bl x)) 1)
                       | _ => Some (S sn, a_nat2fb (sem_factor size reg b x) size <? a_nat2fb ((sem_factor size reg b x)) size)
              end
                   | ceq f b x y =>
              match b with Bl => Some (S sn,a_nat2fb (sem_factor size reg Bl x) 1 =? a_nat2fb ((sem_factor size reg Bl x)) 1)
                         | _ => Some (S sn,a_nat2fb (sem_factor size reg b x) size =? a_nat2fb ((sem_factor size reg b x)) size)
              end
                   | iseven x => Some (sn,(a_nat2fb (sem_factor size reg Nat x) size) mod 2 =? 0)
          end
   else None.

Definition bin_xor (f1 f2:nat -> bool) (size:nat) :=
  cut_n (fun x => xorb (f1 x) (f2 x)) size.

Definition sub_def (f1 f2:nat -> bool) (size:nat) :=
         if a_nat2fb f1 size <? a_nat2fb f2 size then (a_nat2fb f1 size + 2^size - a_nat2fb f2 size) mod 2^size
                  else (a_nat2fb f1 size + a_nat2fb f2 size) mod 2^size.

Fixpoint init_reg (r:reg) (l:list (btype * var)) : reg  :=
   match l with [] => r
             | ((t,x)::xl) => qupdate (init_reg r xl) (L x) (nat2fb 0)
   end.

Inductive sem_qexp (fv:fenv) (s_lit size:nat): nat -> reg -> qexp -> nat -> reg -> qexp -> Prop :=
 | sem_init : forall sn reg b x v,
      sem_qexp fv s_lit size sn reg (init b x v) sn
                (qupdate reg x (bin_xor (reg x) (sem_factor size reg b v) (if b =b= Bl then 1 else size))) skip
 | sem_nadd : forall sn reg f x y,
      sem_qexp fv s_lit size sn reg (nadd f x y) sn (qupdate reg y (sumfb false (sem_factor size reg Nat x) (reg y))) skip
 | sem_nsub : forall sn reg f x y, 
      sem_qexp fv s_lit size sn reg (nsub f x y) sn
               (qupdate reg y (sumfb true (sem_factor size reg Nat x) (negatem size (reg y)))) skip
 | sem_nmul : forall sn reg f x y, 
      sem_qexp fv s_lit size sn reg (nmul f x y) sn 
                  (qupdate reg y (nat2fb
                      ((a_nat2fb (sem_factor size reg Nat x) size * a_nat2fb (reg y) size) mod 2^size))) skip
 | sem_nqmul : forall sn reg f x y z, 
         reg z = nat2fb 0 ->
      sem_qexp fv s_lit size sn reg (nqmul f x y z) sn 
                  (qupdate reg z  (nat2fb
                      ((a_nat2fb (sem_factor size reg Nat x) size
                                 * (a_nat2fb (sem_factor size reg Nat x) size)) mod 2^size))) skip
 | sem_fadd : forall sn reg f x y,
      sem_qexp fv s_lit size sn reg (fadd f x y) sn 
               (qupdate reg y (sumfb false (sem_factor size reg Flt x) (reg y))) skip
 | sem_fsub : forall sn reg f x y,
      sem_qexp fv s_lit size sn reg (fsub f x y) sn 
                     (qupdate reg y (sumfb true (sem_factor size reg Flt x) (negatem size (reg y)))) skip
 | sem_fmul : forall sn reg f x y z,
      reg z = nat2fb 0 ->
      sem_qexp fv s_lit size sn reg (fmul f x y z) sn 
                  (qupdate reg z (nat2fb 
                       ((a_nat2fb (sem_factor size reg Flt x) size
                             * a_nat2fb (sem_factor size reg Flt x) size) / 2^size))) skip
 | sem_xor : forall sn reg b x y,
      sem_qexp fv s_lit size sn reg (qxor b x y) sn (qupdate reg y
                (bin_xor (sem_factor size reg b x) (reg y) (if b =b= Bl then 1 else size))) skip
 | sem_fac : forall sn reg x y,
      sem_qexp fv s_lit size sn reg (nfac x y) sn
            (qupdate reg (L x) (nat2fb ((fact (a_nat2fb (sem_factor size reg Nat y) size)) mod 2^size))) skip

 | sem_fdiv : forall sn reg x y, 
      sem_qexp fv s_lit size sn reg (fdiv x y) sn
           (qupdate reg (L x) (nat2fb (((a_nat2fb (reg (L x)) size)) / (a_nat2fb (sem_factor size reg Nat y) size)))) skip
 | sem_fndiv : forall sn reg x y z, 
       (a_nat2fb (sem_factor size reg Nat x) size) < (a_nat2fb (sem_factor size reg Nat y) size) ->
      sem_qexp fv s_lit size sn reg (fndiv x y z) sn
           (qupdate reg (L z) (nat2fb
                (((a_nat2fb (sem_factor size reg Nat x) size) * 2^size)
                            / (a_nat2fb (sem_factor size reg Nat y) size)))) skip
 | sem_fnmul : forall sn reg x y, 
      sem_qexp fv s_lit size sn reg (fnmul x y) sn
           (qupdate reg (L x) (nat2fb
                (((a_nat2fb (reg (L x)) size) * (a_nat2fb (sem_factor size reg Nat y) size)) mod 2^ size))) skip
 | sem_qinv_in : forall sn reg b x v, 
      sem_qexp fv s_lit size sn reg (qinv (init b x v)) sn
           (qupdate reg x (bin_xor (reg x) (sem_factor size reg b v) (if b =b= Bl then 1 else size))) skip
 | sem_qinv_nadd : forall sn reg f x y, 
      sem_qexp fv s_lit size sn reg (qinv (nadd f x y)) sn
           (qupdate reg y (sumfb true (sem_factor size reg Nat x) (negatem size (reg y)))) skip
 | sem_qinv_nsub : forall sn reg f x y, 
      sem_qexp fv s_lit size sn reg (qinv (nsub f x y)) sn
           (qupdate reg y (sumfb false (sem_factor size reg Nat x) (reg y))) skip
 | sem_qinv_nmul : forall sn reg f x y v1, 
          (v1 * (a_nat2fb (sem_factor size reg Nat x) size)) mod 2^size = 1 ->
      sem_qexp fv s_lit size sn reg (qinv (nmul f x y)) sn
           (qupdate reg y (nat2fb v1)) skip
 | sem_qinv_nqmul : forall sn reg f x y z, 
      sem_qexp fv s_lit size sn reg (qinv (nqmul f x y z)) sn (qupdate reg z (nat2fb 0)) skip
 | sem_qinv_fadd : forall sn reg f x y, 
      sem_qexp fv s_lit size sn reg (qinv (fadd f x y)) sn
           (qupdate reg y (sumfb true (sem_factor size reg Flt x) (negatem size (reg y)))) skip
 | sem_qinv_fsub : forall sn reg f x y, 
      sem_qexp fv s_lit size sn reg (qinv (fsub f x y)) sn
           (qupdate reg y (sumfb false (sem_factor size reg Flt x) (reg y))) skip
 | sem_qinv_fmul : forall sn reg f x y z, 
      sem_qexp fv s_lit size sn reg (qinv (fmul f x y z)) sn (qupdate reg z (nat2fb 0)) skip
 | sem_qinv_xor : forall sn reg b x v, 
      sem_qexp fv s_lit size sn reg (qinv (qxor b x v)) sn (qupdate reg v
                (bin_xor (sem_factor size reg b x) (reg v) (if b =b= Bl then 1 else size))) skip
 | sem_call : forall sn reg reg' f x l e benv rx, fv f = Some (l,e,benv,rx) -> 
           sem_qexp fv s_lit size sn (init_reg reg l) e sn reg' skip ->
           sem_qexp fv s_lit size sn reg (call f x) sn (qupdate reg x (reg' rx)) skip
 | sem_if_t : forall sn sn' reg ce e1 e2, sem_cexp s_lit size sn reg ce = Some (sn',true) ->
                 sem_qexp fv s_lit size sn reg (qif ce e1 e2) sn' reg e1
 | sem_if_f : forall sn sn' reg ce e1 e2, sem_cexp s_lit size sn reg ce = Some (sn',false) ->
                 sem_qexp fv s_lit size sn reg (qif ce e1 e2) sn' reg e2
 | sem_while : forall sn reg ce e,
                 sem_qexp fv s_lit size sn reg (qwhile ce e) sn reg ((qseq (qif ce e skip) (qwhile ce e)))
 | sem_qseq_con : forall sn reg e1 e2 sn' reg' e1',
                sem_qexp fv s_lit size sn reg e1 sn' reg' e1' ->
                  sem_qexp fv s_lit size sn reg (qseq e1 e2) sn' reg' (qseq e1' e2)
 | sem_qseq_skip : forall sn reg e, 
                  sem_qexp fv s_lit size sn reg (qseq skip e) sn reg e.


Fixpoint init_reg_g (l:list (btype * var * (nat -> bool))) : reg  :=
   match l with [] => (fun _ => allfalse)
             | ((t,x,v)::xl) => qupdate (init_reg_g xl) (G x) v
   end.

Inductive sem_prog (fv:fenv) : prog -> (nat -> bool) -> Prop :=
    sem_main : forall s_lit sloop size gl fl main rx' l e benv rx sn reg, 
         fv main = Some (l,e,benv,rx) ->
         sem_qexp fv s_lit size 0 (init_reg (init_reg_g gl) l) e sn reg skip ->
         sem_prog fv (s_lit,sloop,size,gl,fl,main,rx') (reg rx).

(*
Definition sem_prog (p:prog) : option (reg) :=
     match p with (slit,sloop,size,l,fl,f,rx) =>
         do fv <- type_prog p @
            do tu <- fv f @
              match tu with (vl,e,bsv,rex) => 
                do result <- sem_qexp fv slit sloop 0 size (init_reg (init_reg_g (fun _ => allfalse) vl) l) e @
                          match result with (sn',r') => ret (qupdate (fun _ => allfalse) (G rx) (r' rex))
                          end
              end
     end.
*)



(* Compilation from MiniQASM to VSQIR starts here. *)

Definition ac_size (size:nat) := S (S size).

(*
Definition find_factor_type (benv:benv) (fc:factor) : option atype :=
    match fc with (Var (L x)) => BEnv.find x benv
                | (Var (G x)) => Some Q
                | Num n => Some C
    end.
*)
Lemma xor_not : forall a b, xorb (a<?b) (b<?a) = false -> a = b.
Proof.
  intros.
  bdestruct (a <? b).
  bdestruct (b <? a). lia. simpl in H. inv H.
  bdestruct (b <? a). simpl in H. inv H.
  lia.
Qed.

Definition compare_c (size:nat) (reg:reg) (x y : factor) (stack:var) (sn:nat) (op : nat -> nat -> bool) := 
    match x with Num n =>
       match y with Num m =>   


(reg (L stack)) 

                 ret (sn,Reg.add (L stack) (update sv sn (op (a_nat2fb n size) (a_nat2fb m size))) reg)
                 | Var vy => 
                       (do y_val <- (Reg.find vy reg) @ do sv <- (Reg.find (L stack) reg) @
                     (ret (sn,Reg.add (L stack) (update sv sn (op (a_nat2fb n size) (a_nat2fb y_val size))) reg)))
      end
    | Var vx => 
      match y with Num m => 
        do x_val <- (Reg.find vx reg) @ do sv <- (Reg.find (L stack) reg) @ 
                           ret (sn,Reg.add (L stack) (update sv sn (op (a_nat2fb x_val size) (a_nat2fb m size))) reg)
        | Var vy => 
        do x_val <- (Reg.find vx reg) @ do sv <- (Reg.find (L stack) reg) @
               do y_val <- (Reg.find vy reg) @ 
           ret (sn,Reg.add (L stack) (update sv sn (op (a_nat2fb x_val size) (a_nat2fb y_val size))) reg)
      end
    end.

(*
Definition insert_circuit {A B:Type} (x:option (A,B)) (y:option ) := 
       match Reg.find x reg with None => None
              | Some vx => 
           match Reg.find y reg with None => None 
                | Some vy =>
            match Reg.find (L stack) reg with None => None
                | Some sv => Some (Reg.add (L stack) (update sv sn (a_nat2fb vx size <? a_nat2fb vy size)) reg)
            end
          end
       end.
*)

Definition rz_comparator (x:var) (n:nat) (c:posi) (M:nat) := 
    Exp (rz_sub x n (nat2fb M));; RQFT x ;; Exp (CNOT (x,0) c);; inv_pexp (Exp (rz_sub x n (nat2fb M));; RQFT x).


Definition lt_circuit (size:nat) (reg:reg) (vmap:var_map) (x y :qvar) (stack:var) (sn:nat)  :=
    do u <- (Reg.find x vmap) @
      do v <- (Reg.find y vmap) @
        do stackv <- (Reg.find (L stack) vmap) @
            do vx <- (Reg.find x reg) @
              ret (Exp (comparator01 (ac_size size) u v (stackv,S sn) (stackv,sn))). 

Definition lt_circuit_qft_l (size:nat) (reg:reg) (vmap:var_map) (x:qvar) (y:nat->bool) (stack:var) (sn:nat) :=
        do u <- (Reg.find x vmap) @
          do stackv <- (Reg.find (L stack) vmap) @
              ret (rz_comparator u (ac_size size) (stackv,sn) (a_nat2fb y size)).

Definition eq_circuit (size:nat) (reg:reg) (vmap:var_map) (x y :qvar) (stack:var) (sn:nat) :=
    do u <- (Reg.find x vmap) @
     do v <- (Reg.find y vmap) @
      do stackv <- (Reg.find (L stack) vmap) @
         do vx <- (Reg.find x reg) @
                ret (Exp (comparator01 (ac_size size) u v (stackv,S sn) (stackv,sn); 
                            comparator01 (ac_size size) v u(stackv,S sn) (stackv,sn); X (stackv,sn))).


Definition eq_circuit_qft_l (size:nat) (reg:reg) (vmap:var_map) (x:qvar) (y:nat->bool) (stack:var) (sn:nat)  :=
     do u <- Reg.find x vmap @ 
        do stackv <- Reg.find (L stack) vmap @
           ret (rz_comparator u (ac_size size) (stackv,sn) (a_nat2fb y size);; 
                rz_comparator u (ac_size size) (stackv,sn) (a_nat2fb y size) ;; Exp (X (stackv,sn))).


Definition insert_circuit (gv:option (nat * Reg.t (nat -> bool))) (e:option pexp)
              : option (option pexp * nat * Reg.t (nat -> bool)) :=
          match gv with None => None
               | Some (sn,reg) => Some (e,sn,reg)
          end.

Definition insert_init (e: option pexp) (size:nat) (x:qvar) (vmap:var_map) (reg:reg) : option pexp :=
  do e' <- e @ 
   do u <- Reg.find x vmap @
     do uv <- Reg.find x reg @
           ret (Exp (init_v (ac_size size) u uv) ;; e').

Definition circuit_lt_l (size :nat) (reg:reg) (vmap:var_map) (x y:factor) (stack:var) (sn:nat) := 
            match x with Num n => None
                      | Var vx => match y with Num yn => None
                                      | Var vy => (insert_init
                              (lt_circuit size reg vmap vx vy stack sn) size vy vmap reg)
                                  end
            end.

Definition circuit_lt_r (size :nat) (reg:reg) (vmap:var_map) (x y:factor) (stack:var) (sn:nat) := 
            match x with Num n => None
                      | Var vx => match y with Num yn =>
                                  (insert_init (lt_circuit_qft_l size reg vmap vx yn stack sn) size vx vmap reg)
                                      | Var vy => 
                                    (insert_init (lt_circuit size reg vmap vx vy stack sn) size vx vmap reg)
                                  end
            end.

Definition circuit_lt_m (size :nat) (reg:reg) (vmap:var_map) (x y:factor) (stack:var) (sn:nat) := 
            match x with Num n => None
                      | Var vx => match y with Num yn => lt_circuit_qft_l size reg vmap vx yn stack sn
                                      | Var vy => (lt_circuit size reg vmap vx vy stack sn)
                                  end
            end.

Definition circuit_eq_l (size :nat) (reg:reg) (vmap:var_map) (x y:factor) (stack:var) (sn:nat) := 
            match x with Num n => None
                      | Var vx => match y with Num n => None
                                      | Var vy =>
                                 (insert_init (eq_circuit size reg vmap vx vy stack sn) size vy vmap reg)
                                  end
            end.

Definition circuit_eq_r (size :nat) (reg:reg) (vmap:var_map) (x y:factor) (stack:var) (sn:nat) := 
            match x with Num n => None
                      | Var vx => match y with Num yn => 
                           (insert_init (eq_circuit_qft_l size reg vmap vx yn stack sn) size vx vmap reg)
                                      | Var vy => 
                            (insert_init (eq_circuit size reg vmap vx vy stack sn) size vx vmap reg)
                                  end
            end.

Definition circuit_eq_m (size :nat) (reg:reg) (vmap:var_map) (x y:factor) (stack:var) (sn:nat) := 
            match x with Num n => None
                      | Var vx => match y with Num yn => (eq_circuit_qft_l size reg vmap vx yn stack sn)
                                      | Var vy => (eq_circuit size reg vmap vx vy stack sn)
                                  end
            end.

Definition trans_cexp (sn sl size:nat) (stack temp:var) (benv:benv) (reg: reg) (vmap : var_map) (e:cexp) :=
      if sn <? sl then None else
          match e with clt f x y => 
           do cx <- find_factor_type benv x @
            do cy <- find_factor_type benv y @
                if (cx =a= C) && (cy =a= C) then
                      insert_circuit (compare_c size reg x y stack sn (Nat.ltb)) None
             else if (cx =a= C) && (cy =a= Q) then
                    insert_circuit (compare_c size reg x y stack sn (Nat.ltb)) (circuit_lt_l size reg vmap x y stack sn)
             else if (cx =a= Q) && (cy =a= C) then
                   insert_circuit (compare_c size reg x y stack sn (Nat.ltb)) (circuit_lt_r size reg vmap x y stack sn)
             else  insert_circuit (compare_c size reg x y stack sn (Nat.ltb)) (circuit_lt_m size reg vmap x y stack sn)
         | ceq f x y => 
           do cx <- find_factor_type benv x @
            do cy <- find_factor_type benv y @
                if (cx =a= C) && (cy =a= C) then
                      insert_circuit (compare_c size reg x y stack sn (Nat.eqb)) None
             else if (cx =a= C) && (cy =a= Q) then
                    insert_circuit (compare_c size reg x y stack sn (Nat.eqb)) (circuit_eq_l size reg vmap x y stack sn)
             else if (cx =a= Q) && (cy =a= C) then
                   insert_circuit (compare_c size reg x y stack sn (Nat.eqb)) (circuit_eq_r size reg vmap x y stack sn)
             else  insert_circuit (compare_c size reg x y stack sn (Nat.eqb)) (circuit_eq_m size reg vmap x y stack sn)
          end.

Definition find_stack_pos (reg:reg) (vmap :var_map) (stack:var) (sn:nat) := 
              match Reg.find (L stack) reg with None => None
                                           | Some st => Some (st sn)
                          end.

Definition combine_c (e1 e2:option pexp) : option pexp :=
          match e1 with None => e2
               | Some e1' => match e2 with None => None
                                        | Some e2' => Some (e1';;e2')
                              end
          end.

Definition add_two_c (size:nat) (reg:reg) (x:factor) (xa:atype) (y : qvar) (f:flag) (vmap : var_map) (stack:var) (sn:nat) :=
     do vn <- Reg.find y reg @
       match x with Num n => ret (None,sn,Reg.add y (cut_n (sumfb false n vn) size) reg)
         | Var vx => do vxn <- Reg.find vx reg @
                  if xa =a= C then ret (None,sn,Reg.add y (cut_n (sumfb false vn vxn) size) reg)
                   else 
                     do vy <- Reg.find y vmap @
                      do vx' <- Reg.find vx vmap @
                       ret (Some (match f with QFTA => Exp (rz_adder vy size vxn)
                                             | Classic => 
                                       Exp (init_v size vx' vxn ;adder01 size vx' vy (stack,sn);init_v size vx' vxn)
                                  end),sn,Reg.add y (cut_n (sumfb false vn vxn) size) reg)
        end.

Definition add_two_q (size:nat) (reg:reg) (x:factor) (xa:atype) (y : qvar) (f:flag) (vmap : var_map) (stack:var) (sn:nat) := 
    do vy <- Reg.find y vmap @
        match x with Num n => 
           do ny <- Reg.find y reg @ ret ((match f with QFTA => Some (Exp (rz_adder vy size n))
                              | Classic => None end),sn,Reg.add y (cut_n (sumfb false n ny) size) reg)
          | Var vx => 
            do ny <- Reg.find y reg @
               do nx <- Reg.find vx reg @
                 do vx' <- Reg.find vx vmap @
                if xa =a= C then
                  ret (Some (match f with QFTA => Exp (rz_adder vy size nx)
                                | Classic => Exp (init_v size vx' nx; adder01 size vx' vy (stack,sn); init_v size vx' nx)
                                    end),sn,Reg.add y (cut_n (sumfb false nx ny) size) reg)
               else ret ((match f with QFTA => None
                                | Classic => Some (Exp (adder01 size vx' vy (stack,sn)))
                                    end),sn,Reg.add y (cut_n (sumfb false nx ny) size) reg)
         end.

Definition sub_two_c (size:nat) (reg:reg) (x:factor) (xa:atype) (y : qvar) (f:flag) (vmap : var_map) (stack:var) (sn:nat) :=
   do vn <- Reg.find y reg @
      match x with Num n => ret (None,sn,Reg.add y (sumfb true n (negatem size vn)) reg)
        | Var vx => 
          do vxn <- Reg.find vx reg @
              if xa =a= C then ret (None,sn,Reg.add y (cut_n (sumfb true vn (negatem size vxn)) size) reg)
             else 
             do vy <- Reg.find y vmap @
               do vx' <- Reg.find vx vmap @
                ret (Some (match f with QFTA => Exp (rz_sub vy size vxn)
                             | Classic => Exp (init_v size vx' vxn ;subtractor01 size vx' vy (stack,sn);init_v size vx' vxn) end)
                         ,sn,Reg.add y (cut_n (sumfb true vn (negatem size vxn)) size) reg)
       end.

Definition sub_two_q (size:nat) (reg:reg) (x:factor) (xa:atype) (y : qvar) (f:flag) (vmap : var_map) (stack:var) (sn:nat) := 
   do vy <- Reg.find y vmap @
     do ny <- Reg.find y reg @
        match x with Num n => ret ((match f with QFTA => Some (Exp (rz_sub vy size n))
                              | Classic => None end),sn,Reg.add y (cut_n (sumfb true n (negatem size ny)) size) reg)
          | Var vx => 
         do nx <- Reg.find vx reg @
            do vx' <- Reg.find vx vmap @
               if xa =a= C then ret (Some (match f with QFTA => Exp (rz_sub vy size nx)
                                | Classic => Exp (init_v size vx' nx; subtractor01 size vx' vy (stack,sn); init_v size vx' nx)
                                    end),sn,Reg.add y (cut_n (sumfb true nx (negatem size ny)) size) reg)
              else ret ((match f with QFTA => None
                                | Classic => Some (Exp (subtractor01 size vx' vy (stack,sn)))
                                    end),sn,Reg.add y (cut_n (sumfb false nx ny) size) reg)
        end.

Definition fac_two_q (size:nat) (reg:reg) (x:var) (y : factor) := 
  match y with Num n => let ny := a_nat2fb n size in 
                    ret (Reg.add (L x) (cut_n (nat2fb (fact ny)) size) reg)
            | Var vy =>  
               do ny <- Reg.find vy reg @ let ny' := a_nat2fb ny size in 
                              ret (Reg.add (L x) (cut_n (nat2fb (fact ny')) size) reg)
  end.

Definition div_two_q (size:nat) (reg:reg) (x:var) (y : factor) (f:flag) := 
  match y with Num n =>
         do nx <- Reg.find (L x) reg @ ret (Reg.add (L x) (cut_n (nat2fb (a_nat2fb nx size / (a_nat2fb n size))) size) reg)
            | Var vy => 
       do ny <- Reg.find vy reg @
        do nx <- Reg.find (L x) reg @
            ret (Reg.add (L x) (cut_n (nat2fb (a_nat2fb nx size / (a_nat2fb ny size))) size) reg)
  end.

Definition combine_if (stack : var) (sn:nat) (vmap : var_map) (p1:pexp) (e1:option pexp) (e2:option pexp) :=
  do sv <- Reg.find (L stack) vmap @
     match e1 with None => match e2 with None => Some p1
                                  | Some e2' => Some (p1;; Exp (X (sv,sn)) ;; PCU (sv,sn) e2')
                           end
                  | Some e1' => match e2 with None => Some (p1;; PCU (sv,sn) e1')
                              | Some e2' => Some (p1;; (PCU (sv,sn) e1') ;; Exp (X (sv,sn)) ;; PCU (sv,sn) e2')
                                end
      end.


Definition combine_seq (e1:option pexp) (e2:option pexp) :=
   match e1 with None => e2
        | Some e1' => match e2 with None => Some e1' | Some e2' => Some (e1' ;; e2') end
   end.

Definition fmap :Type := list (fvar * pexp * qvar * var_map).
Fixpoint lookup_fmap (l:fmap) (x:var) : option (pexp * qvar * var_map) :=
   match l with [] => None
          | ((y,a,v,b)::xl) => if x =? y then Some (a,v,b) else lookup_fmap xl x
   end.

Fixpoint copyto (x y:var) size := match size with 0 => SKIP (x,0) 
                  | S m => CNOT (x,m) (y,m) ; copyto x y m
    end.

Fixpoint trans_qexp (sn sl size:nat) (stack temp:var) (benv:benv) (reg: reg) (vmap : var_map) (fmap:fmap) (e:qexp) (sloop:nat) :=
   match e with qwhile c e' => 
         let fix trans_while (sn sl size:nat) (stack temp:var) benv reg vmap fmap (sloop:nat) :=
            match sloop with 0 => Some (None,sn,reg)
                     | S m => match trans_cexp sn sl size stack temp benv reg vmap c with None => None 
                                | Some (cir,sn',reg') => 
                          match find_stack_pos reg vmap stack sn with Some true =>  
                                match trans_qexp sn' sl size stack temp benv reg' vmap fmap e' m
                                                                with None => None
                                                                   | Some (e_cir,sn'',reg'')
                                               => match trans_while sn'' sl size stack temp benv reg'' vmap fmap m with None => None
                                                             | Some (e2',sn3,reg3) =>
                                                         Some (combine_c (combine_c cir e_cir) e2',sn3,reg3)
                                                  end
                                 end
                             | Some false => Some (cir,sn',reg')
                             | None => None
                           end
                          end
            end in trans_while sn sl size stack temp benv reg vmap fmap sloop

           | qadd f x y => match find_factor_type benv (Var y) with None => None
                                      | Some C => match find_factor_type benv x with None => None
                                            | Some c => add_two_c size reg x c y f vmap stack sn
                                            end
                                      | Some Q => match find_factor_type benv x with None => None
                                          | Some c => add_two_q size reg x c y f vmap stack sn
                                       end
                             end
           | qsub f x y => match find_factor_type benv (Var y) with None => None
                                      | Some C => match find_factor_type benv x with None => None
                                            | Some c => sub_two_c size reg x c y f vmap stack sn
                                            end
                                      | Some Q => match find_factor_type benv x with None => None
                                          | Some c => sub_two_q size reg x c y f vmap stack sn
                                       end
                             end
           | qdiv f x y => do reg' <- div_two_q size reg x y f @ ret (None,sn,reg')
           | qfac x y => do reg' <- fac_two_q size reg x y @ ret (None,sn,reg')


           | qif ce e1 e2 => match trans_cexp sn sl size stack temp benv reg vmap ce with None => None
                               | Some (None,sn',reg') =>
                                    match Reg.find (L stack) reg' with None => None
                                         | Some st => if st sn then trans_qexp sn' sl size stack temp benv reg' vmap fmap e1 sloop
                                                        else trans_qexp sn' sl size stack temp benv reg' vmap fmap e2 sloop
                                    end
                               | Some (Some cir,sn',reg') => 
                match trans_qexp sn' sl size stack temp benv reg' vmap fmap e1 sloop with None => None
                    | Some ( e1',sn1,reg1) => 
                     match trans_qexp sn1 sl size stack temp benv reg1 vmap fmap e2 sloop with None => None
                      | Some ( e2',sn2,reg2) => Some (combine_if stack sn vmap cir e1' e2',sn2,reg2)
                     end
                 end
             end
           | qseq e1 e2 => match trans_qexp sn sl size stack temp benv reg vmap fmap e1 sloop with None => None
                    | Some ( e1',sn1,reg1) => 
                     match trans_qexp sn1 sl size stack temp benv reg1 vmap fmap e2 sloop with None => None
                      | Some ( e2',sn2,reg2) => Some (combine_seq e1' e2',sn2,reg2)
                     end
                 end
           | call f x => match lookup_fmap fmap f with None => None
                       | Some (e',u,vmap') => match Reg.find u vmap' with None => None
                                                  | Some u' => 
                                       match Reg.find x vmap with None => None
                                             | Some x' => Some (Some (e';; Exp (copyto u' x' size);;inv_pexp e'), sn,reg)
                                              end
                                       end
                        end
       | _ => None
   end.

Definition stack (l:list var) : var := S(list_max l).

Fixpoint gen_vmap_l' (l:list var) (vmap:var_map) (n:nat) :=
         match l with [] => vmap
              | (x::xl) => gen_vmap_l' xl (Reg.add (L x) n vmap) (S (S n))
         end.
Definition gen_vmap_l (l:list var) (vmap:var_map) := gen_vmap_l' l vmap 1.
 
Fixpoint trans_funs (fv:fenv) (sl size sloop:nat) (temp:var) (reg:reg) (vmap : var_map) (fmap:fmap) (l:list func) :=
    match l with [] => Some fmap
            | (( f , ls , e , rx)::xl) =>
                 match FEnv.find f fv with None => None
                           | Some (ls',e',benv,rx') => 
                    match trans_qexp 0 sl size (stack ls) temp benv (init_reg reg ((stack ls)::ls))
                       (gen_vmap_l ls vmap) fmap e sloop with None => None
                    | Some (None,sn1,reg1) => 
                    match Reg.find (G temp) vmap with None => None
                     | Some xt' => trans_funs fv sl size sloop temp reg vmap ((f,Exp (SKIP (xt',0)), rx, (gen_vmap_l ls vmap))::fmap) xl
                    end
                  | Some (Some e1,sn1,reg1) => 
                        trans_funs fv sl size sloop temp reg vmap ((f,e1, rx, (gen_vmap_l ls vmap))::fmap) xl
                    end
                 end
     end.


Fixpoint gen_vmap_g' (l:list var) (vmap:var_map) (n:nat) :=
         match l with [] => vmap
              | (x::xl) => gen_vmap_g' xl (Reg.add (G x) n vmap) (S (S n))
         end.
Definition gen_vmap_g (l:list var) (vmap:var_map) := gen_vmap_l' l vmap 0.

Definition temp (l:list var) : var := S(list_max l).

Definition trans_prog (p:prog) (fv:fenv) :=
   match p with (sl,sloop,size,m,ls,fl,f,rx') =>
      do fmap <- (trans_funs fv sl size sloop (temp ls) (init_reg_g empty_reg ls) (gen_vmap_g ls empty_var_map) [] fl) @
         match lookup_fmap fmap f with None => None
            | Some (e,x,vmap') => do ax <- Reg.find x vmap' @ Some (e;; copyto ax rx' size ;; inv_pexp e)
          end
   end.


