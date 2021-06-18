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

Definition qdty_eq  (t1 t2:(qvar * nat)) : bool := 
     (fst t1 =q= fst t2) && (snd t1 =? snd t2).

Notation "i '=qd=' j" := (qdty_eq i j) (at level 50).

Lemma qdty_eqb_eq : forall a b, a =qd= b = true -> a = b.
Proof.
 intros. unfold qdty_eq in H.
 destruct a. destruct b.
 apply andb_true_iff in H. destruct H.
 apply qty_eqb_eq in H.
 apply Nat.eqb_eq in H0. simpl in *. subst. easy.
Qed.

Lemma qdty_eqb_neq : forall a b, a =qd= b = false -> a <> b.
Proof.
 intros. unfold qdty_eq in H.
 destruct a. destruct b.
 apply andb_false_iff in H. destruct H.
 apply qty_eqb_neq in H. intros R. inv R. easy.
 apply Nat.eqb_neq in H.
 intros R. inv R. contradiction.
Qed.

Lemma qdty_eq_reflect : forall r1 r2, reflect (r1 = r2) (qdty_eq r1 r2). 
Proof.
  intros.
  destruct (r1 =qd= r2) eqn:eq1.
  apply  ReflectT.
  apply qdty_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply qdty_eqb_neq in eq1.
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

Hint Resolve aty_eq_reflect qty_eq_reflect qdty_eq_reflect bty_eq_reflect typ_eq_reflect : bdestruct.

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

Module QvarNatType <: OrderedType.

 Definition t : Type := (qvar * nat).

 Definition eq := @eq t.

 Definition lt_q (x y : qvar) := match x with
                                 L u => 
                                       match y with L v => (u < v)
                                                  | G v => True
                                       end
                                | G u =>
                                     match y with G v => (u < v)
                                                | L v => False
                                     end
                      end.

 Definition lt (x y : (qvar * nat)) := 
   (lt_q (fst x) (fst y)) \/ (~ lt_q (fst x) (fst y)
                  /\ (((fst x = fst y) /\ snd x < snd y))).

  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.


 Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
 Proof.
 intros. 
 unfold lt,lt_q in *.
 destruct x. destruct y. destruct z. simpl in *.
 destruct q. destruct q0. destruct q1. simpl in *.
 destruct H. destruct H0. left. lia.
 destruct H0 as [X1 [X2 X3]]. inv X2. left. easy.
 destruct H as [X1 [X2 X3]]. inv X2. destruct H0. left. easy.
 destruct H as [B1 [B2 B3]]. inv B2.
 right. split. easy. split. easy. lia.
 destruct H. destruct H0. easy.
 destruct H0 as [X1 [X2 X3]]. inv X2.
 destruct H0. left. easy.
 destruct H as [X1 [X2 X3]].
 destruct H0 as [B1 [B2 B3]].
 inv X2. inv B2.
 destruct H. easy.
 destruct H as [X1 [X2 X3]].
 inv X2.
 destruct q0. destruct q1.
 left. easy.
 destruct H. destruct H0. easy.
 destruct H0 as [X1 [X2 X3]].
 inv X2.
 destruct H0. easy.
 destruct H as [X1 [X2 X3]]. inv X2.
 destruct q1.
 destruct H. left. easy.
 left. easy.
 destruct H. destruct H0. left. lia.
 destruct H0 as [X1 [X2 X3]]. inv X2.
 left. easy.
 destruct H0.
 destruct H as  [X1 [X2 X3]]. inv X2.
 left. easy.
 destruct H as [X1 [X2 X3]]. inv X2.
 destruct H0 as [B1 [B2 B3]]. inv B2.
 right. split. easy. split. easy. lia.
 Qed.

 Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
 Proof.
 intros. 
 unfold lt,lt_q,eq in *.
 destruct x. destruct y. simpl in *.
 destruct q. destruct q0. simpl in *.
 destruct H. intros R. inv R. lia.
 destruct H as [X1 [X2 X3]].
 inv X2. intros R. inv R. lia.
 destruct H. easy.
 destruct H as  [X1 [X2 X3]]. inv X2.
 destruct q0.
 intros R. inv R.
 destruct H. intros R. inv R. lia.
 destruct H as  [X1 [X2 X3]]. inv X2.
 intros R. inv R. lia.
 Qed.

 Definition compare : forall x y : t, Compare lt eq x y.
 Proof.
 intros.
 destruct x. destruct y.
 destruct q. destruct q0.
 bdestruct (v <? v0).
 apply LT. unfold lt,lt_q.
 simpl in *. left. easy.
 bdestruct (v =? v0). subst.
 bdestruct (n <? n0).
 apply LT. unfold lt,lt_q. simpl in *.
 right. split. lia. split. easy. easy.
 bdestruct (n =? n0). subst.
 apply EQ; unfold eq;auto.
 apply GT;unfold lt,lt_q. simpl in *.
 right. split. lia. split. easy. lia.
 apply GT;unfold lt,lt_q. simpl in *.
 left. lia.
 apply GT;unfold lt,lt_q. simpl in *.
 left. lia.
 destruct q0.
 apply LT;unfold lt,lt_q. simpl in *.
 left. lia.
 bdestruct (v =? v0). subst.
 bdestruct (n <? n0).
 apply LT. unfold lt,lt_q.
 simpl in *.
 right. split. lia. split. easy. easy.
 bdestruct (n =? n0).
 apply EQ; unfold eq;auto.
 apply GT. unfold lt,lt_q.
 simpl in *.
 right. split. lia. split. easy. lia.
 bdestruct (v <? v0).
 apply LT. unfold lt,lt_q.
 simpl in *. left. easy.
 apply GT;unfold lt,lt_q. simpl in *.
 left. lia.
 Defined.

 Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
 Proof.
 intros; elim (compare x y); intro H; [ right | left | right ]; auto.
 auto using lt_not_eq.
 assert (~ eq y x); auto using lt_not_eq.
 unfold eq in *. intros R. subst. contradiction.
 Defined.

End QvarNatType.



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
                | nmul (f:flag) (x:cfac) (y:cfac) (z:cfac)
               (* | nqmul (f:flag) (v1:cfac) (v2:cfac) (z:cfac) *)
                | fadd (f:flag) (v:cfac) (x:cfac) 
                | fsub (f:flag) (v:cfac) (x:cfac)
                | fmul (f:flag) (v1:cfac) (v2:cfac) (z:cfac)
                | qxor (b:btype) (v:cfac) (x:cfac)
                | ndiv (x:cfac) (y:cfac) (v:cfac) (*x := y/n where x,n are a nat *)
                | nmod (x:cfac) (y:cfac) (v:cfac) (* x := y mod n where x,n are a nat *)
                | nfac (x:cfac) (v:cfac) (* x := n! where x is a nat & n is  nat *)
                | fdiv (x:cfac) (v:cfac) (* x := x / n where n is a natural number, x is a float. *)
                | ncsub (x:cfac) (y:cfac) (z:cfac) (* x := y - z all natural and C type *)
                | ncadd (x:cfac) (y:cfac) (z:cfac) (* x := y + z all natural and C type *)
                | fcsub (x:cfac) (y:cfac) (z:cfac) (* x := y - z all natural and C type *)
                | fcadd (x:cfac) (y:cfac) (z:cfac) (* x := y + z all natural and C type *)
                | ncmul (x:cfac) (y:cfac) (z:cfac) (* x := y * z all natural and C type *)
                | fndiv (x:cfac) (v:cfac) (z:cfac)(* z = x/v where x and v are natural numbers, z is float
                           x and v are both integers, but the final result in z must be a float < 1 *)
                | qinv (e:qexp)
                | call (f:fvar) (v: cfac)
                | qif (c:cexp) (e1:qexp) (e2:qexp)
                | qfor (x:var) (n:cfac) (e:qexp)
                | qseq (q1:qexp) (q2:qexp).

(*functions will do automatic inverse computation after a function is returned.
  for each ret statement, there is a list of pairs of vars, and the left one is the global variables to return,
   while the left one is the local variables. after a function call is returned,
    it will store all the local variables to their correponding global variables, and then reverse the computation.  *)

Notation "p1 ;;; p2" := (qseq p1 p2) (at level 50) : exp_scope.

Definition func : Type := ( fvar * list (btype * var * nat) * qexp * qvar).
    (* a function is a fun name, a starting block label, and a list of blocks, and the returned variable. *)

Definition prog : Type := (nat * nat * list (btype * var) * list func * fvar * var). 
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


Definition meet_type (t1 t2 : typ) := 
          match t1 with (Q,b) => (Q,b)
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
                       | S m => (2^m * (Nat.b2n (f m))) + a_nat2fb f m
             end.  


Definition allow_inv (e:qexp) : bool :=
   match e with skip | init _ _ _ | nadd _ _ _ | nsub _ _ _
              | nmul _ _ _ _ | fadd _ _ _ | fsub _ _ _ | fmul _ _ _ _ | qxor _ _ _ => true
             | _ => false
   end.

Definition is_q (t:typ) : bool := fst t =a= Q.

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

Fixpoint type_qexp (fv:fenv) (benv:benv) (e:qexp):=
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
                     if is_q re2 then
                       ret (qupdate benv core (Some (put_shell old (Q,Nat))))
                     else None

             | nsub f x y => 
             do re1 <- type_factor benv Nat x @
                do re2 <- type_factor benv Nat y @ 
                   do core <- get_var y @
                    do old <- benv core @
                     if is_q re2 then
                       ret (qupdate benv core (Some (put_shell old (Q,Nat))))
                     else None

             | nmul f x y z => 
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
                      if is_q re2 then
                       ret (qupdate benv core (Some (put_shell old (meet_type re1 re2))))
                      else None

             | fsub f x y => 
             do re1 <- type_factor benv Flt x @
                do re2 <- type_factor benv Flt y @ 
                   do core <- get_var y @
                    do old <- benv core @
                     if is_q re2 then 
                       ret (qupdate benv core (Some (put_shell old (meet_type re1 re2))))
                     else None

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

             | ndiv x y v => 
             do re1 <- type_factor benv Nat x @
                do re2 <- type_factor benv Nat y @ 
                  do re3 <- type_factor benv Nat v @ 
                       if is_q re1 || is_q re2 || is_q re3 then None else ret benv

             | nmod x y v => 
             do re1 <- type_factor benv Nat x @
                do re2 <- type_factor benv Nat y @ 
                  do re3 <- type_factor benv Nat v @ 
                       if is_q re1 || is_q re2 || is_q re3 then None else ret benv

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

             | ncadd x y z => 
             do re1 <- type_factor benv Nat x @
                do re2 <- type_factor benv Nat y @ 
                  do re3 <- type_factor benv Flt z @ 
                       if is_q re1 || is_q re2 || is_q re3 then None else ret benv

             | ncsub x y z => 
             do re1 <- type_factor benv Nat x @
                do re2 <- type_factor benv Nat y @ 
                  do re3 <- type_factor benv Flt z @ 
                       if is_q re1 || is_q re2 || is_q re3 then None else ret benv

             | fcadd x y z => 
             do re1 <- type_factor benv Flt x @
                do re2 <- type_factor benv Flt y @ 
                  do re3 <- type_factor benv Flt z @ 
                       if is_q re1 || is_q re2 || is_q re3 then None else ret benv

             | fcsub x y z => 
             do re1 <- type_factor benv Flt x @
                do re2 <- type_factor benv Flt y @ 
                  do re3 <- type_factor benv Flt z @ 
                       if is_q re1 || is_q re2 || is_q re3 then None else ret benv


             | ncmul x y z => 
             do re1 <- type_factor benv Nat x @
                do re2 <- type_factor benv Nat y @ 
                  do re3 <- type_factor benv Flt z @ 
                       if is_q re1 || is_q re2 || is_q re3 then None else ret benv


              | call f x => 
                 do ref <- fv f @
                   match ref with (tvl,e,fbenv, rx) =>
                        do re1 <- fbenv rx @
                              do core <- get_var x @
                           do old <- benv core @
                                ret (qupdate benv core
                                  (Some (put_shell old (meet_type (get_core re1) (get_core old)))))
                   end

              | qif ce e1 e2 => 
                 do rce <- type_cexp benv ce @
                   do benv' <- type_qexp fv benv e1 @
                       type_qexp fv benv' e2

              | qfor x n e => 
                 do re1 <- type_factor benv Nat (Nor (Var (L x))) @
                  do re2 <- type_factor benv Nat n @     
                     if is_q re1 || is_q re2 then None else type_qexp fv benv e

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

Fixpoint gen_genv (l:list (btype * var)) : benv := 
   match l with [] => (fun _ => None)
             | ((t,x)::xl) => qupdate (gen_genv xl) (G x) (Some (TNor (Q,t)))
   end.

(* ( fvar * list var * qexp ). *)
Definition type_prog (p:prog) : option fenv :=
   match p with (si,n,l,fl,main,rx) => 
      do fv <- type_funs (gen_genv l) (fun _ => None) fl @
            do block <- fv main @ ret fv
   end.

(*The semantics of QLLVM. *)
Module Reg := FMapList.Make QvarNatType.
Module RegFacts := FMapFacts.Facts (Reg).
Definition reg := Reg.t (nat -> bool).
Definition empty_reg := @Reg.empty (nat -> bool).

Definition sem_factor (size:nat) (r:reg) (b:btype) (fc:factor) := 
   match fc with Var x => Reg.find (x,0) r
            | Num n => match b with Bl => Some (cut_n n 1)
                                 | Nat => Some (cut_n n size)
                                 | Flt => Some (cut_n n size)
                       end
   end.

Definition sem_cfac (size:nat) (reg:reg) (b:btype) (fc:cfac) :=
    match fc with Ptr x n => do v <- (sem_factor size reg Nat n) @
                                  Reg.find (L x,a_nat2fb v size) reg
               | Nor x => sem_factor size reg b x
    end.


Definition sem_cexp (sl_size sn size:nat) (reg:reg) (ce:cexp) : option (nat * bool) :=
   if sn <? sl_size then
           match ce with clt f b x y => 
            do v1 <- (sem_cfac size reg b x) @
            do v2 <- (sem_cfac size reg b y) @
             match b with Bl => Some (S sn, a_nat2fb v1 1 <? a_nat2fb v2 1)
                       | _ => Some (S sn, a_nat2fb v1 size <? a_nat2fb v2 size)
             end
              | ceq f b x y => 
            do v1 <- (sem_cfac size reg b x) @
            do v2 <- (sem_cfac size reg b y) @
             match b with Bl => Some (S sn, a_nat2fb v1 1 =? a_nat2fb v2 1)
                         | _ => Some (S sn, a_nat2fb v1 size =? a_nat2fb v2 size)
             end
         | iseven x =>
            do v1 <- (sem_cfac size reg Nat x) @ Some (sn, (a_nat2fb v1 size) mod 2 =? 0)
          end
   else None.


Definition bin_xor (f1 f2:nat -> bool) (size:nat) :=
  cut_n (fun x => xorb (f1 x) (f2 x)) size.

Definition sub_def (f1 f2:nat -> bool) (size:nat) :=
         if a_nat2fb f1 size <? a_nat2fb f2 size then (a_nat2fb f1 size + 2^size - a_nat2fb f2 size) mod 2^size
                  else (a_nat2fb f1 size + a_nat2fb f2 size) mod 2^size.

Fixpoint init_reg_n (r:reg) (x:qvar) (n:nat) :=
   match n with 0 => r
          | S m => Reg.add (x,m) (nat2fb 0) (init_reg_n r x m)
   end.

Fixpoint init_reg (r:reg) (l:list (btype * var * nat)) : reg  :=
   match l with [] => r
             | ((t,x,n)::xl) => (init_reg (init_reg_n r (L x) n) xl)
   end.

Definition eval_var (size:nat) (r:reg) (x:cfac) :=
   match x with Ptr x n => do v <- (sem_factor size r Nat n) @ ret (L x,a_nat2fb v size)
              | Nor (Var x) => Some (x,0)
              | Nor (Num x) => None
   end.

Inductive sem_qexp (fv:fenv) (s_lit size:nat) : nat -> reg -> qexp -> nat -> reg -> Prop :=
   sem_qexp_skip : forall sn r, sem_qexp fv s_lit size sn r skip sn r
 | sem_qexp_init : forall sn r b x v xn x_val val,
           eval_var size r x = Some xn -> Reg.MapsTo xn x_val r ->
           sem_cfac size r b v = Some val ->  
            sem_qexp fv s_lit size sn r (init b x v) sn (Reg.add xn (bin_xor x_val val (if b =b= Bl then 1 else size)) r)
 | sem_qexp_nadd : forall sn r f x y yn y_val x_val, eval_var size r y = Some yn ->
            Reg.MapsTo yn y_val r -> sem_cfac size r Nat x = Some x_val ->
         sem_qexp fv s_lit size sn r (nadd f x y) sn (Reg.add yn (sumfb false x_val y_val) r)
 | sem_qexp_nsub : forall sn r f x y yn y_val x_val, eval_var size r y = Some yn ->
            Reg.MapsTo yn y_val r -> sem_cfac size r Nat x = Some x_val ->
         sem_qexp fv s_lit size sn r (nsub f x y) sn (Reg.add yn (sumfb true x_val (negatem size y_val)) r)
 | sem_qexp_nmul : forall sn r f x y z zn x_val y_val,
          eval_var size r z = Some zn -> sem_cfac size r Nat x = Some x_val
        -> sem_cfac size r Nat y = Some y_val -> Reg.MapsTo zn (nat2fb 0) r ->
         sem_qexp fv s_lit size sn r (nmul f x y z) sn (Reg.add zn
             (nat2fb (((a_nat2fb x_val size) * (a_nat2fb y_val size)) mod 2^size)) r)
 | sem_qexp_fadd : forall sn r f x y yn y_val x_val, eval_var size r y = Some yn ->
            Reg.MapsTo yn y_val r -> sem_cfac size r Flt x = Some x_val ->
         sem_qexp fv s_lit size sn r (fadd f x y) sn (Reg.add yn (sumfb false x_val y_val) r)
 | sem_qexp_fsub : forall sn r f x y yn y_val x_val, eval_var size r y = Some yn ->
            Reg.MapsTo yn y_val r -> sem_cfac size r Flt x = Some x_val ->
         sem_qexp fv s_lit size sn r (fsub f x y) sn (Reg.add yn (sumfb true x_val (negatem size y_val)) r)
 | sem_qexp_fmul : forall sn r f x y z zn x_val y_val,
          eval_var size r z = Some zn -> sem_cfac size r Flt x = Some x_val
        -> sem_cfac size r Flt y = Some y_val -> Reg.MapsTo zn (nat2fb 0) r ->
         sem_qexp fv s_lit size sn r (fmul f x y z) sn (Reg.add zn
             (nat2fb (((a_nat2fb x_val size) * (a_nat2fb y_val size)) / 2^size)) r)
 | sem_qexp_xor : forall sn r b x y yn y_val x_val, eval_var size r y = Some yn ->
            Reg.MapsTo yn y_val r -> sem_cfac size r b x = Some x_val ->
         sem_qexp fv s_lit size sn r (qxor b x y) sn (Reg.add yn (bin_xor x_val y_val (if b =b= Bl then 1 else size)) r)
 | sem_qexp_nfac : forall sn r x y xn y_val, eval_var size r x = Some xn ->
              sem_cfac size r Nat y = Some y_val -> 
        sem_qexp fv s_lit size sn r (nfac x y) sn (Reg.add xn (nat2fb (fact (a_nat2fb y_val size) mod 2^size)) r)

 | sem_qexp_ndiv : forall sn r x y z xn y_val z_val, eval_var size r x = Some xn ->
              sem_cfac size r Nat y = Some y_val -> sem_cfac size r Nat z = Some z_val -> 
        sem_qexp fv s_lit size sn r (ndiv x y z) sn (Reg.add xn (nat2fb ((a_nat2fb y_val size) / (a_nat2fb z_val size))) r)

 | sem_qexp_nmod : forall sn r x y z xn y_val z_val, eval_var size r x = Some xn ->
              sem_cfac size r Nat y = Some y_val -> sem_cfac size r Nat z = Some z_val -> 
        sem_qexp fv s_lit size sn r (nmod x y z) sn (Reg.add xn (nat2fb ((a_nat2fb y_val size) mod (a_nat2fb z_val size))) r)
 
 | sem_qexp_ncadd : forall sn r x y z xn y_val z_val, eval_var size r x = Some xn ->
              sem_cfac size r Nat y = Some y_val -> sem_cfac size r Nat z = Some z_val -> 
        sem_qexp fv s_lit size sn r (ncadd x y z) sn (Reg.add xn (nat2fb ((a_nat2fb y_val size) + (a_nat2fb z_val size))) r)

 | sem_qexp_ncsub : forall sn r x y z xn y_val z_val, eval_var size r x = Some xn ->
              sem_cfac size r Nat y = Some y_val -> sem_cfac size r Nat z = Some z_val -> 
        sem_qexp fv s_lit size sn r (ncsub x y z) sn (Reg.add xn (nat2fb ((a_nat2fb y_val size) - (a_nat2fb z_val size))) r)

 | sem_qexp_ncmul : forall sn r x y z xn y_val z_val, eval_var size r x = Some xn ->
              sem_cfac size r Nat y = Some y_val -> sem_cfac size r Nat z = Some z_val -> 
        sem_qexp fv s_lit size sn r (ncmul x y z) sn (Reg.add xn (nat2fb ((a_nat2fb y_val size) * (a_nat2fb z_val size))) r)

 | sem_qexp_fcadd : forall sn r x y z xn y_val z_val, eval_var size r x = Some xn ->
              sem_cfac size r Flt y = Some y_val -> sem_cfac size r Flt z = Some z_val -> 
        sem_qexp fv s_lit size sn r (fcadd x y z) sn (Reg.add xn (nat2fb ((a_nat2fb y_val size) + (a_nat2fb z_val size))) r)

 | sem_qexp_fcsub : forall sn r x y z xn y_val z_val, eval_var size r x = Some xn ->
              sem_cfac size r Flt y = Some y_val -> sem_cfac size r Flt z = Some z_val -> 
        sem_qexp fv s_lit size sn r (fcsub x y z) sn (Reg.add xn (nat2fb ((a_nat2fb y_val size) - (a_nat2fb z_val size))) r)

 | sem_qexp_fdiv : forall sn r x y xn x_val y_val, eval_var size r x = Some xn ->
              Reg.MapsTo xn x_val r -> sem_cfac size r Nat y = Some y_val -> 
        sem_qexp fv s_lit size sn r (fdiv x y) sn (Reg.add xn (nat2fb (((a_nat2fb x_val size)) / (a_nat2fb y_val size))) r)

 | sem_qexp_fndiv : forall sn r x y z xn y_val z_val, eval_var size r x = Some xn ->
              sem_cfac size r Flt y = Some y_val -> sem_cfac size r Flt z = Some z_val -> 
              (a_nat2fb y_val size) < (a_nat2fb z_val size) ->
        sem_qexp fv s_lit size sn r (fndiv x y z) sn 
             (Reg.add xn (nat2fb (((a_nat2fb y_val size) * 2^size) / (a_nat2fb z_val size))) r)

 | sem_qexp_qinv_init : forall sn r b x v xn x_val val,
           eval_var size r x = Some xn -> Reg.MapsTo xn x_val r ->
           sem_cfac size r b v = Some val ->  
            sem_qexp fv s_lit size sn r (qinv(init b x v)) sn (Reg.add xn (bin_xor x_val val (if b =b= Bl then 1 else size)) r)

 | sem_qexp_qinv_nadd : forall sn r f x y yn y_val x_val, eval_var size r y = Some yn ->
            Reg.MapsTo yn y_val r -> sem_cfac size r Nat x = Some x_val ->
         sem_qexp fv s_lit size sn r (qinv(nadd f x y)) sn (Reg.add yn (sumfb true x_val (negatem size y_val)) r)
 | sem_qexp_qinv_nsub : forall sn r f x y yn y_val x_val, eval_var size r y = Some yn ->
            Reg.MapsTo yn y_val r -> sem_cfac size r Nat x = Some x_val ->
         sem_qexp fv s_lit size sn r (qinv(nsub f x y)) sn (Reg.add yn (sumfb false x_val y_val)  r)
 | sem_qexp_qinv_nmul : forall sn r f x y z zn,
          eval_var size r z = Some zn ->
         sem_qexp fv s_lit size sn r (qinv (nmul f x y z)) sn (Reg.add zn (nat2fb 0) r)
 | sem_qexp_qinv_fadd : forall sn r f x y yn y_val x_val, eval_var size r y = Some yn ->
            Reg.MapsTo yn y_val r -> sem_cfac size r Flt x = Some x_val ->
         sem_qexp fv s_lit size sn r (qinv(fadd f x y)) sn (Reg.add yn (sumfb true x_val (negatem size y_val)) r)
 | sem_qexp_qinv_fsub : forall sn r f x y yn y_val x_val, eval_var size r y = Some yn ->
            Reg.MapsTo yn y_val r -> sem_cfac size r Flt x = Some x_val ->
         sem_qexp fv s_lit size sn r (qinv(fsub f x y)) sn (Reg.add yn (sumfb false x_val y_val)  r)
 | sem_qexp_qinv_fmul : forall sn r f x y z zn,
          eval_var size r z = Some zn ->
         sem_qexp fv s_lit size sn r (qinv (fmul f x y z)) sn (Reg.add zn (nat2fb 0) r)
 | sem_qexp_qinv_xor : forall sn r b x y yn y_val x_val, eval_var size r y = Some yn ->
            Reg.MapsTo yn y_val r -> sem_cfac size r b x = Some x_val ->
         sem_qexp fv s_lit size sn r (qxor b x y) sn (Reg.add yn (bin_xor x_val y_val (if b =b= Bl then 1 else size)) r)

 | sem_qexp_if_t : forall sn r ce e1 e2 sn' sn1 r1, sem_cexp s_lit size sn r ce = Some (sn',true) ->
                    sem_qexp fv s_lit size sn' r e1 sn1 r1 -> 
                    sem_qexp fv s_lit size sn r (qif ce e1 e2) sn1 r1
 | sem_qexp_if_f : forall sn r ce e1 e2 sn' sn1 r1, sem_cexp s_lit size sn r ce = Some (sn',false) ->
                    sem_qexp fv s_lit size sn' r e2 sn1 r1 -> 
                    sem_qexp fv s_lit size sn r (qif ce e1 e2) sn1 r1
 | sem_qexp_call : forall sn r r' f x xn l e benv rx val, fv f = Some (l,e,benv,rx) -> 
           sem_qexp fv s_lit size sn (init_reg r l) e sn r' ->
       eval_var size r x = Some xn -> Reg.find (rx,0) r' = Some val ->
           sem_qexp fv s_lit size sn r (call f x) sn (Reg.add xn val r)
 | sem_qexp_for : forall sn r x n e sn' r' nv,
                sem_cfac size r Nat n = Some nv ->
                 sem_for_exp fv s_lit size sn (Reg.add (L x,0) (nat2fb 0) r)
                   e x (a_nat2fb nv size) sn' r' ->
                           sem_qexp fv s_lit size sn r (qfor x n e) sn' r'

 | sem_qexp_qseq : forall sn r e1 e2 sn' r' sn'' r'',
                sem_qexp fv s_lit size sn r e1 sn' r' ->
                sem_qexp fv s_lit size sn' r' e2 sn'' r'' ->
                  sem_qexp fv s_lit size sn r (qseq e1 e2) sn' r'


with sem_for_exp (fv:fenv) (s_lit size:nat): nat -> reg -> qexp -> var -> nat -> nat -> reg -> Prop :=
  | sem_for_empty : forall sn r x e, sem_for_exp fv s_lit size sn r e x 0 sn r
  | sem_for_many : forall sn r x m e sn' r' sn'' r'' x_val,
    sem_qexp fv s_lit size sn r e sn' r' ->
     Reg.MapsTo (L x,0) x_val r' ->
     sem_for_exp fv s_lit size sn' (Reg.add (L x,0) (nat2fb ((a_nat2fb x_val size) + 1)) r') e x m sn'' r'' ->
     sem_for_exp fv s_lit size sn r e x (S m) sn'' r''.

Fixpoint check_reg_g (l:list (btype * var)) (r:reg) : Prop  :=
   match l with [] => True
             | ((t,x)::xl) => Reg.In (G x,0) r /\ check_reg_g xl r
   end.

Inductive sem_prog (fv:fenv) : reg -> prog -> (nat -> bool) -> Prop :=
    sem_main : forall s_lit size gl fl main rx' l e benv rx sn r r' v, 
         fv main = Some (l,e,benv,rx) -> check_reg_g gl r ->
         sem_qexp fv s_lit size 0 r e sn r' ->
         Reg.find (rx,0) r' = Some v ->
         sem_prog fv r (s_lit,size,gl,fl,main,rx') v.

Fixpoint collect_cvars (bv:benv) (e:qexp) : list qvar :=
   match e with skip
              | init _ _ _
              | nadd _ _ _
              | nsub _ _ _ 
              | nmul _ _ _ _
              | fadd _ _ _ 
              | fsub _ _ _
              | fmul _ _ _ _ => []
              | qxor b v x => match get_var x with None => []
                                             | Some xn => match bv xn with None => []
                                                    | Some t => if is_q (get_core t) then [] else [xn]
                                                         end
                              end
               | ndiv x y z => match get_var x with None => [] | Some xn => [xn] end
               | nmod x y z => match get_var x with None => [] | Some xn => [xn] end
               | nfac x y => match get_var x with None => [] | Some xn => [xn] end
               | fdiv x y => match get_var x with None => [] | Some xn => [xn] end
               | ncsub x y z => match get_var x with None => [] | Some xn => [xn] end
               | ncadd x y z => match get_var x with None => [] | Some xn => [xn] end
               | fcsub x y z => match get_var x with None => [] | Some xn => [xn] end
               | fcadd x y z => match get_var x with None => [] | Some xn => [xn] end
               | ncmul x y z => match get_var x with None => [] | Some xn => [xn] end
               | fndiv x y z => match get_var z with None => [] | Some xn => [xn] end
               | qinv e => collect_cvars bv e
               | call f x => match get_var x with None => []
                                             | Some xn => match bv xn with None => []
                                                    | Some t => if is_q (get_core t) then [] else [xn]
                                                         end
                              end
               | qif ce e1 e2 => []
               | qfor x n e => collect_cvars bv e
               | qseq x y => (collect_cvars bv x)++(collect_cvars bv y)
   end.

Definition in_scope_cfac (l:list qvar) (e:cfac) :=
   match e with Nor (Num x) => True
             | Nor (Var x) => In x l
             | Ptr x (Num n) => In (L x) l
             | Ptr x (Var y) => In (L x) l /\ In y l
   end.

Definition in_scope_if_cexp (l:list qvar) (e:cexp) : Prop :=
    match e with clt f b x y => in_scope_cfac l x /\ in_scope_cfac l y
               | ceq f b x y => in_scope_cfac l x /\ in_scope_cfac l y
               | iseven x => in_scope_cfac l x
    end.

Fixpoint in_scope_if (l:list qvar) (e:qexp): Prop :=
   match e with skip => True
              | init b x y => in_scope_cfac l x /\ in_scope_cfac l y
              | nadd b x y => in_scope_cfac l x /\ in_scope_cfac l y
              | nsub b x y => in_scope_cfac l x /\ in_scope_cfac l y
              | nmul b x y z => in_scope_cfac l x /\ in_scope_cfac l y /\ in_scope_cfac l z
              | fadd b x y => in_scope_cfac l x /\ in_scope_cfac l y
              | fsub b x y => in_scope_cfac l x /\ in_scope_cfac l y
              | fmul b x y z => in_scope_cfac l x /\ in_scope_cfac l y /\ in_scope_cfac l z
              | qxor b x y => in_scope_cfac l x /\ in_scope_cfac l y
              | ndiv x y z => in_scope_cfac l x /\ in_scope_cfac l y /\ in_scope_cfac l z
              | nmod x y z => in_scope_cfac l x /\ in_scope_cfac l y /\ in_scope_cfac l z
              | nfac x y => in_scope_cfac l x /\ in_scope_cfac l y
              | fdiv x y => in_scope_cfac l x /\ in_scope_cfac l y
              | ncsub x y z => in_scope_cfac l x /\ in_scope_cfac l y /\ in_scope_cfac l z
              | ncadd x y z => in_scope_cfac l x /\ in_scope_cfac l y /\ in_scope_cfac l z
              | fcsub x y z => in_scope_cfac l x /\ in_scope_cfac l y /\ in_scope_cfac l z
              | fcadd x y z => in_scope_cfac l x /\ in_scope_cfac l y /\ in_scope_cfac l z
              | ncmul x y z => in_scope_cfac l x /\ in_scope_cfac l y /\ in_scope_cfac l z
              | fndiv x y z => in_scope_cfac l x /\ in_scope_cfac l y /\ in_scope_cfac l z
              | qinv e => in_scope_if l e
              | call f x => in_scope_cfac l x
              | qif ce e1 e2 => in_scope_if_cexp l ce /\ in_scope_if l e1 /\ in_scope_if l e2
              | qfor x n e => in_scope_if (@List.remove qvar (QvarType.eq_dec) (L x) l) e
              | qseq e1 e2 => in_scope_if l e1 /\ in_scope_if l e2
    end.

Definition is_qseq (x:qexp) := match x with a ;;; b => True | _ => False end.

Inductive in_scope_ifs (l:list qvar) : list qexp -> Prop :=
   in_scope_if_empty : in_scope_ifs l []
   | in_scope_if_many: forall e el, in_scope_if l e -> in_scope_ifs l el -> in_scope_ifs l (e:: el).

Fixpoint turn_qseq_lst (e:qexp) :=
   match e with (e1 ;;; e2) => turn_qseq_lst e1 ++ turn_qseq_lst e2
             | e => [e]
   end.

Inductive well_formed_qexp (bv:benv) : qexp -> list qexp -> Prop :=
  | wtq_skip : forall el, well_formed_qexp bv skip el
  | wtq_init : forall el b x v, well_formed_qexp bv (init b x v) el
  | wtq_nadd : forall el b x v, well_formed_qexp bv (nadd b x v) el
  | wtq_nsub : forall el b x v, well_formed_qexp bv (nsub b x v) el
  | wtq_nmul: forall el b x y z, well_formed_qexp bv (nmul b x y z) el
  | wtq_fadd : forall el b x v, well_formed_qexp bv (fadd b x v) el
  | wtq_fsub : forall el b x v, well_formed_qexp bv (fsub b x v) el
  | wtq_fmul : forall el b x y z, well_formed_qexp bv (fmul b x y z) el
  | wtq_qxor : forall el b x v, well_formed_qexp bv (fsub b x v) el
  | wtq_ndiv : forall el x y z, well_formed_qexp bv (ndiv x y z) el
  | wtq_nmod : forall el x y z, well_formed_qexp bv (nmod x y z) el
  | wtq_nfac : forall el x y, well_formed_qexp bv (nfac x y) el
  | wtq_fdiv : forall el x y, well_formed_qexp bv (fdiv x y) el
  | wtq_ncsub : forall el x y z, well_formed_qexp bv (ncsub x y z) el
  | wtq_ncadd : forall el x y z, well_formed_qexp bv (ncadd x y z) el
  | wtq_fcsub : forall el x y z, well_formed_qexp bv (fcsub x y z) el
  | wtq_fcadd : forall el x y z, well_formed_qexp bv (fcadd x y z) el
  | wtq_ncmul : forall el x y z, well_formed_qexp bv (ncmul x y z) el
  | wtq_fndiv : forall el x y z, well_formed_qexp bv (fndiv x y z) el
  | wtq_qinv : forall el e, well_formed_qexp bv e el -> well_formed_qexp bv (qinv e) el
  | wtq_call : forall el f x, well_formed_qexp bv (call f x) el
  | wtq_if_q : forall el ce t e1 e2, type_cexp bv ce = Some t -> is_q t = true -> 
                    in_scope_ifs (collect_cvars bv e1 ++ collect_cvars bv e2) el ->
                    well_formed_qexps bv (turn_qseq_lst e1) -> well_formed_qexps bv (turn_qseq_lst e2) ->
                    well_formed_qexp bv (qif ce e1 e2) el
  | wtq_if_c : forall el ce t e1 e2, type_cexp bv ce = Some t -> is_q t = false -> 
                    well_formed_qexps bv (turn_qseq_lst e1) -> well_formed_qexps bv (turn_qseq_lst e2) ->
                    well_formed_qexp bv (qif ce e1 e2) el
  | wtq_for : forall el x n e,  well_formed_qexps bv (turn_qseq_lst e) ->  well_formed_qexp bv (qfor x n e) el
with well_formed_qexps (bv:benv) : list qexp -> Prop :=
    well_formed_qexps_empty : well_formed_qexps bv []
  | well_formed_qexps_many : forall x xl, well_formed_qexp bv x xl -> well_formed_qexps bv xl -> well_formed_qexps bv (x :: xl).

Definition inter_range (x : var) (n:nat) (y:var) (m:nat) :=
     (x <= y < (x+n)) \/ (x < y + m <= (x + n)) \/ (y < x /\ x+n < y+m).

Inductive diff_vars:  list (btype * var * nat) -> var -> nat -> Prop :=
    diff_vars_empty : forall x n, diff_vars ([]) x n
  | diff_vars_many : forall b y m yl x n, ~ inter_range x n y m -> diff_vars yl x n -> diff_vars ((b,y,m)::yl) x n.

Inductive diff_var_lst : list (btype * var * nat) -> list (btype * var * nat) -> Prop :=
   diff_var_lst_empty : forall l, diff_var_lst l []
 | diff_var_lst_many : forall b x n l1 l2, diff_vars l2 x n -> diff_var_lst l1 ((b,x,n)::l2) -> diff_var_lst ((b,x,n)::l1) l2.

Inductive well_formed_func (bv:benv) : list (btype * var * nat) -> list func -> Prop :=
   well_formed_func_empty : forall olds, well_formed_func bv olds []
 | well_formed_func_many : forall f args e rx olds xl, well_formed_qexps bv (turn_qseq_lst e) 
               -> diff_var_lst ([]) (olds++args) -> well_formed_func bv olds ((f,args,e,rx)::xl).


Definition is_qt (b:ttyp) := 
   match b with TNor t => is_q t
             | TPtr x n => is_q x
   end.

Definition par_eval_fc (size:nat) (bv:benv) (reg:reg) (b:btype) (fc:factor) := 
   match fc with Var x => do re <- bv x @ if is_qt re then None else (Reg.find (x,0) reg)
            | Num n => match b with Bl => Some (cut_n n 1)
                                 | Nat => Some (cut_n n size)
                                 | Flt => Some (cut_n n size)
                       end
   end.

Definition par_eval_cfac (size:nat) (smap : qvar -> nat) (bv:benv) (reg:reg) (b:btype) (fc:cfac) := 
   match fc with Nor x => par_eval_fc size bv reg b x
        | Ptr x n => do v <- par_eval_fc size bv reg Nat n @
                              if a_nat2fb v size <? smap (L x) then
                               (do re <- bv (L x) @ if is_qt re then None else (Reg.find (L x,a_nat2fb v size) reg)) else None
   end.

Definition par_find_var (size:nat) (bv:benv) (reg:reg) (fc:cfac) :=
       match fc with Nor (Var x) => Some (x,0)
                  | Nor (Num x) => None
                  | Ptr x n => do val <- par_eval_fc size bv reg Nat n @ Some (L x,a_nat2fb val size)
       end.

Definition get_vars (size:nat) (bv:benv) (reg:reg) (e:qexp) :=
   match e with skip => Some ([])
              | init b x y => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ ret (var1::var2::[])
              | nadd b x y => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ ret (var1::var2::[])
              | nsub b x y => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ ret (var1::var2::[])
              | nmul b x y z => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ 
                                   do var3 <- par_find_var size bv reg z @  ret (var1::var2::var3::[])
              | fadd b x y => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ ret (var1::var2::[])

              | fsub b x y => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ ret (var1::var2::[])
              | fmul b x y z => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ 
                                   do var3 <- par_find_var size bv reg z @  ret (var1::var2::var3::[])
              | qxor b x y => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ ret (var1::var2::[])
              | ndiv x y z => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ 
                                   do var3 <- par_find_var size bv reg z @  ret (var1::var2::var3::[])

              | nmod x y z => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ 
                                   do var3 <- par_find_var size bv reg z @  ret (var1::var2::var3::[])
              | nfac x y => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ ret (var1::var2::[])
              | fdiv x y => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ ret (var1::var2::[])

              | ncsub x y z => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ 
                                   do var3 <- par_find_var size bv reg z @  ret (var1::var2::var3::[])
              | ncadd x y z => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ 
                                   do var3 <- par_find_var size bv reg z @  ret (var1::var2::var3::[])
              | fcsub x y z => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ 
                                   do var3 <- par_find_var size bv reg z @  ret (var1::var2::var3::[])
              | fcadd x y z => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ 
                                   do var3 <- par_find_var size bv reg z @  ret (var1::var2::var3::[])
              | ncmul x y z => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ 
                                   do var3 <- par_find_var size bv reg z @  ret (var1::var2::var3::[])
              | fndiv x y z => do var1 <- par_find_var size bv reg x @
                                  do var2 <- par_find_var size bv reg y @ 
                                   do var3 <- par_find_var size bv reg z @  ret (var1::var2::var3::[])

              | qinv e => None
              | call f x => do var1 <- (par_find_var size bv reg x) @ ret ([var1])
              | qif ce e1 e2 => None
              | qfor x n e => None
              | qseq e1 e2 => None
   end.


Definition is_qinv (x:qexp) := match x with qinv e => True | _ => False end.

Definition is_no_pass (x:qexp) := match x with qinv _ | qif _ _ _ | qfor _ _ _ | qseq _ _ => True | _ => False end.

Definition intersection (l1 l2 : list (qvar * nat)) : list (qvar * nat) :=
  List.filter (fun n => List.existsb (qdty_eq n) l2) l1.

Lemma intersectionP l1 l2 n : In n (intersection l1 l2) <-> In n l1 /\ In n l2.
Proof.
unfold intersection.
rewrite filter_In, existsb_exists; split.
- intros [H1 [m [H2 e]]]; split; trivial.
  apply qdty_eqb_eq in e. subst. easy.
- intros [H1 H2]; split; trivial.
  exists n. split. easy.
  bdestruct (n =qd= n). easy. easy.
Qed.


Inductive inv_match (l:list (qvar * nat)) (size:nat) (bv:benv) (reg:reg) (x:qexp) : list qexp -> option (list qexp) -> Prop :=
     inv_match_empty : inv_match l size bv reg x [] None
    | inv_match_many_1 : forall y yl , x = y -> inv_match l size bv reg x (y::yl) (Some yl)
    | inv_match_many_2 : forall y yl l' b, x <> y -> (get_vars size bv reg y) = Some l' -> intersection l l'  <> []
                                 -> inv_match l size bv reg x yl b -> inv_match l size bv reg x (y::yl) b.

Inductive inv_well_match_l (size:nat) (bv:benv) (reg:reg) : list qexp -> list qexp -> Prop :=
     inv_well_match_empty : forall el, inv_well_match_l size bv reg [] el
   | inv_well_match_many_1 : forall l e xl el el', get_vars size bv reg e = Some l ->
             inv_match l size bv reg e el (Some el') -> 
                inv_well_match_l size bv reg xl el'
   | inv_well_match_many_2 : forall x xl el, is_no_pass x ->
               inv_well_match_l size bv reg xl [] -> inv_well_match_l size bv reg (x::xl) el
   | inv_well_match_many_3 : forall x xl el, ~ is_no_pass x ->
               inv_well_match_l size bv reg xl (x::el) -> inv_well_match_l size bv reg (x::xl) el.

Definition inv_well_match (size:nat) (bv:benv) (reg:reg) (e:qexp) : Prop :=
    inv_well_match_l size bv reg (turn_qseq_lst e) [].


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

Definition qvar_eq (size:nat) (bv:benv) (reg:reg) (x y: cfac) := 
        match par_find_var size bv reg x with None => false
                    | Some a => match par_find_var size bv reg x with None => false
                         | Some b => (a =qd= b)
                                end
        end.

Definition rz_comparator (x:var) (n:nat) (c:posi) (M:nat) := 
    Exp (rz_sub x n (nat2fb M));; RQFT x ;; Exp (CNOT (x,0) c);; inv_pexp (Exp (rz_sub x n (nat2fb M));; RQFT x).

Definition gen_clt_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (r:reg) (b:btype) (stack:var) (sn:nat) (x y: cfac) : option (option pexp * nat * option bool) := 
     do t1 <- type_factor bv b x @
         do t2 <- type_factor bv b y @
             do vx <- par_find_var size bv r x @  
               do vy <- par_find_var size bv r y @
              if is_q t1 && (¬ (is_q t2))
               then 
                   do t2v <- par_eval_cfac size smap bv r b y @
                      Some (Some (Exp (init_v size (vmap vy) t2v;
                         comparator01 (if b =b= Bl then 1 else size) (vmap vy) (vmap vx) (vmap (L stack,0),S sn)
                                    (vmap (L stack,0),sn) ;init_v size (vmap vy) t2v)),S sn,None)
                else if is_q t1 && (is_q t2) then
                       Some (Some (Exp (comparator01 (if b =b= Bl then 1 else size) (vmap vy) (vmap vx) 
                              (vmap (L stack,0),S sn) (vmap (L stack,0),sn))),S sn, None)
                else if (¬ (is_q t1)) && (is_q t2) then
                   do t1v <- par_eval_cfac size smap bv r b x @
                       Some (Some (Exp (init_v size (vmap vy) t1v;
                         comparator01 (if b =b= Bl then 1 else size) (vmap vy) (vmap vx)
                    (vmap (L stack,0),S sn) (vmap (L stack,0),sn) ;init_v size (vmap vy) t1v)),S sn,None)
                else do t1v <- par_eval_cfac size smap bv r b x @
                      do t2v <- par_eval_cfac size smap bv r b y @
                           Some (None,sn,Some (a_nat2fb t1v size <? a_nat2fb t2v size)).

Definition gen_ceq_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (r:reg) (b:btype) (stack:var) (sn:nat) (x y: cfac) : option (option pexp * nat * option bool) := 
     do t1 <- type_factor bv b x @
         do t2 <- type_factor bv b y @
             do vx <- par_find_var size bv r x @  
               do vy <- par_find_var size bv r y @
              if is_q t1 && (¬ (is_q t2))
               then 
                   do t2v <- par_eval_cfac size smap bv r b y @
                       Some (Some (Exp (init_v size (vmap vy) t2v;
                         comparator01 (if b =b= Bl then 1 else size) 
                               (vmap vy) (vmap vx) (vmap (L stack,0),S sn) (vmap (L stack,0),sn);
                        comparator01 (if b =b= Bl then 1 else size) (vmap vx) (vmap vy)
                      (vmap (L stack,0),S sn) (vmap (L stack,0),sn) ; init_v size (vmap vy) t2v)),S sn, None)
                else if is_q t1 && (is_q t2) then
                       Some (Some (Exp (comparator01 (if b =b= Bl then 1 else size)
                             (vmap vy) (vmap vx) (vmap (L stack,0),S sn) (vmap (L stack,0),sn);
                        comparator01 (if b =b= Bl then 1 else size)
                          (vmap vx) (vmap vy) (vmap (L stack,0),S sn) (vmap (L stack,0),sn))),S sn, None)
                else if (¬ (is_q t1)) && (is_q t2) then
                   do t1v <- par_eval_cfac size smap bv r b x @
                      Some (Some (Exp (init_v size (vmap vy) t1v;
                         comparator01 (if b =b= Bl then 1 else size)
                                (vmap vy) (vmap vx) (vmap (L stack,0),S sn) (vmap (L stack,0),sn);
                        comparator01 (if b =b= Bl then 1 else size)
                               (vmap vx) (vmap vy)
                      (vmap (L stack,0),S sn) (vmap (L stack,0),sn) ;init_v size (vmap vy) t1v)),S sn, None)
                else do t1v <- par_eval_cfac size smap bv r b x @
                      do t2v <- par_eval_cfac size smap bv r b y @
                      Some (None,sn,Some (a_nat2fb t1v size =? a_nat2fb t2v size)).

Definition compile_cexp (sl size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (r:reg) (stack:var) (sn:nat) (e:cexp) : option (option pexp * nat * option bool) :=
   match e with clt f b x y => 
                    if sn <? sl then  
                    if  ¬ (qvar_eq size bv r x y) then 
                                      gen_clt_c size smap vmap bv r b stack sn x y
                                     else None
                    else None
         | ceq f b x y =>  
                    if sn <? sl then 
                        if  ¬ (qvar_eq size bv r x y) then 
                                      gen_ceq_c size smap vmap bv r b stack sn x y
                                     else None
                    else None
         | iseven x => do t1 <- type_factor bv Nat x @ if is_q t1 then None else 
                           do t2v <- par_eval_cfac size smap bv r Nat x @
                              if (a_nat2fb t2v size) mod 2 =? 0 then Some (None, sn, Some true) else Some (None,sn,Some false)
   end.

Definition fmap :Type := list (fvar * pexp * qvar * ((qvar*nat) -> var)).
Fixpoint lookup_fmap (l:fmap) (x:var) : option (pexp * qvar * ((qvar*nat) -> var)) :=
   match l with [] => None
          | ((y,a,v,b)::xl) => if x =? y then Some (a,v,b) else lookup_fmap xl x
   end.

Fixpoint copyto (x y:var) size := match size with 0 => SKIP (x,0) 
                  | S m => CNOT (x,m) (y,m) ; copyto x y m
    end.

Definition combine_c (e1 e2:option pexp) : option pexp :=
          match e1 with None => e2
               | Some e1' => match e2 with None => None
                                        | Some e2' => Some (e1';;e2')
                              end
          end.

Definition combine_seq (e1:option pexp) (e2:option pexp) :=
   match e1 with None => e2
        | Some e1' => match e2 with None => Some e1' | Some e2' => Some (e1' ;; e2') end
   end.

Definition deal_result (r:reg) (re : option (option pexp * nat * option reg)) :=
    match re with None => None
             | Some (a,b,None) => Some (a,b,r)
             | Some (a,b,Some r') => Some (a,b,r')
    end.

Definition nadd_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (r:reg) (stack:var) (sn:nat) (fv:fmap) (x y:cfac) :=
     do t1 <- type_factor bv Nat x @
         do t2 <- type_factor bv Nat y @
             do vx <- par_find_var size bv r x @  
               do vy <- par_find_var size bv r y @
              if is_q t1 && ((is_q t2)) then
                  Some (Some (Exp (adder01 size (vmap vx) (vmap vy) (stack,sn))),sn, r)
              else if is_q t1 && (¬ (is_q t2))
               then 
                   do t2v <- par_eval_cfac size smap bv r Nat y @
                       Some (Some (Exp (Rev (vmap vx);
                         rz_adder (vmap vx) size t2v ; Rev (vmap vx))),sn, r)
                else if (¬ (is_q t1)) && (is_q t2) then
                   do t1v <- par_eval_cfac size smap bv r Nat x @
                       Some (Some (Exp (Rev (vmap vy);
                         rz_adder (vmap vy) size t1v ; Rev (vmap vy))),sn, r)
                else Some (None,sn,r).

Definition nsub_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (r:reg) (stack:var) (sn:nat) (fv:fmap) (x y:cfac) :=
     do t1 <- type_factor bv Nat x @
         do t2 <- type_factor bv Nat y @
             do vx <- par_find_var size bv r x @  
               do vy <- par_find_var size bv r y @
              if is_q t1 && ((is_q t2)) then
                  Some (Some (Exp (subtractor01 size (vmap vx) (vmap vy) (stack,sn))),sn, r)
              else if is_q t1 && (¬ (is_q t2))
               then 
                   do t2v <- par_eval_cfac size smap bv r Nat y @
                       Some (Some (Exp (Rev (vmap vx);
                         rz_sub (vmap vx) size t2v ; Rev (vmap vx))),sn, r)
                else if (¬ (is_q t1)) && (is_q t2) then
                   do t1v <- par_eval_cfac size smap bv r Nat x @
                       Some (Some (Exp (Rev (vmap vy);
                         rz_sub (vmap vy) size t1v ; Rev (vmap vy))),sn, r)
                else Some (None,sn,r).

(*
Definition nmul_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (r:reg) (temp stack:var) (sn:nat) (fv:fmap) (x y:cfac) :=
     do t1 <- type_factor bv Nat x @
         do t2 <- type_factor bv Nat y @
             do vx <- par_find_var size bv r x @  
               do vy <- par_find_var size bv r y @
             if is_q t1 && (¬ (is_q t2))
               then do t2v <- par_eval_cfac size smap bv r Nat y @
                       Some (Some (Exp (Rev (vmap vx);
                         nat_mult size (vmap vx) temp t2v 
                             (nat2fb (inv_finder (a_nat2fb t2v size) size)); Rev (vmap vx))),sn, r)
                else if (¬ (is_q t1)) && (is_q t2) then
                   do t1v <- par_eval_cfac size smap bv r Nat x @
                       Some (Some (Exp (Rev (vmap vy); Rev (vmap vx);
                         nat_mult size (vmap vy) temp t1v 
                             (nat2fb (inv_finder (a_nat2fb t1v size) size)); Rev (vmap vx);Rev (vmap vy))),sn, r)
                else Some (None,sn,r).
*)

Definition nqmul_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (r:reg) (temp stack:var) (sn:nat) (fv:fmap) (x y z:cfac) :=
     do t1 <- type_factor bv Nat x @
         do t2 <- type_factor bv Nat y @
         do t3 <- type_factor bv Nat z @
             do vx <- par_find_var size bv r x @  
               do vy <- par_find_var size bv r y @
               do vz <- par_find_var size bv r z @
             if is_q t1 && ((is_q t2)) && is_q t3 then
                       Some (Some (Exp (Rev (vmap vx);Rev (vmap vy);Rev (vmap vz);
                         nat_full_mult size (vmap vx) (vmap vy) (vmap vz) temp; 
                     Rev (vmap vz);Rev (vmap vy);Rev (vmap vx))),sn, r)
                else None.

Definition fmul_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (r:reg) (temp stack:var) (sn:nat) (fv:fmap) (x y z:cfac) :=
     do t1 <- type_factor bv Nat x @
         do t2 <- type_factor bv Nat y @
         do t3 <- type_factor bv Nat z @
             do vx <- par_find_var size bv r x @  
               do vy <- par_find_var size bv r y @
               do vz <- par_find_var size bv r z @
             if is_q t1 && ((is_q t2)) && is_q t3 then
                       Some (Some (Exp (Rev (vmap vx);
                         flt_full_mult size (vmap vx) (vmap vy) (vmap vz) temp; Rev (vmap vx))),sn, r)
             else if (¬ (is_q t1)) && ((is_q t2)) && is_q t3 then
                 do t1v <- par_eval_cfac size smap bv r Nat x @
                       Some (Some (Exp (init_v size (vmap vx) t1v; Rev (vmap vy);
                         flt_full_mult size (vmap vx) (vmap vy) (vmap vz) temp;
                                  Rev (vmap vy);init_v size (vmap vx) t1v)),sn, r)
             else if (¬ (is_q t1)) && (¬ (is_q t2)) && is_q t3 then
                 do t2v <- par_eval_cfac size smap bv r Nat y @
                       Some (Some (Exp (init_v size (vmap vy) t2v; Rev (vmap vx); Rev (vmap vy); Rev (vmap vz);
                         flt_full_mult size (vmap vx) (vmap vy) (vmap vz) temp;
                          Rev (vmap vz);Rev (vmap vy);Rev (vmap vx);init_v size (vmap vy) t2v)),sn, r)
                else None.

Fixpoint bin_xor_c (n:nat) (x y : var) : exp :=
   match n with 0 => SKIP (x,0)
      | S m => CNOT (x,m) (y,m);bin_xor_c m x y
   end.

Definition qxor_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (r:reg) (temp stack:var) (sn:nat) (fv:fmap) (x y:cfac) :=
     do t1 <- type_factor bv Nat x @
         do t2 <- type_factor bv Nat y @
             do vx <- par_find_var size bv r x @  
               do vy <- par_find_var size bv r y @
             if is_q t1 && ((is_q t2)) then
                       Some (Some (Exp (bin_xor_c size (vmap vx) (vmap vy))),sn, None)
             else if (¬ (is_q t1)) && ((is_q t2)) then
                 do t1v <- par_eval_cfac size smap bv r Nat x @
                       Some (Some (Exp (init_v size (vmap vx) t1v; 
                           bin_xor_c size (vmap vx) (vmap vy) ;init_v size (vmap vx) t1v)),sn, None)
                else 
                 do t1v <- par_eval_cfac size smap bv r Nat x @
                 do t2v <- par_eval_cfac size smap bv r Nat y @
                   Some (None,sn,Some (Reg.add vx (bin_xor t1v t2v size) r)).


Definition combine_if (sv : var) (sn:nat) (vmap: (qvar*nat) -> var)
                      (p1:pexp) (e1:option pexp) (e2:option pexp) :=
   match e1 with None => match e2 with None => Some p1
           | Some e2' => Some (p1 ;; Exp (X ((vmap (L sv,0)),sn));; PCU ((vmap (L sv,0)),sn) e2')
                         end
           | Some e1' => match e2 with None => Some (p1 ;; PCU ((vmap (L sv,0)),sn) e1')
                | Some e2' => Some (p1 ;; PCU ((vmap (L sv,0)),sn) e1' ;; 
                         Exp (X (vmap (L sv,0),sn));; PCU ( vmap (L sv,0),sn) e2')
                         end
    end.

Fixpoint trans_qexp (sl size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (r:reg) (temp stack:var) (sn:nat) (fv:fmap) (e:qexp) : option (option pexp * nat * reg) :=
   match e with qfor x n e' => 
     do t2v <- par_eval_cfac size smap bv r Nat n @
         let fix trans_while (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var) (bv:benv)
                       (r:reg) (temp stack:var) (sn:nat) (fv:fmap) (i:nat) :  option (option pexp * nat * reg) :=
            match i with 0 => Some (None,sn,r)
                     | S m => do re <- trans_qexp sl size smap vmap bv r temp stack sn fv e' @
                               match re with (cir,sn',r') =>
                                 do re' <- trans_while size smap vmap bv r' temp stack sn' fv m @
                                  match re' with (cir',sn'',r'') =>
                                     Some (combine_c cir cir',sn'',r'')
                                  end
                               end
            end in trans_while size smap vmap bv (Reg.add (L x,0) (nat2fb 0) r) temp stack sn fv (a_nat2fb t2v size)


           | skip => Some (None,sn,r)

           | init b x v => 
             do tv <- type_factor bv b v @
              if is_q tv then 
                do v_var <- par_find_var size bv r v @
                 do x_var <- par_find_var size bv r x @
                    Some (Some (Exp (copyto (vmap v_var) (vmap x_var) (if b =b= Bl then 1 else size))),sn,r)
              else 
               do v_val <- par_eval_cfac size smap bv r b v @
                 do x_var <- par_find_var size bv r x @
                    Some (Some (Exp (init_v (if b =b= Bl then 1 else size) (vmap x_var) v_val)),sn,r)


           | nadd f x y => if ¬ (qvar_eq size bv r x y) then
                      (nadd_c size smap vmap bv r stack sn fv x y) 
                        else None
           | nsub f x y => if ¬ (qvar_eq size bv r x y) then
                     (nsub_c size smap vmap bv r stack sn fv x y) 
                        else None

           | nmul f x y z => if ¬ (qvar_eq size bv r x z) && ¬ (qvar_eq size bv r y z) then
                     nqmul_c size smap vmap bv r temp stack sn fv x y z
                        else None

           | fadd f x y => if ¬ (qvar_eq size bv r x y) then
                      (nadd_c size smap vmap bv r stack sn fv x y) 
                        else None

           | fsub f x y => if ¬ (qvar_eq size bv r x y) then
                      (nsub_c size smap vmap bv r stack sn fv x y) 
                        else None

           | fmul f x y z => if ¬ (qvar_eq size bv r x z) && ¬ (qvar_eq size bv r y z) then
                     fmul_c size smap vmap bv r temp stack sn fv x y z
                        else None

           | qxor f x y => if ¬ (qvar_eq size bv r x y) then
                     deal_result r (qxor_c size smap vmap bv r temp stack sn fv x y) 
                        else None



           | ndiv x y n => do t2v <- par_eval_cfac size smap bv r Nat y @
                             do t3v <- par_eval_cfac size smap bv r Nat n @
                              do vx <- par_find_var size bv r x @
                               Some (None,sn,Reg.add vx (nat2fb ((a_nat2fb t2v size) / (a_nat2fb t3v size))) r)



           | nmod x y n => do t2v <- par_eval_cfac size smap bv r Nat y @
                             do t3v <- par_eval_cfac size smap bv r Nat n @
                              do vx <- par_find_var size bv r x @
                               Some (None,sn,Reg.add vx (nat2fb ((a_nat2fb t2v size) mod (a_nat2fb t3v size))) r)

           | nfac x n =>  do t3v <- par_eval_cfac size smap bv r Nat n @
                              do vx <- par_find_var size bv r x @
                               Some (None,sn,Reg.add vx (nat2fb (fact (a_nat2fb t3v size))) r)

           | fdiv x n => do t2v <- par_eval_cfac size smap bv r Flt x @
                             do t3v <- par_eval_cfac size smap bv r Nat n @
                              do vx <- par_find_var size bv r x @
                               Some (None,sn,Reg.add vx (nat2fb (((a_nat2fb t2v size) * 2^size) / (a_nat2fb t3v size))) r)

           | ncadd x y n => do t2v <- par_eval_cfac size smap bv r Nat y @
                             do t3v <- par_eval_cfac size smap bv r Nat n @
                              do vx <- par_find_var size bv r x @
                               Some (None,sn,Reg.add vx (nat2fb (((a_nat2fb t2v size) + (a_nat2fb t3v size)) mod 2^size)) r)
           | ncsub x y n => do t2v <- par_eval_cfac size smap bv r Nat y @
                             do t3v <- par_eval_cfac size smap bv r Nat n @
                              do vx <- par_find_var size bv r x @
                               Some (None,sn,Reg.add vx (nat2fb (((a_nat2fb t2v size) - (a_nat2fb t3v size)) mod 2^size)) r)

           | fcadd x y n => do t2v <- par_eval_cfac size smap bv r Flt y @
                             do t3v <- par_eval_cfac size smap bv r Flt n @
                              do vx <- par_find_var size bv r x @
                               Some (None,sn,Reg.add vx (nat2fb (((a_nat2fb t2v size) + (a_nat2fb t3v size)) mod 2^size)) r)
           | fcsub x y n => do t2v <- par_eval_cfac size smap bv r Flt y @
                             do t3v <- par_eval_cfac size smap bv r Flt n @
                              do vx <- par_find_var size bv r x @
                               Some (None,sn,Reg.add vx (nat2fb (((a_nat2fb t2v size) - (a_nat2fb t3v size)) mod 2^size)) r)


           | ncmul x y n => do t2v <- par_eval_cfac size smap bv r Nat y @
                             do t3v <- par_eval_cfac size smap bv r Nat n @
                              do vx <- par_find_var size bv r x @
                               Some (None,sn,Reg.add vx (nat2fb (((a_nat2fb t2v size) * (a_nat2fb t3v size)) mod 2^size)) r)

           | fndiv x y z => do t2v <- par_eval_cfac size smap bv r Nat x @
                             do t3v <- par_eval_cfac size smap bv r Nat y @
                              do vz <- par_find_var size bv r z @
                               Some (None,sn,Reg.add vz (nat2fb (((a_nat2fb t2v size) *  2^size) / (a_nat2fb t3v size))) r)


           | qseq e1 e2 => match trans_qexp sl size smap vmap bv r temp stack sn fv e1 with None => None
                    | Some ( e1',sn1,reg1) => 
                     match trans_qexp sl size smap vmap bv reg1 temp stack sn1 fv e2 with None => None
                      | Some ( e2',sn2,reg2) => Some (combine_seq e1' e2',sn2,reg2)
                     end
                 end

           | call f x => match lookup_fmap fv f with None => None
                       | Some (e',u,vmap') => 
                  do vx <- par_find_var size bv r x @
                      Some (Some (e';; Exp (copyto (vmap' (u,0)) (vmap vx) size);;inv_pexp e'), sn,r)
                        end

           | qif ce e1 e2 => do ce_val <- compile_cexp sl size smap vmap bv r stack sn ce @
                 match ce_val with (cir,sn',Some true) => 
                   trans_qexp sl size smap vmap bv r temp stack sn' fv e1
                      | (cir,sn',Some false) => 
                   trans_qexp sl size smap vmap bv r temp stack sn' fv e2
                | (cir,sn',None) => 
                 do e1_val <- trans_qexp sl size smap vmap bv r temp stack sn' fv e1 @
                   match e1_val with (e1_cir,sn1,r1)  =>
                  do e2_val <- trans_qexp sl size smap vmap bv r1 temp stack sn1 fv e2 @
                   match e2_val with (e2_cir,sn2,r2) => 
                do cir' <- cir @ Some (combine_if stack sn vmap cir' e1_cir e2_cir,sn2,r2)
                    end end
                 end
          
           | qinv e => do re <- trans_qexp sl size smap vmap bv r temp stack sn fv e @
               match re with (None,sn',r') => Some (None,sn',r')
                      | (Some p,sn',r') => Some (Some (inv_pexp p),sn',r')
               end

   end.

Definition stack (l:list (btype * var * nat)) : var :=
           let (al,_) := split l in let (_,bl) := split al in S(list_max bl).

Definition qdupdate {A} (f : (qvar * nat) -> A) (i : (qvar * nat)) (x : A) :=
  fun j => if j =qd= i then x else f j.

Lemma qdupdate_index_eq : forall {A} (f : (qvar * nat) -> A) i b, (qdupdate f i b) i = b.
Proof.
  intros. 
  unfold qdupdate.
  bdestruct (i =qd= i). easy. easy.
Qed.

Lemma qdupdate_index_neq : forall {A} (f : (qvar * nat) -> A) i j b, i <> j -> (qdupdate f i b) j = f j.
Proof.
  intros. 
  unfold qdupdate.
  bdestruct (j =qd= i). subst. easy. easy.
Qed.

Lemma qdupdate_same : forall {A} (f : (qvar * nat) -> A) i b,
  b = f i -> qdupdate f i b = f.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold qdupdate.
  bdestruct (x =qd= i); subst; reflexivity.
Qed.

Lemma qdupdate_twice_eq : forall {A} (f : (qvar * nat) -> A) i b b',
  qdupdate (qdupdate f i b) i b' = qdupdate f i b'.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold qdupdate.
  bdestruct (x =qd= i); subst; reflexivity.
Qed.  

Lemma qdupdate_twice_neq : forall {A} (f : (qvar * nat) -> A) i j b b',
  i <> j -> qdupdate (qdupdate f i b) j b' = qdupdate (qdupdate f j b') i b.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold qdupdate.
  bdestruct (x =qd= i); bdestruct (x =qd= j); subst; easy.
Qed.

Fixpoint gen_vmap_n (vmap: (qvar*nat) -> var)  (x:qvar) (i:nat) (n:nat) :=
   match n with 0 => vmap
          | S m => qdupdate (gen_vmap_n vmap x i m) (x,m) (i+m)
   end.


Fixpoint gen_vmap_l' (l:list (btype * var * nat))  (vmap: (qvar*nat) -> var) (i:nat) :=
         match l with [] => vmap
              | ((b,x,n)::xl) => gen_vmap_l' xl (gen_vmap_n vmap (L x) i n) (i+n)
         end.
Definition gen_vmap_l (l:list (btype * var * nat)) (vmap:(qvar*nat) -> var) (vmap_num:nat) := gen_vmap_l' l vmap vmap_num.


Fixpoint gen_smap_l (l:list (btype * var * nat)) (smap: qvar -> nat)  :=
  match l with [] => smap
      | ((b,x,n)::xl) => gen_smap_l xl (qupdate smap (L x) n)
  end.

(*
trans_qexp (sl size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (r:reg) (temp stack:var) (sn:nat) (fv:fmap) (e:qexp)
*)

Fixpoint trans_funs (fv:fenv) (sl size:nat) (temp:var) (r:reg)
                  (smap: qvar -> nat) (vmap : (qvar*nat) -> var) (vmap_num:nat) (fmap:fmap) (l:list func) :=
    match l with [] => Some fmap
            | (( f , ls , e , rx)::xl) =>
                 match fv f with None => None
                           | Some (ls',e',bv,rx') => 
                    match trans_qexp sl size 
                   (gen_smap_l ((Nat,stack ls,1)::ls) smap) (gen_vmap_l ((Nat,stack ls,1)::ls) vmap vmap_num)
                     bv (init_reg r ((Nat,stack ls,1)::ls)) temp (stack ls) 0 fmap e'
                    with None => None
                    | Some (None,sn1,reg1) => 
         trans_funs fv sl size temp r smap vmap vmap_num ((f,Exp (SKIP ((vmap (G temp,0)),0)), rx, 
                                        (gen_vmap_l ((Nat,stack ls,1)::ls) vmap vmap_num))::fmap) xl
                  | Some (Some e1,sn1,reg1) => 
          trans_funs fv sl size temp r smap vmap vmap_num 
                  ((f,e1, rx, (gen_vmap_l ((Nat,stack ls,1)::ls) vmap vmap_num))::fmap) xl
                    end
                 end
     end.


Fixpoint gen_vmap_g' (l:list (btype * var)) (vmap:(qvar*nat) -> var) (n:nat) :=
         match l with [] => (vmap,n)
              | ((b,x)::xl) => gen_vmap_g' xl (qdupdate vmap (G x,0) n) ((S n))
         end.
Definition gen_vmap_g (l:list (btype * var)) := gen_vmap_g' l (fun _ => 0) 1.

Definition temp : var := 0.

Fixpoint gen_smap_g (l:list (btype * var))  :=
  match l with [] => (fun _ => 0)
      | ((b,x)::xl) => qupdate (gen_smap_g xl) (G x) 1
  end.

(*
Fixpoint trans_funs (fv:fenv) (sl size:nat) (temp:var) (r:reg)
                  (smap: qvar -> nat) (vmap : (qvar*nat) -> var) (vmap_num:nat) (fmap:fmap) (l:list func) :=
*)

Definition trans_prog (p:prog) (fv:fenv) :=
   match p with (sl,size,ls,fl,f,rx') =>
     let (vmap,vmap_num) := gen_vmap_g ls in 
      do fmap <- (trans_funs fv sl size temp empty_reg (gen_smap_g ls) vmap vmap_num [] fl) @
         match lookup_fmap fmap f with None => None
            | Some (e,x,vmap') => Some (e;; copyto (vmap (x,0)) rx' size ;; inv_pexp e)
          end
   end.


(*Proofs of compilation correctness. *)

Lemma a_nat2fb_small : forall n f, a_nat2fb f n < 2^n.
Proof.
  intros.
  induction n;simpl.
  lia.
  destruct (f n). simpl. lia. simpl. lia.
Qed.

Lemma nat2fb_a_nat2fb' : forall n m f, m <= n -> (forall i, m <= i -> f i = false)
             -> nat2fb (a_nat2fb f n) = f.
Proof.
  induction n; intros; unfold nat2fb; simpl.
  apply functional_extensionality.
  intros. rewrite H0. easy. lia.
  apply functional_extensionality.
  intros.
  bdestruct (x =? n). subst.
Admitted.

Lemma nat2fb_a_nat2fb : forall n f, (forall i, n <= i -> f i = false)
             -> nat2fb (a_nat2fb f n) = f.
Proof.
  intros. rewrite nat2fb_a_nat2fb' with (m := n). easy. lia. easy.
Qed.

Definition is_bl (t:option ttyp) : bool :=
 match t with Some (TNor (a,Bl)) => true
            | Some (TPtr (a,Bl) x) => true
            | _ => false
 end.

Definition is_qtt (t:option ttyp) : Prop :=
 match t with Some (TNor (Q,b)) => True
            | Some (TPtr (Q,b) x) => True
            | _ => False
 end.

Definition cexp_set_up (ce:cexp) (sl size:nat) (stack:var)
          (sn:nat) (vmap : (qvar*nat) -> var) (r:reg) (bv:benv) (f:posi -> val) (aenv:var -> nat) (tenv:env) :=
  match ce with clt fl b x y => 
     match par_find_var size bv r x with None => True
                     | Some vx => 
        match par_find_var size bv r y with None => True
                         | Some vy => 
             ((vmap vx) <> (vmap vy) /\ (vmap vx) <> vmap (L stack,0)
                /\ (vmap vy) <> vmap (L stack,0) /\
                Reg.In vx r /\ Reg.In vy r /\ nor_modes f (vmap vx) size /\
               nor_modes f (vmap vy) size /\ nor_modes f (vmap (L stack,0)) (S sl)
            /\ well_typed_exp tenv (MAJseq (if is_bl (bv (fst vx)) then 1 else size)
                                    (vmap vy) (vmap vx) (vmap (L stack,0),S sn))
           /\ well_typed_exp tenv (X ((vmap (L stack,0),S sn))) 
            /\ well_typed_exp tenv (negator0 (if is_bl (bv (fst vx)) then 1 else size) (vmap vy))
           /\ right_mode_env aenv tenv f)
        end
      end
       | ceq fl b x y => 
     match par_find_var size bv r x with None => True
                     | Some vx => 
        match par_find_var size bv r y with None => True
                         | Some vy => 
             ((vmap vx) <> (vmap vy) /\ (vmap vx) <> vmap (L stack,0)
                /\ (vmap vy) <> vmap (L stack,0) /\  Reg.In vx r /\ Reg.In vy r /\
              nor_modes f (vmap vx) size /\
               nor_modes f (vmap vy) size /\ nor_modes f (vmap (L stack,0)) (S sl)
            /\ well_typed_exp tenv (MAJseq (if is_bl (bv (fst vx)) then 1 else size)
                        (vmap vx) (vmap vy) (vmap (L stack,0),S sn))
            /\ well_typed_exp tenv (MAJseq (if is_bl (bv (fst vx)) then 1 else size)
                         (vmap vy) (vmap vx) (vmap (L stack,0),S sn))
           /\ well_typed_exp tenv (X ((vmap (L stack,0),S sn))) 
           /\ well_typed_exp tenv (negator0 (if is_bl (bv (fst vx)) then 1 else size) (vmap vx))
                 /\ well_typed_exp tenv (negator0 (if is_bl (bv (fst vx)) then 1 else size) (vmap vy))
           /\ right_mode_env aenv tenv f)
         end
     end
        | iseven x => True
  end.


Definition reg_typed (r:reg) (bv:benv) (size:nat) (stack:var) : Prop :=
   forall x v, fst x <> L stack -> Reg.MapsTo x v r -> bv (fst x) <> None ->
           (forall i, (if is_bl (bv (fst x)) then 1 else size) <= i -> v i = false).

Definition reg_match_q (stack:var) (r:reg) (f:posi -> val)
           (bv:benv) (vmap : (qvar*nat) -> var) (aenv:var -> nat) : Prop := 
  forall x v, fst x <> L stack -> Reg.MapsTo x v r -> (bv (fst x)) <> None ->
         is_qtt (bv (fst x)) -> 
            get_cus (aenv (vmap x)) f (vmap x) = v.

Definition reg_match_c (stack:var) (f:posi -> val) (bv:benv)
             (vmap : (qvar*nat) -> var) (aenv:var -> nat) : Prop := 
  forall x, fst x <> L stack -> bv (fst x) <> None ->
                    ~ is_qtt (bv (fst x)) -> get_cus (aenv (vmap x)) f (vmap x) = nat2fb 0.

Definition reg_same_c (stack:var) (rh:reg) (rl:reg) (bv:benv)
             (vmap : (qvar*nat) -> var) (aenv:var -> nat) : Prop := 
  forall x, fst x <> L stack -> bv (fst x) <> None ->
                    ~ is_qtt (bv (fst x)) -> Reg.find x rh = Reg.find x rl.

Definition reg_match_st (sl sn:nat) (stack:var) (f:posi -> val)
             (vmap : (qvar*nat) -> var) : Prop := 
          forall i, sn <= i -> get_cus (S sl) f (vmap (L stack,0)) i = false.

Definition aenv_match (stack:var) (size:nat) (bv:benv) (aenv: var -> nat) (vmap : (qvar*nat) -> var) : Prop := 
          forall x, fst x <> L stack -> aenv (vmap x) = (if is_bl (bv (fst x)) then 1 else size).

Definition no_equal_stack (stack:var) (ce:cexp) (size:nat) (bv:benv) (r:reg) :=
    match ce with clt fl b x y => 
     match par_find_var size bv r x with None => 
             match par_find_var size bv r y with None => True
                       | Some vy => fst vy <> L stack
             end
                     | Some vx => 
        match par_find_var size bv r y with None => fst vx <> L stack
                    | Some vy => fst vx <> L stack /\ fst vy <> L stack
        end
     end
      | ceq fl b x y => 
     match par_find_var size bv r x with None => 
             match par_find_var size bv r y with None => True
                       | Some vy => fst vy <> L stack
             end
                     | Some vx => 
        match par_find_var size bv r y with None => fst vx <> L stack
                    | Some vy => fst vx <> L stack /\ fst vy <> L stack
        end
      end
      | iseven x => True
   end.



Lemma par_find_var_means_cfac : 
   forall size bv r b x vx, par_find_var size bv r x = Some vx -> 
     sem_cfac size r b x = Reg.find vx r.
Proof.
  intros.
  unfold par_find_var,sem_cfac in *.
  destruct x.
  unfold par_eval_fc,sem_factor in *.
  destruct v.
  destruct (bv v) eqn:eq1.
  simpl in *.
  destruct (is_qt t) eqn:eq2. inv H.
  destruct (Reg.find (elt:=nat -> bool) (v, 0) r) eqn:eq3.
  inv H. easy. inv H.
  simpl in *. inv H.
  simpl in *.
  inv H. easy.
  unfold sem_factor.
  destruct v.
  inv H. easy. inv H.
Qed.

Lemma type_factor_means_q : forall x vx b t size bv r, type_factor bv b x = Some t -> 
   par_find_var size bv r x = Some vx -> is_q t = true -> is_qtt (bv (fst vx)).
Proof.
  intros.
  unfold type_factor,typ_factor,par_find_var,par_eval_fc,is_qtt,is_qt,is_q in *.
  destruct x eqn:eq1. destruct v eqn:eq2. simpl in *.
  destruct (bv v0) eqn:eq3. 
  destruct t0 eqn:eq4.
  destruct (bv (L x0)) eqn:eq5.
  destruct t2. destruct t2. inv H. inv H. inv H.
  destruct (bv (L x0)) eqn:eq5.
  destruct t2. destruct t2.
  destruct t1. simpl in *.
  bdestruct (b1 =b= Nat).
  bdestruct (a0 =a= Q). inv H0. simpl in H.
  bdestruct ((a0 =a= C)).
  bdestruct (b0 =b= b). simpl in H. inv H.
  destruct (Reg.find (elt:=nat -> bool) (v0, 0) r).
  inv H0. simpl in *.
  rewrite eq5.
  bdestruct (a =a= Q). subst. lia. inv H1. inv H0.
  simpl in H. inv H. simpl in H. inv H. inv H. inv H. inv H.
  destruct (bv (L x0)) eqn:eq4. inv H0. inv H0.
  simpl in *. inv H0.
  simpl in *.
  destruct (bv (L x0)).
  destruct t0. destruct t0.
  bdestruct (b0 =b= b). inv H. simpl in H1.
  bdestruct (a =a= Q). subst. lia. inv H1. inv H. inv H. inv H.
  destruct v eqn:eq2.
  inv H0. simpl in *.
  destruct (bv v0). destruct t0.
  inv H.
  destruct t0.
  simpl in *.
  bdestruct (b0 =b= b). inv H.
  simpl in H1.
  bdestruct (a =a= Q). subst. easy.
  inv H1. inv H. inv H. inv H0.
Qed.

Lemma type_factor_means_b : forall x vx b t size bv r, type_factor bv b x = Some t -> 
   par_find_var size bv r x = Some vx -> is_bl (bv (fst vx)) = (b =b= Bl).
Proof.
  intros.
  unfold type_factor,typ_factor,par_find_var,par_eval_fc,is_bl,is_qt,is_q in *.
  destruct x eqn:eq1. destruct v eqn:eq2. simpl in *.
  destruct (bv v0) eqn:eq3. 
  destruct t0 eqn:eq4.
  destruct (bv (L x0)) eqn:eq5.
  destruct t2. destruct t2. inv H. inv H. inv H.
  destruct (bv (L x0)) eqn:eq5.
  destruct t2. destruct t2.
  destruct t1. simpl in *.
  bdestruct (b1 =b= Nat).
  simpl in *.
  bdestruct (a0 =a= C).
  bdestruct (b0 =b= b). 
  bdestruct (a0 =a= Q).
  simpl in *. inv H0. simpl in *. inv H.
  destruct (Reg.find (elt:=nat -> bool) (v0, 0) r) eqn:eq6.
  inv H0. simpl in *. rewrite eq5.
  destruct b eqn:eq7.
  simpl. easy. simpl. easy. simpl. easy.
  inv H0. simpl in H. inv H. simpl in H. inv H. inv H. inv H. inv H.
  inv H0.
  simpl in *. inv H0. simpl in *.
  destruct (bv (L x0)) eqn:eq1.
  destruct t0. destruct t0.
  bdestruct (b0 =b= b). inv H.
  destruct b. easy. easy. easy. inv H. inv H. inv H.
  destruct v eqn:eq2. inv H0. simpl in *.
  destruct (bv v0). destruct t0. inv H.
  destruct t0. simpl in *.
  bdestruct (b0 =b= b). inv H.
  destruct b. easy. easy. easy. inv H. inv H. inv H0.
Qed.

Lemma type_factor_means_q_false : forall x vx b t size bv r, type_factor bv b x = Some t -> 
   par_find_var size bv r x = Some vx -> is_q t = false -> bv (fst (vx)) <> None -> ~ is_qtt (bv (fst vx)).
Proof.
  intros.
  unfold type_factor,typ_factor,par_find_var,par_eval_fc,is_qtt,is_qt,is_q in *.
  destruct x eqn:eq1. destruct v eqn:eq2. simpl in *.
  destruct (bv v0) eqn:eq3. 
  destruct t0 eqn:eq4.
  destruct (bv (L x0)) eqn:eq5.
  destruct t2. destruct t2. inv H. inv H. inv H.
  destruct (bv (L x0)) eqn:eq5.
  destruct t2. destruct t2.
  destruct t1. simpl in *.
  bdestruct (b1 =b= Nat).
  bdestruct (a0 =a= Q). inv H0. simpl in H.
  bdestruct ((a0 =a= C)).
  bdestruct (b0 =b= b). simpl in H. inv H.
  destruct (Reg.find (elt:=nat -> bool) (v0, 0) r).
  inv H0. simpl in *.
  rewrite eq5.
  bdestruct (a =a= Q). inv H1. destruct a. easy. easy. inv H0.
  simpl in H. inv H. simpl in H. inv H. inv H. inv H. inv H.
  destruct (bv (L x0)) eqn:eq4. inv H0. inv H0.
  simpl in *. inv H0.
  simpl in *.
  destruct (bv (L x0)).
  destruct t0. destruct t0.
  bdestruct (b0 =b= b). inv H. simpl in H1.
  bdestruct (a =a= Q). inv H1. destruct a. easy. easy. inv H. inv H. inv H.
  destruct v eqn:eq2.
  inv H0. simpl in *.
  destruct (bv v0). destruct t0.
  inv H.
  destruct t0.
  simpl in *.
  bdestruct (b0 =b= b). inv H.
  simpl in H1.
  bdestruct (a =a= Q). inv H1. destruct a. easy. easy.
  inv H. inv H. inv H0.
Qed.

Lemma type_factor_means_some : forall x vx b t size bv r, type_factor bv b x = Some t -> 
   par_find_var size bv r x = Some vx -> bv (fst vx) <> None.
Proof.
  intros.
  unfold type_factor,typ_factor,par_find_var,par_eval_fc,is_qt,is_q in *.
  destruct x eqn:eq1. destruct v eqn:eq2. simpl in *.
  destruct (bv v0) eqn:eq3. 
  destruct t0 eqn:eq4.
  destruct (bv (L x0)) eqn:eq5.
  destruct t2. destruct t2. inv H. inv H. inv H.
  destruct (bv (L x0)) eqn:eq5.
  destruct t2. destruct t2.
  destruct t1. simpl in *.
  bdestruct (a0 =a= Q).
  simpl in *. inv H0.
  bdestruct (b1 =b= Nat).
  simpl in *.
  bdestruct (a0 =a= C).
  bdestruct (b0 =b= b).
  simpl in *. inv H.
  destruct (Reg.find (elt:=nat -> bool) (v0, 0) r) eqn:eq6.
  inv H0. simpl in *. rewrite eq5. easy.
  inv H0. simpl in H. inv H. simpl in H. inv H. inv H. inv H. inv H.
  inv H0.
  simpl in *. inv H0. simpl in *.
  destruct (bv (L x0)) eqn:eq1.
  destruct t0. destruct t0.
  bdestruct (b0 =b= b). inv H. easy.
  inv H. inv H. inv H.
  destruct v eqn:eq2. inv H0. simpl in *.
  destruct (bv v0). destruct t0. inv H.
  destruct t0. simpl in *.
  bdestruct (b0 =b= b). inv H.
  easy. inv H. inv H. inv H0.
Qed.

Definition get_var_factor (x:factor) :=
   match x with Var v => [v]
                  | Num v => []
   end.

Definition get_var_cfac (x:cfac) :=
    match x with Ptr x v => ((L x):: get_var_factor v)
               | Nor v => get_var_factor v
    end.

Definition get_var_cexp (x:cexp) :=
   match x with clt f b x y => get_var_cfac x ++ get_var_cfac y
              | ceq f b x y => get_var_cfac x ++ get_var_cfac y
              | iseven x => get_var_cfac x
   end.

Definition not_stack (stack:var) (l:list qvar) := forall x, In x l -> x <> L stack.


(*
Inductive factor := Var (v:qvar)
                 | Num (n:nat -> bool).
     (* the first m in Num represents the number of bits.
      a value is represented as a natural number x. it means x / 2^m where m is the number of denominator. *)

Inductive cfac := Ptr (x:var) (v:factor) | Nor (v:factor).
*)


Lemma par_find_var_lh : forall b x bv vmap aenv size stack rl rh t vx, type_factor bv b x = Some t
      -> par_find_var size bv rl x = Some vx -> not_stack stack (get_var_cfac x) ->
     reg_same_c stack rh rl bv vmap aenv -> par_find_var size bv rh x = Some vx.
Proof.
  intros.
  unfold reg_same_c in *.
  unfold type_factor,typ_factor,par_find_var,par_eval_fc,is_qt,is_q in *.
  destruct x eqn:eq1. destruct v eqn:eq2.
  destruct (bv (L x0)) eqn:eq3.
  simpl in *. destruct t0. destruct t0.
  destruct (bv v0) eqn:eq4. destruct t0. destruct t0.
  inv H. destruct t0. simpl in *.
  bdestruct (b1 =b= Nat).
  simpl in *.
  bdestruct (a0 =a= C).
  bdestruct (b0 =b= b).
  simpl in *. inv H.
  bdestruct (C =a= Q). easy.
  destruct (Reg.find (elt:=nat -> bool) (v0, 0) rl) eqn:eq5.
  inv H0.
  rewrite <- H2 in eq5.
  rewrite eq5. easy.
  unfold not_stack in H1.
  simpl.
  apply H1. simpl.
  right. left. easy.
  simpl. rewrite eq4. easy.
  unfold is_qtt.
  simpl.
  rewrite eq4. easy.
  inv H0. simpl in *. inv H. simpl in *. inv H. inv H. inv H. inv H.
  simpl in *. inv H.
  destruct (bv (L x0)). destruct t0. destruct t0.
  simpl in *.
  bdestruct (b0 =b= b).
  inv H. inv H0. easy. inv H.
  simpl in *. inv H. simpl in *. inv H.
  destruct v. easy. inv H0.
Qed.

Lemma not_stack_shrink_l : forall l1 l2 stack, not_stack stack (l1++l2) -> not_stack stack l1.
Proof.
 intros. unfold not_stack in *.
 intros. 
 apply H.
 apply in_or_app. left. easy.
Qed.

Lemma not_stack_shrink_r : forall l1 l2 stack, not_stack stack (l1++l2) -> not_stack stack l2.
Proof.
 intros. unfold not_stack in *.
 intros. 
 apply H.
 apply in_or_app. right. easy.
Qed.

Lemma par_find_var_get : forall size bv rl x vx, par_find_var size bv rl x = Some vx -> In (fst vx) (get_var_cfac x).
Proof.
  intros.
  unfold par_find_var,get_var_cfac in *.
  destruct x.
  destruct (par_eval_fc size bv rl Nat v) eqn:eq1.
  simpl in *. inv H. simpl. left. easy.
  simpl in *. inv H.
  unfold get_var_factor. destruct v.
  inv H. simpl. left. easy. inv H.
Qed.

Local Opaque comparator01.

Lemma compile_cexp_sem : forall sl size smap vmap bv rh rl stack sn e p a b re f aenv tenv, 
      compile_cexp sl size smap vmap bv rl stack sn e = Some (p,a,b) ->
      sem_cexp sl sn size rh e = re -> reg_typed rh bv size stack -> 
      0 < size -> 0 < sl ->
      no_equal_stack stack e size bv rh ->
      reg_match_q stack rh f bv vmap aenv ->
      reg_same_c stack rh rl bv vmap aenv ->
      reg_match_c stack f bv vmap aenv ->
      reg_match_st sl sn stack f vmap ->
      aenv_match stack size bv aenv vmap ->
      not_stack stack (get_var_cexp e) ->
      cexp_set_up e sl size stack sn vmap rh bv f aenv tenv
         -> (p = None /\ (exists b', b = Some b' /\ re = Some (sn,b') ))
              \/ ((exists p', p = Some p' /\ b = None
          /\ re = Some (S sn,get_cua (prog_sem aenv p' f (vmap (L stack,0),sn))))).
Proof.
  intros. induction e.
  simpl in *.
  bdestruct (sn <? sl).
  destruct (¬ (qvar_eq size bv rl x y)) eqn:eq1.
  unfold gen_clt_c in H.
  destruct (type_factor bv b0 x) eqn:eq2.
  destruct (type_factor bv b0 y) eqn:eq3.
  destruct (par_find_var size bv rl x) eqn:eq4.
  destruct (par_find_var size bv rl y) eqn:eq5.
  assert (par_find_var size bv rh x = Some p2).
  eapply par_find_var_lh.
  apply eq2. apply eq4.
  apply not_stack_shrink_l in H10. apply H10. apply H6.
  assert (par_find_var size bv rh y = Some p3).
  eapply par_find_var_lh.
  apply eq3. apply eq5.
  apply not_stack_shrink_r in H10. apply H10. apply H6.
  rewrite H13 in *. rewrite H14 in *.
  simpl in *.
  destruct H11 as [X1 [X2 [X3 [X4 [X5 [X6 [X7 [X8 [X9 [X10 [X11 X12]]]]]]]]]]].
  destruct (is_q p0) eqn:eq6.
  destruct (is_q p1) eqn:eq7.
  simpl in *.
  inv H. right.
  exists (comparator01 (if b0 =b= Bl then 1 else size) 
       (vmap p3) (vmap p2) (vmap (L stack0, 0), S sn)
       (vmap (L stack0, 0), sn)).
  split. easy. split. easy.
  unfold sem_cexp.
  bdestruct (sn <? sl).
  rewrite par_find_var_means_cfac with (bv:=bv) (vx := p2).
  rewrite par_find_var_means_cfac with (bv:=bv) (vx := p3).
  simpl in *.
  destruct (Reg.find (elt:=nat -> bool) p2 rh) eqn:eq8.
  destruct (Reg.find (elt:=nat -> bool) p3 rh) eqn:eq9.
  destruct b0 eqn:eq10.
  bdestruct (Nat =b= Bl). inv H0.
  rewrite comparator01_sem_a with (tenv := tenv)
        (v1:= a_nat2fb b1 size) (v2:= a_nat2fb b size); try easy.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb b size <? a_nat2fb b1 size).
  bdestruct ((a_nat2fb b1 size <=? a_nat2fb b size)). lia.
  simpl. easy.
  bdestruct ((a_nat2fb b1 size <=? a_nat2fb b size)).
  simpl. easy. lia.
  apply X8. lia.
  apply a_nat2fb_small.
  apply a_nat2fb_small.
  unfold no_equal. split. lia.
  split. easy. split. easy. split. easy.
  split. easy. iner_p.
  apply X8 ; lia.
  apply X8 ; lia.
  rewrite type_factor_means_b with (x := x) 
           (b:=Nat) (t := p0) (size:=size) (r:= rh) in X9; try easy.
  rewrite type_factor_means_b with (x := x) 
           (b:=Nat) (t := p0) (size:=size) (r:= rh) in X11; try easy.
  unfold reg_match_q in H5.
  destruct H4.
  apply Reg.find_2 in eq9.
  apply par_find_var_get in eq5.
  apply not_stack_shrink_r in H10.
  apply H10 in eq5.
  specialize (H1 p3 b1 eq5 eq9) as eq11.
  apply H5 in eq9; try easy.
  rewrite nat2fb_a_nat2fb.
  assert ( (aenv (vmap p3)) = size).
  unfold aenv_match in H9.
  specialize (H9 p3 eq5).
  rewrite type_factor_means_b with (x := y) 
           (b:=Nat) (t := p1) (size:=size) (r:= rh) in H9; try easy.
  rewrite H15 in eq9. easy.
  rewrite type_factor_means_b with (x := y) 
           (b:=Nat) (t := p1) (size:=size) (r:= rh) in eq11; try easy.
  simpl in eq11.
  apply eq11.
  apply type_factor_means_some with (x := y) 
           (b:=Nat) (t := p1) (size:=size) (r:= rh) ; try easy.
  apply type_factor_means_some with (x := y) 
           (b:=Nat) (t := p1) (size:=size) (r:= rh) ; try easy.
  apply type_factor_means_q with (x := y) 
           (b:=Nat) (t := p1) (size:=size) (r:= rh) ; try easy.
  unfold reg_match_q in H5.
  destruct H4.
  apply Reg.find_2 in eq8.
  apply par_find_var_get in eq4.
  apply not_stack_shrink_l in H10.
  apply H10 in eq4.
  specialize (H1 p2 b eq4 eq8) as eq11.
  apply H5 in eq8; try easy.
  rewrite nat2fb_a_nat2fb.
  assert ( (aenv (vmap p2)) = size).
  unfold aenv_match in H9.
  specialize (H9 p2 eq4).
  rewrite type_factor_means_b with (x := x) 
           (b:=Nat) (t := p0) (size:=size) (r:= rh) in H9; try easy.
  rewrite H15 in eq8. easy.
  rewrite type_factor_means_b with (x := x) 
           (b:=Nat) (t := p0) (size:=size) (r:= rh) in eq11; try easy.
  simpl in eq11.
  apply eq11.
  apply type_factor_means_some with (x := x) 
           (b:=Nat) (t := p0) (size:=size) (r:= rh) ; try easy.
  apply type_factor_means_some with (x := x) 
           (b:=Nat) (t := p0) (size:=size) (r:= rh) ; try easy.
  apply type_factor_means_q with (x := x) 
           (b:=Nat) (t := p0) (size:=size) (r:= rh) ; try easy.
  unfold reg_match_st in H8.
  specialize (H8 (S sn)).
  rewrite <- H8.
  rewrite get_cus_cua. easy. lia. lia.
  unfold reg_match_st in H8.
  specialize (H8 (sn)).
  rewrite <- H8.
  rewrite get_cus_cua. easy. lia. lia.

  bdestruct (Flt =b= Bl). inv H0.
  rewrite comparator01_sem_a with (tenv := tenv)
        (v1:= a_nat2fb b1 size) (v2:= a_nat2fb b size); try easy.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb b size <? a_nat2fb b1 size).
  bdestruct ((a_nat2fb b1 size <=? a_nat2fb b size)). lia.
  simpl. easy.
  bdestruct ((a_nat2fb b1 size <=? a_nat2fb b size)).
  simpl. easy. lia.
  apply X8. lia.
  apply a_nat2fb_small.
  apply a_nat2fb_small.
  unfold no_equal. split. lia.
  split. easy. split. easy. split. easy.
  split. easy. iner_p.
  apply X8 ; lia.
  apply X8 ; lia.
  rewrite type_factor_means_b with (x := x) 
           (b:=Flt) (t := p0) (size:=size) (r:= rh) in X9; try easy.
  rewrite type_factor_means_b with (x := x) 
           (b:=Flt) (t := p0) (size:=size) (r:= rh) in X11; try easy.
  unfold reg_match_q in H5.
  destruct H4.
  apply Reg.find_2 in eq9.
  apply par_find_var_get in eq5.
  apply not_stack_shrink_r in H10.
  apply H10 in eq5.
  specialize (H1 p3 b1 eq5 eq9) as eq11.
  apply H5 in eq9; try easy.
  rewrite nat2fb_a_nat2fb.
  assert ( (aenv (vmap p3)) = size).
  unfold aenv_match in H9.
  specialize (H9 p3 eq5).
  rewrite type_factor_means_b with (x := y) 
           (b:=Flt) (t := p1) (size:=size) (r:= rh) in H9; try easy.
  rewrite H15 in eq9. easy.
  rewrite type_factor_means_b with (x := y) 
           (b:=Flt) (t := p1) (size:=size) (r:= rh) in eq11; try easy.
  simpl in eq11.
  apply eq11.
  apply type_factor_means_some with (x := y) 
           (b:=Flt) (t := p1) (size:=size) (r:= rh) ; try easy.
  apply type_factor_means_some with (x := y) 
           (b:=Flt) (t := p1) (size:=size) (r:= rh) ; try easy.
  apply type_factor_means_q with (x := y) 
           (b:=Flt) (t := p1) (size:=size) (r:= rh) ; try easy.
  unfold reg_match_q in H5.
  destruct H4.
  apply Reg.find_2 in eq8.
  apply par_find_var_get in eq4.
  apply not_stack_shrink_l in H10.
  apply H10 in eq4.
  specialize (H1 p2 b eq4 eq8) as eq11.
  apply H5 in eq8; try easy.
  rewrite nat2fb_a_nat2fb.
  assert ( (aenv (vmap p2)) = size).
  unfold aenv_match in H9.
  specialize (H9 p2 eq4).
  rewrite type_factor_means_b with (x := x) 
           (b:=Flt) (t := p0) (size:=size) (r:= rh) in H9; try easy.
  rewrite H15 in eq8. easy.
  rewrite type_factor_means_b with (x := x) 
           (b:=Flt) (t := p0) (size:=size) (r:= rh) in eq11; try easy.
  simpl in eq11.
  apply eq11.
  apply type_factor_means_some with (x := x) 
           (b:=Flt) (t := p0) (size:=size) (r:= rh) ; try easy.
  apply type_factor_means_some with (x := x) 
           (b:=Flt) (t := p0) (size:=size) (r:= rh) ; try easy.
  apply type_factor_means_q with (x := x) 
           (b:=Flt) (t := p0) (size:=size) (r:= rh) ; try easy.
  unfold reg_match_st in H8.
  specialize (H8 (S sn)).
  rewrite <- H8.
  rewrite get_cus_cua. easy. lia. lia.
  unfold reg_match_st in H8.
  specialize (H8 (sn)).
  rewrite <- H8.
  rewrite get_cus_cua. easy. lia. lia.

  bdestruct (Bl =b= Bl).
  rewrite comparator01_sem_a with (tenv := tenv)
        (v1:= a_nat2fb b1 1) (v2:= a_nat2fb b 1); try easy.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  simpl. repeat rewrite plus_0_r.
  bdestruct (Nat.b2n (b 0) <? Nat.b2n (b1 0)).
  bdestruct ((Nat.b2n (b1 0) <=? Nat.b2n (b 0))). lia.
  simpl. easy.
  bdestruct (((Nat.b2n (b1 0) <=? Nat.b2n (b 0)))).
  simpl. easy. lia.
  apply X8. lia. lia.
  apply a_nat2fb_small.
  apply a_nat2fb_small.
  unfold no_equal. split. lia.
  split. easy. split. easy. split. easy.
  split. easy. iner_p.
  unfold nor_modes. intros.
  apply X7. lia.
  unfold nor_modes. intros.
  apply X6. lia.
  apply X8;lia.
  apply X8;lia.
  rewrite type_factor_means_b with (x := x) 
           (b:=Bl) (t := p0) (size:=size) (r:= rh) in X9; try easy.
  rewrite type_factor_means_b with (x := x) 
           (b:=Bl) (t := p0) (size:=size) (r:= rh) in X11; try easy.
  unfold reg_match_q in H5.
  destruct H4.
  apply Reg.find_2 in eq9.
  apply par_find_var_get in eq5.
  apply not_stack_shrink_r in H10.
  apply H10 in eq5.
  specialize (H1 p3 b1 eq5 eq9) as eq11.
  apply H5 in eq9; try easy.
  rewrite nat2fb_a_nat2fb.
  assert ( (aenv (vmap p3)) = 1).
  unfold aenv_match in H9.
  specialize (H9 p3 eq5).
  rewrite type_factor_means_b with (x := y) 
           (b:=Bl) (t := p1) (size:=size) (r:= rh) in H9; try easy.
  rewrite H15 in eq9. easy.
  rewrite type_factor_means_b with (x := y) 
           (b:=Bl) (t := p1) (size:=size) (r:= rh) in eq11; try easy.
  simpl in eq11.
  apply eq11.
  apply type_factor_means_some with (x := y) 
           (b:=Bl) (t := p1) (size:=size) (r:= rh) ; try easy.
  apply type_factor_means_some with (x := y) 
           (b:=Bl) (t := p1) (size:=size) (r:= rh) ; try easy.
  apply type_factor_means_q with (x := y) 
           (b:=Bl) (t := p1) (size:=size) (r:= rh) ; try easy.
  unfold reg_match_q in H5.
  destruct H4.
  apply Reg.find_2 in eq8.
  apply par_find_var_get in eq4.
  apply not_stack_shrink_l in H10.
  apply H10 in eq4.
  specialize (H1 p2 b eq4 eq8) as eq11.
  apply H5 in eq8; try easy.
  rewrite nat2fb_a_nat2fb.
  assert ( (aenv (vmap p2)) = 1).
  unfold aenv_match in H9.
  specialize (H9 p2 eq4).
  rewrite type_factor_means_b with (x := x) 
           (b:=Bl) (t := p0) (size:=size) (r:= rh) in H9; try easy.
  rewrite H15 in eq8. easy.
  rewrite type_factor_means_b with (x := x) 
           (b:=Bl) (t := p0) (size:=size) (r:= rh) in eq11; try easy.
  simpl in eq11.
  apply eq11.
  apply type_factor_means_some with (x := x) 
           (b:=Bl) (t := p0) (size:=size) (r:= rh) ; try easy.
  apply type_factor_means_some with (x := x) 
           (b:=Bl) (t := p0) (size:=size) (r:= rh) ; try easy.
  apply type_factor_means_q with (x := x) 
           (b:=Bl) (t := p0) (size:=size) (r:= rh) ; try easy.
  unfold reg_match_st in H8.
  specialize (H8 (S sn)).
  rewrite <- H8.
  rewrite get_cus_cua. easy. lia. lia.
  unfold reg_match_st in H8.
  specialize (H8 (sn)).
  rewrite <- H8.
  rewrite get_cus_cua. easy. lia. lia. easy.

  apply RegFacts.in_find_iff in X5. easy.
  apply RegFacts.in_find_iff in X4. easy.
  easy. easy. lia.

  simpl in *.
  destruct (par_eval_cfac size smap bv rl b0 y) eqn:eq8.
  inv H. right.
  exists ((init_v size (vmap p3) b1;
    comparator01 (if b0 =b= Bl then 1 else size) (vmap p3) (vmap p2)
      (vmap (L stack0, 0), S sn) (vmap (L stack0, 0), sn)); init_v size (vmap p3) b1).
  split. easy. split. easy.
  simpl.
Admitted.



(*define example hash_function as the oracle for grover's search.
  https://qibo.readthedocs.io/en/stable/tutorials/hash-grover/README.html *)
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
      qfor x (Nor (Num (nat2fb 10)))
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
Definition f1 :var := 16.
Definition n1 : var := 17. 

Definition m : var := 22. 
Definition x4 : var := 23. 

Definition x_n (size:nat): func :=
   (f1, ((Nat,n,1)::(Nat,m,1)::(Nat, n1,5)::(Flt, x3,5)::(Flt, x4,6)::(Flt,e,1)::[]),
               qfor n (Nor (Num (nat2fb 5))) (
                nmod (Nor (Var (L m))) (Nor (Var (L n))) (Nor (Num (nat2fb 2)));;;
                qif (ceq QFTA Nat (Nor (Var (L m))) (Nor (Num (nat2fb 0)))) 
                 (ndiv (Nor (Var (L n))) (Nor (Var (L n))) (Nor (Num (nat2fb 2)));;;
                  nadd QFTA (Nor (Num (nat2fb 1))) (Ptr n1 (Var (L n1))))
                 (ndiv (Nor (Var (L n))) (Nor (Var (L n))) (Nor (Num (nat2fb 2)))));;;

               init Flt (Ptr x3 ((Num (nat2fb 0)))) (Nor (Var (G x)));;;
               init Flt (Nor (Var (L x4))) (Nor (Num (negatem size (nat2fb 0))));;;
               qfor n (Nor (Num (nat2fb 5))) (
                   qif (ceq QFTA Nat (Nor (Var (L n))) (Nor (Num (nat2fb 0))))
                   (skip)
                   (ncsub (Nor (Var (L m))) (Nor (Var (L n))) (Nor (Num (nat2fb 1)));;;
                    fmul QFTA (Ptr x3 (Var (L m))) (Ptr x3 (Var (L m))) (Ptr x3 (Var (L n)))
                    ));;;
               qfor n (Nor (Num (nat2fb 5))) (
                   qif (ceq QFTA Nat (Ptr n1 (Var (L n))) (Nor (Num (nat2fb 0))))
                   (skip)
                   (ncadd (Nor (Var (L m))) (Nor (Var (L n))) (Nor (Num (nat2fb 1)));;;
                    fmul QFTA (Ptr x3 (Var (L n))) (Ptr x4 (Var (L n))) (Ptr x4 (Var (L m)))
                    ));;;
                init Flt (Nor (Var (L e))) (Ptr x4 (Num (nat2fb 5)))

,L e).

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
         qfor g (Nor (Num (nat2fb 5))) 
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
         (s_size, size,[(Flt,result,v)],(x_n size:: taylor_sin::[]),f,result).

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
         qfor g (Nor (Num (nat2fb 5))) 
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
         (s_size, size,[(Flt,result,v)],(x_n size:: taylor_cos::[]),f,result).
