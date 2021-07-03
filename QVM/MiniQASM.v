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

Inductive flag := QFTA | Classic.

Definition flag_eq  (t1 t2:flag) : bool := 
   match t1 with QFTA => match t2 with QFTA  => true
                            | _ => false
                        end
               | Classic => match t2 with Classic => true
                           | _ => false
                        end
   end.

Notation "i '=fl=' j" := (flag_eq i j) (at level 50).

Lemma flag_eqb_eq : forall a b, a =fl= b = true -> a = b.
Proof.
 intros. unfold flag_eq in H.
 destruct a. destruct b. easy. inv H.
 destruct b. inv H. easy. 
Qed.

Lemma flag_eqb_neq : forall a b, a =fl= b = false -> a <> b.
Proof.
 intros. unfold flag_eq in H.
 destruct a. destruct b. inv H. easy.
 destruct b. easy. inv H. 
Qed.

Lemma flag_eq_reflect : forall r1 r2, reflect (r1 = r2) (flag_eq r1 r2). 
Proof.
  intros.
  destruct (r1 =fl= r2) eqn:eq1.
  apply  ReflectT.
  apply flag_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply flag_eqb_neq in eq1.
  assumption. 
Qed.

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
   and storeister values that can appear in a guantum circuit. *)
Inductive btype := Nat : btype | FixedP : btype | Bl : btype.


Definition bty_eq  (t1 t2:btype) : bool := 
   match t1 with Nat => match t2 with Nat  => true
                            | _ => false
                        end
               | FixedP => match t2 with FixedP => true
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

Inductive  typ :Type := TArray (a:atype) (b:btype) (n:nat) | TNor (a:atype) (b:btype).

Definition typ_eq  (t1 t2:typ) : bool := 
   match t1 with TArray a1 b1 n1 =>
           match t2 with TArray a2 b2 n2  => (a1 =a= a2) && (b1 =b= b2) && (n1 =? n2)
                      | _ => false
                        end
         | TNor a1 b1 => match t2 with TNor a2 b2 => (a1 =a= a2) && (b1 =b= b2) 
                      | _ => false end
   end.

Notation "i '=t=' j" := (typ_eq i j) (at level 50).

Lemma typ_eqb_eq : forall a b, a =t= b = true -> a = b.
Proof.
 intros. unfold typ_eq in H.
 destruct a. destruct b.
 apply andb_true_iff in H.
 destruct H.
 apply andb_true_iff in H.
 destruct H.
 apply aty_eqb_eq in H.
 apply bty_eqb_eq in H1.
 bdestruct (n =? n0). subst. easy. inv H0.
 inv H.
 destruct b. inv H.
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
 apply andb_false_iff in H.
 destruct H.
 apply aty_eqb_neq in H. intros R. inv R. easy.
 apply bty_eqb_neq in H. intros R. inv R. easy.
 bdestruct (n =? n0). inv H. intros R. inv R. easy.
 easy.
 destruct b.
 easy.
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

Hint Resolve flag_eq_reflect aty_eq_reflect qty_eq_reflect qdty_eq_reflect bty_eq_reflect typ_eq_reflect : bdestruct.

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

Inductive cfac := Index (x:qvar) (v:factor) | Nor (v:factor).

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

Inductive cexp := clt (t:btype) (x:cfac) (y:cfac)
                  | ceq (t:btype) (x:cfac) (y:cfac)
                  | iseven (x:cfac).

Inductive qexp :=
                  qinv (x:cfac)
                | call (f:fvar) (v: cfac)
                | qif (c:cexp) (e1:qexp) (e2:qexp)
                | qfor (x:var) (n:cfac) (e:qexp)
                | qseq (q1:qexp) (q2:qexp)
                | skip
                | init (x:cfac) (v:cfac)  
                | nadd (v:cfac) (x:cfac) 
                | nsub (v:cfac) (x:cfac)
                | nmul (x:cfac) (y:cfac) (z:cfac)
               (* | nqmul (f:flag) (v1:cfac) (v2:cfac) (z:cfac) *)
                | fadd (v:cfac) (x:cfac) 
                | fsub (v:cfac) (x:cfac)
                | fmul (v1:cfac) (v2:cfac) (z:cfac)
                | qxor (v:cfac) (x:cfac)
                | slrot (x:cfac)
                | ndiv (x:cfac) (y:cfac) (v:cfac) (*x := y/n where x,n are a nat *)
                | nmod (x:cfac) (y:cfac) (v:cfac) (* x := y mod n where x,n are a nat *)
                | nfac (x:cfac) (v:cfac) (* x := n! where x is a nat & n is  nat *)
                | fdiv (x:cfac) (v:cfac) (* x := x / n where n is a natural number, x is a float. *)
                | ncsub (x:cfac) (y:cfac) (z:cfac) (* x := y - z all natural and C type *)
                | ncadd (x:cfac) (y:cfac) (z:cfac) (* x := y + z all natural and C type *)
                | fcsub (x:cfac) (y:cfac) (z:cfac) (* x := y - z all natural and C type *)
                | fcadd (x:cfac) (y:cfac) (z:cfac) (* x := y + z all natural and C type *)
                | ncmul (x:cfac) (y:cfac) (z:cfac) (* x := y * z all natural and C type *)
                | fndiv (x:cfac) (v:cfac) (z:cfac). (* z = x/v where x and v are natural numbers, z is float
                           x and v are both integers, but the final result in z must be a float < 1 *)

(*functions will do automatic inverse computation after a function is returned.
  for each ret statement, there is a list of pairs of vars, and the left one is the global variables to return,
   while the left one is the local variables. after a function call is returned,
    it will store all the local variables to their correponding global variables, and then reverse the computation.  *)

Notation "p1 ;;; p2" := (qseq p1 p2) (at level 50) : exp_scope.

Definition func : Type := ( fvar * list (typ * var) * qexp * cfac).
    (* a function is a fun name, a starting block label, and a list of blocks, and the returned variable. *)

Definition prog : Type := (nat * list (typ * var) * list func * fvar * var). 
   (* a number of bits in FixedP and Nat
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

Module BEnv := FMapList.Make QvarType.
Module BEnvFacts := FMapFacts.Facts (BEnv).
Definition benv := BEnv.t typ.
Definition empty_benv := @BEnv.empty typ.


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


Module FEnv := FMapList.Make Nat_as_OT.
Module FEnvFacts := FMapFacts.Facts (FEnv).
Definition fenv := FEnv.t (list (typ * var) * qexp * benv * cfac).
Definition fenv_empty := @FEnv.empty (list (typ * var) * qexp * benv * cfac).

Notation "'do' X '<-' A '@' B" := (bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).

Definition typ_factor (bv:benv) (t:btype) (fc:factor) :=
   match fc with Var x => do re <- BEnv.find x bv @
    match re with TArray x y n => None
            | TNor x y => if (y =b= t) then Some (x,y) else None
   end
            | Num n => Some (C,t)
  end.

Definition typ_factor_full (bv:benv) (a:atype) (t:btype) (fc:factor) :=
   match fc with Var x => do re <- BEnv.find x bv @
    match re with TArray x y n => None
            | TNor x y => if (a =a= x) && (y =b= t) then Some (x,y) else None
   end
            | Num n => if a =a= C then Some (C,t) else None
  end.

Definition type_factor (bv:benv) (t:btype) (fc:cfac) :=
   match fc with Index x ic =>
       do re <- BEnv.find x bv @ 
             match re with TArray a b n =>
                  if (b =b= t) then 
                       do ta <- typ_factor_full bv C Nat ic @ Some (a,t)
                  else None

                    | TNor x y => None
             end
               | Nor c => typ_factor bv t c
   end.



Definition type_factor_full (bv:benv) (a:atype) (t:btype) (fc:cfac) :=
   match fc with Index x ic =>
       do re <- BEnv.find x bv @ 
             match re with TArray a' b n =>
                  if (a =a= a') && (b =b= t) then 
                       do ta <- typ_factor_full bv C Nat ic @ Some (a,t)
                  else None

                    | TNor x y => None
             end
               | Nor c => typ_factor_full bv a t c
   end.


Definition meet_type (t1 t2 : (atype * btype)) := 
          match t1 with (Q,b) => (Q,b)
               | (C,b) => match t2 with (Q,b2) => (Q,b) | _ => (C,b) end end.


Definition type_cexp (benv:benv) (c:cexp) := 
   match c with clt b x y => 
             do re1 <- type_factor benv b x @
                do re2 <- type_factor benv b y @ ret (meet_type re1 re2)
            | ceq b x y => 
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

(*
Definition allow_inv (e:qexp) : bool :=
   match e with skip | init _ _  | nadd _ _ | nsub _ _ _
              | nmul _ _ _ _ | fadd _ _ _ | fsub _ _ _ | fmul _ _ _ _ | qxor _ _ _ => true
             | _ => false
   end.
*)

Definition is_q (t:typ) : bool := 
  match t with TArray Q _ _ | TNor Q _ => true
            | _ => false
  end.

Definition is_c (t:typ) : bool := 
  match t with TArray C _ _ | TNor C _ => true
            | _ => false
  end.

Definition get_var (c:cfac) : option qvar :=
   match c with Nor (Var x) => Some x
             | Nor (Num x) => None
             | Index x y => Some x
   end.

Definition get_index (c:cfac) : option factor :=
   match c with Nor x => None
           | Index x y => Some y
   end.

(*
Definition put_shell (c:ttyp) (t:typ) :=
   match c with TNor t' => TNor t
              | TPtr t' n => TPtr t n
   end.
*)

Definition get_ct (c:typ) :=
   match c with TArray x y n => y
              | TNor x y => y
   end.

Definition sub_nor (t1 t2:(atype * btype)) := 
  match t1 with (a1,b1) => match t2 with (a2,b2) 
                             => (b1 =b= b2) && (if a1 =a= C then true else a2 =a= Q)
                           end end.

Definition fresh_loop_fac (x:var) (fc:factor) :=
   match fc with Var y => if y =q= (L x) then false else true
             | Num b => true
   end.

Definition fresh_loop_cfac (x:var) (fc:cfac) :=
   match fc with Index y n => if y =q= (L x) then false else true
             | Nor v => fresh_loop_fac x v
   end.

Fixpoint fresh_loop_c (x:var) (e:qexp) :=
   match e with skip => true
             | init y v => fresh_loop_cfac x y
             | nadd y v => fresh_loop_cfac x y
             | nsub y v => fresh_loop_cfac x y
             | nmul y z v => fresh_loop_cfac x y
             | fadd y v => fresh_loop_cfac x y
             | fsub y v => fresh_loop_cfac x y
             | fmul y z v => fresh_loop_cfac x y
             | qxor y v => fresh_loop_cfac x y
             | slrot y => fresh_loop_cfac x y
             | ndiv y z v => fresh_loop_cfac x y
             | nmod y z v => fresh_loop_cfac x y
             | fdiv y z => fresh_loop_cfac x y
             | nfac y z => fresh_loop_cfac x y
             | ncsub y z v => fresh_loop_cfac x y
             | ncadd y z v => fresh_loop_cfac x y
             | fcsub y z v => fresh_loop_cfac x y
             | fcadd y z v => fresh_loop_cfac x y
             | ncmul y z v => fresh_loop_cfac x y
             | fndiv y z v => fresh_loop_cfac x y
             | qinv y => fresh_loop_cfac x y
             | call f y => fresh_loop_cfac x y
             | qif ce e1 e2 => (fresh_loop_c x e1) && (fresh_loop_c x e2)
             | qfor y n e => (fresh_loop_cfac x n) && (if x =? y then true else fresh_loop_c x e)
             | qseq e1 e2 => (fresh_loop_c x e1) && (fresh_loop_c x e2)
   end.

Fixpoint no_rot (e:qexp) :=
   match e with skip => true
             | init y v => true
             | nadd y v => true
             | nsub y v => true
             | nmul y z v => true
             | fadd y v => true
             | fsub y v => true
             | fmul y z v => true
             | qxor y v => true
             | slrot y => false
             | ndiv y z v => true
             | nmod y z v => true
             | fdiv y z => true
             | nfac y z => true
             | ncsub y z v => true
             | ncadd y z v => true
             | fcsub y z v => true
             | fcadd y z v => true
             | ncmul y z v => true
             | fndiv y z v => true
             | qinv y => true
             | call f y => true
             | qif ce e1 e2 => (no_rot e1) && (no_rot e2)
             | qfor y n e => no_rot e
             | qseq e1 e2 => (no_rot e1) && (no_rot e2)
   end.


Definition is_q_fac (bv:benv) (c:factor) :=
    match c with Var x => match BEnv.find x bv with None => false
                              | Some t => is_q t
                          end
             | Num x => false
    end.

Definition is_q_cfac (bv:benv) (c:cfac) :=
    match c with Index x n => 
          match BEnv.find x bv with None => false
                    | Some t => is_q t
          end
              | Nor x => is_q_fac bv x
    end.

Fixpoint has_c_exp (bv:benv) (e:qexp) :=
   match e with skip => false
             | init y v => false
             | nadd y v => false
             | nsub y v => false
             | nmul y z v => false
             | fadd y v => false
             | fsub y v => false
             | fmul y z v => false
             | qxor y v => ¬ (is_q_cfac bv y)
             | slrot y => ¬ (is_q_cfac bv y)
             | ndiv y z v => true
             | nmod y z v => true
             | fdiv y z => true
             | nfac y z => true
             | ncsub y z v => true
             | ncadd y z v => true
             | fcsub y z v => true
             | fcadd y z v => true
             | ncmul y z v => true
             | fndiv y z v => true
             | qinv y => false
             | call f y => ¬ (is_q_cfac bv y)
             | qif ce e1 e2 => (has_c_exp bv e1) && (has_c_exp bv e2)
             | qfor y n e => has_c_exp bv e
             | qseq e1 e2 => has_c_exp bv e1 && has_c_exp bv e2
   end.

Fixpoint type_qexp (fv:fenv) (bv:benv) (e:qexp):=
   match e with skip => Some bv
             | init x v => 
               do core <- get_var x @ 
                  do c <- BEnv.find core bv @
                    do re <- type_factor bv (get_ct c) v @
                 if is_q c then ret bv else None

             | nadd x y => 
             do re1 <- type_factor bv Nat y @
                do re2 <- type_factor_full bv Q Nat x @ 
                   do core <- get_var x @
                    do old <- BEnv.find core bv @ ret bv

             | nsub x y => 
             do re1 <- type_factor bv Nat y @
                do re2 <- type_factor_full bv Q Nat x @ 
                   do core <- get_var x @
                    do old <- BEnv.find core bv @ ret bv

             | nmul x y z => 
             do re1 <- type_factor_full bv Q Nat x @
                do re2 <- type_factor bv Nat y @ 
                 do re3 <- type_factor bv Nat z @
                   do core <- get_var x @
                    do old <- BEnv.find core bv @ ret bv

             | fadd x y => 
             do re1 <- type_factor bv FixedP y @
                do re2 <- type_factor_full bv Q FixedP x @ 
                   do core <- get_var x @
                    do old <- BEnv.find core bv @ ret bv

             | fsub x y => 
             do re1 <- type_factor bv FixedP y @
                do re2 <- type_factor_full bv Q FixedP x @ 
                   do core <- get_var x @
                    do old <- BEnv.find core bv @ ret bv

             | fmul x y z => 
             do re1 <- type_factor_full bv Q FixedP x @
                do re2 <- type_factor bv FixedP y @ 
                 do re3 <- type_factor bv FixedP z @
                   do core <- get_var x @
                    do old <- BEnv.find core bv @ ret bv

             | qxor x y => 
                   do core <- get_var x @
                    do old <- BEnv.find core bv @ 
                     do re <- type_factor bv (get_ct old) y @ ret bv

             | slrot x =>
                   do core <- get_var x @
                    do old <- BEnv.find core bv @ ret bv

             | qinv x => 
                   do core <- get_var x @
                    do old <- BEnv.find core bv @ 
                     if is_q old then ret bv else None

             | ndiv x y v => 
             do re1 <- type_factor bv Nat x @
                do re2 <- type_factor bv Nat y @ 
                  do re3 <- type_factor bv Nat v @ 
                       if (fst re1 =a= C) && (fst re2 =a= C) && (fst re3 =a= C) then ret bv else None

             | nmod x y v => 
             do re1 <- type_factor bv Nat x @
                do re2 <- type_factor bv Nat y @ 
                  do re3 <- type_factor bv Nat v @ 
                       if (fst re1 =a= C) && (fst re2 =a= C) && (fst re3 =a= C) then ret bv else None

             | nfac x y => 
             do re1 <- type_factor bv Nat x @
                do re2 <- type_factor bv Nat y @ 
                       if (fst re1 =a= C) && (fst re2 =a= C) then ret bv else None

             | fdiv x y => 
             do re1 <- type_factor bv FixedP x @
                do re2 <- type_factor bv Nat y @ 
                       if (fst re1 =a= C) && (fst re2 =a= C) then ret bv else None

             | fndiv x y z => 
             do re1 <- type_factor bv FixedP x @
                do re2 <- type_factor bv Nat y @ 
                  do re3 <- type_factor bv Nat z @ 
                       if (fst re1 =a= C) && (fst re2 =a= C) && (fst re3 =a= C) then ret bv else None

             | ncadd x y z => 
             do re1 <- type_factor bv Nat x @
                do re2 <- type_factor bv Nat y @ 
                  do re3 <- type_factor bv Nat z @ 
                       if (fst re1 =a= C) && (fst re2 =a= C) && (fst re3 =a= C) then ret bv else None

             | ncsub x y z => 
             do re1 <- type_factor bv Nat x @
                do re2 <- type_factor bv Nat y @ 
                  do re3 <- type_factor bv Nat z @ 
                       if (fst re1 =a= C) && (fst re2 =a= C) && (fst re3 =a= C) then ret bv else None

             | ncmul x y z => 
             do re1 <- type_factor bv Nat x @
                do re2 <- type_factor bv Nat y @ 
                  do re3 <- type_factor bv Nat z @ 
                       if (fst re1 =a= C) && (fst re2 =a= C) && (fst re3 =a= C) then ret bv else None

             | fcadd x y z => 
             do re1 <- type_factor bv FixedP x @
                do re2 <- type_factor bv FixedP y @ 
                  do re3 <- type_factor bv FixedP z @ 
                       if (fst re1 =a= C) && (fst re2 =a= C) && (fst re3 =a= C) then ret bv else None

             | fcsub x y z => 
             do re1 <- type_factor bv FixedP x @
                do re2 <- type_factor bv FixedP y @ 
                  do re3 <- type_factor bv FixedP z @ 
                       if (fst re1 =a= C) && (fst re2 =a= C) && (fst re3 =a= C) then ret bv else None

              | call f x => 
                 do ref <- FEnv.find f fv @
                   match ref with (tvl,e,fbenv, rx) =>
                    do rxv <- get_var rx @
                        do re1 <- BEnv.find rxv fbenv @
                          do core <- get_var x @
                           do old <- BEnv.find core bv @
                            if (is_q re1) && (is_q old) && ((get_ct re1) =b= (get_ct old)) then ret bv
                              else if (is_c re1) && ((get_ct re1) =b= (get_ct old)) then ret bv else None
                   end

              | qif ce e1 e2 => 
                 do rce <- type_cexp bv ce @
                   do bv' <- type_qexp fv bv e1 @
                    if no_rot e1 && no_rot e2 then 
                      if (fst rce =a= C) then 
                       type_qexp fv bv' e2 
                      else if (fst rce =a= Q) && (has_c_exp bv e1) && (has_c_exp bv e2) then
                       type_qexp fv bv' e2 
                      else None
                   else None

              | qseq e1 e2 => 
                 do bv' <- type_qexp fv bv e1 @ type_qexp fv bv' e2

              | qfor x n e => 
                do re1 <- BEnv.find (L x) bv @
                 if is_c re1 then
                  do re2 <- type_factor_full bv C Nat n @ 
                   if fresh_loop_c x e then
                     type_qexp fv (BEnv.add (L x) (TNor C Nat) bv) e else None
                 else None


end.

Definition no_zero (t:typ) := match t with TArray x y n => if n =? 0 then false else true 
                | TNor x y => true 
     end.

Fixpoint gen_env (l:list (typ * var)) (bv:benv) : option benv := 
   match l with [] => Some bv
             | ((t,x)::xl) => 
                  do new_env <- gen_env xl bv @
                    if no_zero t then Some (BEnv.add (L x) t new_env) else None
   end.

Fixpoint type_funs (benv:benv) (fv:fenv) (l:list func) : option fenv :=
     match l with [] => Some fv
              | ((f,l,e,rx)::fs) => 
               do benv' <- gen_env l benv @
                 do benv'' <- type_qexp fv benv' e @
                   do core <- get_var rx @
                     do old <- BEnv.find core benv'' @
                     type_funs benv (FEnv.add f ((l,e,benv',rx)) fv) fs
     end.

Fixpoint gen_genv (l:list (typ * var)) : option benv := 
   match l with [] => Some empty_benv
             | ((t,x)::xl) => 
                  do new_env <- gen_genv xl @
                   if no_zero t then Some (BEnv.add (G x) t new_env) else None
   end.

(* ( fvar * list var * qexp ). *)
Definition type_prog (p:prog) : option fenv :=
   match p with (n,l,fl,main,rx) => 
    do bv <- gen_genv l @ 
      do fv <- type_funs bv fenv_empty fl @
            do block <- FEnv.find main fv @ 
              do re <- BEnv.find (G rx) bv @
              match block with (tvl,e,fbenv, x) =>
                 do re1 <- type_factor fbenv (get_ct re) x @ ret fv
              end
   end.

(* Well-type checks for inv. *)
Definition qvar_eq_fac (c:cfac) (x:qvar) :=
    match get_var c with None => false
            | Some y => x =q= y
    end.

Fixpoint fac_in_qvars (c:cfac) (l:list qvar) :=
    match l with [] => false
         | (x::xl) => (qvar_eq_fac c x) || (fac_in_qvars c xl)
    end.

Definition match_q_exp (e:qexp) (x:qvar) :=
   match e with skip => false
             | init y v => qvar_eq_fac y x
             | nadd y v => qvar_eq_fac y x
             | nsub y v => qvar_eq_fac y x
             | nmul y z v => qvar_eq_fac y x
             | fadd y v => qvar_eq_fac y x
             | fsub y v => qvar_eq_fac y x
             | fmul y z v => qvar_eq_fac y x
             | qxor y v => qvar_eq_fac y x
             | slrot y => qvar_eq_fac y x
             | ndiv y z v => false
             | nmod y z v => false
             | fdiv y z => false
             | nfac y z => false
             | ncsub y z v => false
             | ncadd y z v => false
             | fcsub y z v => false
             | fcadd y z v => false
             | ncmul y z v => false
             | fndiv y z v => false
             | qinv y => false
             | call f y => qvar_eq_fac y x 
             | qif ce e1 e2 => false
             | qfor y n e => false
             | qseq e1 e2 => false
   end.

Fixpoint num_eq (f1 f2: (nat -> bool)) (n:nat) :=
   match n with 0 => true
             | S m => (eqb (f1 m) (f2 m)) && num_eq f1 f2 m
   end.

Definition factor_eq (c1 c2:factor) (size:nat) := 
   match c1 with Var x => match c2 with Var y => (x =q= y)
                                    | Num v => false
                          end
              | Num v1 => match c2 with Var y => false
                                   | Num v2 => num_eq v1 v2 size
                         end
   end.

Definition match_q_exp_array (e:qexp) (x:qvar) (i:factor) (size:nat) :=
   match e with skip => Some false
             | init y v => do ind <- get_index y @ if factor_eq i ind size then ret (qvar_eq_fac y x) else None
             | nadd y v => do ind <- get_index y @ if factor_eq i ind size then ret (qvar_eq_fac y x) else None
             | nsub y v => do ind <- get_index y @ if factor_eq i ind size then ret (qvar_eq_fac y x) else None
             | nmul y z v => do ind <- get_index y @ if factor_eq i ind size then ret (qvar_eq_fac y x) else None
             | fadd y v => do ind <- get_index y @ if factor_eq i ind size then ret (qvar_eq_fac y x) else None
             | fsub y v => do ind <- get_index y @ if factor_eq i ind size then ret (qvar_eq_fac y x) else None
             | fmul y z v => do ind <- get_index y @ if factor_eq i ind size then ret (qvar_eq_fac y x) else None
             | qxor y v => do ind <- get_index y @ if factor_eq i ind size then ret (qvar_eq_fac y x) else None
             | slrot y => do ind <- get_index y @ if factor_eq i ind size then ret (qvar_eq_fac y x) else None
             | ndiv y z v => Some false
             | nmod y z v => Some false
             | fdiv y z => Some false
             | nfac y z => Some false
             | ncsub y z v => Some false
             | ncadd y z v => Some false
             | fcsub y z v => Some false
             | fcadd y z v => Some false
             | ncmul y z v => Some false
             | fndiv y z v => Some false
             | qinv y => Some false
             | call f y => do ind <- get_index y @ if factor_eq i ind size then ret (qvar_eq_fac y x) else None
             | qif ce e1 e2 => Some false
             | qfor y n e => Some false
             | qseq e1 e2 => Some false
   end.

Definition is_qinv_x (e:qexp) (x:qvar) :=
   match e with qinv y => match get_var y with None => false
                        | Some y' => (y' =q= x)
                          end
              | _ => false
   end.

Definition no_forward_track (S:list qvar) (e:qexp) :=
   match e with skip => false
             | init y v => fac_in_qvars y S
             | nadd y v => fac_in_qvars y S
             | nsub y v => fac_in_qvars y S
             | nmul y z v => fac_in_qvars y S
             | fadd y v => fac_in_qvars y S
             | fsub y v => fac_in_qvars y S
             | fmul y z v => fac_in_qvars y S
             | qxor y v => fac_in_qvars y S
             | slrot y => fac_in_qvars y S
             | ndiv y z v => fac_in_qvars y S
             | nmod y z v => fac_in_qvars y S
             | fdiv y z => fac_in_qvars y S
             | nfac y z => fac_in_qvars y S
             | ncsub y z v => fac_in_qvars y S
             | ncadd y z v => fac_in_qvars y S
             | fcsub y z v => fac_in_qvars y S
             | fcadd y z v => fac_in_qvars y S
             | ncmul y z v => fac_in_qvars y S
             | fndiv y z v => fac_in_qvars y S
             | call f y => fac_in_qvars y S
             | qif ce e1 e2 => true
             | qfor y n e => true
             | qseq e1 e2 => true
             | qinv y => true
   end.

Definition get_args_in_qexp (e:qexp) :=
   match e with skip => ([]) 
             | init y v => (match get_var v with None => ([]) | Some xv => ([xv]) end)
             | nadd y v => (match get_var v with None => ([]) | Some xv => ([xv]) end)
             | nsub y v => (match get_var v with None => ([]) | Some xv => ([xv]) end)
             | nmul y z v => (match get_var v with None => 
                                 match get_var z with None => ([])
                                              | Some zv => ([zv])
                                 end
                             | Some xv =>
                               match get_var z with None => ([xv])
                                              | Some zv => (xv::[zv])
                                 end end)
             | fadd y v => (match get_var v with None => ([]) | Some xv => ([xv]) end)
             | fsub y v => (match get_var v with None => ([]) | Some xv => ([xv]) end)
             | fmul y z v => (match get_var v with None => 
                                 match get_var z with None => ([])
                                              | Some zv => ([zv])
                                 end
                             | Some xv =>
                               match get_var z with None => ([xv])
                                              | Some zv => (xv::[zv])
                                 end end)
             | qxor y v => (match get_var v with None => ([]) | Some xv => ([xv]) end)
             | slrot y => ([])
             | ndiv y z v => (match get_var v with None => 
                                 match get_var z with None => ([])
                                              | Some zv => ([zv])
                                 end
                             | Some xv =>
                               match get_var z with None => ([xv])
                                              | Some zv => (xv::[zv])
                                 end end)
             | nmod y z v => (match get_var v with None => 
                                 match get_var z with None => ([])
                                              | Some zv => ([zv])
                                 end
                             | Some xv =>
                               match get_var z with None => ([xv])
                                              | Some zv => (xv::[zv])
                                 end end)
             | fdiv y v =>  (match get_var v with None => ([]) | Some xv => ([xv]) end)
             | nfac y v => (match get_var v with None => ([]) | Some xv => ([xv]) end)
             | ncsub y z v => (match get_var v with None => 
                                 match get_var z with None => ([])
                                              | Some zv => ([zv])
                                 end
                             | Some xv =>
                               match get_var z with None => ([xv])
                                              | Some zv => (xv::[zv])
                                 end end)
             | ncadd y z v => (match get_var v with None => 
                                 match get_var z with None => ([])
                                              | Some zv => ([zv])
                                 end
                             | Some xv =>
                               match get_var z with None => ([xv])
                                              | Some zv => (xv::[zv])
                                 end end)
             | fcsub y z v => (match get_var v with None => 
                                 match get_var z with None => ([])
                                              | Some zv => ([zv])
                                 end
                             | Some xv =>
                               match get_var z with None => ([xv])
                                              | Some zv => (xv::[zv])
                                 end end)
             | fcadd y z v => (match get_var v with None => 
                                 match get_var z with None => ([])
                                              | Some zv => ([zv])
                                 end
                             | Some xv =>
                               match get_var z with None => ([xv])
                                              | Some zv => (xv::[zv])
                                 end end)
             | ncmul y z v => (match get_var v with None => 
                                 match get_var z with None => ([])
                                              | Some zv => ([zv])
                                 end
                             | Some xv =>
                               match get_var z with None => ([xv])
                                              | Some zv => (xv::[zv])
                                 end end)
             | fndiv y z v => (match get_var v with None => 
                                 match get_var z with None => ([])
                                              | Some zv => ([zv])
                                 end
                             | Some xv =>
                               match get_var z with None => ([xv])
                                              | Some zv => (xv::[zv])
                                 end end)
             | call f y => ([])
             | qif ce e1 e2 => ([])
             | qfor y n e => ([])
             | qseq e1 e2 => ([])
             | qinv y => ([])
   end.


Fixpoint forward_tracks (l:list qexp) (S:list qvar) :=
    match l with [] => true
           | (x::xl) => if no_forward_track S x then forward_tracks xl S else false
    end.

Fixpoint back_track_inv_nor (l:list qexp) (y:qvar) (al:list qexp) (n:nat) :=
    match l with [] => None
              | (e::xl) => if match_q_exp e y then (* find the matched qinv expression for y to uncompute. *)
                             if n =? 0 then (* if it is the right number. The number indicates the number of nested qinv for y. *)
                               if forward_tracks al (get_args_in_qexp e) then Some (e,xl) else None
                             else back_track_inv_nor xl y (al) (n-1)
                           else if is_qinv_x e y then 
                             back_track_inv_nor xl y (al) (n+1)
                           else back_track_inv_nor xl y (e::al) n
     end.

Fixpoint back_track_inv_array (l:list qexp) (y:qvar) (i:factor) (size:nat) (al:list qexp) (n:nat) :=
    match l with [] => None
              | (e::xl) => do re <- match_q_exp_array e y i size @
                           match re with true =>  (* find the matched qinv expression for y to uncompute. *)
                             if n =? 0 then (* if it is the right number. The number indicates the number of nested qinv for y. *)
                               if forward_tracks al (get_args_in_qexp e) then Some (e,xl) else None
                             else back_track_inv_array xl y i size (al) (n-1)
                      | false =>
                            if is_qinv_x e y then 
                             back_track_inv_array xl y i size (al) (n+1)
                           else back_track_inv_array xl y i size (e::al) n
                          end
     end.

Fixpoint well_formed_inv (l:list qexp) (e:qexp) (size:nat) :=
   match e with skip => Some l
             | init y v => Some ((init y v)::l)
             | nadd y v => Some ((nadd y v)::l)
             | nsub y v => Some ((nsub y v)::l)
             | nmul y z v => Some ((nmul y z v)::l)
             | fadd y v => Some ((fadd y v)::l)
             | fsub y v => Some ((fsub y v)::l)
             | fmul y z v => Some ((fmul y z v)::l)
             | qxor y v => Some ((qxor y v)::l)
             | slrot y => Some ((slrot y)::l)
             | ndiv y z v => Some ((ndiv y z v)::l)
             | nmod y z v => Some ((nmod y z v )::l)
             | fdiv y z => Some ((fdiv y z)::l)
             | nfac y z => Some ((nfac y z)::l)
             | ncsub y z v => Some ((ncsub y z v)::l)
             | ncadd y z v => Some ((ncadd y z v)::l)
             | fcsub y z v => Some ((fcsub y z v)::l)
             | fcadd y z v => Some ((fcadd y z v)::l)
             | ncmul y z v => Some ((ncmul y z v)::l)
             | fndiv y z v => Some ((fndiv y z v)::l)
             | call f y => Some ((call f y)::l)
             | qif ce e1 e2 => do re1 <- well_formed_inv ([]) e1 size @
                                 do re2 <- well_formed_inv ([]) e2 size @ Some ([])
             | qfor y n e => do re1 <- well_formed_inv ([]) e size @ ret ([])
             | qseq e1 e2 => do re1 <- well_formed_inv l e1 size @ well_formed_inv re1 e2 size 
             | qinv y => match y with Index y' i => 
                          do re <- back_track_inv_array l y' i size ([]) 0 @ Some ((qinv y)::l)
                            | Nor y' => do yv <- get_var (Nor y') @
                                  do re <- back_track_inv_nor l yv ([]) 0 @ Some ((qinv y)::l)
                         end
   end.

(*The semantics of QLLVM. *)
Module Store := FMapList.Make QvarNatType.
Module StoreFacts := FMapFacts.Facts (Store).
Definition store : Type := Store.t (list (nat -> bool)).
Definition empty_store := @Store.empty (list (nat -> bool)).

Inductive value {A:Type} := Value (x:A) | Error.

Definition sem_factor (size:nat) (r:store) (b:btype) (fc:factor) := 
   match fc with Var x => do vals <- (Store.find (x,0) r) @ (hd_error vals)
            | Num n => match b with Bl => Some ( (cut_n n 1))
                                 | Nat => Some (  (cut_n n size))
                                 | FixedP => Some (fbrev size (cut_n n size))
                       end
   end.

Definition sem_cfac (smap:qvar -> nat) (size:nat) (store:store) (b:btype) (fc:cfac)
 : option (@value (nat -> bool)) :=
    match fc with Index x n => do v <- (sem_factor size store Nat n) @
                          if (a_nat2fb v size) <? smap x then
                               do l <- Store.find (x,a_nat2fb v size) store @
                                   do val <- (hd_error l) @ Some (Value val)
                          else Some Error
               | Nor x => do val <- sem_factor size store b x @ Some (Value val)
    end.

Definition sem_cexp (smap:qvar -> nat) (size:nat) (store:store) (ce:cexp) : option (@value bool) :=
           match ce with clt b x y => 
            do v1 <- (sem_cfac smap size store b x) @
            do v2 <- (sem_cfac smap size store b y) @
            match v1 with (Value v1') => 
             match v2 with (Value v2') =>
               match b with Bl => Some (Value (a_nat2fb v1' 1 <? a_nat2fb v2' 1))
                       | _ => Some (Value (a_nat2fb v1' size <? a_nat2fb v2' size))
               end
                | _ => Some Error
                 end
            | _ => Some Error
            end
          | ceq b x y => 
            do v1 <- (sem_cfac smap size store b x) @
            do v2 <- (sem_cfac smap size store b y) @
            match v1 with (Value v1') => 
             match v2 with (Value v2') =>
             match b with Bl => Some (Value (a_nat2fb v1' 1 =? a_nat2fb v2' 1))
                         | _ => Some (Value (a_nat2fb v1' size =? a_nat2fb v2' size))
             end
                | _ => Some Error
                 end
            | _ => Some Error
            end
         | iseven x =>
            do v1 <- (sem_cfac smap size store Nat x) @ 
              match v1 with Value v1' => Some (Value ((a_nat2fb v1' size) mod 2 =? 0)) 
                          | _ => Some Error
              end
          end.

Definition bv_store_sub (smap : qvar -> nat) (bv:benv) (st:store) :=
         forall x i, BEnv.In x bv -> i < smap x -> (exists v, Store.MapsTo (x,i) v st /\ length v > 0).

Definition bv_store_gt_0 (smap : qvar -> nat) (bv:benv) :=
         forall x, BEnv.In x bv -> 0 < smap x.
   

Lemma factor_progress: forall e smap size bv st t t', typ_factor bv t e = Some t' ->
        bv_store_sub smap bv st -> bv_store_gt_0 smap bv
         -> (exists v, sem_factor size st t e = Some v).
Proof.
 induction e; intros; simpl in *.
 destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
 destruct t0. inv H.
 bdestruct (b =b= t). inv H.
 destruct (Store.find (elt:=list (nat -> bool)) (v, 0) st) eqn:eq2.
 unfold bv_store_sub in H0. 
 unfold bv_store_gt_0 in H1.
 specialize (H0 v 0).
 assert (BEnv.In (elt:=typ) v bv).
 unfold BEnv.In,BEnv.Raw.PX.In.
 exists (TNor a t).
 apply BEnv.find_2. easy.
 apply H0 in H.
 destruct H. destruct H. destruct x. simpl in H2. easy.
 apply Store.find_1 in H.
 assert ((@pair qvar nat v O) = (@pair BEnv.key nat v O)) by easy.
 rewrite H3 in *.
 rewrite eq2 in H. inv H. exists b. simpl. easy.
 specialize (H1 v). apply H1 in H. easy. 
 unfold bv_store_sub in H0. 
 unfold bv_store_gt_0 in H1.
 specialize (H0 v 0).
 assert (BEnv.In (elt:=typ) v bv).
 unfold BEnv.In,BEnv.Raw.PX.In.
 exists (TNor a t).
 apply BEnv.find_2. easy.
 apply H0 in H.
 destruct H. destruct H.
 apply Store.find_1 in H.
 assert ((@pair qvar nat v O) = (@pair BEnv.key nat v O)) by easy.
 rewrite H3 in *.
 rewrite eq2 in H. inv H.
 apply H1. easy. inv H. inv H. inv H.
 destruct t.
 exists (cut_n n size). easy.
 exists (fbrev size (cut_n n size)). easy.
 exists (cut_n n 1). easy.
Qed.

Lemma factor_full_progress: forall e smap size bv st a t t', typ_factor_full bv a t e = Some t' ->
        bv_store_sub smap bv st -> bv_store_gt_0 smap bv
         -> (exists v, sem_factor size st t e = Some v).
Proof.
 induction e; intros; simpl in *.
 destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
 destruct t0. inv H.
 bdestruct (a =a= a0). 
 bdestruct (b =b= t). simpl in H. inv H.
 destruct (Store.find (elt:=list (nat -> bool)) (v, 0) st) eqn:eq2.
 unfold bv_store_sub in H0. 
 unfold bv_store_gt_0 in H1.
 specialize (H0 v 0).
 assert (BEnv.In (elt:=typ) v bv).
 unfold BEnv.In,BEnv.Raw.PX.In.
 exists (TNor a0 t).
 apply BEnv.find_2. easy.
 apply H0 in H.
 destruct H. destruct H. destruct x. simpl in H2. easy.
 apply Store.find_1 in H.
 assert ((@pair qvar nat v O) = (@pair BEnv.key nat v O)) by easy.
 rewrite H3 in *.
 rewrite eq2 in H. inv H. exists b. simpl. easy.
 specialize (H1 v). apply H1 in H. easy. 
 unfold bv_store_sub in H0. 
 unfold bv_store_gt_0 in H1.
 specialize (H0 v 0).
 assert (BEnv.In (elt:=typ) v bv).
 unfold BEnv.In,BEnv.Raw.PX.In.
 exists (TNor a0 t).
 apply BEnv.find_2. easy.
 apply H0 in H.
 destruct H. destruct H.
 apply Store.find_1 in H.
 assert ((@pair qvar nat v O) = (@pair BEnv.key nat v O)) by easy.
 rewrite H3 in *.
 rewrite eq2 in H. inv H.
 apply H1. easy. simpl in H. inv H. simpl in H. inv H. inv H.
 bdestruct (a =a= C). inv H.
 destruct t.
 exists (cut_n n size). easy.
 exists (fbrev size (cut_n n size)). easy.
 exists (cut_n n 1). easy.
 inv H.
Qed.

Lemma cfac_progress: forall e smap size bv st t t', type_factor bv t e = Some t' ->
        bv_store_sub smap bv st -> bv_store_gt_0 smap bv
         -> (exists v, sem_cfac smap size st t e = Some v).
Proof.
 induction e; intros; simpl in *.
 destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
 destruct t0.
 bdestruct (b =b= t).
 destruct (typ_factor_full bv C Nat v) eqn:eq2. inv H.
 destruct (sem_factor size st Nat v) eqn:eq3.
 bdestruct (a_nat2fb b size <? smap x).
 destruct (Store.find (elt:=list (nat -> bool)) (x, a_nat2fb b size) st) eqn:eq4.
 unfold bv_store_sub in H0. 
 unfold bv_store_gt_0 in H1.
 specialize (H0 x (a_nat2fb b size)).
 assert (BEnv.In (elt:=typ) x bv).
 unfold BEnv.In,BEnv.Raw.PX.In.
 exists ((TArray a t n)).
 apply BEnv.find_2. easy.
 apply H0 in H2.
 destruct H2. destruct H2.
 apply Store.find_1 in H2.
 assert ((@pair qvar nat x (a_nat2fb b size)) = (@pair BEnv.key nat x (a_nat2fb b size))) by easy.
 rewrite H4 in *.
 rewrite eq4 in H2. inv H2.
 destruct x0. simpl in H3. easy.
 simpl. exists (Value b0). easy. easy.
 unfold bv_store_sub in H0. 
 unfold bv_store_gt_0 in H1.
 specialize (H0 x (a_nat2fb b size)).
 assert (BEnv.In (elt:=typ) x bv).
 unfold BEnv.In,BEnv.Raw.PX.In.
 exists ((TArray a t n)).
 apply BEnv.find_2. easy.
 apply H0 in H2.
 destruct H2. destruct H2.
 apply Store.find_1 in H2.
 assert ((@pair qvar nat x (a_nat2fb b size)) = (@pair BEnv.key nat x (a_nat2fb b size))) by easy.
 rewrite H4 in *.
 rewrite eq4 in H2. inv H2. easy. exists Error. easy. 
 apply factor_full_progress with (smap := smap) (size:=size) (st:=st) in eq2; try easy.
 destruct eq2. rewrite H in *. easy. inv H. inv H. inv H. inv H.
 apply factor_progress with (smap := smap) (size:=size) (st:=st)  in H; try easy.
 destruct H. rewrite H. exists (Value x). easy.
Qed.

Lemma cexp_progress : forall e smap size bv st t, type_cexp bv e = Some t ->
        bv_store_sub smap bv st -> bv_store_gt_0 smap bv
       ->  (exists v, sem_cexp smap size st e = Some v).
Proof.
  induction e; intros; simpl in *.
  destruct (type_factor bv t x) eqn:eq1.
  destruct (type_factor bv t y) eqn:eq2.
  apply cfac_progress with (smap := smap) (size:=size) (st:=st) in eq1; try easy.
  apply cfac_progress with (smap := smap) (size:=size) (st:=st) in eq2; try easy.
  destruct eq1. destruct eq2.
  rewrite H2. rewrite H3.
  destruct x0. destruct x1. destruct t.
  exists ((Value (a_nat2fb x0 size <? a_nat2fb x1 size))). easy.
  exists ((Value (a_nat2fb x0 size <? a_nat2fb x1 size))). easy.
  exists ((Value (Nat.b2n (x0 0) + 0 + 0 <? Nat.b2n (x1 0) + 0 + 0))). easy.
  exists Error. easy. exists Error. easy. inv H. inv H.
  destruct (type_factor bv t x) eqn:eq1.
  destruct (type_factor bv t y) eqn:eq2.
  apply cfac_progress with (smap := smap) (size:=size) (st:=st) in eq1; try easy.
  apply cfac_progress with (smap := smap) (size:=size) (st:=st) in eq2; try easy.
  destruct eq1. destruct eq2.
  rewrite H2. rewrite H3.
  destruct x0. destruct x1. destruct t.
  exists ((Value (a_nat2fb x0 size =? a_nat2fb x1 size))). easy.
  exists ((Value (a_nat2fb x0 size =? a_nat2fb x1 size))). easy.
  exists ((Value (Nat.b2n (x0 0) + 0 + 0 =? Nat.b2n (x1 0) + 0 + 0))). easy.
  exists Error. easy. exists Error. easy. inv H. inv H.
  destruct (type_factor bv Nat x) eqn:eq1.
  destruct p. destruct a. destruct b. inv H.
  apply cfac_progress with (smap := smap) (size:=size) (st:=st) in eq1; try easy.
  destruct eq1. rewrite H. destruct x0.
  exists ((Value
       (match snd (Nat.divmod (a_nat2fb x0 size) 1 0 1) with
        | 0 => 1
        | S _ => 0
        end =? 0))). easy.
  exists Error. easy. inv H. inv H. inv H. inv H.
Qed.


Definition bin_xor (f1 f2:nat -> bool) (size:nat) :=
  cut_n (fun x => xorb (f1 x) (f2 x)) size.

Definition sub_def (f1 f2:nat -> bool) (size:nat) :=
         if a_nat2fb f1 size <? a_nat2fb f2 size then (a_nat2fb f1 size + 2^size - a_nat2fb f2 size) mod 2^size
                  else (a_nat2fb f1 size + a_nat2fb f2 size) mod 2^size.


Fixpoint init_store_n (r:store) (x:qvar) (n:nat) : store :=
   match n with 0 => r
          | S m => Store.add (x,m) ([(nat2fb 0)]) (init_store_n r x m)
   end.

Definition get_type_num (t:typ) :=
   match t with TArray x y n => n
           | TNor x y => 1
   end.


Fixpoint init_store (r:store) (l:list (typ * var)) : option store  :=
   match l with [] => Some r
             | ((t,x)::xl) => if get_type_num t =? 0 then None else 
                   do new_store <- init_store r xl @
                             ret (init_store_n new_store (L x) (get_type_num t))
   end.

Fixpoint gen_smap_l (l:list (typ * var)) (smap: qvar -> nat)  :=
  match l with [] => smap
      | ((t,x)::xl) => match gen_smap_l xl smap with new_map => 
                      (qupdate new_map (L x) (get_type_num t)) end
  end.

Lemma init_store_gt_0 : forall l r r', init_store r l = Some r' -> 
           (forall t x, In (t,x) l -> 0 < get_type_num t).
Proof.
 induction l; intros; simpl in *.
 inv H0.
 destruct H0.
 destruct a. inv H0.
 bdestruct (get_type_num t =? 0). inv H. lia.
 destruct a.
 bdestruct (get_type_num t0 =? 0). inv H.
 destruct (init_store r l) eqn:eq1. inv H.
 specialize (IHl r s eq1). apply IHl with (x := x). easy. inv H.
Qed.

Lemma store_find_add : forall k v m,
        @Store.find ((list (nat -> bool))) k (Store.add k v m) = Some v.
Proof.
      intros.
      apply Store.find_1.
      apply Store.add_1.
      easy.
Qed.

Lemma store_mapsto_add1 : forall k v1 v2 s,
        @Store.MapsTo ((list (nat -> bool))) k v1 (Store.add k v2 s) -> v1 = v2.
Proof.
      intros.
      apply Store.find_1 in H.
      rewrite store_find_add in H.
      inversion H.
      reflexivity.
Qed.

Lemma init_store_n_0 : forall n i r x, i < n -> Store.MapsTo (x,i) ([nat2fb 0]) (init_store_n r x n).
Proof.
 induction n; intros; simpl in *. lia.
 bdestruct (i =? n). subst.
 apply Store.add_1. easy.
 apply Store.add_2. intros R. inv R. lia.
 apply IHn. lia.
Qed.

Lemma init_store_n_neq : forall n i r x y v, x <> y -> Store.MapsTo (x,i) v r ->
          Store.MapsTo (x,i) v (init_store_n r y n).
Proof.
 induction n; intros; simpl in *. easy.
 apply Store.add_2. intros R. inv R. easy.
 apply IHn. easy. easy.
Qed.

Lemma init_store_bv_sub : forall l r r' bv bv' smap smap', init_store r l = Some r' -> 
    gen_env l bv = Some bv' -> gen_smap_l l smap = smap' -> bv_store_sub smap bv r ->
            bv_store_sub smap' bv' r'.
Proof.
 induction l; intros; simpl in *.
 inv H. inv H0. easy.
 destruct a.
 bdestruct (get_type_num t =? 0). inv H.
 destruct (gen_env l bv) eqn:eq1.
 assert (no_zero t = true).
 unfold no_zero,get_type_num in *.
 destruct t. bdestruct (n =? 0). lia. easy. easy.
 rewrite H4 in *.
 destruct (init_store r l) eqn:eq2.
 specialize (IHl r s bv b smap (gen_smap_l l smap) eq2 eq1).
 assert (gen_smap_l l smap = gen_smap_l l smap ) by easy.
 specialize (IHl H5 H2).
 inv H. inv H0.
 unfold bv_store_sub in *.
 intros.
 bdestruct (x =q= (L v)). subst.
 exists ([nat2fb 0]).
 split. apply init_store_n_0.
 rewrite qupdate_index_eq in H0. lia.
 simpl. lia.
 assert (BEnv.In x b).
 unfold BEnv.In,BEnv.Raw.PX.In in *.
 destruct H.
 apply BEnv.add_3 in H.
 exists x0. easy. intros R. subst. easy. 
 rewrite qupdate_index_neq in H0.
 specialize (IHl x i H6 H0).
 destruct IHl. destruct H7.
 exists x0. split.
 apply init_store_n_neq. easy. easy. easy.
 intros R. rewrite R in *. easy.
 inv H.
 destruct (init_store r l) eqn:eq2. inv H0. inv H0.
Qed.

Definition eval_var (smap : qvar -> nat) (size:nat) (r:store) (x:cfac) :=
   match x with Index x n => do v <- (sem_factor size r Nat n) @
                  if a_nat2fb v size <? smap x then
                    ret (Value (x,a_nat2fb v size)) else ret Error
              | Nor (Var x) => Some (Value (x,0))
              | Nor (Num x) => None
   end.

Definition l_rotate (f:nat -> bool) (n:nat) := fun i => f ((i + n - 1) mod n).

Inductive sem_qexp (smap:qvar -> nat) (fv:fenv) (bv:benv) (size:nat) : store -> qexp -> @value store -> Prop :=
   sem_qexp_skip : forall r, sem_qexp smap fv bv size r skip (Value r)
 | sem_qexp_init_error_1 : forall r x v,
           eval_var smap size r x = Some Error ->
            sem_qexp smap fv bv size r (init x v) Error
 | sem_qexp_init_error_2 : forall r t x v xn,
           eval_var smap size r x = Some (Value xn) ->
           BEnv.MapsTo (fst xn) t bv ->
           sem_cfac smap size r (get_ct t) v = Some Error ->  
            sem_qexp smap fv bv size r (init x v) Error
 | sem_qexp_init_some : forall r t x v xn x_val xl val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           BEnv.MapsTo (fst xn) t bv ->
           sem_cfac smap size r (get_ct t) v = Some (Value val) ->  
            sem_qexp smap fv bv size r (init x v) 
                (Value (Store.add xn ((bin_xor x_val val (if (get_ct t) =b= Bl then 1 else size))::(x_val::xl)) r))
 | sem_qexp_nadd_error_1 : forall r x y, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (nadd x y) Error
 | sem_qexp_nadd_error_2 : forall r x v,
           sem_cfac smap size r Nat v = Some Error ->  
            sem_qexp smap fv bv size r (nadd x v) Error
 | sem_qexp_nadd_some : forall r x v xn x_val xl val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r Nat v = Some (Value val) ->  
            sem_qexp smap fv bv size r (nadd x v) 
                (Value (Store.add xn ((sumfb false x_val val)::(x_val::xl)) r))
 | sem_qexp_nsub_error_1 : forall r x y, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (nsub x y) Error
 | sem_qexp_nsub_error_2 : forall r x v,
           sem_cfac smap size r Nat v = Some Error ->  
            sem_qexp smap fv bv size r (nsub x v) Error
 | sem_qexp_nsub_some : forall r x v xn x_val xl val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r Nat v = Some (Value val) ->  
            sem_qexp smap fv bv size r (nsub x v) 
                (Value (Store.add xn ((sumfb true x_val (negatem size val))::(x_val::xl)) r))

 | sem_qexp_nmul_error_1 : forall r x y z, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (nmul x y z) Error
 | sem_qexp_nmul_error_2 : forall r x y z,
           sem_cfac smap size r Nat y = Some Error ->  
            sem_qexp smap fv bv size r (nmul x y z) Error
 | sem_qexp_nmul_error_3 : forall r x y z,
           sem_cfac smap size r Nat z = Some Error ->  
            sem_qexp smap fv bv size r (nmul x y z) Error
 | sem_qexp_nmul_some : forall r x y z xn x_val xl y_val z_val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r Nat y = Some (Value y_val) -> 
           sem_cfac smap size r Nat z = Some (Value z_val) ->  
            sem_qexp smap fv bv size r (nmul x y z) 
                (Value (Store.add xn ((bin_xor x_val
                 (nat2fb (((a_nat2fb y_val size) * (a_nat2fb z_val size)) mod 2^size)) size)::(x_val::xl)) r))
 
 | sem_qexp_fadd_error_1 : forall r x y, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (fadd x y) Error
 | sem_qexp_fadd_error_2 : forall r x v,
           sem_cfac smap size r Nat v = Some Error ->  
            sem_qexp smap fv bv size r (fadd x v) Error
 | sem_qexp_fadd_some : forall r x v xn x_val xl val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r FixedP v = Some (Value val) ->  
            sem_qexp smap fv bv size r (fadd x v) 
                (Value (Store.add xn ((fbrev size (sumfb false (fbrev size x_val) val))::(x_val::xl)) r))

 | sem_qexp_fsub_error_1 : forall r x y, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (fsub x y) Error
 | sem_qexp_fsub_error_2 : forall r x v,
           sem_cfac smap size r Nat v = Some Error ->  
            sem_qexp smap fv bv size r (fsub x v) Error
 | sem_qexp_fsub_some : forall r x v xn x_val xl val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r FixedP v = Some (Value val) ->  
            sem_qexp smap fv bv size r (fsub x v) 
                (Value (Store.add xn ((fbrev size (sumfb true (fbrev size x_val) (negatem size val)))::(x_val::xl)) r))

 | sem_qexp_fmul_error_1 : forall r x y z, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (fmul x y z) Error
 | sem_qexp_fmul_error_2 : forall r x y z,
           sem_cfac smap size r FixedP y = Some Error ->  
            sem_qexp smap fv bv size r (fmul x y z) Error
 | sem_qexp_fmul_error_3 : forall r x y z,
           sem_cfac smap size r FixedP z = Some Error ->  
            sem_qexp smap fv bv size r (fmul x y z) Error
 | sem_qexp_fmul_some : forall r x y z xn x_val xl y_val z_val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r FixedP y = Some (Value y_val) -> 
           sem_cfac smap size r FixedP z = Some (Value z_val) ->  
            sem_qexp smap fv bv size r (fmul x y z) 
                (Value (Store.add xn ((fbrev size (bin_xor (fbrev size x_val)
                 (nat2fb (((a_nat2fb y_val size) * (a_nat2fb z_val size)) / 2^size)) size))::(x_val::xl)) r))

 | sem_qexp_xor_error_1 : forall r x v,
           eval_var smap size r x = Some Error ->
            sem_qexp smap fv bv size r (qxor x v) Error
 | sem_qexp_xor_error_2 : forall r t x v xn,
           eval_var smap size r x = Some (Value xn) ->
           BEnv.MapsTo (fst xn) t bv ->
           sem_cfac smap size r (get_ct t) v = Some Error ->  
            sem_qexp smap fv bv size r (qxor x v) Error
 | sem_qexp_xor_some : forall r t x v xn x_val xl val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           BEnv.MapsTo (fst xn) t bv ->
           sem_cfac smap size r (get_ct t) v = Some (Value val) ->  
            sem_qexp smap fv bv size r (qxor x v) 
                (Value (Store.add xn ((bin_xor x_val val (if (get_ct t) =b= Bl then 1 else size))::(x_val::xl)) r))

 | sem_qexp_lrot_error : forall r x,
           eval_var smap size r x = Some Error ->
            sem_qexp smap fv bv size r (slrot x) Error

 | sem_qexp_lrot_some : forall r t x xn x_val xl,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           BEnv.MapsTo (fst xn) t bv ->
            sem_qexp smap fv bv size r (slrot x) 
                (Value (Store.add xn ((l_rotate x_val (if (get_ct t) =b= Bl then 1 else size))::(x_val::xl)) r))


 | sem_qexp_nfac_error_1 : forall r x y, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (nfac x y) Error
 | sem_qexp_nfac_error_2 : forall r x v,
           sem_cfac smap size r Nat v = Some Error ->  
            sem_qexp smap fv bv size r (nfac x v) Error
 | sem_qexp_nfac_some : forall r x v xn x_val xl val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r Nat v = Some (Value val) ->  
            sem_qexp smap fv bv size r (nfac x v) 
                (Value (Store.add xn ((nat2fb (fact (a_nat2fb val size) mod 2^size))::(x_val::xl)) r))

 | sem_qexp_ndiv_error_1 : forall r x y z, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (ndiv x y z) Error
 | sem_qexp_ndiv_error_2 : forall r x y z,
           sem_cfac smap size r Nat y = Some Error ->  
            sem_qexp smap fv bv size r (ndiv x y z) Error
 | sem_qexp_ndiv_error_3 : forall r x y z,
           sem_cfac smap size r Nat z = Some Error ->  
            sem_qexp smap fv bv size r (ndiv x y z) Error
 | sem_qexp_ndiv_error_4 : forall r x y z z_val,
           sem_cfac smap size r Nat z = Some (Value z_val) ->  
           (a_nat2fb z_val size) = 0 ->
            sem_qexp smap fv bv size r (ndiv x y z) Error
 | sem_qexp_ndiv_some : forall r x y z xn x_val xl y_val z_val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r Nat y = Some (Value y_val) -> 
           sem_cfac smap size r Nat z = Some (Value z_val) ->  
           (a_nat2fb z_val size) <> 0 ->
            sem_qexp smap fv bv size r (ndiv x y z) 
                (Value (Store.add xn ((nat2fb (((a_nat2fb y_val size) / (a_nat2fb z_val size))))::(x_val::xl)) r))

 | sem_qexp_nmod_error_1 : forall r x y z, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (nmod x y z) Error
 | sem_qexp_nmod_error_2 : forall r x y z,
           sem_cfac smap size r Nat y = Some Error ->  
            sem_qexp smap fv bv size r (nmod x y z) Error
 | sem_qexp_nmod_error_3 : forall r x y z,
           sem_cfac smap size r Nat z = Some Error ->  
            sem_qexp smap fv bv size r (nmod x y z) Error
 | sem_qexp_nmod_error_4 : forall r x y z z_val,
           sem_cfac smap size r Nat z = Some (Value z_val) ->  
           (a_nat2fb z_val size) = 0 ->
            sem_qexp smap fv bv size r (nmod x y z) Error
 | sem_qexp_nmod_some : forall r x y z xn x_val xl y_val z_val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r Nat y = Some (Value y_val) -> 
           sem_cfac smap size r Nat z = Some (Value z_val) ->  
           (a_nat2fb z_val size) <> 0 ->
            sem_qexp smap fv bv size r (nmod x y z) 
                (Value (Store.add xn ((nat2fb (((a_nat2fb y_val size) mod (a_nat2fb z_val size))))::(x_val::xl)) r))

 | sem_qexp_ncadd_error_1 : forall r x y z, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (ncadd x y z) Error
 | sem_qexp_ncadd_error_2 : forall r x y z,
           sem_cfac smap size r Nat y = Some Error ->  
            sem_qexp smap fv bv size r (ncadd x y z) Error
 | sem_qexp_ncadd_error_3 : forall r x y z,
           sem_cfac smap size r Nat z = Some Error ->  
            sem_qexp smap fv bv size r (ncadd x y z) Error
 | sem_qexp_ncadd_some : forall r x y z xn x_val xl y_val z_val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r Nat y = Some (Value y_val) -> 
           sem_cfac smap size r Nat z = Some (Value z_val) ->  
            sem_qexp smap fv bv size r (ncadd x y z) 
                (Value (Store.add xn ((nat2fb (((a_nat2fb y_val size) + (a_nat2fb z_val size))))::(x_val::xl)) r))

 | sem_qexp_ncsub_error_1 : forall r x y z, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (ncsub x y z) Error
 | sem_qexp_ncsub_error_2 : forall r x y z,
           sem_cfac smap size r Nat y = Some Error ->  
            sem_qexp smap fv bv size r (ncsub x y z) Error
 | sem_qexp_ncsub_error_3 : forall r x y z,
           sem_cfac smap size r Nat z = Some Error ->  
            sem_qexp smap fv bv size r (ncsub x y z) Error
 | sem_qexp_ncsub_some : forall r x y z xn x_val xl y_val z_val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r Nat y = Some (Value y_val) -> 
           sem_cfac smap size r Nat z = Some (Value z_val) ->  
            sem_qexp smap fv bv size r (ncsub x y z) 
                (Value (Store.add xn ((nat2fb (((a_nat2fb y_val size) - (a_nat2fb z_val size))))::(x_val::xl)) r))

 | sem_qexp_ncmul_error_1 : forall r x y z, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (ncmul x y z) Error
 | sem_qexp_ncmul_error_2 : forall r x y z,
           sem_cfac smap size r Nat y = Some Error ->  
            sem_qexp smap fv bv size r (ncmul x y z) Error
 | sem_qexp_ncmul_error_3 : forall r x y z,
           sem_cfac smap size r Nat z = Some Error ->  
            sem_qexp smap fv bv size r (ncmul x y z) Error
 | sem_qexp_ncmul_some : forall r x y z xn x_val xl y_val z_val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r Nat y = Some (Value y_val) -> 
           sem_cfac smap size r Nat z = Some (Value z_val) ->  
            sem_qexp smap fv bv size r (ncmul x y z) 
                (Value (Store.add xn ((nat2fb (((a_nat2fb y_val size) * (a_nat2fb z_val size))))::(x_val::xl)) r))

 | sem_qexp_fcadd_error_1 : forall r x y z, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (fcadd x y z) Error
 | sem_qexp_fcadd_error_2 : forall r x y z,
           sem_cfac smap size r FixedP y = Some Error ->  
            sem_qexp smap fv bv size r (fcadd x y z) Error
 | sem_qexp_fcadd_error_3 : forall r x y z,
           sem_cfac smap size r FixedP z = Some Error ->  
            sem_qexp smap fv bv size r (fcadd x y z) Error
 | sem_qexp_fcadd_some : forall r x y z xn x_val xl y_val z_val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r FixedP y = Some (Value y_val) -> 
           sem_cfac smap size r FixedP z = Some (Value z_val) ->  
            sem_qexp smap fv bv size r (fcadd x y z) 
                (Value (Store.add xn 
                          ((fbrev size (nat2fb (((a_nat2fb y_val size) + (a_nat2fb z_val size)))))::(x_val::xl)) r))


 | sem_qexp_fcsub_error_1 : forall r x y z, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (fcsub x y z) Error
 | sem_qexp_fcsub_error_2 : forall r x y z,
           sem_cfac smap size r FixedP y = Some Error ->  
            sem_qexp smap fv bv size r (fcsub x y z) Error
 | sem_qexp_fcsub_error_3 : forall r x y z,
           sem_cfac smap size r FixedP z = Some Error ->  
            sem_qexp smap fv bv size r (fcsub x y z) Error
 | sem_qexp_fcsub_some : forall r x y z xn x_val xl y_val z_val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r FixedP y = Some (Value y_val) -> 
           sem_cfac smap size r FixedP z = Some (Value z_val) ->  
            sem_qexp smap fv bv size r (fcsub x y z) 
                (Value (Store.add xn ((fbrev size (nat2fb (((a_nat2fb y_val size) - (a_nat2fb z_val size)))))::(x_val::xl)) r))


 | sem_qexp_fdiv_error_1 : forall r x y, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (fdiv x y) Error
 | sem_qexp_fdiv_error_2 : forall r x v,
           sem_cfac smap size r Nat v = Some Error ->  
            sem_qexp smap fv bv size r (fdiv x v) Error
 | sem_qexp_fdiv_error_3 : forall r x v val,
           sem_cfac smap size r Nat v = Some (Value val)->  
           a_nat2fb val size = 0 ->
            sem_qexp smap fv bv size r (fdiv x v) Error
 | sem_qexp_fdiv_some : forall r x v xn x_val xl val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r Nat v = Some (Value val) ->  
           a_nat2fb val size <> 0 ->
            sem_qexp smap fv bv size r (fdiv x v) 
                (Value (Store.add xn ((nat2fb (((a_nat2fb (fbrev size x_val) size)) / (a_nat2fb val size)))::(x_val::xl)) r))

 | sem_qexp_fndiv_error_1 : forall r x y z, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (fndiv x y z) Error
 | sem_qexp_fndiv_error_2 : forall r x y z,
           sem_cfac smap size r FixedP y = Some Error ->  
            sem_qexp smap fv bv size r (fndiv x y z) Error
 | sem_qexp_fndiv_error_3 : forall r x y z,
           sem_cfac smap size r FixedP z = Some Error ->  
            sem_qexp smap fv bv size r (fndiv x y z) Error
 | sem_qexp_fndiv_error_4 : forall r x y z z_val,
           sem_cfac smap size r FixedP z = Some (Value z_val) ->
           (a_nat2fb z_val size) = 0 ->
            sem_qexp smap fv bv size r (fndiv x y z) Error
 | sem_qexp_fndiv_some : forall r x y z xn x_val xl y_val z_val,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           sem_cfac smap size r FixedP y = Some (Value y_val) -> 
           sem_cfac smap size r FixedP z = Some (Value z_val) ->  
           (a_nat2fb z_val size) <> 0 ->
            sem_qexp smap fv bv size r (fndiv x y z) 
                (Value (Store.add xn
                  ((fbrev size (nat2fb ((((a_nat2fb y_val size) * 2^size) / (a_nat2fb z_val size)))))::(x_val::xl)) r))


 | sem_qexp_qinv_error : forall r x,
           eval_var smap size r x = Some Error ->
            sem_qexp smap fv bv size r (qinv x) Error

 | sem_qexp_qinv_some : forall r x xn x_val xl,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
            sem_qexp smap fv bv size r (qinv x)  (Value (Store.add xn xl r))

 | sem_qexp_if_error : forall r ce e1 e2, sem_cexp smap size r ce = Some Error ->
                    sem_qexp smap fv bv size r (qif ce e1 e2) Error
 | sem_qexp_if_t : forall r ce e1 e2 r1, sem_cexp smap size r ce = Some (Value true) ->
                    sem_qexp smap fv bv size r e1 r1 -> 
                    sem_qexp smap fv bv size r (qif ce e1 e2) r1
 | sem_qexp_if_f : forall r ce e1 e2 r1, sem_cexp smap size r ce = Some (Value false) ->
                    sem_qexp smap fv bv size r e2 r1 -> 
                    sem_qexp smap fv bv size r (qif ce e1 e2) r1

 | sem_qexp_call_error_1 : forall l e fbv rx f x r r' r'',
         FEnv.MapsTo f (l,e,fbv,rx) fv -> 
         init_store r l = Some r' ->
         sem_qexp (gen_smap_l l smap) fv fbv size r' e (Value r'') ->
         eval_var (gen_smap_l l smap) size r'' rx = Some Error ->
         sem_qexp smap fv bv size r (call f x) Error

 | sem_qexp_call_error_2 : forall f x r,
         eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (call f x) Error

 | sem_qexp_call_error_3 : forall l e fbv rx f x r r' , FEnv.MapsTo f (l,e,fbv,rx) fv -> 
         init_store r l = Some r' ->
         sem_qexp (gen_smap_l l smap) fv fbv size r' e Error ->
         sem_qexp smap fv bv size r (call f x) Error

 | sem_qexp_call_some : forall l e fbv rx rxn f x xn r r' r'' rxv rxl xl, FEnv.MapsTo f (l,e,fbv,rx) fv -> 
         init_store r l = Some r' ->
         eval_var smap size r x = Some (Value xn) ->
         sem_qexp (gen_smap_l l smap) fv fbv size r' e (Value r'') ->
         eval_var (gen_smap_l l smap) size r'' rx = Some (Value rxn) ->
         Store.MapsTo rxn (rxv::rxl) r'' ->
         Store.MapsTo xn xl r ->
         sem_qexp smap fv bv size r (call f x) (Value (Store.add xn (rxv::xl) r))

 | sem_qexp_qseq_error : forall r e1 e2,
                sem_qexp smap fv bv size r e1 Error ->
                  sem_qexp smap fv bv size r (qseq e1 e2) Error

 | sem_qexp_qseq_some : forall r e1 e2 r' r'',
                sem_qexp smap fv bv size r e1 (Value r') ->
                sem_qexp smap fv bv size r' e2 r'' ->
                  sem_qexp smap fv bv size r (qseq e1 e2) r''

 | sem_qexp_for_error_1 : forall r x n e,
                sem_cfac smap size r Nat n = Some Error ->
                           sem_qexp smap fv bv size r (qfor x n e) Error

 | sem_qexp_for_error_2 : forall r x n e nv xl,
      sem_cfac smap size r Nat n = Some (Value nv) ->
       Store.MapsTo (L x,0) xl r ->
        sem_for_exp smap fv bv size (Store.add (L x,0) ((nat2fb 0)::xl) r) e x (a_nat2fb nv size) Error ->
                           sem_qexp smap fv bv size r (qfor x n e) Error

 | sem_qexp_for_some : forall r x n e xl nv nv' xl' r',
      sem_cfac smap size r Nat n = Some (Value nv) ->
       Store.MapsTo (L x,0) xl r ->
        sem_for_exp smap fv bv size (Store.add (L x,0) ((nat2fb 0)::xl) r) e x (a_nat2fb nv size) (Value r') ->
        Store.MapsTo (L x,0) (nv'::xl') r' ->
                           sem_qexp smap fv bv size r (qfor x n e) (Value (Store.add (L x,0) xl' r'))

with sem_for_exp (smap: qvar -> nat) (fv:fenv) (bv:benv) (size:nat): store -> qexp -> var -> nat -> @value store -> Prop :=
  | sem_for_empty : forall r x e, sem_for_exp smap fv bv size r e x 0 (Value r)
  | sem_for_many_error_1 : forall r x m e,
    sem_qexp smap fv bv size r e Error  ->
     sem_for_exp smap fv bv size r e x (S m) Error
  | sem_for_many_error_2 : forall r x m e r' nv xl,
    sem_qexp smap fv bv size r e (Value r')  ->
    Store.MapsTo (L x,0) (nv::xl) r' ->
     sem_for_exp smap fv bv size (Store.add (L x,0) ((nat2fb (S (a_nat2fb nv size)))::xl) r') e x m Error ->
       sem_for_exp smap fv bv size r e x (S m) Error
  | sem_for_many : forall r x m e r' nv xl r'',
    sem_qexp smap fv bv size r e (Value r')  ->
    Store.MapsTo (L x,0) (nv::xl) r' ->
     sem_for_exp smap fv bv size (Store.add (L x,0) ((nat2fb (S (a_nat2fb nv size)))::xl) r') e x m (Value r'') ->
       sem_for_exp smap fv bv size r e x (S m) (Value r'').


Fixpoint check_store_g (l:list (btype * var)) (r:store) : Prop  :=
   match l with [] => True
             | ((t,x)::xl) => Store.In (G x,0) r /\ check_store_g xl r
   end.

Inductive sem_prog (fv:fenv) : prog -> (@value (nat -> bool)) -> Prop :=
    sem_main_error_1 : forall size gl fl main x l e bv rx r r',
              FEnv.MapsTo main (l,e,bv,rx) fv ->
              init_store empty_store gl = Some r ->
              init_store r l = Some r' ->
              sem_qexp (gen_smap_l l (gen_smap_l gl (fun _ => 0))) fv bv size r' e Error -> 
              sem_prog fv (size,gl,fl,main,x) Error
   | sem_main_error_2 : forall size gl fl main x l e bv rx r r' r'',
              FEnv.MapsTo main (l,e,bv,rx) fv ->
              init_store empty_store gl = Some r ->
              init_store r l = Some r' ->
              sem_qexp (gen_smap_l l (gen_smap_l gl (fun _ => 0))) fv bv size r' e (Value r'') -> 
              eval_var (gen_smap_l l (gen_smap_l gl (fun _ => 0))) size r'' rx = Some Error ->
              sem_prog fv (size,gl,fl,main,x) Error
   | sem_main_some : forall size gl fl main x l e bv rx r r' r'' rxn v vl,
              FEnv.MapsTo main (l,e,bv,rx) fv ->
              init_store empty_store gl = Some r ->
              init_store r l = Some r' ->
              sem_qexp (gen_smap_l l (gen_smap_l gl (fun _ => 0))) fv bv size r' e (Value r'') -> 
              eval_var (gen_smap_l l (gen_smap_l gl (fun _ => 0))) size r'' rx = Some (Value rxn) ->
              Store.MapsTo rxn (v::vl) r'' ->
              sem_prog fv (size,gl,fl,main,x) (Value v).

Definition well_formed_fv (fv:fenv) (r:store) (smap: qvar -> nat) :=
        forall f l e fbv rx, FEnv.MapsTo f (l,e,fbv,rx) fv ->
             (exists bv', type_qexp fv fbv e = Some bv') /\ 
              (exists r', init_store r l = Some r' /\ bv_store_sub (gen_smap_l l smap) fbv r'
                      /\ bv_store_gt_0 (gen_smap_l l smap) fbv)
             /\ (forall xn, get_var rx = Some xn -> BEnv.In xn fbv).

Lemma qexp_progress : forall e fv smap size bv bv' st inl, well_formed_fv fv st smap ->
        type_qexp fv bv e = Some bv' -> well_formed_inv ([]) e size = Some inl ->
        bv_store_sub smap bv st -> bv_store_gt_0 smap bv
       ->  (exists r', sem_qexp smap fv bv size st e r').
Proof.
  induction e; intros; simpl in *.
  destruct (get_var x) eqn:eq1.
  destruct (BEnv.find (elt:=typ) q bv) eqn:eq2.
  destruct (is_q t) eqn:eq3. inv H0.
  destruct (eval_var smap size st x) eqn:eq4.
  destruct v. destruct x0.
Admitted.

Lemma qexp_preservation : forall e fv smap size bv bv' st st' inl, well_formed_fv fv st smap ->
        type_qexp fv bv e = Some bv' -> well_formed_inv ([]) e size = Some inl ->
        bv_store_sub smap bv st -> bv_store_gt_0 smap bv -> sem_qexp smap fv bv size st e (Value st')
           -> bv_store_sub smap bv st'.
Proof.
  induction e; intros; simpl in *.
Admitted.

(*
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
              | slrot b x => match get_var x with None => []
                                             | Some xn => [xn]
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
              | slrot b x => in_scope_cfac l x
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

Definition par_eval_fc (size:nat) (bv:benv) (store:store) (b:btype) (fc:factor) := 
   match fc with Var x => do re <- bv x @ if is_qt re then None else (Store.find (x,0) store)
            | Num n => match b with Bl => Some (cut_n n 1)
                                 | Nat => Some (cut_n n size)
                                 | FixedP => Some (cut_n n size)
                       end
   end.

Definition par_eval_cfac (size:nat) (smap : qvar -> nat) (bv:benv) (store:store) (b:btype) (fc:cfac) := 
   match fc with Nor x => par_eval_fc size bv store b x
        | Ptr x n => do v <- par_eval_fc size bv store Nat n @
                              if a_nat2fb v size <? smap (L x) then
                               (do re <- bv (L x) @ if is_qt re then None else (Store.find (L x,a_nat2fb v size) store)) else None
   end.

Definition par_find_var (size:nat) (bv:benv) (store:store) (fc:cfac) :=
       match fc with Nor (Var x) => Some (x,0)
                  | Nor (Num x) => None
                  | Ptr x n => do val <- par_eval_fc size bv store Nat n @ Some (L x,a_nat2fb val size)
       end.

Definition get_vars (size:nat) (bv:benv) (store:store) (e:qexp) :=
   match e with skip => Some ([])
              | init b x y => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ ret (var1::var2::[])
              | nadd b x y => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ ret (var1::var2::[])
              | nsub b x y => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ ret (var1::var2::[])
              | nmul b x y z => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ 
                                   do var3 <- par_find_var size bv store z @  ret (var1::var2::var3::[])
              | fadd b x y => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ ret (var1::var2::[])

              | fsub b x y => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ ret (var1::var2::[])
              | fmul b x y z => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ 
                                   do var3 <- par_find_var size bv store z @  ret (var1::var2::var3::[])
              | qxor b x y => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ ret (var1::var2::[])
              | slrot b x => do var1 <- par_find_var size bv store x @ ret (var1::[])
              | ndiv x y z => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ 
                                   do var3 <- par_find_var size bv store z @  ret (var1::var2::var3::[])

              | nmod x y z => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ 
                                   do var3 <- par_find_var size bv store z @  ret (var1::var2::var3::[])
              | nfac x y => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ ret (var1::var2::[])
              | fdiv x y => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ ret (var1::var2::[])

              | ncsub x y z => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ 
                                   do var3 <- par_find_var size bv store z @  ret (var1::var2::var3::[])
              | ncadd x y z => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ 
                                   do var3 <- par_find_var size bv store z @  ret (var1::var2::var3::[])
              | fcsub x y z => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ 
                                   do var3 <- par_find_var size bv store z @  ret (var1::var2::var3::[])
              | fcadd x y z => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ 
                                   do var3 <- par_find_var size bv store z @  ret (var1::var2::var3::[])
              | ncmul x y z => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ 
                                   do var3 <- par_find_var size bv store z @  ret (var1::var2::var3::[])
              | fndiv x y z => do var1 <- par_find_var size bv store x @
                                  do var2 <- par_find_var size bv store y @ 
                                   do var3 <- par_find_var size bv store z @  ret (var1::var2::var3::[])

              | qinv e => None
              | call f x => do var1 <- (par_find_var size bv store x) @ ret ([var1])
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


Inductive inv_match (l:list (qvar * nat)) (size:nat) (bv:benv) (store:store) (x:qexp) : list qexp -> option (list qexp) -> Prop :=
     inv_match_empty : inv_match l size bv store x [] None
    | inv_match_many_1 : forall y yl , x = y -> inv_match l size bv store x (y::yl) (Some yl)
    | inv_match_many_2 : forall y yl l' b, x <> y -> (get_vars size bv store y) = Some l' -> intersection l l'  <> []
                                 -> inv_match l size bv store x yl b -> inv_match l size bv store x (y::yl) b.

Inductive inv_well_match_l (size:nat) (bv:benv) (store:store) : list qexp -> list qexp -> Prop :=
     inv_well_match_empty : forall el, inv_well_match_l size bv store [] el
   | inv_well_match_many_1 : forall l e xl el el', get_vars size bv store e = Some l ->
             inv_match l size bv store e el (Some el') -> 
                inv_well_match_l size bv store xl el'
   | inv_well_match_many_2 : forall x xl el, is_no_pass x ->
               inv_well_match_l size bv store xl [] -> inv_well_match_l size bv store (x::xl) el
   | inv_well_match_many_3 : forall x xl el, ~ is_no_pass x ->
               inv_well_match_l size bv store xl (x::el) -> inv_well_match_l size bv store (x::xl) el.

Definition inv_well_match (size:nat) (bv:benv) (store:store) (e:qexp) : Prop :=
    inv_well_match_l size bv store (turn_qseq_lst e) [].
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

Definition cstore : Type := Store.t ((nat -> bool)).
Definition empty_cstore := @Store.empty ((nat -> bool)).

Lemma store_mapsto_always_same {A:Type} : forall k v1 v2 s,
           @Store.MapsTo A k v1 s ->
            @Store.MapsTo A k v2 s -> 
                       v1 = v2.
Proof.
     intros.
     apply Store.find_1 in H.
     apply Store.find_1 in H0.
     rewrite H in H0.
     injection H0.
     easy.
Qed.

Definition make_value (size:nat) (b:btype) (c: option (nat -> bool)) :=
  do cv <- c @
      match b with Bl => Some (cut_n cv 1)
                | Nat => Some (cut_n cv size)
                | FixedP => Some (fbrev size (cut_n cv size))
      end.

Definition par_eval_fc (bv:benv) (size:nat) (r:cstore) (b:btype) (fc:factor) := 
   match fc with Var x => do re <- BEnv.find x bv @ if is_q re then None else make_value size b (Store.find (x,0) r)
            | Num n => make_value size b (Some n)
   end.

Definition par_eval_cfac (smap : qvar -> nat) (bv:benv) (size:nat) (r:cstore) (b:btype) (fc:cfac) := 
   match fc with Nor x => par_eval_fc bv size r b x
        | Index x n => do v <- par_eval_fc bv size r Nat n @
                              if a_nat2fb v size <? smap x then
                               (do re <- BEnv.find x bv @ if is_q re then None
                      else make_value size b (Store.find (x,a_nat2fb v size) r)) else None
   end.

Definition par_eval_cfac_check (smap : qvar -> nat) (bv:benv) (size:nat) (r:cstore) (b:btype) (fc:cfac) := 
   match fc with Nor x => do val <- par_eval_fc bv size r b x @ Some (Value val)
        | Index x n => do v <- par_eval_fc bv size r Nat n @
                              if a_nat2fb v size <? smap x then
                               (do re <- BEnv.find x bv @ if is_q re then None else 
                  do val <- make_value size b (Store.find (x,a_nat2fb v size) r) @ Some (Value val)) else Some Error
   end.

Definition par_find_var (bv:benv) (size:nat)  (r:cstore) (fc:cfac) :=
       match fc with Nor (Var x) => Some (x,0)
                  | Nor (Num x) => None
                  | Index x n => do val <- par_eval_fc bv size r Nat n @ Some (x,a_nat2fb val size)
       end.

Definition par_find_var_check (smap:qvar -> nat) (bv:benv) (size:nat)  (r:cstore) (fc:cfac) :=
       match fc with Nor (Var x) => Some (Value (x,0))
                  | Nor (Num x) => None
                  | Index x n => do val <- par_eval_fc bv size r Nat n @
                      if a_nat2fb val size <? smap x then Some (Value (x,a_nat2fb val size)) else Some Error
       end.

Definition qvar_eq (bv:benv) (size:nat)  (r:cstore) (x y: cfac) := 
        match par_find_var bv size r x with None => false
                    | Some a => match par_find_var bv size r y with None => false
                         | Some b => (a =qd= b)
                                end
        end.

Definition get_size (size:nat) (t:btype) := if t =b= Bl then 1 else size.

(* compare x <? y *)
Definition clt_circuit_two (size:nat) (f:flag) (b:btype) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (stack: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (comparator01 (get_size size b) (vmap x) (vmap y) (stack,S sn) (stack, sn))
            else rz_full_comparator (vmap x) (get_size size b) (stack, sn) (vmap y).


Definition clt_circuit_left (size:nat) (f:flag) (b:btype) (vmap:(qvar*nat) -> var)
                        (x :(qvar*nat)) (y:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (init_v (get_size size b) (temp) y;
                    comparator01 (get_size size b) (vmap x) (temp) (stack,S sn) (stack, sn);
                    init_v (get_size size b) (temp) y)
            else rz_comparator (vmap x) (get_size size b) (stack, sn) (a_nat2fb y (get_size size b)).

Definition clt_circuit_right (size:nat) (f:flag) (b:btype) (vmap:(qvar*nat) -> var)
                        (x:(nat->bool)) (y :(qvar*nat))  (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (init_v (get_size size b) (temp) x;
                    comparator01 (get_size size b) (temp) (vmap y) (stack,S sn) (stack, sn);
                    init_v (get_size size b) (temp) x)
            else Exp (init_v (get_size size b) (temp) x);;
                rz_full_comparator (temp) (get_size size b) (stack, sn)  (vmap y);;
                        Exp (init_v (get_size size b) (temp) x).


Definition gen_clt_c (smap : qvar -> nat) (vmap: (qvar*nat) -> var)  (bv:benv) (size:nat)  (f:flag)
                (r:cstore) (b:btype) (stack temp:var) (sn:nat) (x y: cfac)
                                      : option (@value (option pexp * nat * option bool)) := 
     do t1 <- type_factor bv b x @
         do t2 <- type_factor bv b y @
            if (fst t1 =a= Q) && (fst t2 =a= C) then
               match par_find_var_check smap bv (get_size size b) r x with Some (Value vx) =>
                   do t2v <- par_eval_cfac_check smap bv size r b y @
                     match t2v with Value t2v' =>
                      Some (Value (Some (clt_circuit_left size f b vmap vx t2v' stack temp sn),S sn,None))
                        | _ => Some Error
                     end
                   | None => None
                   | a => Some Error
               end
           else if (fst t1 =a= Q) && (fst t2 =a= Q) then
              do vxv <- par_find_var_check smap bv (get_size size b) r x @
                do vyv <- par_find_var_check smap bv (get_size size b) r y @
                 match vxv with Value vx => match vyv with Value vy => 
                    Some (Value (Some (clt_circuit_two size f b vmap vx vy stack sn),S sn,None))
                              | _ => Some Error
                       end
                   | _ => Some Error
                 end
           else if (fst t1 =a= C) && (fst t2 =a= Q) then
               match par_find_var_check smap bv (get_size size b) r y with Some (Value vy) =>
                   do t1v <- par_eval_cfac_check smap bv size r b x @
                    match t1v with Value t1v' =>
                      Some (Value (Some (clt_circuit_right size f b vmap t1v' vy stack temp sn),S sn,None))
                      | _ => Some Error
                    end
                   | None => None
                   | a => Some Error
               end
          else  do t1v <- par_eval_cfac_check smap bv size r b x @
                   do t2v <- par_eval_cfac_check smap bv size r b y @ 
                    match t1v with Value t1v' => match t2v with Value t2v' =>
                      Some (Value (None, sn, Some ((a_nat2fb t1v' size <? a_nat2fb t2v' size))))
                       | _ => Some Error end | _ => Some Error
                    end.

(* compare x =? y *)
Definition ceq_circuit_two (size:nat) (f:flag) (b:btype) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (stack: var) (sn:nat) :=
           (if f =fl= Classic then
                       Exp (comparator01 (get_size size b) (vmap y) (vmap x) (stack,S sn)
                                    (stack,sn); 
                        comparator01 (get_size size b) (vmap x) (vmap y) (stack,S sn)
                                    (stack,sn); X (stack,sn))
                 else rz_full_comparator (vmap x) (get_size size b) (stack,sn) (vmap y)
                      ;; rz_full_comparator (vmap y) (get_size size b) (stack,sn) (vmap x);;
                       Exp (X (stack, sn))).

Definition ceq_circuit_left (size:nat) (f:flag) (b:btype) (vmap:(qvar*nat) -> var)
                        (x :(qvar*nat)) (y:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (init_v (get_size size b) (temp) y;
                    comparator01 (get_size size b) (vmap x) (temp) (stack,S sn) (stack, sn);
                    comparator01 (get_size size b) (temp) (vmap x) (stack,S sn) (stack, sn);
                    (X (stack,sn));
                    init_v (get_size size b) (temp) y)
            else Exp (init_v (get_size size b) (temp) y);;
                 rz_comparator (vmap x) (get_size size b) (stack, sn) (a_nat2fb y (get_size size b));;
                rz_full_comparator (temp) (get_size size b) (stack, sn) (vmap x) ;;
                Exp (X (stack,sn);init_v (get_size size b) (temp) y).

Definition ceq_circuit_right (size:nat) (f:flag) (b:btype) (vmap:(qvar*nat) -> var)
                        (x:(nat->bool)) (y :(qvar*nat))  (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (init_v (get_size size b) (temp) x;
                    comparator01 (get_size size b) (temp) (vmap y) (stack,S sn) (stack, sn);
                    comparator01 (get_size size b) (vmap y) (temp) (stack,S sn) (stack, sn);
                    (X (stack,sn));
                    init_v (get_size size b) (temp) x)
            else Exp (init_v (get_size size b) (temp) x);;
                rz_full_comparator (temp) (get_size size b) (stack, sn)  (vmap y);;
                rz_comparator (vmap y) (get_size size b) (stack, sn) (a_nat2fb x (get_size size b));;
                        Exp ((X (stack,sn));init_v (get_size size b) (temp) x).


Definition gen_ceq_c (smap : qvar -> nat) (vmap: (qvar*nat) -> var)  (bv:benv) (size:nat)  (f:flag)
                (r:cstore) (b:btype) (stack temp:var) (sn:nat) (x y: cfac)
                                      : option (@value (option pexp * nat * option bool)) := 
     do t1 <- type_factor bv b x @
         do t2 <- type_factor bv b y @
            if (fst t1 =a= Q) && (fst t2 =a= C) then
               match par_find_var_check smap bv (get_size size b) r x with Some (Value vx) =>
                   do t2v <- par_eval_cfac_check smap bv size r b y @
                    match t2v with Value t2v' =>
                      Some (Value (Some (ceq_circuit_left size f b vmap vx t2v' stack temp sn),S sn,None))
                     | _ => Some Error
                    end
                   | None => None
                   | a => Some Error
               end
           else if (fst t1 =a= Q) && (fst t2 =a= Q) then
              do vxv <- par_find_var_check smap bv (get_size size b) r x @
                do vyv <- par_find_var_check smap bv (get_size size b) r y @
                 match vxv with Value vx => match vyv with Value vy => 
                    Some (Value (Some (ceq_circuit_two size f b vmap vx vy stack sn),S sn,None))
                              | _ => Some Error
                       end
                   | _ => Some Error
                 end
           else if (fst t1 =a= C) && (fst t2 =a= Q) then
               match par_find_var_check smap bv (get_size size b) r y with Some (Value vy) =>
                   do t1v <- par_eval_cfac_check smap bv size r b x @
                    match t1v with Value t1v' =>
                      Some (Value (Some (ceq_circuit_right size f b vmap t1v' vy stack temp sn),S sn,None))
                     | _ => Some Error
                    end
                   | None => None
                   | a => Some Error
               end
          else  do t1v <- par_eval_cfac_check smap bv size r b x @
                   do t2v <- par_eval_cfac_check smap bv size r b y @ 
                     match t1v with Value t1v' => match t2v with Value t2v' =>
                      Some (Value (None, sn, Some ((a_nat2fb t1v' size =? a_nat2fb t2v' size))))
                          | _ => Some Error end | _ => Some Error end.


Definition compile_cexp (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (e:cexp)
                                      : option (@value (option pexp * nat * option bool)) := 
   match e with clt b x y => 
                    if  ¬ (qvar_eq bv size r x y) then 
                                      gen_clt_c smap vmap bv size f r b temp stack sn x y
                                     else None
         | ceq b x y =>  
                        if  ¬ (qvar_eq bv size r x y) then 
                                      gen_ceq_c smap vmap bv size f r b temp stack sn x y
                                     else None
         | iseven x => do t1 <- type_factor bv Nat x @ if fst t1 =a= Q then None else 
                           do t2v <- par_eval_cfac_check smap bv size r Nat x @
                        match t2v with Value t2v' =>
                              if (a_nat2fb t2v' size) mod 2 =? 0 then Some (Value (None, sn, Some true))
                                        else Some (Value (None,sn,Some (false)))
                            | Error => Some Error
                        end
   end.


(*Proofs of compilation correctness for cexp. *)

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

Definition is_bl (t:option typ) : bool :=
 match t with Some (TNor a Bl) => true
            | Some (TArray a Bl x) => true
            | _ => false
 end.

Definition is_qtt (t:option typ) : Prop :=
 match t with Some (TNor Q b) => True
            | Some (TArray Q b x) => True
            | _ => False
 end.

Definition cexp_set_up (ce:cexp) (sl size:nat) (stack:var)
          (sn:nat) (vmap : (qvar*nat) -> var) (r:cstore) (bv:benv) (f:posi -> val) (aenv:var -> nat) (tenv:env) :=
  match ce with clt b x y => 
     match par_find_var bv size r x with None => True
                     | Some vx => 
        match par_find_var bv size r y with None => True
                         | Some vy => 
             ((vmap vx) <> (vmap vy) /\ (vmap vx) <> stack
                /\ (vmap vy) <> stack /\
                Store.In vx r /\ Store.In vy r /\ nor_modes f (vmap vx) size /\
               nor_modes f (vmap vy) size /\ nor_modes f (stack) (S sl)
            /\ well_typed_exp tenv (MAJseq (if is_bl (BEnv.find (fst vx) bv) then 1 else size)
                                    (vmap vy) (vmap vx) (stack,S sn))
           /\ well_typed_exp tenv (X ((stack,S sn))) 
            /\ well_typed_exp tenv (negator0 (if is_bl (BEnv.find (fst vx) bv) then 1 else size) (vmap vy))
           /\ right_mode_env aenv tenv f)
        end
      end
       | ceq b x y => 
     match par_find_var bv size r x with None => True
                     | Some vx => 
        match par_find_var bv size r y with None => True
                         | Some vy => 
             ((vmap vx) <> (vmap vy) /\ (vmap vx) <> stack
                /\ (vmap vy) <> stack /\  Store.In vx r /\ Store.In vy r /\
              nor_modes f (vmap vx) size /\
               nor_modes f (vmap vy) size /\ nor_modes f (stack) (S sl)
            /\ well_typed_exp tenv (MAJseq (if is_bl (BEnv.find (fst vx) bv) then 1 else size)
                        (vmap vx) (vmap vy) (stack,S sn))
            /\ well_typed_exp tenv (MAJseq (if is_bl (BEnv.find (fst vx) bv) then 1 else size)
                         (vmap vy) (vmap vx) (stack,S sn))
           /\ well_typed_exp tenv (X ((stack,S sn))) 
           /\ well_typed_exp tenv (negator0 (if is_bl (BEnv.find (fst vx) bv) then 1 else size) (vmap vx))
                 /\ well_typed_exp tenv (negator0 (if is_bl (BEnv.find (fst vx) bv) then 1 else size) (vmap vy))
           /\ right_mode_env aenv tenv f)
         end
     end
        | iseven x => True
  end.


Definition store_typed (r:cstore) (bv:benv) (size:nat) (stack:var) : Prop :=
   forall x v, fst x <> G stack -> Store.MapsTo x v r -> BEnv.find (fst x) bv <> None ->
           (forall i, (if is_bl (BEnv.find (fst x) bv) then 1 else size) <= i -> v i = false).

Definition store_match_q (stack:var) (r:store) (f:posi -> val)
           (bv:benv) (vmap : (qvar*nat) -> var) (aenv:var -> nat) : Prop := 
  forall x v vl, fst x <> G stack -> Store.MapsTo x (v::vl) r -> (BEnv.find (fst x) bv) <> None ->
         is_qtt (BEnv.find (fst x) bv) -> 
            get_cus (aenv (vmap x)) f (vmap x) = v.

Definition store_match_c (stack:var) (f:posi -> val) (bv:benv)
             (vmap : (qvar*nat) -> var) (aenv:var -> nat) : Prop := 
  forall x, fst x <> G stack -> BEnv.find (fst x) bv <> None ->
                    ~ is_qtt (BEnv.find (fst x) bv) -> get_cus (aenv (vmap x)) f (vmap x) = nat2fb 0.

Definition store_same_c (stack:var) (rh:cstore) (rl:cstore) (bv:benv)
             (vmap : (qvar*nat) -> var) (aenv:var -> nat) : Prop := 
  forall x, fst x <> G stack -> BEnv.find (fst x) bv <> None ->
                    ~ is_qtt (BEnv.find (fst x) bv) -> Store.find x rh = Store.find x rl.

Definition store_match_st (sl sn:nat) (stack:var) (f:posi -> val)
             (vmap : (qvar*nat) -> var) : Prop := 
          forall i, sn <= i -> get_cus (S sl) f (stack) i = false.

Definition aenv_match (stack:var) (size:nat) (bv:benv) (aenv: var -> nat) (vmap : (qvar*nat) -> var) : Prop := 
          forall x, fst x <> G stack -> aenv (vmap x) = (if is_bl (BEnv.find (fst x) bv) then 1 else size).

Definition no_equal_stack (temp stack:var) (ce:cexp) (size:nat) (bv:benv) (r:cstore) :=
    match ce with clt b x y => 
     match par_find_var bv size r x with None => 
             match par_find_var bv size r y with None => True
                       | Some vy => fst vy <> G stack /\ fst vy <> G temp
             end
                     | Some vx => 
        match par_find_var bv size r y with None => fst vx <> G stack /\ fst vx <> G temp
                    | Some vy => fst vx <> G stack /\ fst vy <> G stack /\ fst vx <> G temp /\ fst vy <> G temp
        end
     end
      | ceq b x y => 
     match par_find_var bv size r x with None => 
             match par_find_var bv size r y with None => True
                       | Some vy => fst vy <> G stack /\ fst vy <> G temp
             end
                     | Some vx => 
        match par_find_var bv size r y with None => fst vx <> G stack
                    | Some vy => fst vx <> G stack /\ fst vy <> G stack /\ fst vx <> G temp /\ fst vy <> G temp
        end
      end
      | iseven x => True
   end.

Definition cstore_store_match (smap : qvar -> nat) (s:store) (r:cstore) (bv:benv) :=
       forall x i v vl t, i < smap x -> Store.MapsTo (x,i) (v::vl) s -> 
                    BEnv.MapsTo x t bv -> ~ is_qtt (Some t) -> Store.MapsTo (x,i) v r.

Lemma a_nat2fb_cut_same' : forall size m v, size <= m -> a_nat2fb (cut_n v m) size = a_nat2fb v size.
Proof.
 induction size;intros;simpl. easy.
 simpl.
 rewrite IHsize by lia.
 unfold cut_n.
 bdestruct (size <? m). easy. lia.
Qed.

Lemma a_nat2fb_cut_same : forall size v, a_nat2fb (cut_n v size) size = a_nat2fb v size.
Proof.
 intros. rewrite a_nat2fb_cut_same' by lia. easy.
Qed.

Lemma par_find_var_means_cfac_some : 
   forall smap size bv s r b x t vx val, par_find_var bv size r x = Some vx ->
       cstore_store_match smap s r bv -> bv_store_sub smap bv s -> bv_store_gt_0 smap bv ->
     BEnv.MapsTo (fst vx) t bv -> ~ is_qtt (Some t) ->
     sem_cfac smap size s b x = Some (Value val) -> Store.find vx r = Some val.
Proof.
  intros.
  unfold par_find_var,sem_cfac in *.
  destruct x.
  unfold par_eval_fc,sem_factor in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *.
  destruct (is_q t0) eqn:eq2. inv H.
  destruct (Store.find (elt:=nat -> bool) (v, 0) r) eqn:eq3.
  destruct (Store.find (elt:=list (nat -> bool)) (v, 0) s) eqn:eq4.
  destruct (hd_error l) eqn:eq5.
  destruct l. simpl in eq5. inv eq5. simpl in eq5. inv eq5.
  bdestruct (a_nat2fb b1 size <? smap x).
  unfold cstore_store_match in H0.
  unfold bv_store_gt_0 in H2.
  specialize (H2 v).
  assert (BEnv.In v bv).
  unfold BEnv.In,BEnv.Raw.PX.In. exists t0.
  apply BEnv.find_2. easy.
  apply H2 in H7.
  apply Store.find_2 in eq4.
  apply Store.find_2 in eq3.
  apply BEnv.find_2 in eq1.
  assert (~ is_qtt (Some t0)).
  unfold is_qtt,is_q in *.
  destruct t0. destruct a. 1-2:easy. destruct a. easy. easy.
  specialize (H0 v 0 b1 l t0 H7 eq4 eq1 H8) as eq5.
  apply store_mapsto_always_same with (v1 := b0) in eq5; try easy. subst.
  destruct (Store.find (elt:=list (nat -> bool))
         (x, a_nat2fb b1 size) s) eqn:eq6.
  destruct (hd_error l0) eqn:eq7. inv H5. destruct l0. simpl in *. inv eq7.
  simpl in *. inv eq7.
  inv H.
  unfold bv_store_sub in H1. simpl in H3.
  assert (BEnv.In x bv).
  unfold BEnv.In,BEnv.Raw.PX.In. exists t. easy.
  specialize (H1 x (a_nat2fb b1 size) H H6).
  destruct H1. destruct H1. destruct x0. simpl in *. lia.
  apply Store.find_2 in eq6.
  apply store_mapsto_always_same with (v1 := (b0 :: x0)) in eq6; try easy.
  inv eq6.
  specialize (H0 x (a_nat2fb b1 size) val l0 t H6 H1 H3 H4).
  apply Store.find_1.
  rewrite a_nat2fb_cut_same. easy. inv H5. inv H5. inv H5. inv H5. inv H5.
  inv H. simpl in *. inv H.
  simpl in *. inv H.
  bdestruct (a_nat2fb (cut_n n size) size <? smap x).
  destruct (Store.find (elt:=list (nat -> bool))
         (x, a_nat2fb (cut_n n size) size) s) eqn:eq1.
  destruct (hd_error l) eqn:eq2. destruct l. simpl in *. inv eq2. inv eq2.
  unfold cstore_store_match in H0.
  apply Store.find_2 in eq1.
  simpl in H3.
  specialize (H0 x (a_nat2fb (cut_n n size) size) b0 l t H eq1 H3 H4). inv H5.
  apply Store.find_1. easy. inv H5. inv H5. inv H5. simpl in *.
  destruct v. inv H.
  destruct (sem_factor size s b (Var v)) eqn:eq1. inv H5.
  unfold sem_factor in eq1. simpl in eq1.
  destruct (Store.find (elt:=list (nat -> bool)) (v, 0) s) eqn:eq2.
  destruct l. simpl in eq1. inv eq1. simpl in *. inv eq1.
  unfold bv_store_gt_0 in H2.
  assert (BEnv.In v bv).
  unfold BEnv.In,BEnv.Raw.PX.In. exists t. easy.
  apply H2 in H.
  unfold cstore_store_match in H0.
  apply Store.find_2 in eq2.
  specialize (H0 v 0 val l t H eq2 H3 H4).
  apply Store.find_1. easy.
  inv eq1. inv H5.
  inv H.
Qed.

Lemma type_factor_means_q : forall x vx b t size bv r, type_factor bv b x = Some t -> 
   par_find_var bv size r x = Some vx -> fst t = Q -> is_qtt (BEnv.find (fst vx) bv).
Proof.
  intros.
  unfold type_factor,typ_factor,typ_factor_full,par_find_var,par_eval_fc,is_qtt,is_q in *.
  destruct x eqn:eq1. destruct v eqn:eq2. simpl in *.
  destruct (BEnv.find (elt:=typ) v0 bv) eqn:eq3. 
  destruct t0 eqn:eq4.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq5.
  destruct t1.
  bdestruct (b1 =b= b). inv H. inv H. inv H. inv H.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq5.
  destruct t1.
  bdestruct (b1 =b= b). destruct a eqn:eq6.
  bdestruct ((b0 =b= Nat)). simpl in *. inv H.
  destruct (Store.find (elt:=nat -> bool) (v0, 0) r) eqn:eq6.
  simpl in H1. subst. inv H0. simpl. rewrite eq5. easy. inv H0.
  simpl in *. inv H.
  simpl in *. inv H. inv H. inv H. inv H. inv H0.
  simpl in *.
  inv H0.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq1.
  destruct t0.
  bdestruct (b0 =b= b). inv H. simpl in *. rewrite eq1. rewrite H1. easy.
  inv H. inv H. inv H. simpl in *. destruct v. inv H0.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  destruct t0. inv H.
  bdestruct (b0 =b= b). inv H. simpl in *. rewrite eq1. rewrite H1. easy.
  inv H. inv H. inv H0.
Qed.

Lemma type_factor_means_b : forall x vx b t size bv r, type_factor bv b x = Some t -> 
   par_find_var bv size r x = Some vx -> is_bl (BEnv.find (fst vx) bv) = (b =b= Bl).
Proof.
  intros.
  unfold type_factor,typ_factor,typ_factor_full,par_find_var,par_eval_fc,is_bl,is_q in *.
  destruct x eqn:eq1. destruct v eqn:eq2. simpl in *.
  destruct (BEnv.find (elt:=typ) v0 bv) eqn:eq3. 
  destruct t0.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq4.
  destruct t0.
  bdestruct (b1 =b= b). inv H. inv H. inv H. inv H.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq4.
  destruct t0.
  bdestruct (b1 =b= b). destruct a eqn:eq5.
  bdestruct (b0 =b= Nat). simpl in *. inv H.
  destruct (Store.find (v0,0) r) eqn:eq5. inv H0.
  simpl. rewrite eq4.
  bdestruct (b =b= Bl). rewrite H. easy. destruct b. easy. easy. easy. inv H0.
  simpl in *. inv H. simpl in *. inv H. inv H. inv H. inv H.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq4.
  destruct t0. inv H0. inv H0. inv H0.
  simpl in *.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq4.
  destruct t0.
  bdestruct (b0 =b= b). inv H. inv H0. simpl.
  rewrite eq4.
  bdestruct (b =b= Bl). destruct b. easy. easy. easy.
  destruct b. easy. easy. easy. inv H. inv H. inv H.
  destruct v eqn:eq2. inv H0. simpl in *.
  destruct (BEnv.find (elt:=typ) v0 bv). destruct t0.
  inv H.
  bdestruct (b0 =b= b).
  bdestruct (b =b= Bl). destruct b0. subst. easy. subst. easy. subst. easy.
  subst. destruct b. easy. easy. easy. inv H. inv H. inv H0.
Qed.

Lemma type_factor_means_q_false : forall x vx b t size bv r, type_factor bv b x = Some t -> 
   par_find_var bv size r x = Some vx -> fst t = C -> BEnv.find (fst (vx)) bv <> None -> ~ is_qtt (BEnv.find (fst vx) bv).
Proof.
  intros.
  unfold type_factor,typ_factor,typ_factor_full,par_find_var,par_eval_fc,is_qtt,is_q in *.
  destruct x eqn:eq1. destruct v eqn:eq2. simpl in *.
  destruct (BEnv.find (elt:=typ) v0 bv) eqn:eq3. 
  destruct t0.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq5.
  destruct t0. destruct a. 
  bdestruct (b1 =b= b). inv H. inv H. inv H0. inv H. inv H.
  destruct (BEnv.find (elt:=typ) x0 bv ) eqn:eq5.
  destruct t0. destruct a. 
  bdestruct (b1 =b= b).
  bdestruct (b0 =b= Nat). simpl in *.
  destruct (Store.find (elt:=nat -> bool) (v0, 0) r ) eqn:eq6.
  inv H. destruct vx. simpl in *. inv H0.
  rewrite eq5. easy.
  inv H0. simpl in *. inv H. inv H.
  bdestruct (b1 =b= b). simpl in *. inv H. inv H. inv H. inv H.
  inv H0.
  simpl in *. inv H0.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq1.
  destruct t0.
  bdestruct (b0 =b= b). inv H. simpl in *.
  rewrite eq1. rewrite H1. easy. inv H. inv H. inv H.
  destruct v eqn:eq2. simpl in *.
  destruct (BEnv.find (elt:=typ) v0 bv) eqn:eq3.
  destruct t0. inv H.
  bdestruct (b0 =b= b). inv H0. simpl.
  rewrite eq3. inv H. simpl in *. rewrite H1. easy.
  inv H. inv H. inv H0.
Qed.

Lemma type_factor_means_some : forall x vx b t size bv r, type_factor bv b x = Some t -> 
   par_find_var bv size r x = Some vx -> BEnv.find (fst vx) bv <> None.
Proof.
  intros.
  unfold type_factor,typ_factor,typ_factor_full,par_find_var,par_eval_fc,is_q in *.
  destruct x eqn:eq1. destruct v eqn:eq2. simpl in *.
  destruct (BEnv.find (elt:=typ) v0 bv) eqn:eq3. 
  destruct t0 eqn:eq4.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq5.
  destruct t1.
  bdestruct (b1 =b= b). inv H. inv H. inv H. inv H.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq5.
  destruct t1.
  bdestruct (b1 =b= b).
  destruct a.
  bdestruct (b0 =b= Nat). simpl in *.
  destruct (Store.find (elt:=nat -> bool) (v0, 0) r) eqn:eq6.
  inv H0. simpl. rewrite eq5. easy. inv H0.
  simpl in *. inv H. simpl in *. inv H. inv H. inv H. inv H.
  inv H0.
  simpl in *.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq5.
  destruct t0.
  bdestruct (b0 =b= b). inv H0. simpl.
  rewrite eq5. easy.
  inv H. inv H. inv H.
  destruct v eqn:eq2. simpl in *.
  destruct (BEnv.find (elt:=typ) v0 bv) eqn:eq3. 
  destruct t0. inv H.
  bdestruct (b0 =b= b).
  inv H0. simpl. rewrite eq3. easy.
  inv H. inv H. inv H0.
Qed.

Definition get_var_factor (x:factor) :=
   match x with Var v => [v]
                  | Num v => []
   end.

Definition get_var_cfac (x:cfac) :=
    match x with Index x v => (x:: get_var_factor v)
               | Nor v => get_var_factor v
    end.

Definition get_var_cexp (x:cexp) :=
   match x with clt b x y => get_var_cfac x ++ get_var_cfac y
              | ceq b x y => get_var_cfac x ++ get_var_cfac y
              | iseven x => get_var_cfac x
   end.

Definition not_stack (stack:var) (l:list qvar) := forall x, In x l -> x <> G stack.

(*
Inductive factor := Var (v:qvar)
                 | Num (n:nat -> bool).
     (* the first m in Num represents the number of bits.
      a value is represented as a natural number x. it means x / 2^m where m is the number of denominator. *)

Inductive cfac := Ptr (x:var) (v:factor) | Nor (v:factor).
*)


Lemma par_find_var_lh : forall b x bv vmap aenv size stack rl rh t vx, type_factor bv b x = Some t
      -> par_find_var bv size rl x = Some vx -> not_stack stack (get_var_cfac x) ->
     store_same_c stack rh rl bv vmap aenv -> par_find_var bv size rh x = Some vx.
Proof.
  intros.
  unfold store_same_c in *.
  unfold type_factor,typ_factor,typ_factor_full,par_find_var,par_eval_fc,is_q in *.
  destruct x eqn:eq1. destruct v eqn:eq2.
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq3.
  simpl in *. destruct t0.
  bdestruct (b0 =b= b).
  destruct (BEnv.find (elt:=typ) v0 bv) eqn:eq4. destruct t0.
  inv H. destruct a0. simpl in *.
  bdestruct (b1 =b= Nat).
  simpl in *.
  destruct (Store.find (elt:=nat -> bool) (v0, 0) rl) eqn:eq5.
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
  destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq3.
  destruct t0.
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

Lemma compile_cexp_sem : forall sl size smap vmap bv fl rh rl temp stack sn e st re f aenv tenv, 
      compile_cexp size smap vmap bv fl rl temp stack sn e = Some st ->
      sem_cexp smap size rh e = Some re -> store_typed rl bv size stack -> 
      0 < size -> S sn < sl ->
      cstore_store_match smap rh rl bv -> bv_store_sub smap bv rh -> bv_store_gt_0 smap bv ->
      no_equal_stack temp stack e size bv rl ->
      store_match_q stack rh f bv vmap aenv ->
      store_same_c stack rl rl bv vmap aenv ->
      store_match_c stack f bv vmap aenv ->
      store_match_st sl sn stack f vmap ->
      aenv_match stack size bv aenv vmap ->
      not_stack stack (get_var_cexp e) ->
      cexp_set_up e sl size stack sn vmap rl bv f aenv tenv
         -> (st = Error /\ re = Error) \/ (exists b, st = Value (None,sn,Some b) /\ re = Value b)
              \/ (exists p, st = Value (Some p, S sn,None) 
                 /\ re = (Value (get_cua (prog_sem aenv p f (stack,sn))))).
Proof.
  intros. induction e.
  simpl in *.
  destruct (¬ (qvar_eq bv size rl x y)) eqn:eq1.
  unfold gen_clt_c in H.
  destruct (type_factor bv t x) eqn:eq2.
  destruct (type_factor bv t y) eqn:eq3.
  simpl in *.
  destruct (par_find_var_check smap bv size rl x) eqn:eq4.
  destruct (par_find_var_check smap bv size rl y) eqn:eq5.
  simpl in *.
  bdestruct (fst p =a= Q). bdestruct (fst p0 =a= C).
  simpl in *.
  destruct (par_eval_cfac smap bv size rl t y) eqn:eq6.
  destruct v. destruct v0.
  inv H.
  right. right.
Admitted.

(* Compiler for qexp *)
Definition fmap :Type := list (fvar * cfac * pexp * (qvar -> nat) * ((qvar*nat) -> var) * benv * cstore).
Fixpoint lookup_fmap (l:fmap) (x:fvar) : option (cfac * pexp * (qvar -> nat) * ((qvar*nat) -> var) * benv * cstore) :=
   match l with [] => None
          | ((y,a,p,smap,vmap,bv,r)::xl) => if x =? y then Some (a,p,smap,vmap,bv,r) else lookup_fmap xl x
   end.

Fixpoint copyto (x y:var) size := match size with 0 => SKIP (x,0) 
                  | S m => CNOT (x,m) (y,m) ; copyto x y m
    end.

Definition combine_c (e1 e2:option pexp) : option pexp :=
          match e1 with None => e2
               | Some e1' => match e2 with None => Some e1'
                                        | Some e2' => Some (e1';;e2')
                              end
          end.

Definition combine_seq (e1:option pexp) (e2:option pexp) :=
   match e1 with None => e2
        | Some e1' => match e2 with None => Some e1' | Some e2' => Some (e1' ;; e2') end
   end.

Definition deal_result (r:cstore) (re : option (option pexp * nat * option cstore)) :=
    match re with None => None
             | Some (a,b,None) => Some (a,b,r)
             | Some (a,b,Some r') => Some (a,b,r')
    end.

Definition estore : Type := Store.t (list pexp).
Definition empty_estore := @Store.empty (list pexp).

(* nat: x + y *)
Definition nadd_circuit_two (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (stack: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (adder01 size (vmap x) (vmap y) (stack,S sn))
            else rz_full_adder_form (vmap x) size (vmap y).


Definition nadd_circuit_left (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x :(qvar*nat)) (y:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (init_v size (temp) y;
                    adder01 size (vmap x) (temp) (stack,S sn);
                    init_v size (temp) y)
            else rz_adder_form (vmap x) size y.

Definition nadd_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y:cfac)
                 : option (@value (option pexp * nat * cstore * estore)) :=
     do t1 <- type_factor bv Nat x @
         do t2 <- type_factor bv Nat y @
            match par_find_var_check smap bv size r x with Some (Value vx) => 
              if (fst t1 =a= Q) && (fst t2 =a= C)
               then 
                   do t2v <- par_eval_cfac_check smap bv size r Nat y @
                     match t2v with Value t2v' =>
                 do exps <- Store.find vx es @
                      Some (Value (Some (nadd_circuit_left size f vmap vx t2v' stack temp sn),sn,r,
                      Store.add vx ((nadd_circuit_left size f vmap vx t2v' stack temp sn)::exps) es))
                        | _ => Some Error
                     end
              else if (fst t1 =a= Q) && (fst t2 =a= Q)
               then do vyv <- par_find_var_check smap bv size r y @
                     match vyv with Value vy => 
                 do exps <- Store.find vx es @
                          Some (Value (Some (nadd_circuit_two size f vmap vx vy stack sn),sn,r,
                    Store.add vx ((nadd_circuit_two size f vmap vx vy stack sn)::exps) es))
                      | _ => Some Error
                     end
                 else None
             | None => None
             | a => Some Error
            end.

(* nat: x - y *)
Definition nsub_circuit_two (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (stack: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (subtractor01 size (vmap x) (vmap y) (stack,S sn))
            else rz_full_sub_form (vmap x) size (vmap y).


Definition nsub_circuit_left (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x :(qvar*nat)) (y:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (init_v size (temp) y;
                    subtractor01 size (vmap x) (temp) (stack,S sn);
                    init_v size (temp) y)
            else rz_sub_right (vmap x) size y.

Definition nsub_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y:cfac) 
              : option (@value (option pexp * nat * cstore * estore)) :=
     do t1 <- type_factor bv Nat x @
         do t2 <- type_factor bv Nat y @
            match par_find_var_check smap bv size r x with Some (Value vx) => 
              if (fst t1 =a= Q) && (fst t2 =a= C)
               then 
                   do t2v <- par_eval_cfac_check smap bv size r Nat y @
                     match t2v with Value t2v' =>
                 do exps <- Store.find vx es @
                      Some (Value (Some (nsub_circuit_left size f vmap vx t2v' stack temp sn),sn,r,
                Store.add vx ((nsub_circuit_left size f vmap vx t2v' stack temp sn)::exps) es))
                      | _ => Some Error
                     end
              else if (fst t1 =a= Q) && (fst t2 =a= Q)
               then do vyv <- par_find_var_check smap bv size r y @
                     match vyv with Value vy => 
                 do exps <- Store.find vx es @
                          Some (Value (Some (nsub_circuit_two size f vmap vx vy stack sn),sn,r,
                Store.add vx ((nsub_circuit_two size f vmap vx vy stack sn)::exps) es))
                      | _ => Some Error
                     end
                 else None
             | None => None
             | a => Some Error
            end.


(* fixedp: x + y *)
Definition fadd_circuit_two (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (stack: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (Rev (vmap x);Rev (vmap y);
               adder01 size (vmap x) (vmap y) (stack,S sn);inv_exp (Rev (vmap x);Rev (vmap y)))
            else Exp (Rev (vmap x);Rev (vmap y));;
                   rz_full_adder_form (vmap x) size (vmap y);;inv_pexp (Exp (Rev (vmap x);Rev (vmap y))).


Definition fadd_circuit_left (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x :(qvar*nat)) (y:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (init_v size (temp) y;
                   Rev (vmap x);Rev (temp);
                    adder01 size (vmap x) (temp) (stack,S sn);
                   inv_exp (Rev (vmap x);Rev (temp));
                    init_v size (temp) y)
            else Exp (Rev (vmap x));;rz_adder_form (vmap x) size (fbrev size y);; (inv_pexp (Exp (Rev (vmap x)))).

Definition fadd_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y:cfac)
              : option (@value (option pexp * nat * cstore * estore)) :=
     do t1 <- type_factor bv FixedP x @
         do t2 <- type_factor bv FixedP y @
            match par_find_var_check smap bv size r x with Some (Value vx) => 
              if (fst t1 =a= Q) && (fst t2 =a= C)
               then 
                   do t2v <- par_eval_cfac_check smap bv size r FixedP y @
                    match t2v with Value t2v' => 
                 do exps <- Store.find vx es @
                      Some (Value (Some (fadd_circuit_left size f vmap vx t2v' stack temp sn),sn,r,
                     Store.add vx ((fadd_circuit_left size f vmap vx t2v' stack temp sn)::exps) es))
                      | _ => Some Error
                    end
              else if (fst t1 =a= Q) && (fst t2 =a= Q)
               then do vyv <- par_find_var_check smap bv size r y @
                     match vyv with Value vy => 
                     do exps <- Store.find vx es @
                          Some (Value (Some (fadd_circuit_two size f vmap vx vy stack sn),sn,r,
                     Store.add vx( (fadd_circuit_two size f vmap vx vy stack sn)::exps) es))
                      | _ => Some Error
                     end
                 else None
             | None => None
             | a => Some Error
            end.

(* fixedp: x - y *)
Definition fsub_circuit_two (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (stack: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (Rev (vmap x);Rev (vmap y);
               subtractor01 size (vmap x) (vmap y) (stack,S sn);inv_exp (Rev (vmap x);Rev (vmap y)))
            else Exp (Rev (vmap x);Rev (vmap y));;
                   rz_full_sub_form (vmap x) size (vmap y);;inv_pexp (Exp (Rev (vmap x);Rev (vmap y))).


Definition fsub_circuit_left (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x :(qvar*nat)) (y:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
              Exp (init_v size (temp) y;
                   Rev (vmap x);Rev (temp);
                    subtractor01 size (vmap x) (temp) (stack,S sn);
                   inv_exp (Rev (vmap x);Rev (temp));
                    init_v size (temp) y)
            else Exp (Rev (vmap x));;rz_sub_right (vmap x) size (fbrev size y);; (inv_pexp (Exp (Rev (vmap x)))).

Definition fsub_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y:cfac)
              : option (@value (option pexp * nat * cstore * estore)) :=
     do t1 <- type_factor bv FixedP x @
         do t2 <- type_factor bv FixedP y @
            match par_find_var_check smap bv size r x with Some (Value vx) => 
              if (fst t1 =a= Q) && (fst t2 =a= C)
               then 
                   do t2v <- par_eval_cfac_check smap bv size r FixedP y @
                    match t2v with Value t2v' =>
                     do exps <- Store.find vx es @
                      Some (Value (Some (fsub_circuit_left size f vmap vx t2v' stack temp sn),sn,r,
                       Store.add vx ((fsub_circuit_left size f vmap vx t2v' stack temp sn)::exps) es))
                     | _ => Some Error
                   end
              else if (fst t1 =a= Q) && (fst t2 =a= Q)
               then do vyv <- par_find_var_check smap bv size r y @
                     match vyv with Value vy => 
                     do exps <- Store.find vx es @
                          Some (Value (Some (fsub_circuit_two size f vmap vx vy stack sn),sn,r,
                       Store.add vx ((fsub_circuit_two size f vmap vx vy stack sn)::exps) es))
                      | _ => Some Error
                     end
                 else None
             | None => None
             | a => Some Error
            end.

(*nat : x = y * z *)
Definition nmul_circuit_two (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x y z:(qvar*nat)) (temp stack: var) (sn:nat) :=
            if f =fl= Classic then
               cl_full_mult size (vmap y) (vmap z) (vmap x) (temp) (stack,sn)
            else 
               nat_full_mult size (vmap y) (vmap z) (vmap x) (temp).


Definition nmul_circuit_one (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (z:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
                     Exp (cl_nat_mult size (vmap y) (vmap x) temp (stack,sn) z)
            else nat_mult size (vmap y) (vmap x) z.

Definition nqmul_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y z:cfac)
              : option (@value (option pexp * nat * cstore * estore)) :=
     do t1 <- type_factor bv Nat x @
         do t2 <- type_factor bv Nat y @
         do t3 <- type_factor bv Nat z @
             do vx <- par_find_var bv size r x @  
              if (fst t2 =a= Q) && (fst t3 =a= Q) then
                 do vyv <- par_find_var_check smap bv size r y @
                   do vzv <- par_find_var_check smap bv size r z @
                    match vyv with Value vy => 
                     match vzv with Value vz =>
                     do exps <- Store.find vx es @
                         Some (Value (Some (nmul_circuit_two size f vmap vy vz vx temp stack sn),sn,r,
                      Store.add vx ((nmul_circuit_two size f vmap vy vz vx temp stack sn)::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end
              else if (fst t2 =a= Q) && (fst t3 =a= C) then
                 do vyv <- par_find_var_check smap bv size r y @
                  do vzv <- par_eval_cfac_check smap bv size r Nat z @
                     match vyv with Value vy => 
                       match vzv with Value tzv => 
                     do exps <- Store.find vx es @
                           Some (Value (Some (nmul_circuit_one size f vmap vx vy tzv stack temp sn),sn,r,
                      Store.add vx ((nmul_circuit_one size f vmap vx vy tzv stack temp sn)::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end
              else if (fst t2 =a= C) && (fst t3 =a= Q) then
                 do vzv <- par_find_var_check smap bv size r z @
                  do vyv <- par_eval_cfac_check smap bv size r Nat y @
                     match vzv with Value vz => 
                       match vyv with Value tyv => 
                     do exps <- Store.find vx es @
                           Some (Value (Some (nmul_circuit_one size f vmap vx vz tyv stack temp sn),sn,r,
                      Store.add vx ((nmul_circuit_one size f vmap vx vz tyv stack temp sn)::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end
              else do vyv <- par_eval_cfac_check smap bv size r Nat y @
                    do vzv <- par_eval_cfac_check smap bv size r Nat z @
                       match vyv with Value tyv => 
                        match vzv with Value tzv => 
                     do exps <- Store.find vx es @
                    Some (Value (Some (Exp (init_v size (vmap vx)
                               (nat2fb (((a_nat2fb tyv size) * (a_nat2fb tzv size)) mod 2^size)))),sn,r,
                      Store.add vx ((Exp (init_v size (vmap vx)
                               (nat2fb (((a_nat2fb tyv size) * (a_nat2fb tzv size)) mod 2^size))))::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end.

Definition fmul_circuit_two (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x y z:(qvar*nat)) (temp stack: var) (sn:nat) :=
            if f =fl= Classic then
               Exp (Rev (vmap y); Rev (vmap z); Rev (vmap x));;
               cl_full_mult size (vmap y) (vmap z) (vmap x) (temp) (stack,sn);;
               (inv_pexp (Exp (Rev (vmap y); Rev (vmap z); Rev (vmap x))))
            else 
               Exp (Rev (vmap y); Rev (vmap z); Rev (vmap x));;
               nat_full_mult size (vmap y) (vmap z) (vmap x) (temp);;
               (inv_pexp (Exp (Rev (vmap y); Rev (vmap z); Rev (vmap x)))).


Definition fmul_circuit_one (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (z:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
                     Exp (cl_nat_mult size (vmap y) (vmap x) temp (stack,sn) z)
            else nat_mult size (vmap y) (vmap x) z.


Definition fmul_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y z:cfac)
              : option (@value (option pexp * nat * cstore * estore)) :=
     do t1 <- type_factor bv FixedP x @
         do t2 <- type_factor bv FixedP y @
         do t3 <- type_factor bv FixedP z @
             do vx <- par_find_var bv size r x @  
              if (fst t2 =a= Q) && (fst t3 =a= Q) then
                 do vyv <- par_find_var_check smap bv size r y @
                   do vzv <- par_find_var_check smap bv size r z @
                    match vyv with Value vy => 
                     match vzv with Value vz =>
                     do exps <- Store.find vx es @
                         Some (Value (Some (fmul_circuit_two size f vmap vy vz vx temp stack sn),sn,r,
                      Store.add vx ((fmul_circuit_two size f vmap vy vz vx temp stack sn)::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end
              else if (fst t2 =a= Q) && (fst t3 =a= C) then
                 do vyv <- par_find_var_check smap bv size r y @
                  do vzv <- par_eval_cfac_check smap bv size r FixedP z @
                     match vyv with Value vy => 
                       match vzv with Value tzv => 
                     do exps <- Store.find vx es @
                           Some (Value (Some (fmul_circuit_one size f vmap vx vy tzv stack temp sn),sn,r,
                      Store.add vx ((fmul_circuit_one size f vmap vx vy tzv stack temp sn)::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end
              else if (fst t2 =a= C) && (fst t3 =a= Q) then
                 do vzv <- par_find_var_check smap bv size r z @
                  do vyv <- par_eval_cfac_check smap bv size r FixedP y @
                     match vzv with Value vz => 
                       match vyv with Value tyv => 
                     do exps <- Store.find vx es @
                           Some (Value (Some (fmul_circuit_one size f vmap vx vz tyv stack temp sn),sn,r,
                      Store.add vx ((fmul_circuit_one size f vmap vx vz tyv stack temp sn)::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end
              else do vyv <- par_eval_cfac_check smap bv size r FixedP y @
                    do vzv <- par_eval_cfac_check smap bv size r FixedP z @
                       match vyv with Value tyv => 
                        match vzv with Value tzv => 
                     do exps <- Store.find vx es @
                           Some (Value (Some (Exp (init_v size (vmap vx)
                               (nat2fb (((a_nat2fb tyv size) * (a_nat2fb tzv size)) mod 2^size)))),sn,r,
                      Store.add vx ((Exp (init_v size (vmap vx)
                               (nat2fb (((a_nat2fb tyv size) * (a_nat2fb tzv size)) mod 2^size))))::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end.

Fixpoint bin_xor_q (n:nat) (x y : var) : exp :=
   match n with 0 => SKIP (x,0)
      | S m => CNOT (x,m) (y,m);bin_xor_q m x y
   end.

Fixpoint bin_xor_c (n:nat) (x : var) (y:nat->bool) : exp :=
   match n with 0 => SKIP (x,0)
      | S m => if y m then X (x,m); bin_xor_c m x y else bin_xor_c m x y
   end.


Definition qxor_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var) (bv:benv) (r:cstore) (sn:nat) (es:estore) (x y:cfac) 
              : option (@value (option pexp * nat * cstore * estore)) :=
          do vxv <- par_find_var_check smap bv size r x @
            match vxv with Value vx =>   
              do t <- BEnv.find (fst vx) bv @
               if is_q t then
                do t2 <- type_factor bv (get_ct t) y @
                 if fst t2 =a= Q then
                  do vyv <- par_find_var_check smap bv size r y @
                   match vyv with Value vy =>
                   do exps <- Store.find vx es @
                     Some (Value (Some (Exp (bin_xor_q (get_size size (get_ct t)) (vmap vy) (vmap vx))),sn,r,
                         Store.add vx ((Exp (bin_xor_q (get_size size (get_ct t)) (vmap vy) (vmap vx)))::exps) es))
                   | _ => Some Error
                  end
                 else do t2v <- par_eval_cfac_check smap bv size r (snd t2) y @
                   match t2v with Value t2v' => 
                   do exps <- Store.find vx es @
                     Some (Value (Some (Exp (bin_xor_c (get_size size (get_ct t)) (vmap vx) t2v')),sn,r,
                              Store.add vx ((Exp (bin_xor_c (get_size size (get_ct t)) (vmap vx) t2v'))::exps) es))
                    | _ => Some Error
                   end
               else do t1v <- par_eval_cfac_check smap bv size r (get_ct t) x @
                     do t2v <- par_eval_cfac_check smap bv size r (get_ct t) y @
                       match t1v with Value t1v' => 
                         match t2v with Value t2v' => 
                            Some (Value (None,sn, (Store.add vx (bin_xor t1v' t2v' (get_size size (get_ct t))) r),es))
                          | _ => Some Error end
                        | _ => Some Error
                         end
               |_ => Some Error
            end.

Definition init_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var) (bv:benv) (r:cstore) (sn:nat) (es:estore) (x y:cfac) 
              : option (@value (option pexp * nat * cstore * estore)) :=
           do vxv <- par_find_var_check smap bv size r x @
            match vxv with Value vx =>
              do t <- BEnv.find (fst vx) bv @
              if is_q t then 
                do t2 <- type_factor bv (get_ct t) y @
                 if fst t2 =a= Q then
                  do vyv <- par_find_var_check smap bv size r y @
                   match vyv with Value vy =>
                    do exps <- Store.find vx es @ 
                     Some (Value (Some (Exp (bin_xor_q (get_size size (get_ct t)) (vmap vy) (vmap vx))),sn,r,
                          Store.add vx ((Exp (bin_xor_q (get_size size (get_ct t)) (vmap vy) (vmap vx)))::exps) es))
                   | _ => Some Error
                  end
                 else do t2v <- par_eval_cfac_check smap bv size r (snd t2) y @
                   match t2v with Value t2v' => 
                    do exps <- Store.find vx es @ 
                     Some (Value (Some (Exp (bin_xor_c (get_size size (get_ct t)) (vmap vx) t2v')),sn,r,
                      Store.add vx ((Exp (bin_xor_c (get_size size (get_ct t)) (vmap vx) t2v'))::exps) es))
                    | _ => Some Error
                   end
               else None
               |_ => Some Error
           end.

Definition lrot_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var) (bv:benv) (r:cstore) (sn:nat) (es:estore) (x:cfac) :=
    do vxv <- par_find_var_check smap bv size r x @
       match vxv with Value vx => 
          do t <- BEnv.find (fst vx) bv @
               if is_q t then
                do exps <- Store.find vx es @
                   Some (Value (Some (Exp (Rshift (vmap vx))), sn, r,Store.add vx ((Exp (Rshift (vmap vx)))::exps) es))
               else
                do t1v <- Store.find vx r @
                   Some (Value (None,sn, (Store.add vx (l_rotate t1v (get_size size (get_ct t))) r),es))
            | _ => Some Error
       end.


Definition combine_if (sv : var) (sn:nat) (p1:pexp) (e1:option pexp) (e2:option pexp) :=
   match e1 with None => match e2 with None => Some p1
           | Some e2' => Some (p1 ;; Exp (X (sv,sn));; PCU (sv,sn) e2')
                         end
           | Some e1' => match e2 with None => Some (p1 ;; PCU (sv,sn) e1')
                | Some e2' => Some (p1 ;; PCU (sv,sn) e1' ;; 
                         Exp (X (sv,sn));; PCU (sv,sn) e2')
                         end
    end.

Fixpoint trans_qexp (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (fl:flag) (r:cstore) (temp stack:var)
                  (sn:nat) (fv:fmap) (es:estore) (e:qexp) : option (@value (option pexp * nat * cstore * estore)) :=
   match e with qfor x n e' => 
     do t2v' <- par_eval_cfac_check smap bv size r Nat n @
       match t2v' with Value t2v =>
         let fix trans_while (r:cstore) (sn:nat) (es:estore) (i:nat) : option (@value (option pexp * nat * cstore * estore)) :=
            match i with 0 => Some (Value (None,sn,r,es))
                     | S m => do re <- trans_qexp size smap vmap bv fl r temp stack sn fv es e' @
                               match re with Value (cir,sn',r',es') =>
                                 do re' <- trans_while r' sn' es' m @
                                  match re' with Value (cir',sn'',r'',es'') =>
                                     Some (Value (combine_c cir cir',sn'',r'',es''))
                                     | _ => Some Error
                                  end
                                     | _ => Some Error
                               end
            end in trans_while (Store.add (L x,0) (nat2fb 0) r) sn (empty_estore) (a_nat2fb t2v size)
            | _ => Some Error

       end

           | qinv x => 
                 do vx <- par_find_var_check smap bv size r x @
                    match vx with Value vx' => 
                        do exps <- Store.find vx' es @
                             do exp <- hd_error exps @ Some (Value (Some (inv_pexp exp),sn,r,Store.add vx' (tl exps) es))
                           | _ => Some Error
                    end

           | call f x => match lookup_fmap fv f with None => None
                       | Some (u,e',smap',vmap',bv',r') => 
                  do vuv <- par_find_var_check smap' bv' size r' u @
                   match vuv with Value vu =>
                    do t <- BEnv.find (fst vu) bv' @
                      do vxv <- par_find_var_check smap bv size r x @
                       match vxv with Value vx => 
                         do t' <- BEnv.find (fst vx) bv @
                         if (is_q t') && (is_q t) then
                            do exps <- Store.find vx es @
                             Some (Value (Some (e';; Exp (copyto (vmap' vu) (vmap vx) (get_size size (get_ct t)));; inv_pexp e'),sn,r,
                               Store.add vx ((e';; Exp (copyto (vmap' vu) (vmap vx) (get_size size (get_ct t)));; inv_pexp e')::exps) es))
                         else if (is_q t') && (is_c t) then
                            do exps <- Store.find vx es @
                             do uv <- Store.find vu r' @
                             Some (Value (Some (Exp (init_v (get_size size (get_ct t)) (vmap vx) uv)),sn,r,
                               Store.add vx ((Exp (init_v (get_size size (get_ct t)) (vmap vx) uv))::exps) es))
                         else do uv <- Store.find vu r' @ 
                               do xv <- Store.find vx r @  Some (Value (None,sn,Store.add vx xv r,es))
                      | _ => Some Error end
                   | _ => Some Error end
                        end


           | qif ce e1 e2 => do ce_val <- compile_cexp size smap vmap bv fl r temp stack sn ce @
                 match ce_val with Value (cir,sn',Some true) => 
                   trans_qexp size smap vmap bv fl r temp stack sn' fv es e1
                      | Value (cir,sn',Some false) => 
                   trans_qexp size smap vmap bv fl r temp stack sn' fv es e2
                | Value (Some cir,sn',_) => 
                 do e1_val <- trans_qexp size smap vmap bv fl r temp stack sn' fv empty_estore e1 @
                   match e1_val with Value (e1_cir,sn1,r1,es1)  =>
                  do e2_val <- trans_qexp size smap vmap bv fl r1 temp stack sn1 fv empty_estore e2 @
                   match e2_val with Value (e2_cir,sn2,r2,es2) => 
                           Some (Value (combine_if stack sn cir e1_cir e2_cir,sn2,r2,es))
                         | _ => Some Error
                    end
                    | _ => Some Error
                  end
                | _ => Some Error
                 end

           | init x v => if ¬ (qvar_eq bv size r x v) then init_c size smap vmap bv r sn es x v else Some Error


           | slrot x => lrot_c size smap vmap bv r sn es x

           | qxor x y => if ¬ (qvar_eq bv size r x y) then init_c size smap vmap bv r sn es x y else Some Error

           | nadd x y => if ¬ (qvar_eq bv size r x y) then
                      (nadd_c size smap vmap bv fl r temp stack sn es x y) else Some Error

           | nsub x y => if ¬ (qvar_eq bv size r x y) then
                      (nsub_c size smap vmap bv fl r temp stack sn es x y) else Some Error

           | nmul x y z => if ¬ (qvar_eq bv size r x z) && ¬ (qvar_eq bv size r y z) then
                     nqmul_c size smap vmap bv fl r temp stack sn es x y z
                  else Some Error

           | fadd x y => if ¬ (qvar_eq bv size r x y) then
                      (fadd_c size smap vmap bv fl r temp stack sn es x y) else Some Error

           | fsub x y => if ¬ (qvar_eq bv size r x y) then
                      (fsub_c size smap vmap bv fl r temp stack sn es x y) else Some Error

           | fmul x y z => if ¬ (qvar_eq bv size r x z) && ¬ (qvar_eq bv size r y z) then
                     fmul_c size smap vmap bv fl r temp stack sn es x y z
                  else Some Error

           | skip => Some (Value (None,sn,r,es))


           | ndiv x y n => do t2v <- par_eval_cfac_check smap bv size r Nat y @
                             do t3v <- par_eval_cfac_check smap bv size r Nat n @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx' (nat2fb ((a_nat2fb t2v' size) / (a_nat2fb t3v' size))) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end


           | nmod x y n => do t2v <- par_eval_cfac_check smap bv size r Nat y @
                             do t3v <- par_eval_cfac_check smap bv size r Nat n @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx' (nat2fb ((a_nat2fb t2v' size) mod (a_nat2fb t3v' size))) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end

           | nfac x n =>  do t3v <- par_eval_cfac_check smap bv size r Nat n @
                              do vx <- par_find_var_check smap bv size r x @
                      match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value (None,sn,Store.add vx' (nat2fb (fact (a_nat2fb t3v' size))) r,es))
                        | _ => Some Error end | _ => Some Error end

           | fdiv x n =>  do t3v <- par_eval_cfac_check smap bv size r Nat n @
                              do vx <- par_find_var_check smap bv size r x @
                      match t3v with Value t3v' => match vx with Value vx' =>
                       do txv <- Store.find vx' r @
                               Some (Value (None,sn,Store.add vx' 
                            (nat2fb (((a_nat2fb txv size) * 2^size) / (a_nat2fb t3v' size))) r,es))
                        | _ => Some Error end | _ => Some Error end

           | ncadd x y n => do t2v <- par_eval_cfac_check smap bv size r Nat y @
                             do t3v <- par_eval_cfac_check smap bv size r Nat n @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx' (nat2fb (((a_nat2fb t2v' size) + (a_nat2fb t3v' size)) mod 2^size)) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end

           | ncsub x y n => do t2v <- par_eval_cfac_check smap bv size r Nat y @
                             do t3v <- par_eval_cfac_check smap bv size r Nat n @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx' (nat2fb (((a_nat2fb t2v' size) - (a_nat2fb t3v' size)) mod 2^size)) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end

           | fcadd x y n => do t2v <- par_eval_cfac_check smap bv size r FixedP y @
                             do t3v <- par_eval_cfac_check smap bv size r FixedP n @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx'
                          (fbrev size (nat2fb (((a_nat2fb (fbrev size t2v') size) + (a_nat2fb (fbrev size t3v') size)) mod 2^size))) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end

           | fcsub x y n => do t2v <- par_eval_cfac_check smap bv size r FixedP y @
                             do t3v <- par_eval_cfac_check smap bv size r FixedP n @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx'
                          (fbrev size (nat2fb (((a_nat2fb (fbrev size t2v') size) - (a_nat2fb (fbrev size t3v') size)) mod 2^size))) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end

           | ncmul x y n => do t2v <- par_eval_cfac_check smap bv size r Nat y @
                             do t3v <- par_eval_cfac_check smap bv size r Nat n @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx' (nat2fb (((a_nat2fb t2v' size) * (a_nat2fb t3v' size)) mod 2^size)) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end

           | fndiv x y n => do t2v <- par_eval_cfac_check smap bv size r Nat y @
                             do t3v <- par_eval_cfac_check smap bv size r Nat n @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx' (nat2fb ((((a_nat2fb t2v' size) * 2^size)
                                      / (a_nat2fb t3v' size)) mod 2^size)) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end

           | qseq e1 e2 => match trans_qexp size smap vmap bv fl r temp stack sn fv es e1 with None => None
                    | Some (Value ( e1',sn1,store1,es1)) => 
                     match trans_qexp size smap vmap bv fl store1 temp stack sn1 fv es1 e2 with None => None
                      | Some (Value ( e2',sn2,store2,es2)) => Some (Value (combine_seq e1' e2',sn2,store2,es2))
                      | _ => Some Error
                     end
                     | _ => Some Error
                 end
 end.

(*
Definition stack (l:list (btype * var * nat)) : var :=
           let (al,_) := split l in let (_,bl) := split al in S(list_max bl).
*)
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


Fixpoint gen_vmap_l (l:list (typ * var))  (vmap: (qvar*nat) -> var) (i:nat) :=
         match l with [] => vmap
              | ((t,x)::xl) => if is_q t then gen_vmap_l xl (gen_vmap_n vmap (L x) i (get_type_num t)) (i+(get_type_num t))
                               else gen_vmap_l xl vmap i
         end.

Fixpoint gen_vmap_n_l (vmaps: list ((qvar*nat) * var))  (x:qvar) (i:nat) (n:nat) :=
   match n with 0 => vmaps
          | S m =>  (((x,m),i+m)::(gen_vmap_n_l vmaps x i m))
   end.

Fixpoint gen_vmap_ll (l:list (typ * var))  (vmaps: list ((qvar*nat) * var)) (i:nat) :=
         match l with [] => (vmaps,i)
              | ((t,x)::xl) => if is_q t then gen_vmap_ll xl (gen_vmap_n_l vmaps (L x) i (get_type_num t)) (i+(get_type_num t))
                                else gen_vmap_ll xl vmaps i
         end.

Fixpoint init_cstore_n (r:cstore) (x:qvar) (n:nat) : cstore :=
   match n with 0 => r
          | S m => Store.add (x,m) ((nat2fb 0)) (init_cstore_n r x m)
   end.

Fixpoint init_cstore (r:cstore) (l:list (typ * var)) : cstore  :=
   match l with [] => r
             | ((t,x)::xl) => init_cstore (init_cstore_n r (L x) (get_type_num t)) xl
   end.

(*
trans_qexp (sl size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (r:store) (temp stack:var) (sn:nat) (fv:fmap) (e:qexp)

Definition func : Type := ( fvar * list (typ * var) * qexp * cfac).
Fixpoint trans_qexp (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (fl:flag) (r:cstore) (temp stack:var)
                  (sn:nat) (fv:fmap) (es:estore) (e:qexp) : option (@value (option pexp * nat * cstore * estore)) :=

Definition fmap :Type := list (fvar * cfac * pexp * (qvar -> nat) * ((qvar*nat) -> var) * benv * cstore).

*) 

Fixpoint trans_funs (fv:fenv) (size sn:nat) (temp stack:var) (fl:flag) (r:cstore)
                  (smap: qvar -> nat) (vmap : (qvar*nat) -> var) 
            (vmaps: list ((qvar *nat)*var)) (vmap_num:nat) (fmap:fmap) (l:list func) :=
    match l with [] => Some (Value (vmaps , sn, fmap))
            | (( f , ls , e , rx)::xl) =>
                 match FEnv.find f fv with None => None
                           | Some (ls',e',bv,rx') => 
                    match trans_qexp size 
                   (gen_smap_l ls smap) (gen_vmap_l ls vmap vmap_num)
                     bv fl (init_cstore r (ls)) temp stack 0 fmap empty_estore e
                    with None => None
                    | Some Error => Some Error
                    | Some (Value (None,sn1,store1,es)) => 
         trans_funs fv size sn temp stack fl r smap vmap vmaps vmap_num ((f,rx,Exp (SKIP ((stack),0)), (gen_smap_l ls smap),
                              (gen_vmap_l ls vmap vmap_num),bv,store1)::fmap) xl
                  | Some (Value (Some e1,sn1,store1,es)) =>
        match gen_vmap_ll ls vmaps vmap_num with (vmaps',vmap_num') =>
         trans_funs fv size (Nat.max sn sn1) temp stack fl r smap (gen_vmap_l ls vmap vmap_num)
                 vmaps' vmap_num' ((f,rx,Exp (SKIP ((stack),0)), (gen_smap_l ls smap),
                              (gen_vmap_l ls vmap vmap_num),bv,store1)::fmap) xl
        end

                    end
                 end
     end.

Fixpoint gen_vmap_g' (l:list (typ * var)) (vmap:(qvar*nat) -> var) (i:nat) :=
         match l with [] => (vmap,i)
              | ((t,x)::xl) => gen_vmap_g' xl (gen_vmap_n vmap (G x) i (get_type_num t)) (i+(get_type_num t))
         end.
Definition gen_vmap_g (l:list (typ * var)) := gen_vmap_g' l (fun _ => 0) 2.

Definition temp : var := 0.
Definition stack : var := 1.

Fixpoint gen_vmap_gl' (l:list (typ * var))  (vmaps: list ((qvar*nat) * var)) (i:nat) :=
         match l with [] => vmaps
              | ((t,x)::xl) => gen_vmap_gl' xl (gen_vmap_n_l vmaps (L x) i (get_type_num t)) (i+(get_type_num t))
         end.
Definition gen_vmap_gl (l:list (typ * var)) := gen_vmap_gl' l ([]) 2.

(*
Definition prog : Type := (nat * list (typ * var) * list func * fvar * var). 

Fixpoint trans_funs (fv:fenv) (size:nat) (temp stack:var) (fl:flag) (r:cstore)
                  (smap: qvar -> nat) (vmap : (qvar*nat) -> var) (vmaps: list ((qvar *nat)*var)) (vmap_num:nat) (fmap:fmap) (l:list func) :=
*)

Definition trans_prog' (p:prog) (flag:flag) (fv:fenv) :=
   match p with (size,ls,fl,f,rx') =>
     let (vmap,vmap_num) := gen_vmap_g ls in
      do v <- (trans_funs fv size 0 temp stack flag empty_cstore (gen_smap_l ls (fun _ => 0))
            vmap (gen_vmap_gl ls) vmap_num ([]) fl) @
       match v with Error => Some Error
               | (Value (vmaps,sn,fmap)) => 
         match lookup_fmap fmap f with None => None
            | Some (rx,p,smap,vmap',bv,r) => 
               do vx <- par_find_var_check smap bv size r rx @
               match vx with Value vx' => 
                do t <- BEnv.find (fst vx') bv @ 
               if is_q t then 
                    Some (Value (vmaps,size,sn,p;;Exp 
                         (copyto (vmap' vx') (vmap ((G rx'),0)) (get_size size (get_ct t)))))
                else do vxv <- Store.find vx' r @
                    Some (Value (([((G rx',0),vmap (G rx',0))]),size,sn,Exp (init_v (get_size size (get_ct t)) (vmap (G rx',0)) vxv)))
                   | _ => Some Error
               end
        end
    end
   end.

Definition trans_prog (p:prog) (f:flag) :=
   match type_prog p with None => None | Some fv => trans_prog' p f fv end.

Fixpoint gen_vars_vmap' (vmaps: list ((qvar * nat) * var)) (size:nat) (i:nat) :=
  match vmaps with [] => ((fun _ => (0,0,id_nat,id_nat)),i)
           | ((x,y)::l) => match gen_vars_vmap' l size i with (vars,m) =>
                   ((fun a => if a =? y then (m,size,id_nat,id_nat) else vars a),m+size)
                           end
  end.
Definition gen_vars_vmap (vmaps: list ((qvar * nat) * var)) (size:nat) (sn:nat) : (vars * nat) :=
       match gen_vars_vmap' vmaps size 0 with (vars,i) => 
           ((fun x => if x =? stack then (i+size,S sn,id_nat,id_nat) else 
                      if x =? temp then (i,size,id_nat,id_nat)
                     else vars x),i+size+(S sn))
       end.

Definition avs_gen (size:nat) (length : nat) : nat -> posi := 
              fun x => (x / size, if (x/size) <? length+1 then x mod size else x - (x/size * (length+1))).


Definition prog_to_sqir (p:prog) (f:flag) : option (nat * nat * pexp * vars * (nat -> posi)) :=
   match trans_prog p f with Some (Value (vmaps,size,sn,p)) => 
          match gen_vars_vmap vmaps size sn with (vars,d) => 
             match avs_gen size (length vmaps) with avs =>
                 Some (d,size,p,vars,avs)
             end
          end
        | _ => None 
   end.

Check prog_to_sqir.

Check trans_pexp.

(*
Definition prog_to_sqir_real (p:prog) (f:flag) :=
  match prog_to_sqir p f with Some (d,size,p,vars,avs) => (fst (trans_pexp vars d p avs))
                  None => ?
  end
*)         



