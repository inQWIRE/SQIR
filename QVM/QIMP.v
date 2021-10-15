Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
Require Import PQASM.
Require Import CLArith.
Require Import RZArith.

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.

(* The definition of QSSA. *)
Local Open Scope exp_scope.
Local Open Scope nat_scope.

(* Define function variables. *)
Definition fvar := nat.


(* Flag for setting if one wants to generate QFT circuit or classical circuit. *)
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

(* Global and local variables are different like @x and %x in LLVM. *)
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

(* Variables can be C or Q mode. Q stands for quantum variables, while C stands for constants. *)
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

(* A type for a variable in a program can be an Array type or a single value type. *)
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

Inductive qop := nadd | nsub | nmul | fadd | fsub | fmul | qxor | ndiv | nmod | nfac | fdiv
                  | fndiv.

Definition qop_eq  (t1 t2:qop) : bool := 
   match (t1,t2) with (nadd,nadd) => true
                    | (nsub,nsub) => true
                    | (nmul,nmul) => true
                    | (fadd,fadd) => true
                    | (fsub,fsub) => true
                    | (fmul,fmul) => true
                    | (qxor,qxor) => true
                    | (ndiv,ndiv) => true
                    | (nmod,nmod) => true
                    | (nfac,nfac) => true
                    | (fdiv,fdiv) => true
                    | (fndiv,fndiv) => true
                    | _ => false
   end.

Notation "i '=op=' j" := (qop_eq i j) (at level 50).

Lemma qop_eqb_eq : forall a b, a =op= b = true -> a = b.
Proof.
 intros. unfold qop_eq in H.
 destruct a. destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
Qed.

Lemma qop_eqb_neq : forall a b, a =op= b = false -> a <> b.
Proof.
 intros. unfold qop_eq in H.
 destruct a. destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
 destruct b. 1-12:easy.
Qed.

Lemma qop_eq_reflect : forall r1 r2, reflect (r1 = r2) (qop_eq r1 r2). 
Proof.
  intros.
  destruct (r1 =op= r2) eqn:eq1.
  apply  ReflectT.
  apply qop_eqb_eq in eq1.
  assumption. 
  constructor. 
  apply qop_eqb_neq in eq1.
  assumption. 
Qed.

Hint Resolve flag_eq_reflect aty_eq_reflect qty_eq_reflect qdty_eq_reflect bty_eq_reflect typ_eq_reflect qop_eq_reflect : bdestruct.

(* Make maps in Coq. *)
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


(* Basic element is a Var or a number. Number is represented as bitstring. *)
Inductive factor := Var (v:qvar)
                 | Num (t:btype) (n:nat -> bool).
     (* the first m in Num represents the number of bits.
      a value is represented as a natural number x. it means x / 2^m where m is the number of denominator. *)

Inductive cfac := Index (x:qvar) (v:factor) | Nor (v:factor).


(* qadd/qsub/qmul has the property as x = y op x, which is corresponding to
   [y][x] -> [y][y op x] structure.
   for qadd/qsub, x and y are both float numbers. For mult, x is a natural number while y is a float.
   for comparator operations, both are floats. *)

Inductive cexp := clt (x:cfac) (y:cfac)
                  | ceq (x:cfac) (y:cfac)
                  | iseven (x:cfac).


(*x := y/n where x,n are a nat *)
(* x := y mod n where x,n are a nat *)
(* x := n! where x is a nat & n is  nat *)
(* x := x / n where n is a natural number, x is a float. *)
(* x := y - z all natural and C type *)
(* x := y + z all natural and C type *)
(* x := y - z all natural and C type *)
(* x := y + z all natural and C type *)
(* x := y * z all natural and C type *)
(* z = x/v where x and v are natural numbers, z is float
                           x and v are both integers, but the final result in z must be a float < 1 *)

Inductive qexp :=
                  qinv (x:cfac)
                | call (v:cfac) (f:fvar) (args: list cfac)
                | qif (c:cexp) (e1:qexp) (e2:qexp)
                | qfor (x:var) (n:cfac) (e:qexp)
                | qseq (q1:qexp) (q2:qexp)
                | skip
                | init (x:cfac) (v:cfac)
                | slrot (x:cfac) (* static rotation. *)
                | unary (x:cfac) (aop:qop) (v:cfac) 
                | binapp (x:cfac) (aop:qop) (v1:cfac) (v2:cfac).

(*functions will do automatic inverse computation after a function is returned.
  for each ret statement, there is a list of pairs of vars, and the left one is the global variables to return,
   while the left one is the local variables. after a function call is returned,
    it will store all the local variables to their correponding global variables, and then reverse the computation.  *)

Notation "p1 ;; p2" := (qseq p1 p2) (at level 50) : exp_scope.

Definition func : Type := ( fvar * list (atype * btype * var) * list (typ * var) * qexp * cfac).
    (* a function is a fun name, a starting block label, and a list of blocks, and the returned variable. *)

Definition prog : Type := (nat * list (typ * var) * list func * fvar * var). 
   (* a number of bits in FixedP and Nat
          and a list of global vars, and a list of functions.
     and the main function to call, and the final global var to write to. *)


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

(*Function map consists with an argument list, an expression, a type environment for function body and return type. *)
Module FEnv := FMapList.Make Nat_as_OT.
Module FEnvFacts := FMapFacts.Facts (FEnv).
Definition fenv := FEnv.t (list (atype * btype * var) * list (typ * var) * qexp * benv * cfac).
Definition fenv_empty := @FEnv.empty (list (atype * btype * var) * list (typ * var) * qexp * benv * cfac).

Definition bind {A B} (a : option A) f : option B := 
  match a with None => None | Some a => f a end.
Definition ret {A} (a : A) := Some a.
Notation "'do' X '<-' A '@' B" := (bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).

Definition typ_factor (bv:benv) (fc:factor) :=
   match fc with Var x => do re <- BEnv.find x bv @
    match re with TArray x y n => None
            | TNor x y => Some (x,y)
   end
            | Num t n => Some (C,t)
  end.

Definition typ_factor_full (bv:benv) (a:atype) (b:btype) (fc:factor) :=
   match fc with Var x => do re <- BEnv.find x bv @
    match re with TArray x y n => None
            | TNor x y => if (a =a= x) && (y =b= b) then Some (x,y) else None
   end
            | Num t n => if (a =a= C) && (b =b= t) then Some (C,t) else None
  end.

Definition type_factor (bv:benv) (fc:cfac) :=
   match fc with Index x ic =>
       do re <- BEnv.find x bv @ 
             match re with TArray a b n =>
                       do ta <- typ_factor_full bv C Nat ic @ Some (a,b)
                    | TNor x y => None
             end
               | Nor c => typ_factor bv c
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

(* C \subseteq Q *)
Definition meet_atype (a1 a2: atype) := 
       match a1 with Q => Q | C => a2 end.

Definition meet_btype (b1 b2: btype) := 
             if b1 =b= b2 then Some b1 else None.

Definition meet_type (t1 t2 : (atype * btype)) := 
          match t1 with (a1,b1) =>
            match  t2 with (a2,b2) => 
                do bty <- meet_btype b1 b2 @ ret (meet_atype a1 a2, bty)
            end
          end.


Definition type_cexp (benv:benv) (c:cexp) := 
   match c with clt x y => 
             do re1 <- type_factor benv x @
                do re2 <- type_factor benv y @ (meet_type re1 re2)
            | ceq x y => 
             do re1 <- type_factor benv x @
                do re2 <- type_factor benv y @ (meet_type re1 re2)
            | iseven x => type_factor_full benv C Nat x
   end.
(*
a_nat2fb is to turn a nat-> bool value to nat. 
*)

Definition a_nat2fb f n := natsum n (fun i => Nat.b2n (f i) * 2^i).

Lemma a_nat2fb_scope : forall n f, a_nat2fb f n < 2^n.
Proof.
  induction n;intros;simpl.
  unfold a_nat2fb. simpl. lia.
  specialize (IHn f).
  unfold a_nat2fb in *. simpl.
  destruct (f n). simpl. lia.
  simpl. lia.
Qed.

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
             | Nor (Num b x) => None
             | Index x y => Some x
   end.

Definition get_index (c:cfac) : option factor :=
   match c with Nor x => None
           | Index x y => Some y
   end.


Definition get_ct (c:typ) :=
   match c with TArray x y n => y
              | TNor x y => y
   end.

(*The semantics of QLLVM.
   A store is impelemented as a a list of history values, and the top in the list is the current value.
   We kept history values to do inv. *)
Module Store := FMapList.Make QvarNatType.
Module StoreFacts := FMapFacts.Facts (Store).
Definition store : Type := Store.t (list (nat -> bool)).
Definition empty_store := @Store.empty (list (nat -> bool)).

Inductive value {A:Type} := Value (x:A) | Error.

Definition sem_factor (size:nat) (r:store) (fc:factor) := 
   match fc with Var x => do vals <- (Store.find (x,0) r) @ (hd_error vals)
            | Num b n => if b =b= Bl then Some ( (cut_n n 1))
                         else if b =b= Nat then Some (  (cut_n n size))
                          else Some (fbrev size (cut_n n size))
   end.

Definition sem_cfac (smap:qvar -> nat) (size:nat) (store:store) (fc:cfac)
 : option (@value (nat -> bool)) :=
    match fc with Index x n => do v <- (sem_factor size store n) @
                          if (a_nat2fb v size) <? smap x then
                               do l <- Store.find (x,a_nat2fb v size) store @
                                   do val <- (hd_error l) @ Some (Value val)
                          else Some Error
               | Nor x => do val <- sem_factor size store x @ Some (Value val)
    end.

Definition get_size (size:nat) (t:btype) := if t =b= Bl then 1 else size.

Definition sem_cexp (smap:qvar -> nat) (bv:benv) (size:nat) (store:store) (ce:cexp) : option (@value bool) :=
           match ce with clt x y => 
            do t <- type_factor bv x @
            do v1 <- (sem_cfac smap size store x) @
            do v2 <- (sem_cfac smap size store y) @
            match v1 with (Value v1') => 
             match v2 with (Value v2') => 
                     Some 
                      (Value (a_nat2fb v1' (get_size size (snd t)) <? a_nat2fb v2' (get_size size (snd t))))
                | _ => Some Error
                 end
            | _ => Some Error
            end
          | ceq x y => 
            do t <- type_factor bv x @
            do v1 <- (sem_cfac smap size store x) @
            do v2 <- (sem_cfac smap size store y) @
            match v1 with (Value v1') => 
             match v2 with (Value v2') =>
                  Some (Value (a_nat2fb v1' (get_size size (snd t)) =? a_nat2fb v2' (get_size size (snd t))))
                | _ => Some Error
                 end
            | _ => Some Error
            end
         | iseven x =>
           do t <- type_factor bv x @
            do v1 <- (sem_cfac smap size store x) @ 
              match v1 with Value v1' => 
                   Some (Value ((a_nat2fb v1' (get_size size (snd t))) mod 2 =? 0)) 
                          | _ => Some Error
              end
          end.

Definition bv_store_sub (smap : qvar -> nat) (bv:benv) (st:store) :=
         forall x i, BEnv.In x bv -> i < smap x -> (exists v, Store.MapsTo (x,i) v st /\ length v > 0).

Definition bv_store_gt_0 (smap : qvar -> nat) (bv:benv) :=
         forall x, BEnv.In x bv -> 0 < smap x.


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

Fixpoint init_store_args (r:store) (l:list (atype * btype * var)) (vl: list (nat -> bool)) : option store  :=
   match l with [] => Some r
             | ((a,b,x)::xl) => 
          match vl with [] => None
                 | (v::vl') => init_store_args (Store.add (L x,0) ([v]) r) xl vl'
          end
   end.

Fixpoint init_store (r:store) (l:list (typ * var)) : option store  :=
   match l with [] => Some r
             | ((t,x)::xl) => if get_type_num t =? 0 then None else 
                   do new_store <- init_store r xl @
                             ret (init_store_n new_store (L x) (get_type_num t))
   end.

Fixpoint gen_smap_args (l:list (atype * btype * var)) (smap: qvar -> nat)  :=
  match l with [] => smap
      | ((a,b,x)::xl) => match gen_smap_args xl smap with new_map => 
                      (qupdate new_map (L x) 1) end
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

Definition no_zero (t:typ) := match t with TArray x y n => if n =? 0 then false else true 
                | TNor x y => true 
     end.

Fixpoint gen_env (l:list (typ * var)) (bv:benv) : option benv := 
   match l with [] => Some bv
             | ((t,x)::xl) => 
                  do new_env <- gen_env xl bv @
                    if no_zero t then Some (BEnv.add (L x) t new_env) else None
   end.

Fixpoint gen_env_l (l:list (atype * btype * var)) (bv:benv) : option benv := 
   match l with [] => Some bv
             | ((a,t,x)::xl) => 
                  do new_env <- gen_env_l xl bv @ Some (BEnv.add (L x) (TNor a t) new_env)
   end.

Fixpoint gen_genv (l:list (typ * var)) : option benv := 
   match l with [] => Some empty_benv
             | ((t,x)::xl) => 
                  do new_env <- gen_genv xl @
                   if no_zero t then Some (BEnv.add (G x) t new_env) else None
   end.

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

(* When compiling scrath space, we genearte two extra for ancilla qubits in addition.  *)
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

(* cstore is to store the current value for C-mode variables/constants. *)
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
      match b with Bl => Some ((cut_n cv 1))
                | Nat => Some ((cut_n cv size))
                | FixedP => Some ((fbrev size (cut_n cv size)))
      end.

(* Partially evaluate a factor by cstore. *)
Definition par_eval_fc (bv:benv) (size:nat) (r:cstore) (fc:factor) := 
   match fc with Var x => do re <- BEnv.find x bv @ if is_q re then None else (Store.find (x,0) r)
            | Num t n => make_value size t (Some n)
   end.

Definition make_value_t (size:nat) (b:btype) (c: option (nat -> bool)) :=
  do cv <- c @
      match b with Bl => Some (Value (cut_n cv 1))
                | Nat => Some (Value (cut_n cv size))
                | FixedP => Some (Value (fbrev size (cut_n cv size)))
      end.

(* Partially evaluate a factor. *)
Definition par_eval_cfac (smap : qvar -> nat) (bv:benv) (size:nat) (r:cstore) (fc:cfac) := 
   match fc with Nor x => do v <- par_eval_fc bv size r x @ Some (Value v)
        | Index x n => do v <- par_eval_fc bv size r n @
                              if a_nat2fb v size <? smap x then
                               (do re <- BEnv.find x bv @ if is_q re then None
                      else do val <- (Store.find (x,a_nat2fb v size) r) @ Some (Value val)) else None
   end.

(* Partially evaluate a factor but also checks array index. *)
Definition par_eval_cfac_check (smap : qvar -> nat) (bv:benv) (size:nat) (r:cstore) (fc:cfac) := 
   match fc with Nor x => do val <- par_eval_fc bv size r x @ Some (Value val)
        | Index x n => do v <- par_eval_fc bv size r n @
                              if a_nat2fb v size <? smap x then
                               (do re <- BEnv.find x bv @ if is_q re then None else 
                  do val <- (Store.find (x,a_nat2fb v size) r) @ Some (Value val)) else Some Error
   end.

(* Partially find an indexed-variable.
   Every variable has the form (x,n) where x is the variable and n is the indexed.
   For Nor variable, n is always 0. *)
Definition par_find_var (bv:benv) (size:nat)  (r:cstore) (fc:cfac) :=
       match fc with Nor (Var x) => Some (x,0)
                  | Nor (Num t x) => None
                  | Index x n => do val <- par_eval_fc bv size r n @ Some (x,a_nat2fb val size)
       end.

(* Partially find an indexed-variable with array bound checks. *)
Definition par_find_var_check (smap:qvar -> nat) (bv:benv) (size:nat)  (r:cstore) (fc:cfac) :=
       match fc with Nor (Var x) => Some (Value (x,0))
                  | Nor (Num t x) => None
                  | Index x n => do val <- par_eval_fc bv size r n @
                      if a_nat2fb val size <? smap x then Some (Value (x,a_nat2fb val size)) else Some Error
       end.

(* Check if two variables are equal *)
Definition qvar_eq (smap:qvar -> nat) (bv:benv) (size:nat)  (r:cstore) (x y: cfac) := 
        match par_find_var_check smap bv size r x with None => None
                    | Some Error => Some Error
                    | Some (Value a) => match par_find_var_check smap bv size r y with None => None
                         | Some Error => Some Error
                         | Some (Value b) => Some (Value (a =qd= b))
                                end
        end.

(* Circuit generation for <. *)
Definition clt_circuit_two (size:nat) (f:flag) (b:btype) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (stack: var) (sn:nat) :=
            if f =fl= Classic then
              (comparator01 (get_size size b) (vmap y) (vmap x) (stack,S sn) (stack, sn))
            else (comparator01 (get_size size b) (vmap y) (vmap x) (stack,S sn) (stack, sn)).


Definition clt_circuit_left (size:nat) (f:flag) (b:btype) (vmap:(qvar*nat) -> var)
                        (x :(qvar*nat)) (y:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
              (init_v (get_size size b) (temp) y;
                    comparator01 (get_size size b) (temp) (vmap x) (stack,S sn) (stack, sn);
                    inv_exp (init_v (get_size size b) (temp) y))
            else (init_v (get_size size b) (temp) y;
                    comparator01 (get_size size b) temp (vmap x) (stack,S sn) (stack, sn);
                    inv_exp (init_v (get_size size b) (temp) y)).

Definition clt_circuit_right (size:nat) (f:flag) (b:btype) (vmap:(qvar*nat) -> var)
                        (x:(nat->bool)) (y :(qvar*nat))  (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
               (init_v (get_size size b) (temp) x;
                    comparator01 (get_size size b) (vmap y) temp (stack,S sn) (stack, sn);
                    inv_exp (init_v (get_size size b) (temp) x))
            else (init_v (get_size size b) (temp) x;
                    comparator01 (get_size size b) (vmap y) temp (stack,S sn) (stack, sn);
                    inv_exp (init_v (get_size size b) (temp) x)).

(* Different cases in < *)
Definition gen_clt_c (smap : qvar -> nat) (vmap: (qvar*nat) -> var)  (bv:benv) (size:nat)  (f:flag)
                (r:cstore) (stack temp:var) (sn:nat) (x y: cfac)
                                      : option (@value (option exp * nat * option bool)) := 
     do t1 <- type_factor bv x @
         do t2 <- type_factor bv y @
            if (fst t1 =a= Q) && (fst t2 =a= C) then
               match par_find_var_check smap bv size r x with Some (Value vx) =>
                   do t2v <- par_eval_cfac_check smap bv size r y @
                     match t2v with Value t2v' =>
                      Some (Value (Some (clt_circuit_left size f (snd t1) vmap vx t2v' stack temp sn),S sn,None))
                        | _ => Some Error
                     end
                   | None => None
                   | a => Some Error
               end
           else if (fst t1 =a= Q) && (fst t2 =a= Q) then
              do vxv <- par_find_var_check smap bv size r x @
                do vyv <- par_find_var_check smap bv size r y @
                 match vxv with Value vx => match vyv with Value vy => 
                    Some (Value (Some (clt_circuit_two size f (snd t1) vmap vx vy stack sn),S sn,None))
                              | _ => Some Error
                       end
                   | _ => Some Error
                 end
           else if (fst t1 =a= C) && (fst t2 =a= Q) then
               match par_find_var_check smap bv size r y with Some (Value vy) =>
                   do t1v <- par_eval_cfac_check smap bv size r x @
                    match t1v with Value t1v' =>
                      Some (Value (Some (clt_circuit_right size f (snd t1) vmap t1v' vy stack temp sn),S sn,None))
                      | _ => Some Error
                    end
                   | None => None
                   | a => Some Error
               end
          else  do t1v <- par_eval_cfac_check smap bv size r x @
                   do t2v <- par_eval_cfac_check smap bv size r y @ 
                    match t1v with Value t1v' => match t2v with Value t2v' =>
                      Some (Value (None, sn, Some ((a_nat2fb t1v' (get_size size (snd t1)) <? a_nat2fb t2v' (get_size size (snd t2))))))
                       | _ => Some Error end | _ => Some Error
                    end.

(* compare x =? y *)
Definition ceq_circuit_two (size:nat) (f:flag) (b:btype) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (stack: var) (sn:nat) :=
           if f =fl= Classic then
                        (comparator01 (get_size size b) (vmap y) (vmap x) (stack,S sn)
                                    (stack,sn); 
                        comparator01 (get_size size b) (vmap x) (vmap y) (stack,S sn)
                                    (stack,sn); X (stack,sn))
                 else (comparator01 (get_size size b) (vmap y) (vmap x) (stack,S sn)
                                    (stack,sn); 
                        comparator01 (get_size size b) (vmap x) (vmap y) (stack,S sn)
                                    (stack,sn); X (stack,sn)).

Definition ceq_circuit_left (size:nat) (f:flag) (b:btype) (vmap:(qvar*nat) -> var)
                        (x :(qvar*nat)) (y:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
               (init_v (get_size size b) (temp) y;
                    comparator01 (get_size size b) (vmap x) (temp) (stack,S sn) (stack, sn);
                    comparator01 (get_size size b) (temp) (vmap x) (stack,S sn) (stack, sn);
                    (X (stack,sn));
                    inv_exp (init_v (get_size size b) (temp) y))
            else (init_v (get_size size b) (temp) y;
                    comparator01 (get_size size b) (vmap x) (temp) (stack,S sn) (stack, sn);
                    comparator01 (get_size size b) (temp) (vmap x) (stack,S sn) (stack, sn);
                    (X (stack,sn));
                    inv_exp (init_v (get_size size b) (temp) y)).

Definition ceq_circuit_right (size:nat) (f:flag) (b:btype) (vmap:(qvar*nat) -> var)
                        (x:(nat->bool)) (y :(qvar*nat))  (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
               (init_v (get_size size b) (temp) x;
                    comparator01 (get_size size b) (temp) (vmap y) (stack,S sn) (stack, sn);
                    comparator01 (get_size size b) (vmap y) (temp) (stack,S sn) (stack, sn);
                    (X (stack,sn));
                    inv_exp (init_v (get_size size b) (temp) x))
            else (init_v (get_size size b) (temp) x;
                    comparator01 (get_size size b) (temp) (vmap y) (stack,S sn) (stack, sn);
                    comparator01 (get_size size b) (vmap y) (temp) (stack,S sn) (stack, sn);
                    (X (stack,sn));
                    inv_exp (init_v (get_size size b) (temp) x)).


Definition gen_ceq_c (smap : qvar -> nat) (vmap: (qvar*nat) -> var)  (bv:benv) (size:nat)  (f:flag)
                (r:cstore) (stack temp:var) (sn:nat) (x y: cfac)
                                      : option (@value (option exp * nat * option bool)) := 
     do t1 <- type_factor bv x @
         do t2 <- type_factor bv y @
            if (fst t1 =a= Q) && (fst t2 =a= C) then
               match par_find_var_check smap bv size r x with Some (Value vx) =>
                   do t2v <- par_eval_cfac_check smap bv size r y @
                    match t2v with Value t2v' =>
                      Some (Value (Some (ceq_circuit_left size f (snd t1) vmap vx t2v' stack temp sn),S sn,None))
                     | _ => Some Error
                    end
                   | None => None
                   | a => Some Error
               end
           else if (fst t1 =a= Q) && (fst t2 =a= Q) then
              do vxv <- par_find_var_check smap bv size r x @
                do vyv <- par_find_var_check smap bv size r y @
                 match vxv with Value vx => match vyv with Value vy => 
                    Some (Value (Some (ceq_circuit_two size f  (snd t1) vmap vx vy stack sn),S sn,None))
                              | _ => Some Error
                       end
                   | _ => Some Error
                 end
           else if (fst t1 =a= C) && (fst t2 =a= Q) then
               match par_find_var_check smap bv size r y with Some (Value vy) =>
                   do t1v <- par_eval_cfac_check smap bv size r x @
                    match t1v with Value t1v' =>
                      Some (Value (Some (ceq_circuit_right size f  (snd t1) vmap t1v' vy stack temp sn),S sn,None))
                     | _ => Some Error
                    end
                   | None => None
                   | a => Some Error
               end
          else  do t1v <- par_eval_cfac_check smap bv size r x @
                   do t2v <- par_eval_cfac_check smap bv size r y @ 
                     match t1v with Value t1v' => match t2v with Value t2v' =>
                      Some (Value (None, sn, Some ((a_nat2fb t1v' (get_size size (snd t1)) =? a_nat2fb t2v' (get_size size (snd t1))))))
                          | _ => Some Error end | _ => Some Error end.

(*Proofs of compilation correctness for cexp. *)

Lemma nat2fb_a_nat2fb' : forall n m f, m <= n -> (forall i, m <= i -> f i = false)
             -> nat2fb (a_nat2fb f n) = f.
Proof.
  intros.
  assert (f = cut_n f n).
  unfold cut_n.
  apply functional_extensionality.
  intros.
  bdestruct (x <? n). easy. rewrite H0. easy. lia.
  assert ((a_nat2fb f n) = (a_nat2fb (cut_n f n) n)).
  rewrite <- H1. easy. rewrite H2.
  specialize (f_num_0 f n) as eq1. destruct eq1.
  rewrite H3.
  assert ((a_nat2fb (nat2fb x) n) = bindecomp n x).
  unfold a_nat2fb, bindecomp. easy.
  rewrite H4.
  rewrite H1. rewrite H3.
  rewrite bindecomp_spec.
  rewrite <- cut_n_mod.
  rewrite <- H3.
  rewrite cut_n_twice_same. easy.
Qed.

Lemma nat2fb_a_nat2fb : forall n f, (forall i, n <= i -> f i = false)
             -> nat2fb (a_nat2fb f n) = f.
Proof.
  intros. rewrite nat2fb_a_nat2fb' with (m := n). easy. lia. easy.
Qed.

Lemma a_nat2fb_cut_n' : forall n m f, n <= m -> a_nat2fb f n = a_nat2fb (cut_n f m) n.
Proof.
  induction n; intros; unfold a_nat2fb in *; simpl. easy.
  rewrite IHn with (m := m); try lia.
  assert (f n = cut_n f m n).
  unfold cut_n. bdestruct (n <? m). easy. lia.
  rewrite <- H0. easy.
Qed.

Lemma a_nat2fb_cut_n : forall n f, nat2fb (a_nat2fb f n) = cut_n f n.
Proof.
  intros.
  rewrite a_nat2fb_cut_n' with (m := n); try easy.
  rewrite nat2fb_a_nat2fb; try easy.
  intros. unfold cut_n. bdestruct (i <? n). lia. easy.
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

(* This definition compiles conditional expressions. *)
Definition compile_cexp (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (stack temp:var) (sn:nat) (e:cexp)
                                      : option (@value (option exp * nat * option bool)) := 
   match e with clt x y => 
                   match  (qvar_eq smap bv size r x y) with None => None
                      | Some Error => Some Error
                      | Some (Value bval) => if ¬ bval then gen_clt_c smap vmap bv size f r stack temp sn x y
                                else Some (Value (None, sn, Some false))
                   end
         | ceq x y =>  match (qvar_eq smap bv size r x y) with None => None
                           | Some Error => Some Error
                        | Some (Value bval) =>  if ¬ bval then 
                                      gen_ceq_c smap vmap bv size f r stack temp sn x y
                                     else Some (Value (None, sn, Some true))
                        end
         | iseven x => do t1 <- type_factor bv x @ if fst t1 =a= Q then None else 
                           do t2v <- par_eval_cfac_check smap bv size r x @
                        match t2v with Value t2v' =>
                              if (a_nat2fb t2v' size) mod 2 =? 0 then Some (Value (None, sn, Some true))
                                        else Some (Value (None,sn,Some (false)))
                            | Error => Some Error
                        end
   end.

(* Set up theorem assumptions for cexp. *)

Definition store_typed (r:store) (bv:benv) (size:nat) : Prop :=
   forall x vl v, Store.MapsTo x vl r -> In v vl ->
           (forall i, (if is_bl (BEnv.find (fst x) bv) then 1 else size) <= i -> v i = false).

Definition store_match_q (r:store) (f:posi -> val)
           (bv:benv) (vmap : (qvar*nat) -> var) (aenv:var -> nat) : Prop := 
  forall x v vl, Store.MapsTo x (v::vl) r -> (BEnv.find (fst x) bv) <> None ->
         is_qtt (BEnv.find (fst x) bv) -> 
            get_cus (aenv (vmap x)) f (vmap x) = cut_n v (aenv (vmap x)).

Definition store_match_st (sl sn:nat) (stack:var) (f:posi -> val)
             (vmap : (qvar*nat) -> var) : Prop := 
          forall i, sn <= i -> get_cus sl f (stack) i = false.

Definition aenv_match (stack temp:var) (size:nat) (bv:benv) (aenv: var -> nat) (vmap : (qvar*nat) -> var) : Prop := 
          forall x, vmap x <> stack -> vmap x <> temp -> aenv (vmap x) = (if is_bl (BEnv.find (fst x) bv) then 1 else size).

(* Defining the equivalence relation between (cstore, circuit-run) and semantics store in QIMP. *)
Definition cstore_store_match (smap : qvar -> nat) (s:store) (r:cstore) (bv:benv) :=
       forall x i v vl t, i < smap x -> Store.MapsTo (x,i) (v::vl) s -> 
                    BEnv.MapsTo x t bv -> ~ is_qtt (Some t) -> Store.MapsTo (x,i) v r.

Lemma a_nat2fb_cut_same' : forall size m v, size <= m -> a_nat2fb (cut_n v m) size = a_nat2fb v size.
Proof.
 induction size;unfold a_nat2fb in *;intros;simpl. easy.
 simpl.
 rewrite IHsize by lia.
 unfold cut_n.
 bdestruct (size <? m). easy. lia.
Qed.

Lemma a_nat2fb_cut_same : forall size v, a_nat2fb (cut_n v size) size = a_nat2fb v size.
Proof.
 intros. rewrite a_nat2fb_cut_same' by lia. easy.
Qed.


Lemma factor_type_c : forall v b bv p, typ_factor_full bv C b v = Some p -> fst p = C.
Proof.
  intros.
  unfold typ_factor_full in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *. destruct t. inv H. destruct a.
  bdestruct (b0 =b= b). simpl in *. inv H. easy.
  simpl in *. inv H. simpl in *. inv H.
  simpl in *. inv H.
  bdestruct (C =a= C).
  bdestruct (b =b= t). simpl in *. inv H. easy.
  simpl in *. inv H. simpl in *. inv H. 
Qed.

Lemma factor_type_all : forall v a b bv p, typ_factor_full bv a b v = Some p -> p = (a,b).
Proof.
  intros.
  unfold typ_factor_full in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *. destruct t. inv H. 
  bdestruct ((a =a= a0)). subst.
  bdestruct (b0 =b= b). simpl in *. inv H. easy.
  simpl in *. inv H. simpl in *. inv H.
  simpl in *. inv H.
  bdestruct (a =a= C).
  bdestruct (b =b= t). simpl in *. inv H. easy.
  simpl in *. inv H. simpl in *. inv H. 
Qed.

Lemma cfac_type_c : forall v bv a b p, type_factor_full bv a b v = Some p -> p = (a,b).
Proof.
  intros.
  unfold type_factor_full in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
  simpl in *. destruct t.
  bdestruct (a =a= a0).
  bdestruct (b0 =b= b). simpl in *. 
  destruct (typ_factor_full bv C Nat v) eqn:eq2. subst.
  simpl in *. inv H. easy.
  easy. simpl in *. easy. simpl in *. easy. easy. easy.
  unfold typ_factor_full in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *. destruct t. easy. 
  bdestruct (a =a= a0).
  bdestruct (b0 =b= b). simpl in *.  inv H. easy.
  simpl in *. easy. easy. easy.
  bdestruct (a =a= C).
  bdestruct (b =b= t). simpl in *.  inv H. easy. easy. easy.  
Qed.

Lemma type_factor_full_same : forall v bv a b p, type_factor_full bv a b v = Some p -> type_factor bv v = Some p.
Proof.
  intros.
  unfold type_factor_full,type_factor in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
  simpl in *. destruct t.
  bdestruct (a =a= a0).
  bdestruct (b0 =b= b). simpl in *. subst. easy. 
  simpl in *. inv H. easy. easy. easy.
  unfold typ_factor_full,typ_factor in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *. destruct t. easy. 
  bdestruct (a =a= a0).
  bdestruct (b0 =b= b). subst. simpl in *. easy. easy. easy. easy.
  bdestruct (a =a= C).
  bdestruct (b =b= t). simpl in *. easy. easy. easy. 
Qed.

Definition get_var_factor (x:factor) :=
   match x with Var v => [v]
                  | Num t v => []
   end.

Definition get_var_cfac (x:cfac) :=
    match x with Index x v => (x:: get_var_factor v)
               | Nor v => get_var_factor v
    end.

Definition get_var_cexp (x:cexp) :=
   match x with clt x y => get_var_cfac x ++ get_var_cfac y
              | ceq x y => get_var_cfac x ++ get_var_cfac y
              | iseven x => get_var_cfac x
   end.

Definition not_stack (stack temp:var) (vmap : (qvar*nat) -> var) (smap:qvar -> nat) (l:list qvar)
             := forall x, In x l -> (forall i, i < smap x -> vmap (x,i) <> stack /\ vmap (x,i) <> temp).

Definition all_nor (vmap : (qvar*nat) -> var) (smap:qvar -> nat) (l:list qvar) (tenv:env)
           := forall x, In x l -> (forall i, i < smap x -> Env.MapsTo (vmap (x,i)) PQASM.Nor tenv).

Definition in_store (s:store) (smap:qvar -> nat) (l:list qvar) :=
     forall x, In x l -> (forall i, i < smap x -> Store.In (x,i) s).

Definition vmap_bij (vmap : (qvar*nat) -> var) :=
    forall x y, x <> y -> vmap x <> vmap y.

Local Opaque comparator01.

Lemma mapsto_is_in : forall type bv x y, @BEnv.MapsTo type x y bv -> @BEnv.In type x bv.
Proof.
  intros. unfold BEnv.In,BEnv.Raw.PX.In in *. exists y. easy.
Qed.

Lemma type_factor_sem_no_none : forall x t bv smap size rh, typ_factor bv x = Some t ->
     bv_store_gt_0 smap bv -> bv_store_sub smap bv rh -> sem_factor size rh x <> None.
Proof.
 intros. destruct x.
 unfold sem_factor,typ_factor in *.
 destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
 simpl in *. destruct t0. inv H. inv H.
 unfold bv_store_gt_0 in *.
 apply BEnv.find_2 in eq1.
 apply mapsto_is_in in eq1. specialize (H0 v eq1).
 unfold bv_store_sub in *.
 unfold in_store in *.
 specialize (H1 v 0 eq1 H0).
 destruct H1. destruct H.
 apply Store.find_1 in H.
 assert ((@pair BEnv.key nat v O) = (@pair qvar nat v O)) by easy.
 rewrite H2 in *. rewrite H.
 simpl.
 destruct x. simpl in *. lia.
 simpl. easy.
 simpl in *. inv H.
 simpl.
 destruct t0. simpl. easy. simpl. easy. simpl. easy.
Qed.

Lemma type_factor_full_sem_no_none : forall x t a b bv smap size rh, typ_factor_full bv a b x = Some t ->
     bv_store_gt_0 smap bv -> bv_store_sub smap bv rh -> sem_factor size rh x <> None.
Proof.
 intros. destruct x.
 unfold sem_factor,typ_factor_full in *.
 destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
 simpl in *. destruct t0. inv H.
 bdestruct ((a =a= a0)). bdestruct ((b0 =b= b)). subst. simpl in *. inv H.
 unfold bv_store_gt_0 in *.
 apply BEnv.find_2 in eq1.
 apply mapsto_is_in in eq1. specialize (H0 v eq1).
 unfold bv_store_sub in *.
 unfold in_store in *.
 specialize (H1 v 0 eq1 H0).
 destruct H1. destruct H.
 apply Store.find_1 in H.
 assert ((@pair BEnv.key nat v O) = (@pair qvar nat v O)) by easy.
 rewrite H2 in *. rewrite H.
 simpl.
 destruct x. simpl in *. lia.
 simpl. easy.
 simpl in *. inv H. simpl in *. inv H.
 simpl in *. inv H.
 simpl.
 destruct t0. simpl. easy. simpl. easy. simpl. easy.
Qed.

Lemma type_cfac_sem_no_none : forall x t bv smap size rh, type_factor bv x = Some t ->
    bv_store_gt_0 smap bv -> bv_store_sub smap bv rh -> sem_cfac smap size rh x <> None.
Proof.
 intros. destruct x.
 unfold sem_cfac,type_factor in *.
 destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
 simpl in *. destruct t0.
 destruct (typ_factor_full bv C Nat v) eqn:eq2.
 simpl in *. inv H.
 destruct (sem_factor size rh v) eqn:eq3.
 simpl in *. 
 bdestruct (a_nat2fb b0 size <? smap x).
 unfold bv_store_sub in *.
 apply BEnv.find_2 in eq1.
 apply mapsto_is_in in eq1.
 specialize (H1 x (a_nat2fb b0 size) eq1 H).
 destruct H1. destruct H1.
 apply Store.find_1 in H1.
 assert ((@pair BEnv.key nat x (a_nat2fb b0 size)) = (@pair qvar nat x (a_nat2fb b0 size))) by easy.
 rewrite H3 in *.
 rewrite H1.
 simpl. destruct x0. simpl in *. lia.
 simpl. easy. easy.
 assert (sem_factor size rh v <> None).
 apply (type_factor_full_sem_no_none v p C Nat bv smap); try easy.
 contradiction.
 simpl in *. inv H. inv H. simpl in *. inv H.
 simpl in *.
 destruct (sem_factor size rh v) eqn:eq1.
 simpl in *. easy.
 assert (sem_factor size rh v <> None).
 apply (type_factor_sem_no_none v t bv smap); try easy.
 contradiction.
Qed.

Lemma sem_factor_par_eval_same_c : forall x t bv smap size rh rl,
    typ_factor bv x = Some t -> fst t = C -> cstore_store_match smap rh rl bv 
     ->  bv_store_sub smap bv rh -> bv_store_gt_0 smap bv -> 
           par_eval_fc bv size rl x = sem_factor size rh x.
Proof.
  intros. destruct x.
  unfold typ_factor,par_eval_fc,sem_factor in *.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *. destruct t0. inv H. inv H. simpl in *. subst.
  unfold bv_store_gt_0 in *. 
  apply BEnv.find_2 in eq1.
  apply mapsto_is_in in eq1 as eq2.
  specialize (H3 v eq2).
  unfold bv_store_sub in H2. 
  specialize (H2 v 0 eq2 H3).
  destruct H2. destruct H.
  destruct x. simpl in *. lia.
  unfold cstore_store_match in H1.
  specialize (H1 v 0 b0 x (TNor C b) H3 H eq1).
  assert ( ~ is_qtt (Some (TNor C b))).
  unfold is_qtt. easy.
  apply H1 in H2.
  apply Store.find_1 in H.
  apply Store.find_1 in H2.
  assert ((@pair qvar nat v O) = (@pair BEnv.key nat v O)) by easy.
  rewrite H4 in *.
  rewrite H. rewrite H2.
  simpl in *. easy.
  simpl in *. inv H.
  unfold typ_factor,par_eval_fc,sem_factor,make_value in *.
  simpl in *. 
  destruct t0. bdestruct (Nat =b= Bl). inv H4.
  bdestruct (Nat =b= Nat). easy. easy.
  bdestruct (FixedP =b= Bl). inv H4.
  bdestruct (FixedP =b= Nat). inv H5. easy.
  bdestruct (Bl =b= Bl). easy. easy.
Qed.

Lemma sem_factor_full_par_eval_same_c : forall x t a b bv smap size rh rl,
    typ_factor_full bv a b x = Some t -> fst t = C -> cstore_store_match smap rh rl bv 
     ->  bv_store_sub smap bv rh -> bv_store_gt_0 smap bv -> 
           par_eval_fc bv size rl x = sem_factor size rh x.
Proof.
  intros. destruct x.
  unfold typ_factor_full,par_eval_fc,sem_factor in *.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *. destruct t0. inv H.
  bdestruct ((a =a= a0)).
  bdestruct ((b0 =b= b)). simpl in *. inv H.
  simpl in H0. subst.
  unfold bv_store_gt_0 in *. 
  apply BEnv.find_2 in eq1.
  apply mapsto_is_in in eq1 as eq2.
  specialize (H3 v eq2).
  unfold bv_store_sub in H2. 
  specialize (H2 v 0 eq2 H3).
  destruct H2. destruct H.
  destruct x. simpl in *. lia.
  unfold cstore_store_match in H1.
  specialize (H1 v 0 b0 x (TNor C b) H3 H eq1).
  assert ( ~ is_qtt (Some (TNor C b))).
  unfold is_qtt. easy.
  apply H1 in H2.
  apply Store.find_1 in H.
  apply Store.find_1 in H2.
  assert ((@pair qvar nat v O) = (@pair BEnv.key nat v O)) by easy.
  rewrite H4 in *.
  rewrite H. rewrite H2.
  simpl in *. easy.
  simpl in *. inv H.
  simpl in *.  inv H. simpl in *.  inv H.
  unfold typ_factor_full,par_eval_fc,sem_factor,make_value in *.
  simpl in *. 
  destruct t0. bdestruct (Nat =b= Bl). inv H4.
  bdestruct (Nat =b= Nat). easy. easy.
  bdestruct (FixedP =b= Bl). inv H4.
  bdestruct (FixedP =b= Nat). inv H5. easy.
  bdestruct (Bl =b= Bl). easy. easy.
Qed.

Lemma sem_cfac_par_eval_same_c : forall x t smap bv size rh rl,
    type_factor bv x = Some t -> fst t = C -> cstore_store_match smap rh rl bv 
     ->  bv_store_sub smap bv rh -> bv_store_gt_0 smap bv -> 
           par_eval_cfac_check smap bv size rl x = sem_cfac smap size rh x.
Proof.
  intros. destruct x.
  unfold type_factor,par_eval_cfac_check,sem_cfac in *.
  destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
  simpl in *.
  destruct t0.
  destruct (typ_factor_full bv C Nat v) eqn:eq2.
  destruct (par_eval_fc bv size rl v) eqn:eq3.
  simpl in *.
  assert (sem_factor size rh v = Some b0).
  rewrite <- (sem_factor_full_par_eval_same_c v p C Nat bv smap size rh rl); try easy.
  apply (factor_type_c v Nat bv); try easy.
  rewrite H4. simpl in *.
  bdestruct (a_nat2fb b0 size <? smap x).
  inv H. simpl in *. subst.
  destruct (Store.find (elt:=list (nat -> bool)) (x, a_nat2fb b0 size) rh) eqn:eq4.
  unfold bv_store_sub in *.
  apply BEnv.find_2 in eq1.
  apply mapsto_is_in in eq1 as eq5.
  specialize (H2 x (a_nat2fb b0 size) eq5 H5).
  destruct H2. destruct H.
  unfold cstore_store_match in H1.
  destruct x0. simpl in *. lia.
  apply Store.find_2 in eq4.
  specialize (H1 x (a_nat2fb b0 size) b1 x0 (TArray C b n) H5 H eq1).
  assert (~ is_qtt (Some (TArray C b n))). easy.
  apply H1 in H2.
  apply store_mapsto_always_same with (v1 := (b1 :: x0)) in eq4; try easy.
  destruct l. inv eq4. inv eq4.
  apply Store.find_1 in H2. rewrite H2.
  simpl. easy.
  unfold bv_store_sub in *.
  apply BEnv.find_2 in eq1.
  apply mapsto_is_in in eq1 as eq5.
  specialize (H2 x (a_nat2fb b0 size) eq5 H5).
  destruct H2. destruct H.
  apply Store.find_1 in H.
  assert ((@pair qvar nat x (a_nat2fb b0 size)) = (@pair BEnv.key nat x (a_nat2fb b0 size))) by easy.
  rewrite H2 in *.
  rewrite H in eq4. inv eq4. easy.
  simpl in *.
  assert (sem_factor size rh v = None).
  rewrite <- (sem_factor_full_par_eval_same_c v p C Nat bv smap size rh rl); try easy.
  apply (factor_type_c v Nat bv); try easy.
  rewrite H4. simpl. easy.
  simpl in *. inv H. inv H.
  simpl in *. inv H.
  unfold par_eval_cfac_check,sem_cfac.
  simpl in H.
  rewrite sem_factor_par_eval_same_c with (t := t) (smap := smap) (rh := rh); try easy.
Qed.

Lemma type_cfac_sem_error : forall x t bv smap size rh rl, type_factor bv x = Some t ->
    cstore_store_match smap rh rl bv -> bv_store_sub smap bv rh -> bv_store_gt_0 smap bv -> 
    par_find_var_check smap bv size rl x = Some Error ->
               sem_cfac smap size rh x = Some Error.
Proof.
 intros. destruct x.
 unfold sem_cfac,par_find_var_check,type_factor in *.
 destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
 simpl in *. destruct t0.
 destruct (typ_factor_full bv C Nat v) eqn:eq2.
 simpl in *. inv H.
 destruct (par_eval_fc bv size rl v) eqn:eq3.
 rewrite (sem_factor_full_par_eval_same_c v p C Nat bv smap size rh rl) in eq3; try easy.
 rewrite eq3.
 simpl in *. 
 bdestruct (a_nat2fb b0 size <? smap x). inv H3. easy.
 apply factor_type_c in eq2. easy.
 simpl in *. easy.
 simpl in *. easy. easy. simpl in *. easy.
 simpl in *. destruct v. inv H3. easy.
Qed.

Lemma type_cfac_sem_value : forall x xv t bv smap size rh rl, type_factor bv x = Some t ->
    cstore_store_match smap rh rl bv -> bv_store_sub smap bv rh -> bv_store_gt_0 smap bv -> 
    par_find_var_check smap bv size rl x = Some (Value xv) ->
              (exists v, sem_cfac smap size rh x = Some (Value v)).
Proof.
 intros. destruct x.
 unfold sem_cfac,par_find_var_check,type_factor in *.
 destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
 simpl in *. destruct t0.
 destruct (typ_factor_full bv C Nat v) eqn:eq2.
 simpl in *. inv H.
 destruct (par_eval_fc bv size rl v) eqn:eq3.
 rewrite (sem_factor_full_par_eval_same_c v p C Nat bv smap size rh rl) in eq3; try easy.
 rewrite eq3.
 simpl in *. 
 bdestruct (a_nat2fb b0 size <? smap x). inv H3.
 unfold bv_store_gt_0,bv_store_sub in *.
 apply BEnv.find_2 in eq1.
 assert (BEnv.In (elt:=typ) x bv).
 unfold BEnv.In,BEnv.Raw.PX.In. exists ((TArray a b n)). easy.
 specialize (H1 x (a_nat2fb b0 size) H3 H).
 destruct H1. destruct H1. apply Store.find_1 in H1. 
 destruct x0. easy. exists b1.
 assert ((@pair BEnv.key nat x (a_nat2fb b0 size)) = (@pair qvar nat x (a_nat2fb b0 size))) by easy.
 rewrite H5 in *.
 rewrite H1. simpl in *. easy. easy. simpl in *.
 apply factor_type_c in eq2. easy.
 simpl in *. easy.
 simpl in *. easy. easy. simpl in *. easy.
 simpl in *. destruct v. inv H3. simpl in *.
 destruct (BEnv.find (elt:=typ) v bv) eqn:eq1. simpl in *. destruct t0. easy.
 unfold bv_store_gt_0,bv_store_sub in *.
 apply BEnv.find_2 in eq1.
 assert (BEnv.In (elt:=typ) v bv).
 unfold BEnv.In,BEnv.Raw.PX.In. exists (TNor a b). easy.
 apply H2 in H3 as X1. specialize (H1 v 0 H3 X1).
 destruct H1. destruct H1. destruct x. easy. exists b0.
 apply Store.find_1 in H1.
 assert ((@pair BEnv.key nat v 0) = (@pair qvar nat v 0)) by easy.
 rewrite H5 in *. rewrite H1. simpl in *. easy. easy. easy.
Qed.

Lemma type_cfac_sem_value_same : forall x y xv t t' bv smap size rh rl, type_factor bv x = Some t ->
   type_factor bv y = Some t' ->
    cstore_store_match smap rh rl bv -> bv_store_sub smap bv rh -> bv_store_gt_0 smap bv -> 
    par_find_var_check smap bv size rl x = Some (Value xv) ->
    par_find_var_check smap bv size rl y = Some (Value xv) ->
             sem_cfac smap size rh x = sem_cfac smap size rh y.
Proof.
 intros. destruct x. destruct y.
 unfold sem_cfac,par_find_var_check,type_factor in *.
 destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
 simpl in *. destruct t0.
 destruct (typ_factor_full bv C Nat v) eqn:eq2.
 simpl in *. inv H.
 destruct (BEnv.find (elt:=typ) x0 bv) eqn:eq3.
 simpl in *. destruct t.
 destruct (typ_factor_full bv C Nat v0) eqn:eq4.
 simpl in *. inv H0.
 destruct (par_eval_fc bv size rl v) eqn:eq5.
 rewrite (sem_factor_full_par_eval_same_c v p C Nat bv smap size rh rl) in eq5; try easy.
 rewrite eq5.
 simpl in *. 
 destruct (par_eval_fc bv size rl v0) eqn:eq6.
 rewrite (sem_factor_full_par_eval_same_c v0 p0 C Nat bv smap size rh rl) in eq6; try easy.
 rewrite eq6.
 simpl in *. 
 bdestruct (a_nat2fb b1 size <? smap x).
 bdestruct (a_nat2fb b2 size <? smap x0). inv H4. inv H5. easy. inv H5. inv H4.
 apply factor_type_c in eq4. easy. easy.
 apply factor_type_c in eq2. easy. easy. easy. easy. easy. easy. easy. easy.
 simpl in *.
 destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
 simpl in *. destruct t0.
 destruct (typ_factor_full bv C Nat v) eqn:eq2.
 simpl in *. inv H.
 destruct (par_eval_fc bv size rl v) eqn:eq5.
 rewrite (sem_factor_full_par_eval_same_c v p C Nat bv smap size rh rl) in eq5; try easy.
 rewrite eq5.
 simpl in *. 
 destruct v0. inv H5.
 bdestruct (a_nat2fb b0 size <? smap x).
 inv H4. rewrite H7 in *.
 unfold sem_factor.
 unfold bv_store_gt_0,bv_store_sub in *.
 apply BEnv.find_2 in eq1.
 assert (BEnv.In (elt:=typ) v0 bv).
 unfold BEnv.In,BEnv.Raw.PX.In. exists (TArray a b n). easy.
  apply H3 in H4 as X1.
 specialize (H2 v0 0 H4 X1). destruct H2. destruct H2. destruct x. easy.
 apply Store.find_1 in H2.
 assert ((@pair BEnv.key nat v0 0) = (@pair qvar nat v0 0)) by easy.
 rewrite H6 in *.
 rewrite H2.
 simpl. easy. easy. easy. 
 apply factor_type_c in eq2. easy. easy. easy. easy. easy.
 destruct y. simpl in *.
 destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
 simpl in *. destruct t0. 
 destruct (typ_factor_full bv C Nat v0) eqn:eq2.
 simpl in *. inv H.
 destruct (par_eval_fc bv size rl v0) eqn:eq5.
 rewrite (sem_factor_full_par_eval_same_c v0 p C Nat bv smap size rh rl) in eq5; try easy.
 rewrite eq5.
 simpl in *. 
 destruct v.
 bdestruct (a_nat2fb b0 size <? smap x). inv H4. inv H5.
 simpl in *. rewrite H8.
 unfold bv_store_gt_0,bv_store_sub in *.
 apply BEnv.find_2 in eq1.
 assert (BEnv.In (elt:=typ) v bv).
 unfold BEnv.In,BEnv.Raw.PX.In. exists (TArray a b n). easy.
  apply H3 in H4 as X1.
 specialize (H2 v 0 H4 X1). destruct H2. destruct H2. destruct x. easy.
 apply Store.find_1 in H2.
 assert ((@pair BEnv.key nat v 0) = (@pair qvar nat v 0)) by easy.
 rewrite H6 in *.
 rewrite H2.
 simpl. easy. easy. easy. 
 apply factor_type_c in eq2. easy. easy. easy. easy. easy.
 simpl in *.
 destruct v. destruct v0. inv H4. inv H5. easy. easy. easy.
Qed.

Lemma type_cfac_find_var_error : forall x t bv smap size rh rl, type_factor bv x = Some t ->
    cstore_store_match smap rh rl bv -> bv_store_sub smap bv rh -> bv_store_gt_0 smap bv -> 
    sem_cfac smap size rh x = Some Error ->
    par_find_var_check smap bv size rl x = Some Error.
Proof.
 intros. destruct x.
 unfold sem_cfac,par_find_var_check,type_factor in *.
 destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
 simpl in *. destruct t0.
 destruct (typ_factor_full bv C Nat v) eqn:eq2.
 simpl in *. inv H.
 destruct (sem_factor size rh v) eqn:eq3.
 rewrite <- (sem_factor_full_par_eval_same_c v p C Nat bv smap size rh rl) in eq3; try easy.
 rewrite eq3 in *.
 simpl in *. 
 bdestruct (a_nat2fb b0 size <? smap x).
 destruct (Store.find (elt:=list (nat -> bool)) 
        (x, a_nat2fb b0 size) rh ) eqn:eq4.
 simpl in *. destruct l. simpl in *. easy. easy. easy. easy.
 apply factor_type_c in eq2. easy.
 simpl in *. easy.
 simpl in *. easy. easy. simpl in *. easy.
 simpl in *. destruct (sem_factor size rh v) eqn:eq1.
 simpl in *. inv H3. easy.
Qed.

Lemma q_var_same_value : forall x xv t v smap vmap bv size rh rl f aenv,
     store_match_q rh f bv vmap aenv ->
     type_factor bv x = Some t -> fst t = Q -> 
     par_find_var_check smap bv size rl x = Some (Value xv) -> 
     sem_cfac smap size rh x = Some (Value v) -> 
     cstore_store_match smap rh rl bv ->
      bv_store_sub smap bv rh -> bv_store_gt_0 smap bv -> 
     get_cus (aenv (vmap xv)) f (vmap xv) = cut_n v (aenv (vmap xv)).
Proof.
  intros.
  unfold type_factor,sem_cfac,par_find_var_check in *.
  destruct x.
  destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
  simpl in *.
  destruct t0.
  simpl in *.
  destruct (typ_factor_full bv C Nat v0) eqn:eq2.
  apply factor_type_c in eq2 as eq3.
  destruct (par_eval_fc bv size rl v0) eqn:eq4.
  simpl in *.
  assert (sem_factor size rh v0 = Some b0).
  rewrite <- (sem_factor_full_par_eval_same_c v0 p C Nat bv smap size rh rl); try easy.
  rewrite H7 in *.
  simpl in *.
  bdestruct (a_nat2fb b0 size <? smap x).
  inv H2.
  destruct (Store.find (elt:=list (nat -> bool)) (x, a_nat2fb b0 size) rh) eqn:eq5.
  destruct l. simpl in *. inv H3.
  simpl in *. inv H3.
  unfold store_match_q in *.
  apply Store.find_2 in eq5.
  apply H in eq5. easy.
  simpl. rewrite eq1. easy.
  simpl. rewrite eq1. unfold is_qtt.
  inv H0. simpl in *. rewrite H1. easy.
  simpl in *. inv H3.
  inv H2. simpl in *. inv H2. simpl in *. inv H0.
  inv H0. simpl in *. inv H0.
  destruct v0. inv H2.
  simpl in *.
  destruct (BEnv.find (elt:=typ) v0 bv) eqn:eq1.
  simpl in *. destruct t0. inv H0.
  destruct (Store.find (elt:=list (nat -> bool)) (v0, 0) rh) eqn:eq2.
  destruct l.
  simpl in *. inv H3.
  simpl in *. inv H3.
  unfold store_match_q in *.
  apply Store.find_2 in eq2.
  apply H in eq2. easy.
  simpl. rewrite eq1. easy.
  inv H0. simpl in *. rewrite H1 in *.
  unfold is_qtt.
  rewrite eq1. easy.
  simpl in *. inv H3.
  simpl in *. inv H0.
  inv H2.
Qed.


Lemma clt_circuit_right_sem : forall aenv vmap tenv f b size fl x y v stack temp sn sl,
      0 < size -> S (S sn) < sl ->
      aenv (vmap y) = (get_size size b) ->
      vmap y <> stack -> vmap y <> temp -> stack <> temp ->
      aenv temp = (get_size size b) -> aenv stack = sl ->
      get_cus (get_size size b) f (vmap y) = v ->
      store_match_st sl sn stack f vmap ->
      get_cus (get_size size b) f temp = nat2fb 0 ->
      Env.MapsTo (vmap y) PQASM.Nor tenv -> Env.MapsTo stack PQASM.Nor tenv -> Env.MapsTo temp PQASM.Nor tenv ->
      right_mode_env aenv tenv f ->  qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
      get_cua (exp_sem aenv (clt_circuit_right size fl b vmap x y stack temp sn) f (stack, sn))
         = (a_nat2fb x (get_size size b) <? a_nat2fb v (get_size size b)).
Proof.
  intros. 
  unfold clt_circuit_right.
  bdestruct (fl =fl= Classic).
  simpl.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (tenv := tenv) (v1 := a_nat2fb v (get_size size b))
           (v2:= (a_nat2fb x (get_size size b))) (f':=f) ; try easy.
  assert ((exp_sem aenv (inv_exp (init_v (get_size size b) temp x))
     ((put_cus f temp (cut_n x (get_size size b))
         (get_size size b)) [(stack, sn)
      |-> put_cu (f (stack, sn))
            (a_nat2fb x (get_size size b) <?
             a_nat2fb v (get_size size b))]) = f[(stack, sn)
      |-> put_cu (f (stack, sn))
            (a_nat2fb x (get_size size b) <?
             a_nat2fb v (get_size size b))])).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same; easy.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite put_cus_update_flip. easy. iner_p.
  rewrite get_cus_up by iner_p.
  easy.
  apply right_mode_exp_up_same; try easy.
  assert ((¬ (a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b)))
           = (a_nat2fb x (get_size size b) <? a_nat2fb v (get_size size b))).
  bdestruct (a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b)).
  bdestruct ((a_nat2fb x (get_size size b) <? a_nat2fb v (get_size size b))). lia.
  easy.
  bdestruct ((a_nat2fb x (get_size size b) <? a_nat2fb v (get_size size b))).
  easy. lia.
  rewrite H18.
  rewrite H17.
  rewrite eupdate_index_eq.
  apply get_put_cu.
  unfold nor_mode.
  unfold right_mode_env in H13.
  specialize (H13 PQASM.Nor (stack, sn)).
  apply H13 in H11.
  inv H11. easy.
  simpl. lia.
  unfold get_size.
  bdestruct (b =b= Bl). lia. easy.
  simpl. lia.
  simpl. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_put_cus_same; easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite <- H5.
  apply type_nor_modes with (env := tenv); try easy.
  rewrite get_cus_put_neq by iner_p.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy.
  rewrite <- H5.
  apply type_nor_modes with (env := tenv); try easy.
  rewrite cus_get_neq by iner_p.
  unfold store_match_st in H8.
  specialize (H8 (S sn)).
  assert (sn <= S sn) by lia. apply H8 in H17.
  rewrite get_cus_cua in H17 by lia. easy.
  rewrite cus_get_neq by iner_p.
  unfold store_match_st in H8.
  specialize (H8 (sn)).
  assert (sn <= sn) by lia. apply H8 in H17.
  rewrite get_cus_cua in H17 by lia. easy.
  rewrite get_r_put_same. easy.
  simpl.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (tenv := tenv) (v1 := a_nat2fb v (get_size size b))
           (v2:= (a_nat2fb x (get_size size b))) (f':=f) ; try easy.
  assert ((exp_sem aenv (inv_exp (init_v (get_size size b) temp x))
     ((put_cus f temp (cut_n x (get_size size b))
         (get_size size b)) [(stack, sn)
      |-> put_cu (f (stack, sn))
            (a_nat2fb x (get_size size b) <?
             a_nat2fb v (get_size size b))]) = f[(stack, sn)
      |-> put_cu (f (stack, sn))
            (a_nat2fb x (get_size size b) <?
             a_nat2fb v (get_size size b))])).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same; easy.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite put_cus_update_flip. easy. iner_p.
  rewrite get_cus_up by iner_p.
  easy.
  apply right_mode_exp_up_same; try easy.
  assert ((¬ (a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b)))
           = (a_nat2fb x (get_size size b) <? a_nat2fb v (get_size size b))).
  bdestruct (a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b)).
  bdestruct ((a_nat2fb x (get_size size b) <? a_nat2fb v (get_size size b))). lia.
  easy.
  bdestruct ((a_nat2fb x (get_size size b) <? a_nat2fb v (get_size size b))).
  easy. lia.
  rewrite H18.
  rewrite H17.
  rewrite eupdate_index_eq.
  apply get_put_cu.
  unfold nor_mode.
  unfold right_mode_env in H13.
  specialize (H13 PQASM.Nor (stack, sn)).
  apply H13 in H11.
  inv H11. easy.
  simpl. lia.
  unfold get_size.
  bdestruct (b =b= Bl). lia. easy.
  simpl. lia.
  simpl. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_put_cus_same; easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite <- H5.
  apply type_nor_modes with (env := tenv); try easy.
  rewrite get_cus_put_neq by iner_p.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy.
  rewrite <- H5.
  apply type_nor_modes with (env := tenv); try easy.
  rewrite cus_get_neq by iner_p.
  unfold store_match_st in H8.
  specialize (H8 (S sn)).
  assert (sn <= S sn) by lia. apply H8 in H17.
  rewrite get_cus_cua in H17 by lia. easy.
  rewrite cus_get_neq by iner_p.
  unfold store_match_st in H8.
  specialize (H8 (sn)).
  assert (sn <= sn) by lia. apply H8 in H17.
  rewrite get_cus_cua in H17 by lia. easy.
  rewrite get_r_put_same. easy.
Qed.

Lemma ceq_circuit_right_sem : forall aenv vmap tenv f b size fl x y v stack temp sn sl,
      0 < size -> S (S sn) < sl ->
      aenv (vmap y) = (get_size size b) ->
      vmap y <> stack -> vmap y <> temp -> stack <> temp ->
      aenv temp = (get_size size b) -> aenv stack = sl ->
      get_cus (get_size size b) f (vmap y) = v ->
      store_match_st sl sn stack f vmap ->
      get_cus (get_size size b) f temp = nat2fb 0 ->
      Env.MapsTo (vmap y) PQASM.Nor tenv -> Env.MapsTo stack PQASM.Nor tenv -> Env.MapsTo temp PQASM.Nor tenv ->
      right_mode_env aenv tenv f ->  qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
      get_cua (exp_sem aenv (ceq_circuit_right size fl b vmap x y stack temp sn) f (stack, sn))
         = (a_nat2fb x (get_size size b) =? a_nat2fb v (get_size size b)).
Proof.
  intros. 
  assert (nor_modes f (vmap y) (get_size size b)) as V1.
  rewrite <- H1.
  apply type_nor_modes with (env := tenv); try easy.
  assert (nor_modes f temp (get_size size b)) as V2.
  rewrite <- H5.
  apply type_nor_modes with (env := tenv); try easy.
  assert (nor_modes f stack sl) as V3.
  rewrite <- H6.
  apply type_nor_modes with (env := tenv); try easy.
  assert (get_cua (f (stack,sn)) = false) as V4.
  unfold nor_modes,nor_mode in *.
  specialize (V3 sn). assert (sn < sl) by lia. apply V3 in H16.
  unfold store_match_st in *.
  assert (sn <= sn) by lia. apply H8 in H17.
  rewrite get_cus_cua in H17. easy. lia.
  assert (get_cua (f (stack,S sn)) = false) as V5.
  unfold nor_modes,nor_mode in *.
  specialize (V3 (S sn)). assert (S sn < sl) by lia. apply V3 in H16.
  unfold store_match_st in *.
  assert (sn <= S sn) by lia. apply H8 in H17.
  rewrite get_cus_cua in H17. easy. lia.
  unfold ceq_circuit_right.
  bdestruct (fl =fl= Classic).
  remember ( X (stack, sn)) as xop.
  simpl.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (x := temp) (tenv := tenv) (v1 := a_nat2fb x (get_size size b))
           (v2:= (a_nat2fb v (get_size size b))) (f':=f) ; try easy.
  bdestruct ((a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b))).
  simpl.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite eupdate_same.
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (tenv := tenv) (v1 := a_nat2fb v (get_size size b))
           (v2:= (a_nat2fb x (get_size size b))) (f':=f) ; try easy.
  rewrite Heqxop.
  rewrite x_nor_sem with (v := put_cu (f (stack, sn))
               ((a_nat2fb v (get_size size b) <=?
                   a_nat2fb x (get_size size b)))).
  rewrite eupdate_twice_eq.
  assert ((exp_sem aenv (inv_exp (init_v (get_size size b) temp x))
     ((put_cus f temp (cut_n x (get_size size b)) (get_size size b))
      [(stack, sn) |-> put_cu (f (stack, sn)) (a_nat2fb v (get_size size b) <=?
             a_nat2fb x (get_size size b))]))
       = (f[(stack, sn) |-> put_cu (f (stack, sn)) ((a_nat2fb v (get_size size b) <=?
             a_nat2fb x (get_size size b)))])).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same; easy.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite put_cus_update_flip. easy. iner_p.
  rewrite get_cus_up by iner_p.
  easy.
  apply right_mode_exp_up_same; try easy.
  rewrite H18.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb x (get_size size b) =? a_nat2fb v (get_size size b)).
  rewrite H19. 
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb v (get_size size b))). easy.
  lia.
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b))). lia. easy.
  apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up_1. apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite put_cu_cus.
  rewrite put_cus_update_flip by iner_p.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  assert ((¬ (¬ (a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b)))) = 
             ((a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b)))) by btauto.
  rewrite H18. easy.
  apply V3. lia. unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. subst. lia. simpl. subst. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_put_cus_same; easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite get_cus_put_neq by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite get_r_put_same. easy.
  rewrite <- V4. rewrite put_get_cu. easy. apply V3. lia.
  simpl.
  rewrite comparator01_correct_true_1 with (tenv := tenv) (v1 := a_nat2fb v (get_size size b))
           (v2:= (a_nat2fb x (get_size size b))) (f':=f) ; try easy.
  rewrite Heqxop.
  rewrite eupdate_twice_eq.
  rewrite x_nor_sem with (v := put_cu (f (stack, sn))
               (¬  (a_nat2fb v (get_size size b) <=?
                   a_nat2fb x (get_size size b)))).
  rewrite eupdate_twice_eq.
  assert ((exp_sem aenv (inv_exp (init_v (get_size size b) temp x))
     ((put_cus f temp (cut_n x (get_size size b)) (get_size size b))
      [(stack, sn) |-> put_cu (f (stack, sn)) (¬ (a_nat2fb v (get_size size b) <=?
             a_nat2fb x (get_size size b)))]))
       = (f[(stack, sn) |-> put_cu (f (stack, sn)) (¬(a_nat2fb v (get_size size b) <=?
             a_nat2fb x (get_size size b)))])).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same; easy.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite put_cus_update_flip. easy. iner_p.
  rewrite get_cus_up by iner_p.
  easy.
  apply right_mode_exp_up_same; try easy.
  rewrite H18.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb x (get_size size b) =? a_nat2fb v (get_size size b)).
  rewrite H19. 
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb v (get_size size b))). lia.
  easy.
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b))). easy. lia.
  apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up_1. apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite put_cu_cus.
  rewrite put_cus_update_flip by iner_p.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  easy.
  apply V3. lia. unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. subst. lia. simpl. subst. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  rewrite <- put_cus_update_flip by iner_p.
  apply right_mode_exp_put_cus_same; try easy.
  apply right_mode_exp_up_same; easy.
  rewrite <- put_cus_update_flip by iner_p.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_uniform_put_cu_same; try easy.
  apply right_mode_exp_up_same; easy.
  rewrite <- put_cus_update_flip by iner_p.
  apply qft_gt_put_cus_same; try easy.
  apply qft_gt_put_cu_same; easy.
  unfold nor_modes. intros. nor_mode_simpl. apply V2. easy.
  rewrite get_cus_up by iner_p.
  rewrite get_cus_put_neq by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite get_cus_up by iner_p.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite cus_get_neq by iner_p. easy.
  rewrite eupdate_index_eq. rewrite get_put_cu. easy. apply V3. lia.
  rewrite eupdate_index_eq.
  rewrite get_r_put_cu_same. easy. apply V3. lia.
  unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. lia. simpl. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_put_cus_same; try easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy. easy.
  rewrite get_cus_put_neq by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite get_r_put_same. easy.
  remember ( X (stack, sn)) as xop.
  simpl.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (x := temp) (tenv := tenv) (v1 := a_nat2fb x (get_size size b))
           (v2:= (a_nat2fb v (get_size size b))) (f':=f) ; try easy.
  bdestruct ((a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b))).
  simpl.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite eupdate_same.
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (tenv := tenv) (v1 := a_nat2fb v (get_size size b))
           (v2:= (a_nat2fb x (get_size size b))) (f':=f) ; try easy.
  rewrite Heqxop.
  rewrite x_nor_sem with (v := put_cu (f (stack, sn))
               ((a_nat2fb v (get_size size b) <=?
                   a_nat2fb x (get_size size b)))).
  rewrite eupdate_twice_eq.
  assert ((exp_sem aenv (inv_exp (init_v (get_size size b) temp x))
     ((put_cus f temp (cut_n x (get_size size b)) (get_size size b))
      [(stack, sn) |-> put_cu (f (stack, sn)) (a_nat2fb v (get_size size b) <=?
             a_nat2fb x (get_size size b))]))
       = (f[(stack, sn) |-> put_cu (f (stack, sn)) ((a_nat2fb v (get_size size b) <=?
             a_nat2fb x (get_size size b)))])).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same; easy.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite put_cus_update_flip. easy. iner_p.
  rewrite get_cus_up by iner_p.
  easy.
  apply right_mode_exp_up_same; try easy.
  rewrite H18.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb x (get_size size b) =? a_nat2fb v (get_size size b)).
  rewrite H19. 
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb v (get_size size b))). easy.
  lia.
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b))). lia. easy.
  apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up_1. apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite put_cu_cus.
  rewrite put_cus_update_flip by iner_p.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  assert ((¬ (¬ (a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b)))) = 
             ((a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b)))) by btauto.
  rewrite H18. easy.
  apply V3. lia. unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. subst. lia. simpl. subst. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_put_cus_same; easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite get_cus_put_neq by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite get_r_put_same. easy.
  rewrite <- V4. rewrite put_get_cu. easy. apply V3. lia.
  simpl.
  rewrite comparator01_correct_true_1 with (tenv := tenv) (v1 := a_nat2fb v (get_size size b))
           (v2:= (a_nat2fb x (get_size size b))) (f':=f) ; try easy.
  rewrite Heqxop.
  rewrite eupdate_twice_eq.
  rewrite x_nor_sem with (v := put_cu (f (stack, sn))
               (¬  (a_nat2fb v (get_size size b) <=?
                   a_nat2fb x (get_size size b)))).
  rewrite eupdate_twice_eq.
  assert ((exp_sem aenv (inv_exp (init_v (get_size size b) temp x))
     ((put_cus f temp (cut_n x (get_size size b)) (get_size size b))
      [(stack, sn) |-> put_cu (f (stack, sn)) (¬ (a_nat2fb v (get_size size b) <=?
             a_nat2fb x (get_size size b)))]))
       = (f[(stack, sn) |-> put_cu (f (stack, sn)) (¬(a_nat2fb v (get_size size b) <=?
             a_nat2fb x (get_size size b)))])).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same; easy.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite put_cus_update_flip. easy. iner_p.
  rewrite get_cus_up by iner_p.
  easy.
  apply right_mode_exp_up_same; try easy.
  rewrite H18.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb x (get_size size b) =? a_nat2fb v (get_size size b)).
  rewrite H19. 
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb v (get_size size b))). lia.
  easy.
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b))). easy. lia.
  apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up_1. apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite put_cu_cus.
  rewrite put_cus_update_flip by iner_p.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  easy.
  apply V3. lia. unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. subst. lia. simpl. subst. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  rewrite <- put_cus_update_flip by iner_p.
  apply right_mode_exp_put_cus_same; try easy.
  apply right_mode_exp_up_same; easy.
  rewrite <- put_cus_update_flip by iner_p.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_uniform_put_cu_same; try easy.
  apply right_mode_exp_up_same; easy.
  rewrite <- put_cus_update_flip by iner_p.
  apply qft_gt_put_cus_same; try easy.
  apply qft_gt_put_cu_same; easy.
  unfold nor_modes. intros. nor_mode_simpl. apply V2. easy.
  rewrite get_cus_up by iner_p.
  rewrite get_cus_put_neq by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite get_cus_up by iner_p.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite cus_get_neq by iner_p. easy.
  rewrite eupdate_index_eq. rewrite get_put_cu. easy. apply V3. lia.
  rewrite eupdate_index_eq.
  rewrite get_r_put_cu_same. easy. apply V3. lia.
  unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. lia. simpl. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_put_cus_same; try easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy. easy.
  rewrite get_cus_put_neq by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite get_r_put_same. easy.
Qed.

Lemma clt_circuit_left_sem : forall aenv vmap tenv f b size fl x y v stack temp sn sl,
      0 < size -> S (S sn) < sl ->
      aenv (vmap y) = (get_size size b) ->
      vmap y <> stack -> vmap y <> temp -> stack <> temp ->
      aenv temp = (get_size size b) -> aenv stack = sl ->
      get_cus (get_size size b) f (vmap y) = v ->
      store_match_st sl sn stack f vmap ->
      get_cus (get_size size b) f temp = nat2fb 0 ->
      Env.MapsTo (vmap y) PQASM.Nor tenv -> Env.MapsTo stack PQASM.Nor tenv -> Env.MapsTo temp PQASM.Nor tenv ->
      right_mode_env aenv tenv f ->  qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
      get_cua (exp_sem aenv (clt_circuit_left size fl b vmap y x stack temp sn) f (stack, sn))
         = (a_nat2fb v (get_size size b) <? a_nat2fb x (get_size size b)).
Proof.
  intros. 
  unfold clt_circuit_left.
  bdestruct (fl =fl= Classic).
  simpl.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (tenv := tenv) (v1 := a_nat2fb x (get_size size b))
           (v2:= (a_nat2fb v (get_size size b))) (f':=f) ; try easy.
  assert ((exp_sem aenv (inv_exp (init_v (get_size size b) temp x))
     ((put_cus f temp (cut_n x (get_size size b))
         (get_size size b)) [(stack, sn)
      |-> put_cu (f (stack, sn))
            (a_nat2fb v (get_size size b) <?
             a_nat2fb x (get_size size b))]) = f[(stack, sn)
      |-> put_cu (f (stack, sn))
            (a_nat2fb v (get_size size b) <?
             a_nat2fb x (get_size size b))])).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same; easy.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite put_cus_update_flip. easy. iner_p.
  rewrite get_cus_up by iner_p.
  easy.
  apply right_mode_exp_up_same; try easy.
  assert ((¬ (a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b)))
           = (a_nat2fb v (get_size size b) <? a_nat2fb x (get_size size b))).
  bdestruct (a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b)).
  bdestruct ((a_nat2fb v (get_size size b) <? a_nat2fb x (get_size size b))). lia.
  easy.
  bdestruct ((a_nat2fb v (get_size size b) <? a_nat2fb x (get_size size b))).
  easy. lia.
  rewrite H18.
  rewrite H17.
  rewrite eupdate_index_eq.
  apply get_put_cu.
  unfold nor_mode.
  unfold right_mode_env in H13.
  specialize (H13 PQASM.Nor (stack, sn)).
  apply H13 in H11.
  inv H11. easy.
  simpl. lia.
  unfold get_size.
  bdestruct (b =b= Bl). lia. easy.
  simpl. lia.
  simpl. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_put_cus_same; easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite <- H5.
  apply type_nor_modes with (env := tenv); try easy.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy.
  rewrite <- H5.
  apply type_nor_modes with (env := tenv); try easy.
  rewrite get_cus_put_neq by iner_p.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite cus_get_neq by iner_p.
  unfold store_match_st in H8.
  specialize (H8 (S sn)).
  assert (sn <= S sn) by lia. apply H8 in H17.
  rewrite get_cus_cua in H17 by lia. easy.
  rewrite cus_get_neq by iner_p.
  unfold store_match_st in H8.
  specialize (H8 (sn)).
  assert (sn <= sn) by lia. apply H8 in H17.
  rewrite get_cus_cua in H17 by lia. easy.
  rewrite get_r_put_same. easy.
  simpl.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (tenv := tenv) (v1 := a_nat2fb x (get_size size b))
           (v2:= (a_nat2fb v (get_size size b))) (f':=f) ; try easy.
  assert ((exp_sem aenv (inv_exp (init_v (get_size size b) temp x))
     ((put_cus f temp (cut_n x (get_size size b))
         (get_size size b)) [(stack, sn)
      |-> put_cu (f (stack, sn))
            (a_nat2fb v (get_size size b) <?
             a_nat2fb x (get_size size b))]) = f[(stack, sn)
      |-> put_cu (f (stack, sn))
            (a_nat2fb v (get_size size b) <?
             a_nat2fb x (get_size size b))])).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same; easy.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite put_cus_update_flip. easy. iner_p.
  rewrite get_cus_up by iner_p.
  easy.
  apply right_mode_exp_up_same; try easy.
  assert ((¬ (a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b)))
           = (a_nat2fb v (get_size size b) <? a_nat2fb x (get_size size b))).
  bdestruct (a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b)).
  bdestruct ((a_nat2fb v (get_size size b) <? a_nat2fb x (get_size size b))). lia.
  easy.
  bdestruct ((a_nat2fb v (get_size size b) <? a_nat2fb x (get_size size b))).
  easy. lia.
  rewrite H18.
  rewrite H17.
  rewrite eupdate_index_eq.
  apply get_put_cu.
  unfold nor_mode.
  unfold right_mode_env in H13.
  specialize (H13 PQASM.Nor (stack, sn)).
  apply H13 in H11.
  inv H11. easy.
  simpl. lia.
  unfold get_size.
  bdestruct (b =b= Bl). lia. easy.
  simpl. lia.
  simpl. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_put_cus_same; easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite <- H5.
  apply type_nor_modes with (env := tenv); try easy.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy.
  rewrite <- H5.
  apply type_nor_modes with (env := tenv); try easy.
  rewrite get_cus_put_neq by iner_p.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite cus_get_neq by iner_p.
  unfold store_match_st in H8.
  specialize (H8 (S sn)).
  assert (sn <= S sn) by lia. apply H8 in H17.
  rewrite get_cus_cua in H17 by lia. easy.
  rewrite cus_get_neq by iner_p.
  unfold store_match_st in H8.
  specialize (H8 (sn)).
  assert (sn <= sn) by lia. apply H8 in H17.
  rewrite get_cus_cua in H17 by lia. easy.
  rewrite get_r_put_same. easy.
Qed.

Lemma ceq_circuit_left_sem : forall aenv vmap tenv f b size fl x y v stack temp sn sl,
      0 < size -> S (S sn) < sl ->
      aenv (vmap y) = (get_size size b) ->
      vmap y <> stack -> vmap y <> temp -> stack <> temp ->
      aenv temp = (get_size size b) -> aenv stack = sl ->
      get_cus (get_size size b) f (vmap y) = v ->
      store_match_st sl sn stack f vmap ->
      get_cus (get_size size b) f temp = nat2fb 0 ->
      Env.MapsTo (vmap y) PQASM.Nor tenv -> Env.MapsTo stack PQASM.Nor tenv -> Env.MapsTo temp PQASM.Nor tenv ->
      right_mode_env aenv tenv f ->  qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
      get_cua (exp_sem aenv (ceq_circuit_left size fl b vmap y x stack temp sn) f (stack, sn))
         = (a_nat2fb x (get_size size b) =? a_nat2fb v (get_size size b)).
Proof.
  intros. 
  assert (nor_modes f (vmap y) (get_size size b)) as V1.
  rewrite <- H1.
  apply type_nor_modes with (env := tenv); try easy.
  assert (nor_modes f temp (get_size size b)) as V2.
  rewrite <- H5.
  apply type_nor_modes with (env := tenv); try easy.
  assert (nor_modes f stack sl) as V3.
  rewrite <- H6.
  apply type_nor_modes with (env := tenv); try easy.
  assert (get_cua (f (stack,sn)) = false) as V4.
  unfold nor_modes,nor_mode in *.
  specialize (V3 sn). assert (sn < sl) by lia. apply V3 in H16.
  unfold store_match_st in *.
  assert (sn <= sn) by lia. apply H8 in H17.
  rewrite get_cus_cua in H17. easy. lia.
  assert (get_cua (f (stack,S sn)) = false) as V5.
  unfold nor_modes,nor_mode in *.
  specialize (V3 (S sn)). assert (S sn < sl) by lia. apply V3 in H16.
  unfold store_match_st in *.
  assert (sn <= S sn) by lia. apply H8 in H17.
  rewrite get_cus_cua in H17. easy. lia.
  unfold ceq_circuit_left.
  bdestruct (fl =fl= Classic).
  remember ( X (stack, sn)) as xop.
  simpl.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite comparator01_correct_1 with (x := vmap y) (tenv := tenv) (v1 := a_nat2fb v (get_size size b))
           (v2:= (a_nat2fb x (get_size size b))) (f':=f) ; try easy.
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b))).
  simpl.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite eupdate_same.
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (x := temp) (tenv := tenv) (v1 := a_nat2fb x (get_size size b))
           (v2:= (a_nat2fb v (get_size size b))) (f':=f) ; try easy.
  rewrite Heqxop.
  rewrite x_nor_sem with (v := put_cu (f (stack, sn))
               ((a_nat2fb x (get_size size b) <=?
                   a_nat2fb v (get_size size b)))).
  rewrite eupdate_twice_eq.
  assert ((exp_sem aenv (inv_exp (init_v (get_size size b) temp x))
     ((put_cus f temp (cut_n x (get_size size b)) (get_size size b))
      [(stack, sn) |-> put_cu (f (stack, sn)) (a_nat2fb x (get_size size b) <=?
             a_nat2fb v (get_size size b))]))
       = (f[(stack, sn) |-> put_cu (f (stack, sn)) ((a_nat2fb x (get_size size b) <=?
             a_nat2fb v (get_size size b)))])).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same; easy.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite put_cus_update_flip. easy. iner_p.
  rewrite get_cus_up by iner_p.
  easy.
  apply right_mode_exp_up_same; try easy.
  rewrite H18.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb x (get_size size b) =? a_nat2fb v (get_size size b)).
  rewrite H19. 
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb v (get_size size b))). easy.
  lia.
  bdestruct ((a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b))). lia. easy.
  apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up_1. apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite put_cu_cus.
  rewrite put_cus_update_flip by iner_p.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  assert ((¬ (¬ (a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b)))) = 
             ((a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b)))) by btauto.
  rewrite H18. easy.
  apply V3. lia. unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. subst. lia. simpl. subst. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_put_cus_same; easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy. easy.
  rewrite get_cus_put_neq by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite get_r_put_same. easy.
  rewrite <- V4. rewrite put_get_cu. easy. apply V3. lia.
  simpl.
  rewrite comparator01_correct_true_1 with (tenv := tenv) (v1 := a_nat2fb x (get_size size b))
           (v2:= (a_nat2fb v (get_size size b))) (f':=f) ; try easy.
  rewrite Heqxop.
  rewrite eupdate_twice_eq.
  rewrite x_nor_sem with (v := put_cu (f (stack, sn))
               (¬  (a_nat2fb x (get_size size b) <=?
                   a_nat2fb v (get_size size b)))).
  rewrite eupdate_twice_eq.
  assert ((exp_sem aenv (inv_exp (init_v (get_size size b) temp x))
     ((put_cus f temp (cut_n x (get_size size b)) (get_size size b))
      [(stack, sn) |-> put_cu (f (stack, sn)) (¬ (a_nat2fb x (get_size size b) <=?
             a_nat2fb v (get_size size b)))]))
       = (f[(stack, sn) |-> put_cu (f (stack, sn)) (¬(a_nat2fb x (get_size size b) <=?
             a_nat2fb v (get_size size b)))])).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same; easy.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite put_cus_update_flip. easy. iner_p.
  rewrite get_cus_up by iner_p.
  easy.
  apply right_mode_exp_up_same; try easy.
  rewrite H18.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb x (get_size size b) =? a_nat2fb v (get_size size b)).
  rewrite H19. 
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb v (get_size size b))). lia.
  easy.
  bdestruct ((a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b))). easy. lia.
  apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up_1. apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite put_cu_cus.
  rewrite put_cus_update_flip by iner_p.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  easy.
  apply V3. lia. unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. subst. lia. simpl. subst. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  rewrite <- put_cus_update_flip by iner_p.
  apply right_mode_exp_put_cus_same; try easy.
  apply right_mode_exp_up_same; easy.
  rewrite <- put_cus_update_flip by iner_p.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_uniform_put_cu_same; try easy.
  apply right_mode_exp_up_same; easy.
  rewrite <- put_cus_update_flip by iner_p.
  apply qft_gt_put_cus_same; try easy.
  apply qft_gt_put_cu_same; easy.
  unfold nor_modes. intros. nor_mode_simpl. apply V2. easy.
  rewrite get_cus_up by iner_p.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy. easy.
  rewrite get_cus_up by iner_p.
  rewrite get_cus_put_neq by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite cus_get_neq by iner_p. easy.
  rewrite eupdate_index_eq. rewrite get_put_cu. easy. apply V3. lia.
  rewrite eupdate_index_eq.
  rewrite get_r_put_cu_same. easy. apply V3. lia.
  unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. lia. simpl. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_put_cus_same; try easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite get_cus_put_neq by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite get_r_put_same. easy.
  remember ( X (stack, sn)) as xop.
  simpl.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite comparator01_correct_1 with (x := vmap y) (tenv := tenv) (v1 := a_nat2fb v (get_size size b))
           (v2:= (a_nat2fb x (get_size size b))) (f':=f) ; try easy.
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb x (get_size size b))).
  simpl.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite eupdate_same.
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (x := temp) (tenv := tenv) (v1 := a_nat2fb x (get_size size b))
           (v2:= (a_nat2fb v (get_size size b))) (f':=f) ; try easy.
  rewrite Heqxop.
  rewrite x_nor_sem with (v := put_cu (f (stack, sn))
               ((a_nat2fb x (get_size size b) <=?
                   a_nat2fb v (get_size size b)))).
  rewrite eupdate_twice_eq.
  assert ((exp_sem aenv (inv_exp (init_v (get_size size b) temp x))
     ((put_cus f temp (cut_n x (get_size size b)) (get_size size b))
      [(stack, sn) |-> put_cu (f (stack, sn)) (a_nat2fb x (get_size size b) <=?
             a_nat2fb v (get_size size b))]))
       = (f[(stack, sn) |-> put_cu (f (stack, sn)) ((a_nat2fb x (get_size size b) <=?
             a_nat2fb v (get_size size b)))])).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same; easy.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite put_cus_update_flip. easy. iner_p.
  rewrite get_cus_up by iner_p.
  easy.
  apply right_mode_exp_up_same; try easy.
  rewrite H18.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb x (get_size size b) =? a_nat2fb v (get_size size b)).
  rewrite H19. 
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb v (get_size size b))). easy.
  lia.
  bdestruct ((a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b))). lia. easy.
  apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up_1. apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite put_cu_cus.
  rewrite put_cus_update_flip by iner_p.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  assert ((¬ (¬ (a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b)))) = 
             ((a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b)))) by btauto.
  rewrite H18. easy.
  apply V3. lia. unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. subst. lia. simpl. subst. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_put_cus_same; easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy. easy.
  rewrite get_cus_put_neq by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite get_r_put_same. easy.
  rewrite <- V4. rewrite put_get_cu. easy. apply V3. lia.
  simpl.
  rewrite comparator01_correct_true_1 with (tenv := tenv) (v1 := a_nat2fb x (get_size size b))
           (v2:= (a_nat2fb v (get_size size b))) (f':=f) ; try easy.
  rewrite Heqxop.
  rewrite eupdate_twice_eq.
  rewrite x_nor_sem with (v := put_cu (f (stack, sn))
               (¬  (a_nat2fb x (get_size size b) <=?
                   a_nat2fb v (get_size size b)))).
  rewrite eupdate_twice_eq.
  assert ((exp_sem aenv (inv_exp (init_v (get_size size b) temp x))
     ((put_cus f temp (cut_n x (get_size size b)) (get_size size b))
      [(stack, sn) |-> put_cu (f (stack, sn)) (¬ (a_nat2fb x (get_size size b) <=?
             a_nat2fb v (get_size size b)))]))
       = (f[(stack, sn) |-> put_cu (f (stack, sn)) (¬(a_nat2fb x (get_size size b) <=?
             a_nat2fb v (get_size size b)))])).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv); try easy.
  apply well_typed_init_v. easy.
  apply right_mode_exp_up_same; try easy.
  apply qft_uniform_put_cu_same. easy.
  apply qft_gt_put_cu_same; easy.
  rewrite init_v_sem with (size := (get_size size b)) (tenv := tenv); try easy.
  rewrite put_cus_update_flip. easy. iner_p.
  rewrite get_cus_up by iner_p.
  easy.
  apply right_mode_exp_up_same; try easy.
  rewrite H18.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb x (get_size size b) =? a_nat2fb v (get_size size b)).
  rewrite H19. 
  bdestruct ((a_nat2fb v (get_size size b) <=? a_nat2fb v (get_size size b))). lia.
  easy.
  bdestruct ((a_nat2fb x (get_size size b) <=? a_nat2fb v (get_size size b))). easy. lia.
  apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  apply nor_mode_cus_eq.
  apply nor_mode_up_1. apply V3. lia.
  rewrite <- put_cus_update_flip by iner_p.
  rewrite put_cu_cus.
  rewrite put_cus_update_flip by iner_p.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  easy.
  apply V3. lia. unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. subst. lia. simpl. subst. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  rewrite <- put_cus_update_flip by iner_p.
  apply right_mode_exp_put_cus_same; try easy.
  apply right_mode_exp_up_same; easy.
  rewrite <- put_cus_update_flip by iner_p.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_uniform_put_cu_same; try easy.
  apply right_mode_exp_up_same; easy.
  rewrite <- put_cus_update_flip by iner_p.
  apply qft_gt_put_cus_same; try easy.
  apply qft_gt_put_cu_same; easy.
  unfold nor_modes. intros. nor_mode_simpl. apply V2. easy.
  rewrite get_cus_up by iner_p.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy. easy.
  rewrite get_cus_up by iner_p.
  rewrite get_cus_put_neq by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite eupdate_index_neq by iner_p.
  rewrite cus_get_neq by iner_p. easy.
  rewrite eupdate_index_eq. rewrite get_put_cu. easy. apply V3. lia.
  rewrite eupdate_index_eq.
  rewrite get_r_put_cu_same. easy. apply V3. lia.
  unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. lia. simpl. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_put_cus_same; try easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite get_cus_put_neq by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite get_put_cus_cut_n.
  rewrite cut_n_twice_same.
  rewrite a_nat2fb_cut_n. easy. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite cus_get_neq by iner_p. easy.
  rewrite get_r_put_same. easy.
Qed.

Lemma clt_circuit_two_sem : forall aenv vmap tenv f b size fl x y v1 v2 stack sn sl,
      0 < size -> S (S sn) < sl ->
      aenv (vmap x) = (get_size size b) ->
      aenv (vmap y) = (get_size size b) ->
      vmap x <> vmap y -> vmap x <> stack -> vmap y <> stack ->
      aenv stack = sl ->
      get_cus (get_size size b) f (vmap x) = v1 ->
      get_cus (get_size size b) f (vmap y) = v2 ->
      store_match_st sl sn stack f vmap ->
      Env.MapsTo (vmap x) PQASM.Nor tenv -> Env.MapsTo (vmap y) PQASM.Nor tenv -> Env.MapsTo stack PQASM.Nor tenv ->
      right_mode_env aenv tenv f ->  qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
      get_cua (exp_sem aenv (clt_circuit_two size fl b vmap x y stack sn) f (stack, sn))
         = (a_nat2fb v1 (get_size size b) <? a_nat2fb v2 (get_size size b)).
Proof.
  intros. 
  unfold clt_circuit_two.
  bdestruct (fl =fl= Classic).
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (tenv := tenv) (v1 := a_nat2fb v2 (get_size size b))
           (v2:= (a_nat2fb v1 (get_size size b))) (f':=f) ; try easy.
  assert ((¬ (a_nat2fb v2 (get_size size b) <=? a_nat2fb v1 (get_size size b)))
           = (a_nat2fb v1 (get_size size b) <? a_nat2fb v2 (get_size size b))).
  bdestruct (a_nat2fb  v2 (get_size size b) <=? a_nat2fb v1 (get_size size b)).
  bdestruct ((a_nat2fb v1 (get_size size b) <? a_nat2fb v2 (get_size size b))). lia.
  easy.
  bdestruct ((a_nat2fb v1 (get_size size b) <? a_nat2fb v2 (get_size size b))).
  easy. lia.
  rewrite H17.
  rewrite eupdate_index_eq.
  apply get_put_cu.
  unfold nor_mode.
  unfold right_mode_env in H13.
  specialize (H13 PQASM.Nor (stack, sn)).
  apply H13 in H12.
  inv H12. easy.
  simpl. lia.
  unfold get_size.
  bdestruct (b =b= Bl). lia. easy.
  simpl. lia.
  simpl. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  rewrite nat2fb_a_nat2fb. easy.
  intros. rewrite <- H8.
  unfold get_cus.
  bdestruct (i <? get_size size b).
  lia. easy.
  rewrite nat2fb_a_nat2fb. easy.
  intros. rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b).
  lia. easy.
  unfold store_match_st in H9.
  specialize (H9 (S sn)).
  assert (sn <= S sn) by lia. apply H9 in H17.
  rewrite get_cus_cua in H17 by lia. easy.
  unfold store_match_st in H9.
  specialize (H9 (sn)).
  assert (sn <= sn) by lia. apply H9 in H17.
  rewrite get_cus_cua in H17 by lia. easy.
  rewrite comparator01_correct_1 with (tenv := tenv) (v1 := a_nat2fb v2 (get_size size b))
           (v2:= (a_nat2fb v1 (get_size size b))) (f':=f) ; try easy.
  assert ((¬ (a_nat2fb v2 (get_size size b) <=? a_nat2fb v1 (get_size size b)))
           = (a_nat2fb v1 (get_size size b) <? a_nat2fb v2 (get_size size b))).
  bdestruct (a_nat2fb  v2 (get_size size b) <=? a_nat2fb v1 (get_size size b)).
  bdestruct ((a_nat2fb v1 (get_size size b) <? a_nat2fb v2 (get_size size b))). lia.
  easy.
  bdestruct ((a_nat2fb v1 (get_size size b) <? a_nat2fb v2 (get_size size b))).
  easy. lia.
  rewrite H17.
  rewrite eupdate_index_eq.
  apply get_put_cu.
  unfold nor_mode.
  unfold right_mode_env in H13.
  specialize (H13 PQASM.Nor (stack, sn)).
  apply H13 in H12.
  inv H12. easy.
  simpl. lia.
  unfold get_size.
  bdestruct (b =b= Bl). lia. easy.
  simpl. lia.
  simpl. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  rewrite nat2fb_a_nat2fb. easy.
  intros. rewrite <- H8.
  unfold get_cus.
  bdestruct (i <? get_size size b).
  lia. easy.
  rewrite nat2fb_a_nat2fb. easy.
  intros. rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b).
  lia. easy.
  unfold store_match_st in H9.
  specialize (H9 (S sn)).
  assert (sn <= S sn) by lia. apply H9 in H17.
  rewrite get_cus_cua in H17 by lia. easy.
  unfold store_match_st in H9.
  specialize (H9 (sn)).
  assert (sn <= sn) by lia. apply H9 in H17.
  rewrite get_cus_cua in H17 by lia. easy.
Qed.

Lemma ceq_circuit_two_sem : forall aenv vmap tenv f b size fl x y v1 v2 stack sn sl,
      0 < size -> S (S sn) < sl ->
      aenv (vmap x) = (get_size size b) ->
      aenv (vmap y) = (get_size size b) ->
      vmap x <> vmap y -> vmap x <> stack -> vmap y <> stack ->
      aenv stack = sl ->
      get_cus (get_size size b) f (vmap x) = v1 ->
      get_cus (get_size size b) f (vmap y) = v2 ->
      store_match_st sl sn stack f vmap ->
      Env.MapsTo (vmap x) PQASM.Nor tenv -> Env.MapsTo (vmap y) PQASM.Nor tenv -> Env.MapsTo stack PQASM.Nor tenv ->
      right_mode_env aenv tenv f ->  qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
      get_cua (exp_sem aenv (ceq_circuit_two size fl b vmap x y stack sn) f (stack, sn))
         = (a_nat2fb v1 (get_size size b) =? a_nat2fb v2 (get_size size b)).
Proof.
  intros. 
  assert (nor_modes f (vmap x) (get_size size b)) as V1.
  rewrite <- H1.
  apply type_nor_modes with (env := tenv); try easy.
  assert (nor_modes f (vmap y) (get_size size b)) as V2.
  rewrite <- H2.
  apply type_nor_modes with (env := tenv); try easy.
  assert (nor_modes f stack sl) as V3.
  rewrite <- H6.
  apply type_nor_modes with (env := tenv); try easy.
  assert (get_cua (f (stack,sn)) = false) as V4.
  unfold nor_modes,nor_mode in *.
  specialize (V3 sn). assert (sn < sl) by lia. apply V3 in H16.
  unfold store_match_st in *.
  assert (sn <= sn) by lia. apply H9 in H17.
  rewrite get_cus_cua in H17. easy. lia.
  assert (get_cua (f (stack,S sn)) = false) as V5.
  unfold nor_modes,nor_mode in *.
  specialize (V3 (S sn)). assert (S sn < sl) by lia. apply V3 in H16.
  unfold store_match_st in *.
  assert (sn <= S sn) by lia. apply H9 in H17.
  rewrite get_cus_cua in H17. easy. lia.
  unfold ceq_circuit_two.
  bdestruct (fl =fl= Classic).
  remember ( X (stack, sn)) as xop.
  simpl.
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (x:=vmap y) (tenv := tenv) (v1 := a_nat2fb v2 (get_size size b))
           (v2:= (a_nat2fb v1 (get_size size b))) (f':=f) ; try easy.
  bdestruct ((a_nat2fb v2 (get_size size b) <=? a_nat2fb v1 (get_size size b))).
  simpl.
  rewrite eupdate_same.
  rewrite comparator01_correct_1 with (tenv := tenv) (v1 := a_nat2fb v1 (get_size size b))
           (v2:= (a_nat2fb v2 (get_size size b))) (f':=f) ; try easy.
  rewrite Heqxop.
  rewrite x_nor_sem with (v := put_cu (f (stack, sn))
               ((a_nat2fb v1 (get_size size b) <=?
                   a_nat2fb v2 (get_size size b)))).
  rewrite eupdate_twice_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb v1 (get_size size b) =? a_nat2fb v2 (get_size size b)).
  rewrite H18. 
  bdestruct ((a_nat2fb v2 (get_size size b) <=? a_nat2fb v2 (get_size size b))). easy.
  lia.
  bdestruct ((a_nat2fb v1 (get_size size b) <=? a_nat2fb v2 (get_size size b))). lia. easy.
  apply V3. lia.
  apply nor_mode_up_1. apply V3. lia.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  rewrite get_put_cu.
  assert ((¬ (¬ (a_nat2fb v1 (get_size size b) <=? a_nat2fb v2 (get_size size b)))) = 
             ((a_nat2fb v1 (get_size size b) <=? a_nat2fb v2 (get_size size b)))) by btauto.
  rewrite H18. easy.
  apply V3. lia. unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. subst. lia. simpl. subst. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  rewrite H7. 
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite H8. 
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H8.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite <- V4. rewrite put_get_cu. easy. apply V3. lia.
  simpl.
  rewrite comparator01_correct_true_1 with (tenv := tenv) (v1 := a_nat2fb v1 (get_size size b))
           (v2:= (a_nat2fb v2 (get_size size b))) (f':=f) ; try easy.
  rewrite Heqxop.
  rewrite eupdate_twice_eq.
  rewrite x_nor_sem with (v := put_cu (f (stack, sn))
               (¬  (a_nat2fb v1 (get_size size b) <=?
                   a_nat2fb v2 (get_size size b)))).
  rewrite eupdate_twice_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb v1 (get_size size b) =? a_nat2fb v2 (get_size size b)).
  rewrite H18. 
  bdestruct ((a_nat2fb v2 (get_size size b) <=? a_nat2fb v2 (get_size size b))). lia.
  easy.
  bdestruct ((a_nat2fb v1 (get_size size b) <=? a_nat2fb v2 (get_size size b))). easy. lia.
  apply V3. lia.
  apply nor_mode_up_1. apply V3. lia.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  rewrite get_put_cu.
  easy.
  apply V3. lia. unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. subst. lia. simpl. subst. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_up_same; easy.
  apply qft_uniform_put_cu_same; try easy.
  apply qft_gt_put_cu_same; easy.
  rewrite get_cus_up by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite get_cus_up by iner_p.
  rewrite H8.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H8.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite eupdate_index_eq. rewrite get_put_cu. easy. apply V3. lia.
  rewrite eupdate_index_eq.
  rewrite get_r_put_cu_same. easy. apply V3. lia.
  unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. lia. simpl. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  rewrite H8.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H8.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  remember ( X (stack, sn)) as xop.
  simpl.
  Check comparator01_correct_1.
  rewrite comparator01_correct_1 with (x:=vmap y) (tenv := tenv) (v1 := a_nat2fb v2 (get_size size b))
           (v2:= (a_nat2fb v1 (get_size size b))) (f':=f) ; try easy.
  bdestruct ((a_nat2fb v2 (get_size size b) <=? a_nat2fb v1 (get_size size b))).
  simpl.
  rewrite eupdate_same.
  rewrite comparator01_correct_1 with (tenv := tenv) (v1 := a_nat2fb v1 (get_size size b))
           (v2:= (a_nat2fb v2 (get_size size b))) (f':=f) ; try easy.
  rewrite Heqxop.
  rewrite x_nor_sem with (v := put_cu (f (stack, sn))
               ((a_nat2fb v1 (get_size size b) <=?
                   a_nat2fb v2 (get_size size b)))).
  rewrite eupdate_twice_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb v1 (get_size size b) =? a_nat2fb v2 (get_size size b)).
  rewrite H18. 
  bdestruct ((a_nat2fb v2 (get_size size b) <=? a_nat2fb v2 (get_size size b))). easy.
  lia.
  bdestruct ((a_nat2fb v1 (get_size size b) <=? a_nat2fb v2 (get_size size b))). lia. easy.
  apply V3. lia.
  apply nor_mode_up_1. apply V3. lia.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  rewrite get_put_cu.
  assert ((¬ (¬ (a_nat2fb v1 (get_size size b) <=? a_nat2fb v2 (get_size size b)))) = 
             ((a_nat2fb v1 (get_size size b) <=? a_nat2fb v2 (get_size size b)))) by btauto.
  rewrite H18. easy.
  apply V3. lia. unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. subst. lia. simpl. subst. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  rewrite H7. 
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite H8. 
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H8.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite <- V4. rewrite put_get_cu. easy. apply V3. lia.
  simpl.
  rewrite comparator01_correct_true_1 with (tenv := tenv) (v1 := a_nat2fb v1 (get_size size b))
           (v2:= (a_nat2fb v2 (get_size size b))) (f':=f) ; try easy.
  rewrite Heqxop.
  rewrite eupdate_twice_eq.
  rewrite x_nor_sem with (v := put_cu (f (stack, sn))
               (¬  (a_nat2fb v1 (get_size size b) <=?
                   a_nat2fb v2 (get_size size b)))).
  rewrite eupdate_twice_eq.
  rewrite eupdate_index_eq.
  rewrite get_put_cu.
  bdestruct (a_nat2fb v1 (get_size size b) =? a_nat2fb v2 (get_size size b)).
  rewrite H18. 
  bdestruct ((a_nat2fb v2 (get_size size b) <=? a_nat2fb v2 (get_size size b))). lia.
  easy.
  bdestruct ((a_nat2fb v1 (get_size size b) <=? a_nat2fb v2 (get_size size b))). easy. lia.
  apply V3. lia.
  apply nor_mode_up_1. apply V3. lia.
  rewrite eupdate_index_eq.
  rewrite put_cu_twice_eq.
  rewrite get_put_cu.
  easy.
  apply V3. lia. unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. subst. lia. simpl. subst. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  apply right_mode_exp_up_same; easy.
  apply qft_uniform_put_cu_same; try easy.
  apply qft_gt_put_cu_same; easy.
  rewrite get_cus_up by iner_p.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite get_cus_up by iner_p.
  rewrite H8.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H8.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite eupdate_index_neq by iner_p. easy.
  rewrite eupdate_index_eq. rewrite get_put_cu. easy. apply V3. lia.
  rewrite eupdate_index_eq.
  rewrite get_r_put_cu_same. easy. apply V3. lia.
  unfold get_size. destruct b. simpl. lia. simpl. lia. simpl. lia.
  simpl. lia. simpl. lia.
  apply a_nat2fb_scope.
  apply a_nat2fb_scope.
  unfold no_equal.
  split. lia. split. iner_p.
  split. iner_p. split. iner_p. split. iner_p. iner_p.
  rewrite H8.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H8.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
  rewrite H7.
  rewrite nat2fb_a_nat2fb. easy.
  intros.
  rewrite <- H7.
  unfold get_cus.
  bdestruct (i <? get_size size b). lia. easy.
Qed.

Lemma aenv_match_value_cfac : forall x t xv size aenv bv smap vmap rh rl stack temp,
       type_factor bv x = Some t -> vmap xv <> stack -> vmap xv <> temp ->
       cstore_store_match smap rh rl bv ->  bv_store_sub smap bv rh -> bv_store_gt_0 smap bv -> 
       aenv_match stack temp size bv aenv vmap -> par_find_var_check smap bv size rl x = Some (Value xv) ->
       aenv (vmap xv) = get_size size (snd t).
Proof.
  intros. 
  unfold type_factor,aenv_match,par_find_var_check in *.
  destruct x.
  destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
  simpl in *. destruct t0.
  destruct (typ_factor_full bv C Nat v) eqn:eq2.
  apply factor_type_c in eq2 as eq3.
  destruct p. simpl in *. inv H.
  destruct (par_eval_fc bv size rl v) eqn:eq3.
  simpl in *.
  bdestruct (a_nat2fb b1 size <? smap x).
  inv H6.
  specialize (H5 (x, a_nat2fb b1 size) H0 H1).
  rewrite H5. unfold get_size.
  simpl in *. rewrite eq1.
  unfold is_bl.
  bdestruct (b =b= Bl). subst. easy. destruct b. easy. easy. easy.
  inv H6.
  assert (par_eval_fc bv size rl v <> None).
  rewrite (sem_factor_full_par_eval_same_c v (C,b0) C Nat bv smap size rh); try easy.
  easy. simpl in *. easy. inv H. simpl in *. easy.
  unfold typ_factor in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *. destruct t0. easy. inv H. inv H6.
  apply H5 in H1. rewrite H1.
  unfold is_bl. simpl in *. rewrite eq1.
  unfold get_size.
  destruct b eqn:eq2. easy. easy. easy. easy.
  simpl in *. inv H. easy.
Qed.

Lemma par_find_get_var : forall smap bv size rl x xv, 
    par_find_var_check smap bv size rl x = Some (Value xv) -> (exists xvar, hd_error (get_var_cfac x) = Some xvar).
Proof.
  intros. unfold par_find_var_check,get_var_cfac in *.
  destruct x.
  exists x. easy.
  destruct v.
  simpl. exists v. easy.
  easy.
Qed.

Lemma hd_list_in {A} : forall x l, hd_error l = Some x -> @In A x l.
Proof.
  intros. destruct l. simpl in *. easy. inv H. simpl. left. easy.
Qed.

Lemma not_eq_stack_var : forall stack temp vmap smap l bv size rl x xvar xv t, 
         hd_error (get_var_cfac x) = Some xvar -> In xvar l -> 
         par_find_var_check smap bv size rl x = Some (Value xv) ->
         type_factor bv x = Some t -> bv_store_gt_0 smap bv ->
         not_stack stack temp vmap smap l -> vmap xv <> stack.
Proof.
  intros.
  unfold par_find_var_check,get_var_cfac,type_factor in *.
  destruct x. simpl in *.
  destruct (par_eval_fc bv size rl v) eqn:eq1.
  simpl in *.
  bdestruct (a_nat2fb b size <? smap x). inv H1.
  unfold not_stack in *.
  inv H.
  specialize (H4 xvar H0 (a_nat2fb b size) H5).
  easy. inv H1. simpl in *. easy.
  unfold typ_factor in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *.
  destruct t0. easy. inv H2.
  unfold bv_store_gt_0 in H3.
  specialize (H3 v).
  unfold BEnv.In,BEnv.Raw.PX.In in H3.
  apply BEnv.find_2 in eq1.
  assert ((exists e : typ, BEnv.Raw.PX.MapsTo v e (BEnv.this bv))).
  exists (TNor a b). easy. apply H3 in H2.
  unfold not_stack in *.
  inv H1. inv H.
  specialize (H4 xvar H0 0). apply H4 in H2. easy.
  simpl in *. easy. easy.
Qed.

Lemma not_eq_temp_var : forall stack temp vmap smap l bv size rl x xvar xv t, 
         hd_error (get_var_cfac x) = Some xvar -> In xvar l -> 
         par_find_var_check smap bv size rl x = Some (Value xv) ->
         type_factor bv x = Some t -> bv_store_gt_0 smap bv ->
         not_stack stack temp vmap smap l -> vmap xv <> temp.
Proof.
  intros.
  unfold par_find_var_check,get_var_cfac,type_factor in *.
  destruct x. simpl in *.
  destruct (par_eval_fc bv size rl v) eqn:eq1.
  simpl in *.
  bdestruct (a_nat2fb b size <? smap x). inv H1.
  unfold not_stack in *.
  inv H.
  specialize (H4 xvar H0 (a_nat2fb b size) H5).
  easy. inv H1. simpl in *. easy.
  unfold typ_factor in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *.
  destruct t0. easy. inv H2.
  unfold bv_store_gt_0 in H3.
  specialize (H3 v).
  unfold BEnv.In,BEnv.Raw.PX.In in H3.
  apply BEnv.find_2 in eq1.
  assert ((exists e : typ, BEnv.Raw.PX.MapsTo v e (BEnv.this bv))).
  exists (TNor a b). easy. apply H3 in H2.
  unfold not_stack in *.
  inv H1. inv H.
  specialize (H4 xvar H0 0). apply H4 in H2. easy.
  simpl in *. easy. easy.
Qed.

Lemma all_nor_var : forall vmap smap tenv l bv size rl x xvar xv t, 
         hd_error (get_var_cfac x) = Some xvar -> In xvar l -> 
         par_find_var_check smap bv size rl x = Some (Value xv) ->
         type_factor bv x = Some t -> bv_store_gt_0 smap bv ->
         all_nor vmap smap l tenv -> Env.MapsTo (vmap xv) PQASM.Nor tenv.
Proof.
  intros.
  unfold par_find_var_check,get_var_cfac,type_factor in *.
  destruct x. simpl in *.
  destruct (par_eval_fc bv size rl v) eqn:eq1.
  simpl in *.
  bdestruct (a_nat2fb b size <? smap x). inv H1.
  unfold all_nor in *.
  inv H.
  specialize (H4 xvar H0 (a_nat2fb b size) H5).
  easy. inv H1. simpl in *. easy.
  unfold typ_factor in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *.
  destruct t0. easy. inv H2.
  unfold bv_store_gt_0 in H3.
  specialize (H3 v).
  unfold BEnv.In,BEnv.Raw.PX.In in H3.
  apply BEnv.find_2 in eq1.
  assert ((exists e : typ, BEnv.Raw.PX.MapsTo v e (BEnv.this bv))).
  exists (TNor a b). easy. apply H3 in H2.
  unfold all_nor in *.
  inv H1. inv H.
  specialize (H4 xvar H0 0). apply H4 in H2. easy.
  simpl in *. easy. easy.
Qed.

Lemma stored_value_typed : forall smap rh bv size x xv a b, 
     sem_cfac smap size rh x = Some (Value xv) -> type_factor bv x = Some (a,b) ->
     store_typed rh bv size ->
     ( forall i : nat, i >= get_size size b -> xv i = false).
Proof.
  intros.
  unfold sem_cfac,type_factor in *.
  destruct x.
  destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
  destruct (sem_factor size rh v) eqn:eq2.
  simpl in *.
  destruct t.
  destruct (typ_factor_full bv C Nat v) eqn:eq3.
  simpl in *.
  bdestruct (a_nat2fb b0 size <? smap x).
  destruct (Store.find (elt:=list (nat -> bool)) (x, a_nat2fb b0 size) rh) eqn:eq4.
  simpl in *.
  destruct l. simpl in *. easy. simpl in *.
  inv H.
  unfold store_typed in *.
  apply Store.find_2 in eq4.
  assert (In xv (xv::l)). simpl. left. easy.
  specialize (H1 (x, a_nat2fb b0 size) (xv :: l) xv eq4 H).
  apply H1.
  unfold is_bl,get_size in *.
  simpl in *.
  rewrite eq1.
  inv H0. bdestruct (b =b= Bl). subst. lia.
  destruct b. lia. lia. easy.
  easy. inv H. simpl in *. easy. easy.
  simpl in *. easy. simpl in *. easy.
  unfold typ_factor in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) v bv ) eqn:eq1.
  simpl in *.
  destruct (Store.find (elt:=list (nat -> bool)) (v, 0) rh) eqn:eq2.
  destruct l. simpl in *. easy.
  simpl in *. inv H.
  destruct t. easy.
  inv H0.
  unfold store_typed in H1.
  apply Store.find_2 in eq2.
  assert (In xv (xv::l)). simpl. left. easy.
  specialize (H1 (v,0) (xv::l) xv eq2 H).
  apply H1.
  unfold is_bl,get_size in *.
  simpl. rewrite eq1.
  bdestruct (b =b= Bl). subst. lia. destruct b. lia. lia. easy.
  easy. easy. simpl in *.
  unfold get_size in *. inv H0. bdestruct (b =b= Bl).
  simpl in *. inv H.
  unfold cut_n.
  bdestruct (i <? 1). lia. easy.
  bdestruct (b =b= Nat). simpl in *. inv H.
  unfold cut_n.
  bdestruct (i <? size). lia. easy.
  simpl in *. inv H.
  unfold fbrev,cut_n.
  bdestruct (i <? size). lia. easy.
Qed.

Lemma get_cus_small : forall size f x n, n <= size -> 
        get_cus size f x = allfalse -> get_cus n f x = allfalse.
Proof.
  intros.
  unfold get_cus in *.
  apply functional_extensionality.
  intros.
  bdestruct (x0 <? n).
  rewrite <- H0.
  bdestruct (x0 <? size). easy. lia.
  easy.
Qed.

Lemma par_find_var_check_eq : forall smap bv size rl x xv,
   par_find_var_check smap bv size rl x = Some (Value xv) -> par_find_var bv size rl x = Some xv.
Proof.
  intros. unfold par_find_var_check,par_find_var in *.
  destruct x.
  destruct (par_eval_fc bv size rl v) eqn:eq1.
  simpl in *.
  bdestruct (a_nat2fb b size <? smap x).
  inv H. easy.
  inv H. easy.
  destruct v. inv H. easy. easy.
Qed.

(* Main theorem for the correctness of cexp. Compilation correctness. *)
Lemma compile_cexp_sem : forall t sl size smap vmap bv fl rh rl stack temp sn e st re f aenv tenv, 
      type_cexp bv e = Some t ->
      compile_cexp size smap vmap bv fl rl stack temp sn e = Some st ->
      sem_cexp smap bv size rh e = Some re ->
      0 < size -> S (S sn) < sl ->
      cstore_store_match smap rh rl bv -> bv_store_sub smap bv rh -> bv_store_gt_0 smap bv ->
      store_typed rh bv size -> store_match_q rh f bv vmap (aenv (get_size size (snd t))) ->
      store_match_st sl sn stack f vmap ->
      aenv_match stack temp size bv ((aenv (get_size size (snd t)))) vmap ->
      not_stack stack temp vmap smap (get_var_cexp e) ->
      all_nor vmap smap (get_var_cexp e) tenv -> 
      stack <> temp -> aenv (get_size size (snd t)) temp = (get_size size (snd t))
      -> aenv (get_size size (snd t)) stack = sl -> get_cus size f temp = nat2fb 0 ->
      Env.MapsTo temp PQASM.Nor tenv -> Env.MapsTo stack PQASM.Nor tenv ->
      right_mode_env (aenv (get_size size (snd t))) tenv f -> qft_uniform (aenv (get_size size (snd t))) tenv f 
         -> qft_gt (aenv (get_size size (snd t)))  tenv f
          -> vmap_bij vmap
         -> (st = Error /\ re = Error) \/ (exists b, st = Value (None,sn,Some b) /\ re = Value b)
              \/ (exists p, st = Value (Some p, S sn,None) 
                 /\ re = (Value (get_cua (exp_sem (aenv (get_size size (snd t))) p f (stack,sn))))).
Proof.
  intros. destruct e.
 - 
  simpl in *.
  destruct (qvar_eq smap bv size rl x y) eqn:Y1.
  destruct v as [bval| ]. destruct (¬ bval) eqn:eq1.
  unfold gen_clt_c in *.
  destruct (type_factor bv x) eqn:eq2.
  destruct (type_factor bv y) eqn:eq3.
  simpl in *.
  unfold meet_type,meet_btype,meet_atype in H.
  destruct p. destruct p0. simpl in *.
  bdestruct (b =b= b0). simpl in H. subst.
  destruct a eqn:eq4. unfold ret in H. 
  bdestruct (C =a= Q). inv H15. simpl in *.
  bdestruct (a0 =a= Q). subst.
  destruct (sem_cfac smap size rh x) eqn:eq5.
  destruct v. 
  destruct (sem_cfac smap size rh y) eqn:eq6. 
  destruct v. simpl in *. inv H1.
  destruct (par_find_var_check smap bv size rl y) eqn:eq7.
  destruct v.
  assert (par_eval_cfac_check smap bv size rl x = Some (Value x0)).
  rewrite sem_cfac_par_eval_same_c with (t := (C, b0)) (rh := rh); try easy.
  rewrite H1 in *.
  simpl in *. inv H0.
  right. right.
  exists (clt_circuit_right size fl b0 vmap x0 x2 stack temp sn). split.
  easy.
  remember (aenv (get_size size (snd t)) stack) as sl.
  assert (aenv (get_size size b0) (vmap x2) = get_size size b0) as eq8.
  rewrite (aenv_match_value_cfac y (Q, b0) x2
          size (aenv (get_size size b0)) bv smap vmap rh rl stack temp); try easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy. inv H. easy.
  rewrite clt_circuit_right_sem with (tenv := tenv) (v := x1) (sl := sl); try easy.
  inv H. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy. 
  inv H. simpl in *. easy.
  rewrite <- eq8.
  inv H. simpl in *.
  rewrite (q_var_same_value y x2 (Q, b0) x1 smap vmap bv size rh rl); try easy.
  rewrite eq8. apply cut_n_eq.
  apply (stored_value_typed smap rh bv size y x1 Q); try easy.
  unfold nat2fb in *. simpl in *.
  apply get_cus_small with (size := size); try easy.
  unfold get_size. bdestruct (b0 =b= Bl). lia. lia.
  apply par_find_get_var in eq7 as X1. destruct X1.
  Check all_nor_var.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
             bv size rl y x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy. 
  inv H0.
  rewrite type_cfac_sem_error with (t := (Q, b0)) (bv:=bv) (rl:=rl) in eq6; try easy.
  easy.
  simpl in *.
  assert (par_find_var_check smap bv size rl y = Some Error).
  apply type_cfac_find_var_error with (t := (Q,b0)) (rh := rh); try easy.
  rewrite H23 in *.
  inv H1. inv H0. left. easy.
  simpl in *. inv H1.
  simpl in *. 
  destruct (par_find_var_check smap bv size rl y) eqn:eq6.
  simpl in *. destruct v.
  assert (par_eval_cfac_check smap bv size rl x = Some Error).
  rewrite sem_cfac_par_eval_same_c with (t := (C, b0)) (rh := rh); try easy.
  rewrite H23 in *.
  simpl in *.
  destruct (sem_cfac smap size rh y). simpl in *.
  inv H1. inv H0. left. easy.
  easy.
  destruct (sem_cfac smap size rh y). simpl in *. 
  inv H1. inv H0. left. easy.
  easy. easy.
  simpl in *. easy.
  simpl in *.
  destruct a0.
  destruct (sem_cfac smap size rh x) eqn:eq5.
  destruct v. 
  destruct (sem_cfac smap size rh y) eqn:eq6. 
  destruct v. simpl in *. inv H1.
  rewrite <- sem_cfac_par_eval_same_c with (t := (C, b0)) (bv := bv) (rl:=rl) in eq5; try easy.
  rewrite <- sem_cfac_par_eval_same_c with (t := (C, b0)) (bv := bv) (rl:=rl) in eq6; try easy.
  rewrite eq5 in *. rewrite eq6 in *. simpl in *.
  inv H0.
  right. 
  left.
  exists ((a_nat2fb x0 (get_size size b0) <?
       a_nat2fb x1 (get_size size b0))). easy.
  rewrite <- sem_cfac_par_eval_same_c with (t := (C, b0)) (bv := bv) (rl:=rl) in eq5; try easy.
  rewrite <- sem_cfac_par_eval_same_c with (t := (C, b0)) (bv := bv) (rl:=rl) in eq6; try easy.
  rewrite eq5 in *. rewrite eq6 in *. simpl in *.
  inv H1. inv H0. left. easy.
  simpl in *. easy.
  simpl in *.
  rewrite <- sem_cfac_par_eval_same_c with (t := (C, b0)) (bv := bv) (rl:=rl) in eq5; try easy.
  rewrite eq5 in *.
  simpl in *.
  destruct (sem_cfac smap size rh y).
  destruct (par_eval_cfac_check smap bv size rl y).
  simpl in *. 
  inv H1. inv H0. left. easy.
  simpl in *. 
  inv H1. inv H0. left. easy.
  simpl in *. easy. easy.
  inv H. simpl in *.
  destruct a0. simpl in *.
  destruct (sem_cfac smap size rh x) eqn:eq5.
  destruct v. 
  destruct (sem_cfac smap size rh y) eqn:eq6. 
  destruct v. simpl in *. inv H1.
  destruct (par_find_var_check smap bv size rl x) eqn:eq7.
  destruct v.
  assert (par_eval_cfac_check smap bv size rl y = Some (Value x1)).
  rewrite sem_cfac_par_eval_same_c with (t := (C, b0)) (rh := rh); try easy.
  rewrite H in *.
  simpl in *. inv H0.
  right. right.
  exists ((clt_circuit_left size fl b0 vmap x2 x1 stack temp sn)). split.
  easy.
  remember (aenv (get_size size b0) stack) as sl.
  assert (aenv (get_size size b0) (vmap x2) = get_size size b0) as eq8.
  Check aenv_match_value_cfac.
  rewrite (aenv_match_value_cfac x (Q, b0) x2
          size (aenv (get_size size b0)) bv smap vmap rh rl stack temp); try easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy. 
  Check clt_circuit_left_sem.
  rewrite clt_circuit_left_sem with (tenv := tenv) (v := x0) (sl := sl); try easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy. 
  rewrite <- eq8.
  Check q_var_same_value.
  rewrite (q_var_same_value x x2 (Q, b0) x0 smap vmap bv size rh rl); try easy.
  rewrite eq8. apply cut_n_eq.
  apply (stored_value_typed smap rh bv size x x0 Q); try easy.
  unfold nat2fb in *. simpl in *.
  apply get_cus_small with (size := size); try easy.
  unfold get_size. bdestruct (b0 =b= Bl). lia. lia.
  apply par_find_get_var in eq7 as X1. destruct X1.
  Check all_nor_var.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
             bv size rl x x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy. 
  inv H0.
  rewrite type_cfac_sem_error with (t := (Q, b0)) (bv:=bv) (rl:=rl) in eq5; try easy.
  easy.
  simpl in *.
  destruct (par_find_var_check smap bv size rl x) eqn:eq7.
  simpl in *. destruct v.
  assert (par_eval_cfac_check smap bv size rl y = Some Error).
  rewrite sem_cfac_par_eval_same_c with (t := (C, b0)) (rh := rh); try easy.
  rewrite H in *.
  simpl in *.
  inv H1. inv H0. left. easy.
  inv H1. inv H0. left. easy. easy.
  simpl in *. easy. simpl in *.
  assert (par_find_var_check smap bv size rl x = Some Error).
  apply type_cfac_find_var_error with (t := (Q,b0)) (rh := rh); try easy.
  rewrite H in *.
  destruct (sem_cfac smap size rh y). simpl in *.
  inv H1. inv H0. left. easy.
  simpl in *. easy.
  easy.
  destruct (sem_cfac smap size rh x) eqn:eq5.
  destruct v. 
  destruct (sem_cfac smap size rh y) eqn:eq6. 
  destruct v. simpl in *. inv H1.
  destruct (par_find_var_check smap bv size rl x) eqn:eq7.
  destruct v.
  destruct (par_find_var_check smap bv size rl y) eqn:eq8.
  destruct v. simpl in *. inv H0.
  right. right.
  assert (aenv (get_size size b0) (vmap x2) = get_size size b0) as eq9.
  rewrite (aenv_match_value_cfac x (Q, b0) x2
          size (aenv (get_size size b0)) bv smap vmap rh rl stack temp); try easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x4 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x4 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  assert (aenv (get_size size b0) (vmap x3) = get_size size b0) as eq10.
  rewrite (aenv_match_value_cfac y (Q, b0) x3
          size (aenv (get_size size b0)) bv smap vmap rh rl stack temp); try easy.
  apply par_find_get_var in eq8 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x4 x3 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  apply par_find_get_var in eq8 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x4 x3 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  exists (clt_circuit_two size fl b0 vmap x2 x3 stack sn). split. easy.
  remember (aenv (get_size size b0) stack) as sl.
  rewrite clt_circuit_two_sem with (tenv := tenv) (v1 := x0) (v2 := x1) (sl := sl) ; try easy.
  unfold qvar_eq in Y1.
  rewrite eq7 in Y1. rewrite eq8 in Y1.
  bdestruct (x2 =qd= x3). inv Y1. easy.
  apply H22. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x4 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq8 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x4 x3 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  Check q_var_same_value.
  rewrite <- eq9.
  rewrite (q_var_same_value x x2 (Q, b0) x0 smap vmap bv size rh rl); try easy.
  rewrite eq9. apply cut_n_eq.
  apply (stored_value_typed smap rh bv size x x0 Q); try easy.
  rewrite <- eq10.
  rewrite (q_var_same_value y x3 (Q, b0) x1 smap vmap bv size rh rl); try easy.
  rewrite eq10. apply cut_n_eq.
  apply (stored_value_typed smap rh bv size y x1 Q); try easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  Check all_nor_var.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
             bv size rl x x4 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy. 
  apply par_find_get_var in eq8 as X1. destruct X1.
  Check all_nor_var.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
             bv size rl y x4 x3 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  simpl in *.
  rewrite type_cfac_sem_error with (t := (Q, b0)) (bv:=bv) (rl:=rl) in eq6; try easy.
  simpl in *. easy.
  simpl in *. 
  rewrite type_cfac_sem_error with (t := (Q, b0)) (bv:=bv) (rl:=rl) in eq5; try easy.
  simpl in *. easy.
  simpl in *.
  destruct (par_find_var_check smap bv size rl x) eqn:eq7. destruct v.
  destruct (par_find_var_check smap bv size rl y) eqn:eq8. destruct v. simpl in *.
  rewrite type_cfac_find_var_error with (t := (Q, b0)) (bv:=bv) (rh:=rh) in eq8; try easy.
  simpl in *. inv H0. inv H1. left. easy.
  simpl in *. easy.
  rewrite type_cfac_sem_error with (t := (Q, b0)) (bv:=bv) (rl:=rl) in eq5; try easy.
  simpl in *. easy.
  simpl in *. easy.
  simpl in *.
  destruct (par_find_var_check smap bv size rl x) eqn:eq7. destruct v. 
  rewrite type_cfac_find_var_error with (t := (Q, b0)) (bv:=bv) (rh:=rh) in eq7; try easy.
  simpl in *.
  destruct (sem_cfac smap size rh y). destruct (par_find_var_check smap bv size rl y).
  simpl in *.
  inv H0. inv H1. left. easy.
  simpl in *.
  inv H0. inv H1. left. easy.
  1-4:easy. inv H0.
  unfold qvar_eq in Y1.
  destruct (type_factor bv x) eqn:eq2. destruct p.
  destruct (type_factor bv y) eqn:eq3. destruct p. simpl in *.
  destruct (par_find_var_check smap bv size rl x) eqn:eq4. destruct v.
  destruct (par_find_var_check smap bv size rl y) eqn:eq5. destruct v.
  bdestruct ((x0 =qd= x1)). subst.
  apply type_cfac_sem_value with (t := (a,b)) (rh := rh) in eq4 as X1; try easy.
  destruct X1.
  rewrite H0 in *.
  Check type_cfac_sem_value_same.
  rewrite (type_cfac_sem_value_same x y x1 (a,b) (a0,b0) bv smap size rh rl) in H0; try easy.
  rewrite H0 in *. 
  simpl in *. inv H1.
  right. left. exists false. split. easy.
  bdestruct ((a_nat2fb x0 (get_size size b) <? a_nat2fb x0 (get_size size b))). lia. easy.
  inv Y1. 1-7:easy.
  unfold qvar_eq in *.
  destruct (par_find_var_check smap bv size rl x) eqn:eq1. destruct v.
  destruct (par_find_var_check smap bv size rl y) eqn:eq2. destruct v. easy.
  destruct (type_factor bv x) eqn:eq3.
  destruct (type_factor bv y) eqn:eq4.
  apply type_cfac_sem_error with (t:= p0) (rh := rh) in eq2; try easy.
  rewrite eq2 in *. simpl in *.
  destruct (sem_cfac smap size rh x) eqn:eq5. simpl in *. destruct v.
  inv H0. inv H1. left. easy.
  inv H0. inv H1. left. easy.
  1-4:easy.
  destruct (type_factor bv x) eqn:eq3.
  apply type_cfac_sem_error with (t:= p) (rh := rh) in eq1; try easy.
  rewrite eq1 in *. simpl in *.
  destruct (sem_cfac smap size rh y).
  inv H0. inv H1. left. easy.
  inv H0. inv H1. left. easy.
  easy. easy.
 - 
  simpl in *.
  destruct (qvar_eq smap bv size rl x y) eqn:Y1.
  destruct v as [bval| ]. destruct (¬ bval) eqn:eq1.
  unfold gen_ceq_c in *.
  destruct (type_factor bv x) eqn:eq2.
  destruct (type_factor bv y) eqn:eq3.
  simpl in *.
  unfold meet_type,meet_btype,meet_atype in H.
  destruct p. destruct p0. simpl in *.
  bdestruct (b =b= b0). simpl in H. subst.
  destruct a eqn:eq4. unfold ret in H. inv H. simpl in *.
  bdestruct (a0 =a= Q). subst.
  destruct (sem_cfac smap size rh x) eqn:eq5.
  destruct v. 
  destruct (sem_cfac smap size rh y) eqn:eq6. 
  destruct v. simpl in *. inv H1.
  destruct (par_find_var_check smap bv size rl y) eqn:eq7.
  destruct v.
  assert (par_eval_cfac_check smap bv size rl x = Some (Value x0)).
  rewrite sem_cfac_par_eval_same_c with (t := (C, b0)) (rh := rh); try easy.
  rewrite H in *.
  simpl in *. inv H0.
  right. right.
  exists (ceq_circuit_right size fl b0 vmap x0 x2 stack temp sn). split.
  easy.
  remember (aenv (get_size size b0) stack) as sl.
  assert (aenv (get_size size b0) (vmap x2) = get_size size b0) as eq8.
  rewrite (aenv_match_value_cfac y (Q, b0) x2
          size (aenv (get_size size b0)) bv smap vmap rh rl stack temp); try easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  rewrite ceq_circuit_right_sem with (tenv := tenv) (v := x1) (sl := sl); try easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy. 
  rewrite <- eq8.
  rewrite (q_var_same_value y x2 (Q, b0) x1 smap vmap bv size rh rl); try easy.
  rewrite eq8. apply cut_n_eq.
  apply (stored_value_typed smap rh bv size y x1 Q); try easy.
  unfold nat2fb in *. simpl in *.
  apply get_cus_small with (size := size); try easy.
  unfold get_size. bdestruct (b0 =b= Bl). lia. lia.
  apply par_find_get_var in eq7 as X1. destruct X1.
  Check all_nor_var.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
             bv size rl y x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy. 
  inv H0.
  rewrite type_cfac_sem_error with (t := (Q, b0)) (bv:=bv) (rl:=rl) in eq6; try easy.
  easy.
  simpl in *.
  assert (par_find_var_check smap bv size rl y = Some Error).
  apply type_cfac_find_var_error with (t := (Q,b0)) (rh := rh); try easy.
  rewrite H in *.
  inv H1. inv H0. left. easy.
  simpl in *. inv H1.
  simpl in *. 
  destruct (par_find_var_check smap bv size rl y) eqn:eq6.
  simpl in *. destruct v.
  assert (par_eval_cfac_check smap bv size rl x = Some Error).
  rewrite sem_cfac_par_eval_same_c with (t := (C, b0)) (rh := rh); try easy.
  rewrite H in *.
  simpl in *.
  destruct (sem_cfac smap size rh y). simpl in *.
  inv H1. inv H0. left. easy.
  easy.
  destruct (sem_cfac smap size rh y). simpl in *. 
  inv H1. inv H0. left. easy.
  easy. easy.
  simpl in *. easy.
  simpl in *.
  destruct a0.
  destruct (sem_cfac smap size rh x) eqn:eq5.
  destruct v. 
  destruct (sem_cfac smap size rh y) eqn:eq6. 
  destruct v. simpl in *. inv H1.
  rewrite <- sem_cfac_par_eval_same_c with (t := (C, b0)) (bv := bv) (rl:=rl) in eq5; try easy.
  rewrite <- sem_cfac_par_eval_same_c with (t := (C, b0)) (bv := bv) (rl:=rl) in eq6; try easy.
  rewrite eq5 in *. rewrite eq6 in *. simpl in *.
  inv H0.
  right. 
  left.
  exists ((a_nat2fb x0 (get_size size b0) =?
       a_nat2fb x1 (get_size size b0))). easy.
  rewrite <- sem_cfac_par_eval_same_c with (t := (C, b0)) (bv := bv) (rl:=rl) in eq5; try easy.
  rewrite <- sem_cfac_par_eval_same_c with (t := (C, b0)) (bv := bv) (rl:=rl) in eq6; try easy.
  rewrite eq5 in *. rewrite eq6 in *. simpl in *.
  inv H1. inv H0. left. easy.
  simpl in *. easy.
  simpl in *.
  rewrite <- sem_cfac_par_eval_same_c with (t := (C, b0)) (bv := bv) (rl:=rl) in eq5; try easy.
  rewrite eq5 in *.
  simpl in *.
  destruct (sem_cfac smap size rh y).
  destruct (par_eval_cfac_check smap bv size rl y).
  simpl in *. 
  inv H1. inv H0. left. easy.
  simpl in *. 
  inv H1. inv H0. left. easy.
  simpl in *. easy. easy.
  inv H. simpl in *.
  destruct a0. simpl in *.
  destruct (sem_cfac smap size rh x) eqn:eq5.
  destruct v. 
  destruct (sem_cfac smap size rh y) eqn:eq6. 
  destruct v. simpl in *. inv H1.
  destruct (par_find_var_check smap bv size rl x) eqn:eq7.
  destruct v.
  assert (par_eval_cfac_check smap bv size rl y = Some (Value x1)).
  rewrite sem_cfac_par_eval_same_c with (t := (C, b0)) (rh := rh); try easy.
  rewrite H in *.
  simpl in *. inv H0.
  right. right.
  exists ((ceq_circuit_left size fl b0 vmap x2 x1 stack temp sn)). split.
  easy.
  remember (aenv (get_size size b0) stack) as sl.
  assert (aenv (get_size size b0) (vmap x2) = get_size size b0) as eq8.
  Check aenv_match_value_cfac.
  rewrite (aenv_match_value_cfac x (Q, b0) x2
          size (aenv (get_size size b0)) bv smap vmap rh rl stack temp); try easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy. 
  Check ceq_circuit_left_sem.
  rewrite ceq_circuit_left_sem with (tenv := tenv) (v := x0) (sl := sl); try easy.
  bdestruct ((a_nat2fb x0 (get_size size b0) =? a_nat2fb x1 (get_size size b0))).
  bdestruct ((a_nat2fb x1 (get_size size b0) =? a_nat2fb x0 (get_size size b0))).
  easy. lia.
  bdestruct ((a_nat2fb x1 (get_size size b0) =? a_nat2fb x0 (get_size size b0))).
  lia. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy. 
  rewrite <- eq8.
  Check q_var_same_value.
  rewrite (q_var_same_value x x2 (Q, b0) x0 smap vmap bv size rh rl); try easy.
  rewrite eq8. apply cut_n_eq.
  apply (stored_value_typed smap rh bv size x x0 Q); try easy.
  unfold nat2fb in *. simpl in *.
  apply get_cus_small with (size := size); try easy.
  unfold get_size. bdestruct (b0 =b= Bl). lia. lia.
  apply par_find_get_var in eq7 as X1. destruct X1.
  Check all_nor_var.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
             bv size rl x x3 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy. 
  inv H0.
  rewrite type_cfac_sem_error with (t := (Q, b0)) (bv:=bv) (rl:=rl) in eq5; try easy.
  easy.
  simpl in *.
  destruct (par_find_var_check smap bv size rl x) eqn:eq7.
  simpl in *. destruct v.
  assert (par_eval_cfac_check smap bv size rl y = Some Error).
  rewrite sem_cfac_par_eval_same_c with (t := (C, b0)) (rh := rh); try easy.
  rewrite H in *.
  simpl in *.
  inv H1. inv H0. left. easy.
  inv H1. inv H0. left. easy. easy.
  simpl in *. easy. simpl in *.
  assert (par_find_var_check smap bv size rl x = Some Error).
  apply type_cfac_find_var_error with (t := (Q,b0)) (rh := rh); try easy.
  rewrite H in *.
  destruct (sem_cfac smap size rh y). simpl in *.
  inv H1. inv H0. left. easy.
  simpl in *. easy.
  easy.
  destruct (sem_cfac smap size rh x) eqn:eq5.
  destruct v. 
  destruct (sem_cfac smap size rh y) eqn:eq6. 
  destruct v. simpl in *. inv H1.
  destruct (par_find_var_check smap bv size rl x) eqn:eq7.
  destruct v.
  destruct (par_find_var_check smap bv size rl y) eqn:eq8.
  destruct v. simpl in *. inv H0.
  right. right.
  assert (aenv (get_size size b0) (vmap x2) = get_size size b0) as eq9.
  rewrite (aenv_match_value_cfac x (Q, b0) x2
          size (aenv (get_size size b0)) bv smap vmap rh rl stack temp); try easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x4 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x4 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  assert (aenv (get_size size b0) (vmap x3) = get_size size b0) as eq10.
  rewrite (aenv_match_value_cfac y (Q, b0) x3
          size (aenv (get_size size b0)) bv smap vmap rh rl stack temp); try easy.
  apply par_find_get_var in eq8 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x4 x3 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  apply par_find_get_var in eq8 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x4 x3 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  exists (ceq_circuit_two size fl b0 vmap x2 x3 stack sn). split. easy.
  remember (aenv (get_size size b0) stack) as sl.
  rewrite ceq_circuit_two_sem with (tenv := tenv) (v1 := x0) (v2 := x1) (sl := sl) ; try easy.
  unfold qvar_eq in Y1.
  rewrite eq7 in Y1. rewrite eq8 in Y1.
  bdestruct (x2 =qd= x3). inv Y1. easy.
  apply H22. easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl x x4 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq8 as X1. destruct X1.
  apply (not_eq_stack_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv size rl y x4 x3 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  Check q_var_same_value.
  rewrite <- eq9.
  rewrite (q_var_same_value x x2 (Q, b0) x0 smap vmap bv size rh rl); try easy.
  rewrite eq9. apply cut_n_eq.
  apply (stored_value_typed smap rh bv size x x0 Q); try easy.
  rewrite <- eq10.
  rewrite (q_var_same_value y x3 (Q, b0) x1 smap vmap bv size rh rl); try easy.
  rewrite eq10. apply cut_n_eq.
  apply (stored_value_typed smap rh bv size y x1 Q); try easy.
  apply par_find_get_var in eq7 as X1. destruct X1.
  Check all_nor_var.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
             bv size rl x x4 x2 (Q, b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy. 
  apply par_find_get_var in eq8 as X1. destruct X1.
  Check all_nor_var.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
             bv size rl y x4 x3 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  simpl in *.
  rewrite type_cfac_sem_error with (t := (Q, b0)) (bv:=bv) (rl:=rl) in eq6; try easy.
  simpl in *. easy.
  simpl in *. 
  rewrite type_cfac_sem_error with (t := (Q, b0)) (bv:=bv) (rl:=rl) in eq5; try easy.
  simpl in *. easy.
  simpl in *.
  destruct (par_find_var_check smap bv size rl x) eqn:eq7. destruct v.
  destruct (par_find_var_check smap bv size rl y) eqn:eq8. destruct v. simpl in *.
  rewrite type_cfac_find_var_error with (t := (Q, b0)) (bv:=bv) (rh:=rh) in eq8; try easy.
  simpl in *. inv H0. inv H1. left. easy.
  simpl in *. easy.
  rewrite type_cfac_sem_error with (t := (Q, b0)) (bv:=bv) (rl:=rl) in eq5; try easy.
  simpl in *. easy.
  simpl in *. easy.
  simpl in *.
  destruct (par_find_var_check smap bv size rl x) eqn:eq7. destruct v. 
  rewrite type_cfac_find_var_error with (t := (Q, b0)) (bv:=bv) (rh:=rh) in eq7; try easy.
  simpl in *.
  destruct (sem_cfac smap size rh y). destruct (par_find_var_check smap bv size rl y).
  simpl in *.
  inv H0. inv H1. left. easy.
  simpl in *.
  inv H0. inv H1. left. easy.
  1-4:easy. inv H0.
  unfold qvar_eq in Y1.
  destruct (type_factor bv x) eqn:eq2. destruct p.
  destruct (type_factor bv y) eqn:eq3. destruct p. simpl in *.
  destruct (par_find_var_check smap bv size rl x) eqn:eq4. destruct v.
  destruct (par_find_var_check smap bv size rl y) eqn:eq5. destruct v.
  bdestruct ((x0 =qd= x1)). subst.
  apply type_cfac_sem_value with (t := (a,b)) (rh := rh) in eq4 as X1; try easy.
  destruct X1.
  rewrite H0 in *.
  Check type_cfac_sem_value_same.
  rewrite (type_cfac_sem_value_same x y x1 (a,b) (a0,b0) bv smap size rh rl) in H0; try easy.
  rewrite H0 in *. 
  simpl in *. inv H1.
  right. left. exists true. split. easy.
  bdestruct ((a_nat2fb x0 (get_size size b) =? a_nat2fb x0 (get_size size b))). easy. lia.
  inv Y1. 1-7:easy.
  unfold qvar_eq in *.
  destruct (par_find_var_check smap bv size rl x) eqn:eq1. destruct v.
  destruct (par_find_var_check smap bv size rl y) eqn:eq2. destruct v. easy.
  destruct (type_factor bv x) eqn:eq3.
  destruct (type_factor bv y) eqn:eq4.
  apply type_cfac_sem_error with (t:= p0) (rh := rh) in eq2; try easy.
  rewrite eq2 in *. simpl in *.
  destruct (sem_cfac smap size rh x) eqn:eq5. simpl in *. destruct v.
  inv H0. inv H1. left. easy.
  inv H0. inv H1. left. easy.
  1-4:easy.
  destruct (type_factor bv x) eqn:eq3.
  apply type_cfac_sem_error with (t:= p) (rh := rh) in eq1; try easy.
  rewrite eq1 in *. simpl in *.
  destruct (sem_cfac smap size rh y).
  inv H0. inv H1. left. easy.
  inv H0. inv H1. left. easy.
  easy. easy.
 -
  unfold type_cexp in *.
  apply cfac_type_c in H as V1.
  rewrite V1 in *. clear V1.
  unfold compile_cexp,sem_cexp in *.
  assert (type_factor bv x = Some (C, Nat)) as V2.
  apply type_factor_full_same in H; easy.
  rewrite V2 in *. simpl in *.
  destruct (par_eval_cfac_check smap bv size rl x) eqn:eq1. destruct v.
  rewrite sem_cfac_par_eval_same_c with (t := (C,Nat)) (rh := rh) in eq1; try easy.
  rewrite eq1 in *. 
  simpl in *.
  unfold get_size in H1.
  bdestruct (Nat =b= Bl). easy.
  destruct (snd (Nat.divmod (a_nat2fb x0 size) 1 0 1)) eqn:eq2.
  bdestruct (1 =? 0). lia. inv H0. inv H1.
  right. left. exists false. easy.
  bdestruct (0 =? 0). inv H0. inv H1.
  right. left. exists true. easy. lia.
  rewrite sem_cfac_par_eval_same_c with (t := (C,Nat)) (rh := rh) in eq1; try easy.
  rewrite eq1 in *.
  simpl in *. inv H0. inv H1. left. easy.
  simpl in *.
  rewrite sem_cfac_par_eval_same_c with (t := (C,Nat)) (rh := rh) in eq1; try easy.
Qed.

(* Type system, semantics and compilation procedure for qexp. *)

(* For any Q-mode statements (the assigmment variable being Q mode) we require that the 
   assignment variables are different from the arguments. *)
Definition fresh_loop_cfac (x:var) (fc:cfac) :=
   match fc with  Nor (Var y) => if y =q= (L x) then false else true
             | _ => true
   end.

Fixpoint fresh_loop_c (x:var) (e:qexp) :=
   match e with skip => true
             | init y v => fresh_loop_cfac x y
             | unary y op v => fresh_loop_cfac x y
             | binapp y op z v => fresh_loop_cfac x y
             | slrot y => fresh_loop_cfac x y
             | qinv y => fresh_loop_cfac x y
             | call y f vs => fresh_loop_cfac x y
             | qif ce e1 e2 => (fresh_loop_c x e1) && (fresh_loop_c x e2)
             | qfor y n e => (fresh_loop_cfac x n) && (if x =? y then true else fresh_loop_c x e)
             | qseq e1 e2 => (fresh_loop_c x e1) && (fresh_loop_c x e2)
   end.

(* slrot is current static, so it cannot be used inside a if-condition,
    and we plan to make it also non-static. *)
Fixpoint no_rot (e:qexp) :=
   match e with skip => true
             | init y v => true
             | unary y op v => true
             | binapp y op z v => true
             | slrot y => false
             | qinv y => true
             | call y f vs => true
             | qif ce e1 e2 => (no_rot e1) && (no_rot e2)
             | qfor y n e => no_rot e
             | qseq e1 e2 => (no_rot e1) && (no_rot e2)
   end.


Definition is_q_fac (bv:benv) (c:factor) :=
    match c with Var x => match BEnv.find x bv with None => false
                              | Some t => is_q t
                          end
             | Num b x => false
    end.

Definition is_q_cfac (bv:benv) (c:cfac) :=
    match c with Index x n => 
          match BEnv.find x bv with None => false
                    | Some t => is_q t
          end
              | Nor x => is_q_fac bv x
    end.

(* Checks if an expression in if-branch has a C mode assigment. *)
Fixpoint has_c_exp (bv:benv) (e:qexp) :=
   match e with skip => false
             | init y v => ¬ (is_q_cfac bv y)
             | unary y op v => ¬ (is_q_cfac bv y)
             | slrot y => ¬ (is_q_cfac bv y)
             | binapp y op z v => ¬ (is_q_cfac bv y)
             | qinv y => false
             | call y f vs => ¬ (is_q_cfac bv y)
             | qif ce e1 e2 => (has_c_exp bv e1) && (has_c_exp bv e2)
             | qfor y n e => has_c_exp bv e
             | qseq e1 e2 => has_c_exp bv e1 && has_c_exp bv e2
   end.

Fixpoint type_factors_full (bv:benv) (tvl : list (atype * btype * var)) (fc: list cfac) :=
   match fc with [] => match tvl with [] => Some bv | _ => None end
         | (fc::fcl) => match tvl with [] => None
           | ((a,b,v)::tvl') => 
                  do re <- type_factor_full bv a b fc @ type_factors_full bv tvl' fcl
                         end
   end.

Definition check_fst_type (x:qop) (t : btype) :=
   match x with nadd | nsub | nmul | ndiv | nmod | nfac => (Nat =b= t)
              | fadd | fsub | fmul | fdiv | fndiv => (FixedP =b= t)
              | qxor => true
   end.

Definition check_snd_type (x:qop) (t : btype) :=
   match x with nadd | nsub | nmul | ndiv | nmod | nfac | fdiv => (Nat =b= t)
              | fadd | fsub | fmul | fndiv => (FixedP =b= t)
              | qxor => true
   end.

Definition check_trd_type (x:qop) (t : btype) :=
   match x with nadd | nsub | nmul | ndiv | nmod | nfac | fdiv | fndiv => (Nat =b= t)
              | fadd | fsub | fmul  => (FixedP =b= t)
              | qxor => true
   end.

Definition check_xor_type (x:qop) (t1 t2 : btype) :=
     if x =op= qxor then (t1 =b= t2) else true.

Definition is_c_unary (x:qop) := 
   match x with nadd | nsub | qxor | nfac | fdiv | fadd | fsub => true
            | _ => false
   end.

Definition is_q_unary (x:qop) := 
   match x with nadd | nsub | qxor | fadd | fsub => true
            | _ => false
   end.


Definition is_unary (a:atype) (x:qop) := 
   if a =a= C then is_c_unary x else is_q_unary x.

Definition is_bin (x:qop) := 
   match x with nadd | nsub | nmul | fadd | fsub | fmul | ndiv | nmod | fndiv => true
            | _ => false
   end.

Definition get_unary_type (x:qop) (t:btype) :=
    match x with fdiv => Nat | _ => t end.


Definition sub_atype (a1 a2 : (atype)) :=
    if a1 =a= C then true else a2 =a= Q.

Definition sub_type (t1 t2:(atype * btype)) := 
    (snd t1 =b= snd t2) && sub_atype (fst t1) (fst t2).

Definition opp_atype (a:atype) := if a =a= C then Q else C.

(* Typing rule for statements. sub_nor *)
Fixpoint type_qexp (fv:fenv) (bv:benv) (a:atype) (e:qexp):=
   match e with skip => Some bv
             | init x v => 
               do core <- get_var x @ 
                  do re1 <- type_factor bv x @
                    do re2 <- type_factor bv v @ 
                   if (sub_type re2 re1) && sub_atype a (fst re1) then ret bv else None

             | slrot x =>
                   do core <- get_var x @
                    do re <- type_factor bv x @ 
                   if a =a= C then ret bv else None

             | unary x op y => 
             do core <- get_var x @
               do re1 <- type_factor bv x @
                do re2 <- type_factor bv y @ 
                        if is_unary (fst re1) op && check_fst_type op (snd re1)
                                  && check_snd_type op (snd re2)
                                 && sub_atype (fst re2) (fst re1) && sub_atype a (fst re1)
                                 && check_xor_type op (snd re1) (snd re2) then ret bv else None

             | binapp x op y z => 
              do core <- get_var x @
               do re1 <- type_factor bv x @
                do re2 <- type_factor bv y @ 
                 do re3 <- type_factor bv z @
                        if is_bin op && check_fst_type op (snd re1)
                          && check_snd_type op (snd re2)
                          && check_trd_type op (snd re3)
                          && sub_type re2 re1 && sub_atype a (fst re1) then ret bv else None

              | call x f vs => 
                 do ref <- FEnv.find f fv @
                   match ref with (tvl,tcl,e,fbenv, rx) =>
                    do res <- type_factors_full bv tvl vs @
                     do rxv <- type_factor fbenv rx @
                          do core <- get_var x @
                           do old <- type_factor bv x @
                              if sub_type rxv old && sub_atype a (fst old) then ret bv else None
                   end

              | qif ce e1 e2 => 
                 do rce <- type_cexp bv ce @
                   do bv' <- type_qexp fv bv (opp_atype (fst rce)) e1 @
                       type_qexp fv bv (opp_atype (fst rce)) e2 

              | qseq e1 e2 => 
                 do bv <- type_qexp fv bv a e1 @ type_qexp fv bv a e2

              | qfor x n e => 
                do re1 <- BEnv.find (L x) bv @
                 match re1 with (TNor C Nat) =>
                  do re2 <- type_factor_full bv C Nat n @ 
                   if fresh_loop_c x e then 
                     type_qexp fv bv a e
                   else None
                     | _ => None
                 end


             | _ => None
    end.


Fixpoint type_funs (benv:benv) (fv:fenv) (l:list func) : option fenv :=
     match l with [] => Some fv
              | ((f,tvl,l,e,rx)::fs) => 
              do benv' <- gen_env_l tvl benv @
               do benv'' <- gen_env l benv' @
                 do benv''' <- type_qexp fv benv'' C e @
                   do core <- get_var rx @
                     do old <- BEnv.find core benv''' @
                     type_funs benv (FEnv.add f ((tvl,l,e,benv'',rx)) fv) fs
     end.



(* A program type will return a function environment. *)
Definition type_prog (p:prog) : option fenv :=
   match p with (n,l,fl,main,rx) => 
    do bv <- gen_genv l @ 
      do fv <- type_funs bv fenv_empty fl @
            do block <- FEnv.find main fv @ 
              do re <- BEnv.find (G rx) bv @
              match block with (tvl,e,fbenv, x) =>
                 do re1 <- type_factor fbenv x @ ret fv
              end
   end.


(* The Semantics of statements. *)
Definition eval_var (smap : qvar -> nat) (size:nat) (r:store) (x:cfac) :=
   match x with Index x n => do v <- (sem_factor size r n) @
                  if a_nat2fb v size <? smap x then
                    ret (Value (x,a_nat2fb v size)) else ret Error
              | Nor (Var x) => Some (Value (x,0))
              | Nor (Num b x) => None
   end.

Lemma eval_cfac_sem_error : forall x smap size rh, 
    eval_var smap size rh x = Some Error ->
               sem_cfac smap size rh x = Some Error.
Proof.
 intros. destruct x.
 unfold sem_cfac,eval_var in *.
 destruct (sem_factor size rh v) eqn:eq1.
 simpl in *. bdestruct (a_nat2fb b size <? smap x).
 inv H. easy. simpl in *. easy.
 simpl in *. destruct v. inv H. easy.
Qed.

Lemma eval_cfac_find_var_error : forall x smap size rh,
    sem_cfac smap size rh x = Some Error -> eval_var smap size rh x = Some Error.
Proof.
 intros. destruct x.
 unfold sem_cfac,eval_var in *.
 destruct (sem_factor size rh v) eqn:eq1.
 simpl in *. bdestruct (a_nat2fb b size <? smap x).
 destruct (Store.find (elt:=list (nat -> bool)) (x, a_nat2fb b size) rh) eqn:eq2.
 simpl in *. destruct l. simpl in *. easy. simpl in *. inv H.
 simpl in *. easy. easy.
 simpl in *. easy.
 simpl in *. destruct (sem_factor size rh v) eqn:eq1.
 simpl in *. inv H. simpl in *. easy.
Qed.


Lemma stored_value_typed_1 : forall smap rh bv size x xn xv xl a b, 
     type_factor bv x = Some (a,b) -> 
     eval_var smap size rh x = Some (Value xn) ->
     Store.MapsTo xn (xv :: xl) rh -> 
     store_typed rh bv size ->
     ( forall i : nat, i >= get_size size b -> xv i = false).
Proof.
  intros.
  unfold eval_var,type_factor,store_typed in *.
  assert (In xv (xv :: xl)). simpl. left. easy.
  specialize (H2 xn (xv :: xl) xv H1 H4).
  destruct x.
  destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
  destruct (sem_factor size rh v) eqn:eq2.
  simpl in *.
  destruct t.
  destruct (typ_factor_full bv C Nat v) eqn:eq3. simpl in *. inv H.
  bdestruct (a_nat2fb b0 size <? smap x).
  inv H0.
  simpl in *.
  rewrite eq1 in *.
  unfold is_bl,get_size in *.
  specialize (H2 i).
  destruct b. simpl in *. assert (size <= i) by lia.
  apply H2 in H0.
  easy.
  simpl in *.
  assert (size <= i) by lia.
  apply H2 in H0.
  easy.
  simpl in *.
  assert (1 <= i) by lia.
  apply H2 in H0.
  easy.
  inv H0. easy. easy.
  simpl in *. easy. easy.
  unfold typ_factor in *.
  destruct v.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *. destruct t. easy.
  inv H. inv H0.
  simpl in *.
  rewrite eq1 in H2.
  specialize (H2 i).
  unfold is_bl,get_size in *.
  destruct b.
  simpl in *.
  assert (size <= i) by lia.
  apply H2 in H.
  easy.
  simpl in *.
  assert (size <= i) by lia.
  apply H2 in H.
  easy.
  simpl in *.
  assert (1 <= i) by lia.
  apply H2 in H.
  easy. easy. easy.
Qed.

Definition qvar_eq_eval (smap:qvar -> nat) (size:nat)  (r:store) (x y: cfac) := 
        do a <- eval_var smap size r x @
          do b <- eval_var smap size r y @ match a with Error => ret Error
                                                     | Value av => match b with Error => ret Error
                                                                            | Value bv => Some (Value (av =qd= bv))
                                                                   end
                                           end.

Definition l_rotate (f:nat -> bool) (n:nat) := fun i => f ((i + n - 1) mod n).

Definition apply_unary (op:qop) (size:nat) (t:btype) (x:(nat -> bool)) (y:(nat -> bool)) :=
    match op with nadd => cut_n (sumfb false x y) size
                | nsub => cut_n (sumfb true (negatem size x) y) size
                | fadd => cut_n (sumfb false x y) size
                | fsub => cut_n (sumfb true (negatem size x) y) size
                | qxor => (bin_xor y x (if t =b= Bl then 1 else size))
                | nfac => (nat2fb (fact (a_nat2fb x size) mod 2^size))
                | fdiv => (nat2fb (((a_nat2fb y size)) / (a_nat2fb x size)))
                | _ => nat2fb 0
    end.

Definition apply_bin (op:qop) (size:nat) (t:btype) (x:(nat -> bool)) (y:(nat -> bool)) (z:(nat->bool)) :=
    match op with nadd => sumfb false y z
                | nsub => (sumfb true y (negatem size z))
                | fadd => (sumfb false y z)
                | fsub => (sumfb true y (negatem size z))
                | nmul => (bin_xor x (nat2fb (((a_nat2fb y size) * (a_nat2fb z size)) mod 2^size)) size)
                | ndiv => (bin_xor x (nat2fb (((a_nat2fb y size) / (a_nat2fb z size)))) size)
                | nmod => (bin_xor x (nat2fb (((a_nat2fb y size) mod (a_nat2fb z size)))) size)
                | fmul => (bin_xor x (nat2fb (((a_nat2fb y size) * (a_nat2fb z size)) / 2^size)) size)
                | fndiv => (nat2fb (((a_nat2fb y size) * (a_nat2fb z size)) / 2^size))
                | _ => nat2fb 0
    end.

Fixpoint sem_cfacs (smap:qvar -> nat) (size:nat) (store:store) (vs:list cfac) :=
   match vs with [] => Some (Value ([]))
              | (v::vs') => do newv <- sem_cfac smap size store v @
                             do vsv <- sem_cfacs smap size store vs' @ 
                              match newv with Error => Some Error
                              | Value newv' => 
                               match vsv with Error => Some Error
                                          | Value vsv' => Some (Value (newv'::vsv'))
                              end
                              end
   end.

(* Semantics for statments. Just like C. 
   For dealing with inv, we pop out history values. *)
Inductive sem_qexp (smap:qvar -> nat) (fv:fenv) (bv:benv) (size:nat) : store -> qexp -> @value store -> Prop :=
   sem_qexp_skip : forall r, sem_qexp smap fv bv size r skip (Value r)
 | sem_qexp_lrot_error : forall r x,
           eval_var smap size r x = Some Error ->
            sem_qexp smap fv bv size r (slrot x) Error

 | sem_qexp_lrot_some : forall r t x xn x_val xl,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           BEnv.MapsTo (fst xn) t bv ->
            sem_qexp smap fv bv size r (slrot x) 
                (Value (Store.add xn ((l_rotate x_val (if (get_ct t) =b= Bl then 1 else size))::(x_val::xl)) r))
 | sem_qexp_init_error_1 : forall r x v,
           eval_var smap size r x = Some Error ->
            sem_qexp smap fv bv size r (init x v) Error
 | sem_qexp_init_error_2 : forall r x v,
           sem_cfac smap size r v = Some Error ->  
            sem_qexp smap fv bv size r (init x v) Error
 | sem_qexp_init_error_3 : forall r x v,
           qvar_eq_eval smap size r x v = Some Error ->  
            sem_qexp smap fv bv size r (init x v) Error
 | sem_qexp_init_error_4 : forall t r x v,
           type_factor bv x = Some (Q,t) -> 
           qvar_eq_eval smap size r x v = Some (Value true) ->  
            sem_qexp smap fv bv size r (init x v) Error
 | sem_qexp_init_some : forall r t x v xn x_val xl val,
           (forall t, type_factor bv x = Some (Q,t) -> 
           qvar_eq_eval smap size r x v = Some (Value false)) ->
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
           BEnv.MapsTo (fst xn) t bv ->
           sem_cfac smap size r v = Some (Value val) ->  
            sem_qexp smap fv bv size r (init x v) 
                (Value (Store.add xn ((bin_xor x_val val (get_size size (get_ct t)))::(x_val::xl)) r))
 | sem_qexp_unary_error_1 : forall r x op y, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (unary x op y) Error
 | sem_qexp_unary_error_2 : forall r x op v,
           sem_cfac smap size r v = Some Error ->  
            sem_qexp smap fv bv size r (unary x op v) Error
 | sem_qexp_unary_error_3 : forall r x op v,
           qvar_eq_eval smap size r x v = Some Error ->  
            sem_qexp smap fv bv size r (unary x op v) Error
 | sem_qexp_unary_error_4 : forall t r x op v,
           type_factor bv x = Some (Q,t) -> 
           qvar_eq_eval smap size r x v = Some (Value true) ->  
            sem_qexp smap fv bv size r (unary x op v) Error
 | sem_qexp_unary_some : forall r x op v t xn x_val xl val,
           (forall t, type_factor bv x = Some (Q,t) -> 
                qvar_eq_eval smap size r x v = Some (Value false)) ->
          eval_var smap size r x = Some (Value xn)
           -> Store.MapsTo xn (x_val::xl) r
            -> type_factor bv x = Some t ->
           sem_cfac smap size r v = Some (Value val) ->  
            sem_qexp smap fv bv size r (unary x op v) 
                (Value (Store.add xn ((apply_unary op size (snd t) val x_val)::(x_val::xl)) r))

 | sem_qexp_bin_error_1 : forall r x op y z, eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (binapp x op y z) Error
 | sem_qexp_bin_error_2 : forall r x op y z,
           sem_cfac smap size r y = Some Error ->  
            sem_qexp smap fv bv size r (binapp x op y z) Error
 | sem_qexp_bin_error_3 : forall r x op y z,
           sem_cfac smap size r z = Some Error ->  
            sem_qexp smap fv bv size r (binapp x op y z) Error
 | sem_qexp_bin_error_4 : forall r x op y z,
           qvar_eq_eval smap size r x y = Some Error ->  
            sem_qexp smap fv bv size r (binapp x op y z) Error
 | sem_qexp_bin_error_5 : forall r x op y z,
           qvar_eq_eval smap size r x z = Some Error ->  
            sem_qexp smap fv bv size r (binapp x op y z) Error
 | sem_qexp_bin_error_6 : forall t r x op y z,
           type_factor bv x = Some (Q,t) ->
           qvar_eq_eval smap size r x y = Some (Value true) ->  
            sem_qexp smap fv bv size r (binapp x op y z) Error
 | sem_qexp_bin_error_7 : forall t r x op y z,
           type_factor bv x = Some (Q,t) ->
           qvar_eq_eval smap size r x z = Some (Value true) ->  
            sem_qexp smap fv bv size r (binapp x op y z) Error
 | sem_qexp_bin_some : forall r x op y z t xn x_val xl y_val z_val,
           (forall t, type_factor bv x = Some t ->
                qvar_eq_eval smap size r x y = Some (Value false)
                    /\ qvar_eq_eval smap size r x z = Some (Value false)) ->
           eval_var smap size r x = Some (Value xn)
           -> Store.MapsTo xn (x_val::xl) r
            -> type_factor bv x = Some t ->
           sem_cfac smap size r y = Some (Value y_val) ->  
           sem_cfac smap size r y = Some (Value z_val) ->  
            sem_qexp smap fv bv size r (binapp x op y z) 
                (Value (Store.add xn ((apply_bin op size (snd t) x_val y_val z_val)::(x_val::xl)) r))

 | sem_qexp_qinv_error : forall r x,
           eval_var smap size r x = Some Error ->
            sem_qexp smap fv bv size r (qinv x) Error

 | sem_qexp_qinv_some : forall r x xn x_val xl,
           eval_var smap size r x = Some (Value xn) -> Store.MapsTo xn (x_val::xl) r ->
            sem_qexp smap fv bv size r (qinv x)  (Value (Store.add xn xl r))

 | sem_qexp_if_error : forall r ce e1 e2, sem_cexp smap bv size r ce = Some Error ->
                    sem_qexp smap fv bv size r (qif ce e1 e2) Error
 | sem_qexp_if_t : forall r ce e1 e2 r1, sem_cexp smap bv size r ce = Some (Value true) ->
                    sem_qexp smap fv bv size r e1 r1 -> 
                    sem_qexp smap fv bv size r (qif ce e1 e2) r1
 | sem_qexp_if_f : forall r ce e1 e2 r1, sem_cexp smap bv size r ce = Some (Value false) ->
                    sem_qexp smap fv bv size r e2 r1 -> 
                    sem_qexp smap fv bv size r (qif ce e1 e2) r1

 | sem_qexp_call_error_1 : forall tvl l e fbv rx f x vs r,
         FEnv.MapsTo f (tvl, l,e,fbv,rx) fv -> 
         sem_cfacs smap size r vs = Some Error ->
         sem_qexp smap fv bv size r (call x f vs) Error
 | sem_qexp_call_error_2 : forall tvl l e fbv rx f x vs vs' r r1 r2 r3,
         FEnv.MapsTo f (tvl, l,e,fbv,rx) fv -> 
         sem_cfacs smap size r vs = Some (Value vs') ->
         init_store_args r tvl vs' = Some r1->
         init_store r1 l = Some r2 ->
         sem_qexp (gen_smap_l l (gen_smap_args tvl smap)) fv fbv size r2 e (Value r3) ->
         eval_var (gen_smap_l l (gen_smap_args tvl smap)) size r3 rx = Some Error ->
         sem_qexp smap fv bv size r (call x f vs) Error

 | sem_qexp_call_error_3 : forall x f vs r,
         eval_var smap size r x = Some Error ->
         sem_qexp smap fv bv size r (call x f vs) Error

 | sem_qexp_call_error_4 : forall tvl l e fbv rx x f vs vs' r r1 r2,
         FEnv.MapsTo f (tvl,l,e,fbv,rx) fv -> 
         sem_cfacs smap size r vs = Some (Value vs') ->
         init_store_args r tvl vs' = Some r1->
         init_store r1 l = Some r2 ->
         sem_qexp (gen_smap_l l (gen_smap_args tvl smap)) fv fbv size r2 e Error ->
         sem_qexp smap fv bv size r (call x f vs) Error

 | sem_qexp_call_some : forall tvl l e fbv rx f vs vs' x xn r r1 r2 r3 rxn xl,
         FEnv.MapsTo f (tvl,l,e,fbv,rx) fv -> 
         sem_cfacs smap size r vs = Some (Value vs') ->
         init_store_args r tvl vs' = Some r1->
         init_store r1 l = Some r2 ->
         eval_var smap size r x = Some (Value xn) ->
         sem_qexp (gen_smap_l l (gen_smap_args tvl smap)) fv fbv size r2 e (Value r3) ->
         sem_cfac (gen_smap_l l (gen_smap_args tvl smap)) size r3 rx = Some (Value rxn) ->
         Store.MapsTo xn xl r ->
         sem_qexp smap fv bv size r (call x f vs) (Value (Store.add xn (rxn::xl) r))

 | sem_qexp_qseq_error : forall r e1 e2,
                sem_qexp smap fv bv size r e1 Error ->
                  sem_qexp smap fv bv size r (qseq e1 e2) Error

 | sem_qexp_qseq_some : forall r e1 e2 r' r'',
                sem_qexp smap fv bv size r e1 (Value r') ->
                sem_qexp smap fv bv size r' e2 r'' ->
                  sem_qexp smap fv bv size r (qseq e1 e2) r''

 | sem_qexp_for_error_1 : forall r x n e,
                sem_cfac smap size r n = Some Error ->
                           sem_qexp smap fv bv size r (qfor x n e) Error

 | sem_qexp_for_error_2 : forall r x n e nv xl,
      sem_cfac smap size r n = Some (Value nv) ->
       Store.MapsTo (L x,0) xl r ->
        sem_for_exp smap fv bv size (Store.add (L x,0) ((nat2fb 0)::xl) r) e x (a_nat2fb nv size) Error ->
                           sem_qexp smap fv bv size r (qfor x n e) Error

 | sem_qexp_for_some : forall r x n e xl nv nv' xl' r',
      sem_cfac smap size r n = Some (Value nv) ->
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

(* Program semantics is to evaluate the main function. *)
Inductive sem_prog (fv:fenv) : prog -> (@value (nat -> bool)) -> Prop :=
    sem_main_error_1 : forall size gl fl main x l e bv rx r r',
              FEnv.MapsTo main (([]),l,e,bv,rx) fv ->
              init_store empty_store gl = Some r ->
              init_store r l = Some r' ->
              sem_qexp (gen_smap_l l (gen_smap_l gl (fun _ => 0))) fv bv size r' e Error -> 
              sem_prog fv (size,gl,fl,main,x) Error
   | sem_main_error_2 : forall size gl fl main x l e bv rx r r' r'',
              FEnv.MapsTo main (([]),l,e,bv,rx) fv ->
              init_store empty_store gl = Some r ->
              init_store r l = Some r' ->
              sem_qexp (gen_smap_l l (gen_smap_l gl (fun _ => 0))) fv bv size r' e (Value r'') -> 
              eval_var (gen_smap_l l (gen_smap_l gl (fun _ => 0))) size r'' rx = Some Error ->
              sem_prog fv (size,gl,fl,main,x) Error
   | sem_main_some : forall size gl fl main x l e bv rx r r' r'' rxn v vl,
              FEnv.MapsTo main (([]),l,e,bv,rx) fv ->
              init_store empty_store gl = Some r ->
              init_store r l = Some r' ->
              sem_qexp (gen_smap_l l (gen_smap_l gl (fun _ => 0))) fv bv size r' e (Value r'') -> 
              eval_var (gen_smap_l l (gen_smap_l gl (fun _ => 0))) size r'' rx = Some (Value rxn) ->
              Store.MapsTo rxn (v::vl) r'' ->
              sem_prog fv (size,gl,fl,main,x) (Value v).

(* Compilation from MiniQASM to PQASM starts here. *)

(* Compiler for qexp *)
Definition fmap :Type := list (fvar * cfac * exp * (qvar -> nat) * ((qvar*nat) -> var) * benv * cstore).
Fixpoint lookup_fmap (l:fmap) (x:fvar) : option (cfac * exp * (qvar -> nat) * ((qvar*nat) -> var) * benv * cstore) :=
   match l with [] => None
          | ((y,a,p,smap,vmap,bv,r)::xl) => if x =? y then Some (a,p,smap,vmap,bv,r) else lookup_fmap xl x
   end.

Definition combine_c (e1 e2:option exp) : option exp :=
          match e1 with None => e2
               | Some e1' => match e2 with None => Some e1'
                                        | Some e2' => Some (e1';e2')
                              end
          end.

Definition combine_seq (e1:option exp) (e2:option exp) :=
   match e1 with None => e2
        | Some e1' => match e2 with None => Some e1' | Some e2' => Some (e1' ; e2') end
   end.

Definition deal_result (r:cstore) (re : option (option exp * nat * option cstore)) :=
    match re with None => None
             | Some (a,b,None) => Some (a,b,r)
             | Some (a,b,Some r') => Some (a,b,r')
    end.

(* estore is to  store the list of statements for inv functions. 
   Once we compile an inv operation, we need to locate the predesessor of the variable in inv. *)
Definition estore : Type := Store.t (list exp).
Definition empty_estore := @Store.empty (list exp).

(* nat: x + y *)
Definition nadd_circuit_two (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (stack: var) (sn:nat) :=
            if f =fl= Classic then
              (adder01 size (vmap x) (vmap y) (stack,S sn))
            else rz_full_adder_form (vmap x) size (vmap y).


Definition nadd_circuit_left (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x :(qvar*nat)) (y:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
              (init_v size (temp) y;
                    adder01 size (vmap x) (temp) (stack,S sn);
                    init_v size (temp) y)
            else rz_adder_form (vmap x) size y.

Definition nadd_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y:cfac)
                 : option (@value (option exp * nat * cstore * estore)) :=
     do t1 <- type_factor bv x @
         do t2 <- type_factor bv y @
            match par_find_var_check smap bv size r x with Some (Value vx) => 
              if (fst t1 =a= Q) && (fst t2 =a= C)
               then 
                   do t2v <- par_eval_cfac_check smap bv size r y @
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
              (subtractor01 size (vmap x) (vmap y) (stack,S sn))
            else rz_full_sub_form (vmap x) size (vmap y).


Definition nsub_circuit_left (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x :(qvar*nat)) (y:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
              (init_v size (temp) y;
                    subtractor01 size (vmap x) (temp) (stack,S sn);
                    init_v size (temp) y)
            else rz_sub_right (vmap x) size y.

Definition nsub_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y:cfac) 
              : option (@value (option exp * nat * cstore * estore)) :=
     do t1 <- type_factor bv  x @
         do t2 <- type_factor bv  y @
            match par_find_var_check smap bv size r x with Some (Value vx) => 
              if (fst t1 =a= Q) && (fst t2 =a= C)
               then 
                   do t2v <- par_eval_cfac_check smap bv size r  y @
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
              (Rev (vmap x);Rev (vmap y);
               adder01 size (vmap x) (vmap y) (stack,S sn);inv_exp (Rev (vmap x);Rev (vmap y)))
            else (Rev (vmap x);Rev (vmap y));
                   rz_full_adder_form (vmap x) size (vmap y);inv_exp ( (Rev (vmap x);Rev (vmap y))).


Definition fadd_circuit_left (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x :(qvar*nat)) (y:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
               (init_v size (temp) y;
                   Rev (vmap x);Rev (temp);
                    adder01 size (vmap x) (temp) (stack,S sn);
                   inv_exp (Rev (vmap x);Rev (temp));
                    init_v size (temp) y)
            else (Rev (vmap x));rz_adder_form (vmap x) size (fbrev size y); (inv_exp ( (Rev (vmap x)))).

Definition fadd_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y:cfac)
              : option (@value (option exp * nat * cstore * estore)) :=
     do t1 <- type_factor bv  x @
         do t2 <- type_factor bv  y @
            match par_find_var_check smap bv size r x with Some (Value vx) => 
              if (fst t1 =a= Q) && (fst t2 =a= C)
               then 
                   do t2v <- par_eval_cfac_check smap bv size r y @
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
               (Rev (vmap x);Rev (vmap y);
               subtractor01 size (vmap x) (vmap y) (stack,S sn);inv_exp (Rev (vmap x);Rev (vmap y)))
            else (Rev (vmap x);Rev (vmap y));
                   rz_full_sub_form (vmap x) size (vmap y);inv_exp ( (Rev (vmap x);Rev (vmap y))).


Definition fsub_circuit_left (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x :(qvar*nat)) (y:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
               (init_v size (temp) y;
                   Rev (vmap x);Rev (temp);
                    subtractor01 size (vmap x) (temp) (stack,S sn);
                   inv_exp (Rev (vmap x);Rev (temp));
                    init_v size (temp) y)
            else  (Rev (vmap x));rz_sub_right (vmap x) size (fbrev size y); (inv_exp ( (Rev (vmap x)))).

Definition fsub_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y:cfac)
              : option (@value (option exp * nat * cstore * estore)) :=
     do t1 <- type_factor bv  x @
         do t2 <- type_factor bv y @
            match par_find_var_check smap bv size r x with Some (Value vx) => 
              if (fst t1 =a= Q) && (fst t2 =a= C)
               then 
                   do t2v <- par_eval_cfac_check smap bv size r y @
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
                        (x y z:(qvar*nat)) (stack: var) (sn:nat) :=
            if f =fl= Classic then
               cl_full_mult size (vmap y) (vmap z) (vmap x) (stack,sn)
            else 
               nat_full_mult size (vmap y) (vmap z) (vmap x).


Definition nmul_circuit_one (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (z:(nat->bool)) (stack: var) (sn:nat) :=
            if f =fl= Classic then
                     (cl_nat_mult size (vmap y) (vmap x) (stack,sn) z)
            else nat_mult size (vmap y) (vmap x) z.

Definition nqmul_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y z:cfac)
              : option (@value (option exp * nat * cstore * estore)) :=
     do t1 <- type_factor bv x @
         do t2 <- type_factor bv y @
         do t3 <- type_factor bv z @
             do vx <- par_find_var bv size r x @  
              if (fst t2 =a= Q) && (fst t3 =a= Q) then
                 do vyv <- par_find_var_check smap bv size r y @
                   do vzv <- par_find_var_check smap bv size r z @
                    match vyv with Value vy => 
                     match vzv with Value vz =>
                     do exps <- Store.find vx es @
                         Some (Value (Some (nmul_circuit_two size f vmap vy vz vx stack sn),sn,r,
                      Store.add vx ((nmul_circuit_two size f vmap vy vz vx stack sn)::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end
              else if (fst t2 =a= Q) && (fst t3 =a= C) then
                 do vyv <- par_find_var_check smap bv size r y @
                  do vzv <- par_eval_cfac_check smap bv size r z @
                     match vyv with Value vy => 
                       match vzv with Value tzv => 
                     do exps <- Store.find vx es @
                           Some (Value (Some (nmul_circuit_one size f vmap vx vy tzv stack sn),sn,r,
                      Store.add vx ((nmul_circuit_one size f vmap vx vy tzv stack sn)::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end
              else if (fst t2 =a= C) && (fst t3 =a= Q) then
                 do vzv <- par_find_var_check smap bv size r z @
                  do vyv <- par_eval_cfac_check smap bv size r y @
                     match vzv with Value vz => 
                       match vyv with Value tyv => 
                     do exps <- Store.find vx es @
                           Some (Value (Some (nmul_circuit_one size f vmap vx vz tyv stack sn),sn,r,
                      Store.add vx ((nmul_circuit_one size f vmap vx vz tyv stack sn)::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end
              else do vyv <- par_eval_cfac_check smap bv size r y @
                    do vzv <- par_eval_cfac_check smap bv size r z @
                       match vyv with Value tyv => 
                        match vzv with Value tzv => 
                     do exps <- Store.find vx es @
                    Some (Value (Some ( (init_v size (vmap vx)
                               (nat2fb (((a_nat2fb tyv size) * (a_nat2fb tzv size)) mod 2^size)))),sn,r,
                      Store.add vx (( (init_v size (vmap vx)
                               (nat2fb (((a_nat2fb tyv size) * (a_nat2fb tzv size)) mod 2^size))))::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end.

(* z  = x * y for fixedp *)
Definition fmul_circuit_two (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x y z:(qvar*nat)) (temp stack: var) (sn:nat) :=
            if f =fl= Classic then
                (Rev (vmap y); Rev (vmap z); Rev (vmap x));
               clf_full_mult size (vmap y) (vmap z) (vmap x) (temp) (stack,sn);
               (inv_exp ( (Rev (vmap y); Rev (vmap z); Rev (vmap x))))
            else 
                (Rev (vmap y); Rev (vmap z); Rev (vmap x));
               flt_full_mult size (vmap y) (vmap z) (vmap x) (temp);
               (inv_exp ( (Rev (vmap y); Rev (vmap z); Rev (vmap x)))).


Definition fmul_circuit_one (size:nat) (f:flag) (vmap:(qvar*nat) -> var)
                        (x y :(qvar*nat)) (z:(nat->bool)) (stack temp: var) (sn:nat) :=
            if f =fl= Classic then
                     (cl_flt_mult size (vmap y) (vmap x) temp (stack,sn) z)
            else flt_mult size (vmap y) (vmap x) z.


Definition fmul_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y z:cfac)
              : option (@value (option exp * nat * cstore * estore)) :=
     do t1 <- type_factor bv  x @
         do t2 <- type_factor bv  y @
         do t3 <- type_factor bv  z @
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
                  do vzv <- par_eval_cfac_check smap bv size r  z @
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
                  do vyv <- par_eval_cfac_check smap bv size r  y @
                     match vzv with Value vz => 
                       match vyv with Value tyv => 
                     do exps <- Store.find vx es @
                           Some (Value (Some (fmul_circuit_one size f vmap vx vz tyv stack temp sn),sn,r,
                      Store.add vx ((fmul_circuit_one size f vmap vx vz tyv stack temp sn)::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end
              else do vyv <- par_eval_cfac_check smap bv size r  y @
                    do vzv <- par_eval_cfac_check smap bv size r  z @
                       match vyv with Value tyv => 
                        match vzv with Value tzv => 
                     do exps <- Store.find vx es @
                           Some (Value (Some ( (init_v size (vmap vx)
                               (nat2fb (((a_nat2fb tyv size) * (a_nat2fb tzv size)) mod 2^size)))),sn,r,
                      Store.add vx (( (init_v size (vmap vx)
                               (nat2fb (((a_nat2fb tyv size) * (a_nat2fb tzv size)) mod 2^size))))::exps) es))
                      | _ => Some Error
                     end
                       | _ => Some Error
                    end.

(* z  = x xor y *)
Fixpoint bin_xor_q (n:nat) (x y : var) : exp :=
   match n with 0 => SKIP (x,0)
      | S m => CNOT (x,m) (y,m);bin_xor_q m x y
   end.


Definition qxor_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var) (bv:benv) (r:cstore) (sn:nat) (es:estore) (x y:cfac) 
              : option (@value (option exp * nat * cstore * estore)) :=
          do vxv <- par_find_var_check smap bv size r x @
            match vxv with Value vx =>   
              do t <- BEnv.find (fst vx) bv @
               if is_q t then
                do t2 <- type_factor bv y @
                 if fst t2 =a= Q then
                  do vyv <- par_find_var_check smap bv size r y @
                   match vyv with Value vy =>
                   do exps <- Store.find vx es @
                     Some (Value (Some ( (bin_xor_q (get_size size (get_ct t)) (vmap vy) (vmap vx))),sn,r,
                         Store.add vx (( (bin_xor_q (get_size size (get_ct t)) (vmap vy) (vmap vx)))::exps) es))
                   | _ => Some Error
                  end
                 else do t2v <- par_eval_cfac_check smap bv size r y @
                   match t2v with Value t2v' => 
                   do exps <- Store.find vx es @
                     Some (Value (Some ( (init_v (get_size size (get_ct t)) (vmap vx) t2v')),sn,r,
                              Store.add vx (( (init_v (get_size size (get_ct t)) (vmap vx) t2v'))::exps) es))
                    | _ => Some Error
                   end
               else do t1v <- par_eval_cfac_check smap bv size r x @
                     do t2v <- par_eval_cfac_check smap bv size r y @
                       match t1v with Value t1v' => 
                         match t2v with Value t2v' => 
                            Some (Value (None,sn, (Store.add vx (bin_xor t1v' t2v' (get_size size (get_ct t))) r),es))
                          | _ => Some Error end
                        | _ => Some Error
                         end
               |_ => Some Error
            end.

(* init circuit for quantum Q mode variables only. *)
Definition init_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var) (bv:benv) (r:cstore) (sn:nat) (es:estore) (x y:cfac) 
              : option (@value (option exp * nat * cstore * estore)) :=
           do vxv <- par_find_var_check smap bv size r x @
            match vxv with Value vx =>
              do t <- BEnv.find (fst vx) bv @
              if is_q t then 
                do t2 <- type_factor bv y @
                 if fst t2 =a= Q then
                  do vyv <- par_find_var_check smap bv size r y @
                   match vyv with Value vy =>
                    do exps <- Store.find vx es @ 
                     Some (Value (Some ( (bin_xor_q (get_size size (get_ct t)) (vmap vy) (vmap vx))),sn,r,
                          Store.add vx (( (bin_xor_q (get_size size (get_ct t)) (vmap vy) (vmap vx)))::exps) es))
                   | _ => Some Error
                  end
                 else do t2v <- par_eval_cfac_check smap bv size r y @
                   match t2v with Value t2v' => 
                    do exps <- Store.find vx es @ 
                     Some (Value (Some ( (init_v (get_size size (get_ct t)) (vmap vx) t2v')),sn,r,
                      Store.add vx (( (init_v (get_size size (get_ct t)) (vmap vx) t2v'))::exps) es))
                    | _ => Some Error
                   end
               else None
               |_ => Some Error
           end.

(* ndiv circuit for quantum Q/C mode variables only. *)
Definition div_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (fl:flag) (r:cstore) (temp temp1 stack:var) (sn:nat) (es:estore) (x y:cfac) (z:nat -> bool)
              : option (@value (option exp * nat * cstore * estore)) :=
           do vxv <- par_find_var_check smap bv size r x @
            match vxv with Value vx =>
              do t <- BEnv.find (fst vx) bv @
              if is_q t then 
                do t2 <- type_factor bv y @
                 if fst t2 =a= Q then
                  do vyv <- par_find_var_check smap bv size r y @
                   match vyv with Value vy =>
                    do exps <- Store.find vx es @ 
                     if fl =fl= QFTA then 
                     Some (Value (Some ((rz_div size (vmap vy) (vmap vx) temp (a_nat2fb z size))) ,sn,r,
                          Store.add vx (((rz_div size (vmap vy) (vmap vx) temp (a_nat2fb z size)))::exps) es))
                     else 
                     Some (Value (Some ( (cl_div size (vmap vy) (vmap vx) temp temp1 (stack,sn) (a_nat2fb z size))),sn,r,
                          Store.add vx ( ((cl_div size (vmap vy) (vmap vx) temp temp1 (stack,sn) (a_nat2fb z size)))::exps) es))

                   | _ => Some Error
                  end
                 else do t2v <- par_eval_cfac_check smap bv size r y @
                   match t2v with Value t2v' => 
                    do exps <- Store.find vx es @ 
                     Some (Value (Some ( (init_v (get_size size (get_ct t)) (vmap vx) t2v')),sn,r,
                      Store.add vx (( (init_v (get_size size (get_ct t)) (vmap vx) t2v'))::exps) es))
                    | _ => Some Error
                   end
               else do t2v <- par_eval_cfac_check smap bv size r y @
                         match t2v with Value t2v' => 
                               Some (Value ((None,sn,Store.add vx (nat2fb ((a_nat2fb t2v' size) / (a_nat2fb z size))) r,es)))
                             | _ => Some Error
                         end

               |_ => Some Error
           end.

(* nmod circuit for quantum Q/C mode variables only. *)
Definition mod_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (fl:flag) (r:cstore) (temp temp1 stack:var) (sn:nat) (es:estore) (x y:cfac) (z:nat -> bool)
              : option (@value (option exp * nat * cstore * estore)) :=
           do vxv <- par_find_var_check smap bv size r x @
            match vxv with Value vx =>
              do t <- BEnv.find (fst vx) bv @
              if is_q t then 
                do t2 <- type_factor bv y @
                 if fst t2 =a= Q then
                  do vyv <- par_find_var_check smap bv size r y @
                   match vyv with Value vy =>
                    do exps <- Store.find vx es @ 
                     if fl =fl= QFTA then 
                     Some (Value (Some ((rz_moder size (vmap vy) (vmap vx) temp (a_nat2fb z size))) ,sn,r,
                          Store.add vx (((rz_moder size (vmap vy) (vmap vx) temp (a_nat2fb z size)))::exps) es))
                     else 
                     Some (Value (Some ( (cl_moder size (vmap vy) (vmap vx) temp temp1 (stack,sn) (a_nat2fb z size))),sn,r,
                          Store.add vx ( ((cl_moder size (vmap vy) (vmap vx) temp temp1 (stack,sn) (a_nat2fb z size)))::exps) es))

                   | _ => Some Error
                  end
                 else do t2v <- par_eval_cfac_check smap bv size r y @
                   match t2v with Value t2v' => 
                    do exps <- Store.find vx es @ 
                     Some (Value (Some ( (init_v (get_size size (get_ct t)) (vmap vx) t2v')),sn,r,
                      Store.add vx (( (init_v (get_size size (get_ct t)) (vmap vx) t2v'))::exps) es))
                    | _ => Some Error
                   end
               else do t2v <- par_eval_cfac_check smap bv size r y @
                         match t2v with Value t2v' => 
                               Some (Value ((None,sn,Store.add vx (nat2fb ((a_nat2fb t2v' size) mod (a_nat2fb z size))) r,es)))
                             | _ => Some Error
                         end
               |_ => Some Error
           end.

(* Rshift operation. No circuit cost. *)
Definition lrot_c (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var) (bv:benv) (r:cstore) (sn:nat) (es:estore) (x:cfac) :=
    do vxv <- par_find_var_check smap bv size r x @
       match vxv with Value vx => 
          do t <- BEnv.find (fst vx) bv @
               if is_q t then
                do exps <- Store.find vx es @
                   Some (Value (Some ( (Rshift (vmap vx))), sn, r,Store.add vx (( (Rshift (vmap vx)))::exps) es))
               else
                do t1v <- Store.find vx r @
                   Some (Value (None,sn, (Store.add vx (l_rotate t1v (get_size size (get_ct t))) r),es))
            | _ => Some Error
       end.


Definition combine_if (sv : var) (sn:nat) (p1:exp) (e1:option exp) (e2:option exp) :=
   match e1 with None => match e2 with None => Some p1
           | Some e2' => Some (p1 ; (X (sv,sn)); CU (sv,sn) e2')
                         end
           | Some e1' => match e2 with None => Some (p1 ; CU (sv,sn) e1')
                | Some e2' => Some (p1 ; CU (sv,sn) e1' ;
                          (X (sv,sn)); CU (sv,sn) e2')
                         end
    end.

Definition unary_circuit_left_core_cl (op:qop) size (x y:var) (c:posi) :=
            match op with nadd =>  (adder01 size x (y) c)
                        | nsub =>  (subtractor01 size x (y) c)
                        | fadd =>  (adder01 size x (y) c)
                        | fsub =>  (subtractor01 size x (y) c)
                        | _ => PQASM.SKIP (x,0)
            end.

Definition unary_circuit_left (op:qop) (t:btype) (size:nat) (f:flag) (vmap: (qvar*nat) -> var)
            (x:qvar *nat) (y:nat -> bool) (stack temp:var) (sn:nat) :=
    if op =op= qxor then Some (init_v (get_size size t) (vmap x) y) else
        if f =fl= Classic then 
           Some (init_v size temp y;  unary_circuit_left_core_cl op size temp (vmap x) (stack,sn)
           ; inv_exp (init_v size temp y))
        else 
            match op with nadd => Some (rz_adder_form (vmap x) size y)
                        | nsub => Some (rz_sub_right (vmap x) size y)
                        | fadd => Some (rz_adder_form (vmap x) size y)
                        | fsub => Some (rz_sub_right (vmap x) size y)
                        | _ => None
            end.


Definition unary_circuit_two (op:qop) (t:btype) (size:nat) (f:flag) (vmap: (qvar*nat) -> var)
            (x:qvar *nat) (y:qvar *nat) (stack:var) (sn:nat) :=
    if op =op= qxor then Some (copyto (vmap y) (vmap x) (get_size size t)) else
        if f =fl= Classic then 
            match op with nadd => Some ((adder01 size (vmap y) (vmap x) (stack,sn)))
                        | nsub => Some ((subtractor01 size (vmap y) (vmap x) (stack,sn)))
                        | fadd => Some ((adder01 size (vmap y) (vmap x) (stack,sn)))
                        | fsub => Some ((subtractor01 size (vmap y) (vmap x) (stack,sn)))
                        | _ => None
            end
        else 
            match op with nadd => Some (rz_full_adder_form (vmap x) size (vmap y))
                        | nsub => Some (rz_full_sub_form (vmap x) size (vmap y))
                        | fadd => Some (rz_full_adder_form (vmap x) size (vmap y))
                        | fsub => Some (rz_full_sub_form (vmap x) size (vmap y))
                        | _ => None
            end.

Definition unary_c_value (op:qop) (t:btype) (size:nat) (xv yv:nat -> bool) :=
            match op with nadd => Some (cut_n (sumfb false yv xv) size)
                        | nsub => Some (cut_n (sumfb true (negatem size yv) xv) size)
                        | fadd => Some (cut_n (sumfb false yv xv) size)
                        | fsub => Some (cut_n (sumfb true (negatem size yv) xv) size)
                        | qxor => Some (bin_xor xv yv (get_size size t))
                        | nfac => Some (nat2fb (fact (a_nat2fb yv size) mod 2^size))
                        | fdiv => Some (nat2fb (((a_nat2fb xv size)) / (a_nat2fb yv size)))
                        | _ => None
            end.


Definition com_unary (op:qop) (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp stack:var) (sn:nat) (es:estore) (x y:cfac)
                 : option (@value (option exp * nat * cstore * estore)) :=

     do t1 <- type_factor bv x @
         do t2 <- type_factor bv y @
            match par_find_var_check smap bv size r x with Some (Value vx) => 
              if (fst t1 =a= Q) && (fst t2 =a= C)
               then 
                   do t2v <- par_eval_cfac_check smap bv size r y @
                     match t2v with Value t2v' =>
                 do exps <- Store.find vx es @
                   do cir <- unary_circuit_left op (snd t1) size f vmap vx t2v' stack temp sn @
                      Some (Value (Some cir,sn,r,
                      Store.add vx (cir::exps) es))
                        | _ => Some Error
                     end
              else if (fst t1 =a= Q) && (fst t2 =a= Q)
               then do vyv <- par_find_var_check smap bv size r y @
                     match vyv with Value vy =>
                if vx =qd= vy then Some Error
                else
                 do exps <- Store.find vx es @
                    do cir <- unary_circuit_two op (snd t1) size f vmap vx vy stack sn @
                         Some (Value (Some cir,sn,r,Store.add vx (cir::exps) es))
                      | _ => Some Error
                     end
                 else do t3v <- par_eval_cfac_check smap bv size r y @
                          do txv <- Store.find vx r @ 
                     match t3v with Value tyv => 
                       do new_val <- (unary_c_value op (snd t1) size txv tyv) @
                           Some (Value (None,sn,Store.add vx new_val r,es))
                                 | _ => Some Error
                     end

             | None => None
             | a => Some Error
            end.

Lemma qvar_eq_get_var_eq : forall smap size r x y, qvar_eq_eval smap size r x y = Some (Value true)
              -> get_var x = get_var y.
Proof.
  intros. unfold qvar_eq_eval,get_var in *.
  destruct (eval_var smap size r x) eqn:eq1. destruct v.
  destruct (eval_var smap size r y) eqn:eq2. destruct v.
  simpl in *.  inv H.
  bdestruct (x0 =qd= x1). subst.
  destruct x. destruct y.
  unfold eval_var in *.
  destruct (sem_factor size r v) eqn:eq3.
  destruct (sem_factor size r v0) eqn:eq4. simpl in *.
  bdestruct (a_nat2fb b size <? smap x).
  bdestruct (a_nat2fb b0 size <? smap x0).
  inv eq1. inv eq2. easy. inv eq2. inv eq1. simpl in *. easy. easy.
  unfold eval_var in *.
  destruct (sem_factor size r v) eqn:eq3. simpl in *.
  bdestruct (a_nat2fb b size <? smap x).
  destruct v0. inv eq1. inv eq2. easy.
  easy. easy. easy.
  unfold eval_var in *.
  destruct v. destruct y.
  destruct (sem_factor size r v0) eqn:eq3. simpl in *.
  bdestruct (a_nat2fb b size <? smap x).
  inv eq1. inv eq2. easy. easy. easy.
  destruct v0. inv eq1. inv eq2. easy. easy. easy. easy.
  simpl in *. easy. easy. simpl in *.
  destruct (eval_var smap size r y) eqn:eq2. easy. easy.
  simpl in *. easy.
Qed.

Lemma get_var_same_type_same : forall bv v x y t1 t2, get_var x = Some v -> get_var y = Some v
              -> type_factor bv x = Some t1 -> type_factor bv y = Some t2 -> t1 = t2.
Proof.
  intros. unfold get_var,type_factor in *.
  destruct x. destruct y. inv H. inv H0.
  destruct (BEnv.find (elt:=typ) v bv). simpl in *. destruct t.
  destruct ( typ_factor_full bv C Nat v0) eqn:eq2.
  destruct ( typ_factor_full bv C Nat v1) eqn:eq3.
  simpl in *. inv H1. inv H2. easy. easy. easy. easy. 
  simpl in *. easy.
  inv H.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *. destruct t.
  destruct v1. inv H0.
  destruct (typ_factor_full bv C Nat v0). simpl in *.
  rewrite eq1 in *. simpl in *. easy. easy. easy. easy. easy.
  destruct v0. destruct y.
  unfold typ_factor in *.
  inv H. inv H0.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1.
  simpl in *. destruct t. easy. easy. simpl in *. easy.
  unfold typ_factor in *.
  destruct v1. inv H. inv H0.
  destruct (BEnv.find (elt:=typ) v bv) eqn:eq1. simpl in *. destruct t. easy. inv H1. inv H2. easy.
  simpl in *. easy. easy. easy.
Qed.

Lemma par_find_eval_var_same : forall smap bv rh rl size x t x1 x2, 
        type_factor bv x = Some t -> bv_store_gt_0 smap bv -> bv_store_sub smap bv rh
       -> cstore_store_match smap rh rl bv ->  par_find_var_check smap bv size rl x = Some (Value x1)
        -> eval_var smap size rh x = Some (Value x2) -> x1 = x2.
Proof.
  intros. unfold par_find_var_check,eval_var,type_factor in *.
  destruct x.
  destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
  destruct (par_eval_fc bv size rl v) eqn:eq2.
  destruct t0. simpl in *.
  destruct (typ_factor_full bv C Nat v) eqn:eq3.
  simpl in *.
  Check sem_factor_full_par_eval_same_c.
  rewrite (sem_factor_full_par_eval_same_c v p C Nat bv smap size rh rl) in eq2; try easy.
  rewrite eq2 in *.
  simpl in *.
  bdestruct (a_nat2fb b size <? smap x). inv H3. inv H4. easy.
  easy.
  apply factor_type_all in eq3. subst. easy. easy.
  simpl in *. easy. easy. easy.
  destruct v. inv H3. inv H4. easy.
  easy.
Qed.

Lemma par_find_eval_var_same_1 : forall smap bv rh rl size x t x1 x2, 
        type_factor bv x = Some t -> bv_store_gt_0 smap bv -> bv_store_sub smap bv rh
       -> cstore_store_match smap rh rl bv ->  par_find_var_check smap bv size rl x = Some x1
        -> eval_var smap size rh x = Some x2 -> x1 = x2.
Proof.
  intros. unfold par_find_var_check,eval_var,type_factor in *.
  destruct x.
  destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
  destruct (par_eval_fc bv size rl v) eqn:eq2.
  destruct t0. simpl in *.
  destruct (typ_factor_full bv C Nat v) eqn:eq3.
  simpl in *.
  Check sem_factor_full_par_eval_same_c.
  rewrite (sem_factor_full_par_eval_same_c v p C Nat bv smap size rh rl) in eq2; try easy.
  rewrite eq2 in *.
  simpl in *.
  bdestruct (a_nat2fb b size <? smap x). inv H3. inv H4. easy.
  inv H3. inv H4. easy.
  apply factor_type_all in eq3. subst. easy. easy.
  simpl in *. easy. easy. easy.
  destruct v. inv H3. inv H4. easy.
  easy.
Qed.

Lemma par_find_eval_var_same_2 : forall smap bv rh rl size x t x1, 
        type_factor bv x = Some t -> bv_store_gt_0 smap bv -> bv_store_sub smap bv rh
       -> cstore_store_match smap rh rl bv ->  par_find_var_check smap bv size rl x = Some x1
        -> eval_var smap size rh x = Some x1.
Proof.
  intros. unfold par_find_var_check,eval_var,type_factor in *.
  destruct x.
  destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
  destruct (par_eval_fc bv size rl v) eqn:eq2.
  destruct t0. simpl in *.
  destruct (typ_factor_full bv C Nat v) eqn:eq3.
  simpl in *.
  Check sem_factor_full_par_eval_same_c.
  rewrite (sem_factor_full_par_eval_same_c v p C Nat bv smap size rh rl) in eq2; try easy.
  rewrite eq2 in *.
  simpl in *.
  bdestruct (a_nat2fb b size <? smap x). inv H3. easy.
  inv H3. easy.
  apply factor_type_all in eq3. subst. easy. easy.
  simpl in *. easy. easy. easy.
  destruct v. inv H3. easy.
  easy.
Qed.

Lemma par_find_var_store_value : forall smap bv size rl rh x t xn val xl,
   type_factor bv x = Some t ->
    cstore_store_match smap rh rl bv -> bv_store_sub smap bv rh -> bv_store_gt_0 smap bv -> 
   par_find_var_check smap bv size rl x = Some (Value xn) -> Store.MapsTo xn (val :: xl) rh ->
   sem_cfac smap size rh x = Some (Value val).
Proof.
 intros. destruct x.
 unfold sem_cfac,par_find_var_check,type_factor in *.
 destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
 simpl in *. destruct t0.
 destruct (typ_factor_full bv C Nat v) eqn:eq2.
 simpl in *. inv H.
 destruct (par_eval_fc bv size rl v) eqn:eq3.
 rewrite (sem_factor_full_par_eval_same_c v p C Nat bv smap size rh rl) in eq3; try easy.
 rewrite eq3.
 simpl in *. 
 bdestruct (a_nat2fb b0 size <? smap x). inv H3.
 unfold bv_store_gt_0,bv_store_sub in *.
 apply BEnv.find_2 in eq1.
 assert (BEnv.In (elt:=typ) x bv).
 unfold BEnv.In,BEnv.Raw.PX.In. exists ((TArray a b n)). easy.
 specialize (H1 x (a_nat2fb b0 size) H3 H).
 destruct H1. destruct H1. apply Store.find_1 in H1. 
 destruct x0. easy. 
 assert ((@pair BEnv.key nat x (a_nat2fb b0 size)) = (@pair qvar nat x (a_nat2fb b0 size))) by easy.
 rewrite H6 in *.
 rewrite H1. simpl in *.
 apply Store.find_2 in H1.
 apply store_mapsto_always_same with (v1 := (val :: xl)) in H1; try easy. inv H1.
 easy. easy. simpl in *.
 apply factor_type_c in eq2. easy.
 simpl in *. easy.
 simpl in *. easy. easy. simpl in *. easy.
 simpl in *. destruct v. inv H3. simpl in *.
 destruct (BEnv.find (elt:=typ) v bv) eqn:eq1. simpl in *. destruct t0. easy.
 unfold bv_store_gt_0,bv_store_sub in *.
 apply BEnv.find_2 in eq1.
 assert (BEnv.In (elt:=typ) v bv).
 unfold BEnv.In,BEnv.Raw.PX.In. exists (TNor a b). easy.
 apply H2 in H3 as X1. specialize (H1 v 0 H3 X1).
 destruct H1. destruct H1. destruct x. easy.
 apply Store.find_1 in H1.
 assert ((@pair BEnv.key nat v 0) = (@pair qvar nat v 0)) by easy.
 rewrite H6 in *. rewrite H1. simpl in *.
 apply Store.find_2 in H1.
 apply store_mapsto_always_same with (v1 := (val :: xl)) in H1; try easy. inv H1.
 easy. easy. easy.
Qed.

Lemma par_find_var_cstore_same : forall smap bv size rl rh x t xn bval val xl,
   type_factor bv x = Some (C,t) ->
    cstore_store_match smap rh rl bv -> bv_store_gt_0 smap bv -> 
   par_find_var_check smap bv size rl x = Some (Value xn) ->
   Store.MapsTo xn bval rl ->
   Store.MapsTo xn (val :: xl) rh -> bval = val.
Proof.
 intros. destruct x.
 unfold cstore_store_match,bv_store_gt_0 in *.
 unfold par_find_var_check,type_factor in *.
 destruct (BEnv.find (elt:=typ) x bv) eqn:eq1.
 simpl in *. destruct t0.
 destruct (typ_factor_full bv C Nat v) eqn:eq2.
 simpl in *. inv H.
 destruct (par_eval_fc bv size rl v) eqn:eq3.
 simpl in *. 
 bdestruct (a_nat2fb b size <? smap x). inv H2.
 apply H0 with (t := (TArray C t n)) in H4; try easy.
 apply store_mapsto_always_same with (v1 := val) in H3; try easy. 
 apply BEnv.find_2 in eq1. easy.
 1-5:easy.
 simpl in *. unfold typ_factor in *. destruct v.
 destruct (BEnv.find (elt:=typ) v bv) eqn:eq1. simpl in *. destruct t0. easy.
 unfold bv_store_gt_0 in *.
 apply BEnv.find_2 in eq1.
 assert (BEnv.In (elt:=typ) v bv).
 unfold BEnv.In,BEnv.Raw.PX.In. exists (TNor a b). easy.
 inv H.  inv H2.
 apply H1 in H5 as X1.
 unfold cstore_store_match in H0.
 specialize (H0 v 0 val xl (TNor C t)).
 apply H0 in H4; try easy.
 apply store_mapsto_always_same with (v1 := val) in H3; try easy. 
 easy. easy.
Qed.

Definition unary_arith_op_sem (op : qop) (size:nat) (x y : nat-> bool) := 
    match op with nadd => sumfb false x y
                | nsub => (sumfb true (negatem size x) y)
                | fadd => (sumfb false x y)
                | fsub => (sumfb true (negatem size x) y)
                | _ => nat2fb 0
    end.

Lemma unary_core_app_left : 
  forall n f x y c aenv tenv op,
    op = nadd \/ op = nsub \/ op = fadd \/ op = fsub ->
    0 < n -> aenv x = n -> aenv y = n -> snd c < aenv (fst c) ->
    get_cua (f c) = false ->
    Env.MapsTo x PQASM.Nor tenv -> Env.MapsTo y PQASM.Nor tenv -> Env.MapsTo (fst c) PQASM.Nor tenv ->
    right_mode_env aenv tenv f ->
    qft_uniform aenv tenv f -> qft_gt aenv tenv f ->
    x <> y -> x <> fst c -> y <> fst c ->
    exp_sem aenv (unary_circuit_left_core_cl op n x y c) f =
        (put_cus f y (unary_arith_op_sem op n (get_cus n f x) (get_cus n f y)) n).
Proof.
  intros. unfold unary_circuit_left_core_cl,unary_arith_op_sem.
  destruct H. rewrite H in *.
  rewrite adder01_correct_fb; try easy.
  rewrite H4. easy.
  rewrite <- H1.
  apply type_nor_modes with (env := tenv); try easy.
  rewrite <- H2.
  apply type_nor_modes with (env := tenv); try easy.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  destruct H. rewrite H.
  rewrite subtractor01_correct_fb with (tenv := tenv); try easy.
  rewrite H4. simpl. easy.
  destruct H. rewrite H.
  rewrite adder01_correct_fb; try easy.
  rewrite H4. easy.
  rewrite <- H1.
  apply type_nor_modes with (env := tenv); try easy.
  rewrite <- H2.
  apply type_nor_modes with (env := tenv); try easy.
  apply type_nor_mode with (aenv := aenv) (env := tenv); try easy.
  rewrite H.
  rewrite subtractor01_correct_fb with (tenv := tenv); try easy.
  rewrite H4. simpl. easy.
Qed.

Lemma compile_unary_sem : forall bv' t sl size smap vmap fv bv fl rh rl stack temp sn st re f aenv tenv es a op x y, 
      type_qexp fv bv a (unary x op y) = Some bv' ->
      type_factor bv x = Some t ->
      com_unary op size smap vmap bv fl rl temp stack sn es x y = Some st ->
      sem_qexp smap fv bv size rh (unary x op y) re ->
      0 < size -> S (S sn) < sl ->
      cstore_store_match smap rh rl bv -> bv_store_sub smap bv rh -> bv_store_gt_0 smap bv ->
      store_typed rh bv size -> store_match_q rh f bv vmap (aenv (get_size size (snd t))) ->
      store_match_st sl sn stack f vmap ->
      aenv_match stack temp size bv ((aenv (get_size size (snd t)))) vmap ->
      not_stack stack temp vmap smap (get_var_cfac x ++ get_var_cfac y) ->
      all_nor vmap smap (get_var_cfac x ++ get_var_cfac y) tenv -> 
      stack <> temp -> aenv (get_size size (snd t)) temp = (get_size size (snd t))
      -> aenv (get_size size (snd t)) stack = sl -> get_cus size f temp = nat2fb 0 ->
      Env.MapsTo temp PQASM.Nor tenv -> Env.MapsTo stack PQASM.Nor tenv ->
      right_mode_env (aenv (get_size size (snd t))) tenv f -> qft_uniform (aenv (get_size size (snd t))) tenv f 
         -> qft_gt (aenv (get_size size (snd t)))  tenv f
          -> vmap_bij vmap
         -> (st = Error /\ re = Error) 
              \/ (exists xn xvl b, 
                        par_find_var_check smap bv size rl x = Some (Value xn)
                          /\ st = Value (None,sn, (Store.add xn b rl),es)
                          /\ Store.MapsTo xn xvl rh /\ re = Value (Store.add xn (b::xvl) rh))
              \/ (exists xn xvl p esv, st = Value (Some p, sn,rl,Store.add xn (p::esv) es) 
                    /\ par_find_var_check smap bv size rl x = Some (Value xn)
                 /\ Store.MapsTo xn xvl rh 
                 /\ Store.MapsTo xn esv es
                 /\ re = Value (Store.add xn ((get_cus ((get_size size (snd t)))
                               (exp_sem (aenv (get_size size (snd t))) p f) (vmap xn))::xvl) rh)).
Proof.
  intros. unfold type_qexp,com_unary in *.
  destruct (get_var x) eqn:eq1.
  rewrite H0 in *.
  destruct (type_factor bv y) eqn:eq2.
  simpl in *.
  destruct (is_unary (fst t) op && check_fst_type op (snd t) && check_snd_type op (snd p) &&
      sub_atype (fst p) (fst t) && sub_atype a (fst t) &&
      check_xor_type op (snd t) (snd p)) eqn:eq3.
  simpl in *. inv H.
  destruct (par_find_var_check smap bv' size rl x) eqn:eq4.
  destruct v. destruct t. destruct p. simpl in *.
  bdestruct (a0 =a= Q). bdestruct (a1 =a= C).
  destruct (par_eval_cfac_check smap bv' size rl y) eqn:eq5. destruct v.
  simpl in *.
  destruct (Store.find (elt:=list exp) x0 es) eqn:eq6. 
  destruct (unary_circuit_left op b size fl vmap x0 x1 stack temp sn) eqn:eq7. simpl in *.
  inv H2.
  apply eval_cfac_sem_error in H29.
  apply type_cfac_find_var_error with (t := (Q, b)) (bv := bv') (rl := rl) in H29; try easy.
  rewrite H29 in *. easy.
  rewrite <- sem_cfac_par_eval_same_c with (t := (C,b0)) (bv := bv') (rl := rl) in H29; try easy.
  rewrite H29 in *. easy.
  unfold qvar_eq_eval in *. 
  destruct (eval_var smap size rh x) eqn:eq8. destruct v.
  destruct (eval_var smap size rh y) eqn:eq9. destruct v.
  simpl in *. easy. simpl in *.
  apply eval_cfac_sem_error in eq9.
  rewrite <- sem_cfac_par_eval_same_c with (t := (C, b0)) (bv := bv') (rl := rl) in eq9; try easy.
  rewrite eq9 in *. easy.
  simpl in *. easy.
  destruct (eval_var smap size rh y ).
  simpl in *. 
  apply eval_cfac_sem_error in eq8.
  apply type_cfac_find_var_error with (t := (Q, b)) (bv := bv') (rl := rl) in eq8; try easy.
  rewrite eq8 in *. easy.
  simpl in *. easy.
  simpl in *. easy.
  assert (get_var y = Some q). 
  rewrite (qvar_eq_get_var_eq smap size rh) with (y := y) in eq1; try easy.
  specialize (get_var_same_type_same bv' q x y (Q, b) (C,b0) eq1 H H0 eq2) as eq8.
  inv eq8. 
  specialize (par_find_eval_var_same smap bv' rh rl size x (Q, b) x0 xn
                H0 H7 H6 H5 eq4 H28) as X1. subst.
  right. right. inv H1.
  exists xn. exists (x_val :: xl).
  exists e. exists l. split. easy. split. easy. split. easy. split.
  apply Store.find_2 in eq6. easy.
  assert (x1 = val).
  rewrite sem_cfac_par_eval_same_c with (t :=  (C, b0)) (rh := rh) in eq5; try easy.
  rewrite eq5 in *. inv H33. easy. subst.
  apply andb_true_iff in eq3.
  destruct eq3. clear H1.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H. destruct H.
  apply andb_true_iff in H. destruct H.
  unfold unary_circuit_left,is_unary,is_q_unary,check_fst_type,check_snd_type in *.
  simpl in *.
  bdestruct (op =op= qxor). subst.
  unfold apply_unary.
  rewrite H0 in H32. inv H32. simpl in *.
  bdestruct (b =b= Bl). subst.
  Local Opaque init_v.
  simpl in *. inv eq7.
  Local Transparent init_v.
  rewrite init_v_sem_full with (size := (get_size size Bl)) (tenv := tenv) ; try easy.
  rewrite get_put_cus_cut_n; try easy.
  unfold bin_xor.
  rewrite cut_n_twice_same.
  assert (cut_n (fun x0 : nat => x_val x0 ⊕ val x0) 1 
        = cut_n (fun x0 : nat => get_cus (get_size size Bl) f (vmap xn) x0 ⊕ val x0) (get_size size Bl) ).
  replace ((get_size size Bl)) with ((get_size size (snd (Q, Bl)))) by easy.
  rewrite <- (aenv_match_value_cfac x (Q, Bl) xn size 
       (aenv (get_size size Bl)) bv' smap vmap rh rl stack temp); try easy.
  rewrite (q_var_same_value x xn (Q,Bl)
       x_val smap vmap bv' size rh rl f (aenv (get_size size Bl))); try easy.
  rewrite (aenv_match_value_cfac x (Q, Bl) xn size 
       (aenv (get_size size Bl)) bv' smap vmap rh rl stack temp); try easy.
  unfold get_size. simpl.
  apply functional_extensionality. intros.
  unfold cut_n.
  bdestruct (x0 <? 1). easy. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl x x0 xn (Q, Bl)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl x x0 xn (Q, Bl)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply (par_find_var_store_value smap bv' size rl rh x (Q,Bl) xn x_val xl); try easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl x x0 xn (Q, Bl)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl x x0 xn (Q, Bl)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  rewrite H25. easy.
  replace ((get_size size Bl)) with ((get_size size (snd (Q, Bl)))) by easy.
  rewrite <- (aenv_match_value_cfac x (Q, Bl) xn size 
       (aenv (get_size size Bl)) bv' smap vmap rh rl stack temp); try easy.
  apply type_nor_modes with (env := tenv); try easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y) bv'
        size rl x x0 xn (Q,Bl)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl x x0 xn (Q, Bl)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl x x0 xn (Q, Bl)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  rewrite (aenv_match_value_cfac x (Q, Bl) xn size 
       (aenv (get_size size Bl)) bv' smap vmap rh rl stack temp); try easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl x x0 xn (Q, Bl)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl x x0 xn (Q, Bl)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y) bv'
        size rl x x0 xn (Q,Bl)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  inv eq7.
  rewrite init_v_sem_full with (size := (get_size size b)) (tenv := tenv) ; try easy.
  rewrite get_put_cus_cut_n; try easy.
  unfold bin_xor.
  rewrite cut_n_twice_same.
  assert (cut_n (fun x0 : nat => x_val x0 ⊕ val x0) size
        = cut_n (fun x0 : nat => get_cus (get_size size b) f (vmap xn) x0 ⊕ val x0)
        (get_size size b)).
  replace ((get_size size b)) with ((get_size size (snd (Q, b)))) by easy.
  rewrite <- (aenv_match_value_cfac x (Q, b) xn size 
       (aenv (get_size size b)) bv' smap vmap rh rl stack temp); try easy.
  rewrite (q_var_same_value x xn (Q,b)
       x_val smap vmap bv' size rh rl f (aenv (get_size size b))); try easy.
  rewrite (aenv_match_value_cfac x (Q, b) xn size 
       (aenv (get_size size b)) bv' smap vmap rh rl stack temp); try easy.
  unfold get_size. simpl.
  apply functional_extensionality. intros.
  unfold cut_n.
  bdestruct (b =b= Bl). easy.
  bdestruct (x0 <? size).  easy. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply (par_find_var_store_value smap bv' size rl rh x (Q,b) xn x_val xl); try easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  rewrite H26. easy.
  replace ((get_size size b)) with ((get_size size (snd (Q, b)))) by easy.
  rewrite <- (aenv_match_value_cfac x (Q, b) xn size 
       (aenv (get_size size b)) bv' smap vmap rh rl stack temp); try easy.
  apply type_nor_modes with (env := tenv); try easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y) bv'
        size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  rewrite (aenv_match_value_cfac x (Q, b) xn size 
       (aenv (get_size size b)) bv' smap vmap rh rl stack temp); try easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y) bv'
        size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  bdestruct (fl =fl= Classic).
  inv eq7.
  assert (op = nadd \/ op = nsub \/ op = fadd \/ op = fsub) as eq8.
  destruct op. left. easy.
  right. left. easy. right. right. left. easy. right. right. left. easy.
  right. right. right. 1-8:easy.
  assert (get_size size b = size) as eq9.
  unfold get_size. bdestruct (b =b= Bl).
  destruct eq8. subst. easy.
  destruct H29. subst. easy.
  destruct H29. subst. easy.
  subst. easy. easy.
  assert (vmap xn <> stack) as V1.
  apply par_find_get_var in eq4 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  assert (vmap xn <> temp) as V2.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  assert (nor_modes f temp size) as V3.
  rewrite <- eq9.
  rewrite <- H15.
  apply type_nor_modes with (env := tenv);try easy.
  rewrite eq9 in *.
  assert (aenv size (vmap xn) = (get_size size (snd (Q,b)))) as V4.
  Check aenv_match_value_cfac.
  rewrite (aenv_match_value_cfac x (Q,b) xn size (aenv size) bv' smap vmap
           rh rl stack temp); try easy.
  assert (nor_modes f (vmap xn) size) as V5.
  simpl in V4. rewrite eq9 in *. rewrite <- V4.
  apply type_nor_modes with (env := tenv);try easy.
  Check all_nor_var.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  Local Opaque init_v unary_circuit_left_core_cl. simpl.
  rewrite init_v_sem with (size := size) (tenv := tenv); try easy.
  rewrite unary_core_app_left with (tenv := tenv); try easy.
  Local Transparent init_v unary_circuit_left_core_cl.
  rewrite put_cus_twice_neq by lia.
  rewrite get_put_cus_cut_n by easy.
  rewrite get_cus_put_neq by lia.
  rewrite cut_n_twice_same.
  assert ((exp_sem (aenv size) (inv_exp (init_v size temp val))
           (put_cus
              (put_cus f (vmap xn)
                 (unary_arith_op_sem op size (cut_n val size) (get_cus size f (vmap xn))) size) temp
              (cut_n val size) size))
    = (put_cus f (vmap xn)
                 (unary_arith_op_sem op size (cut_n val size) (get_cus size f (vmap xn))) size)).
  apply inv_pexp_reverse with (tenv := tenv) (tenv' := tenv).
  apply well_typed_init_v. easy.
  apply right_mode_exp_put_cus_same; try easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  rewrite init_v_sem with (size := size) (tenv := tenv); try easy.
  rewrite get_cus_put_neq by lia. easy.
  apply right_mode_exp_put_cus_same; try easy.
  rewrite H26. clear H26.
  rewrite get_put_cus_cut_n; try easy.
  rewrite H0 in *. inv H32.
  Check q_var_same_value.
  simpl in *. rewrite eq9 in *.
  assert ((get_cus size f (vmap xn)) = cut_n x_val size).
  rewrite <- V4.
  rewrite (q_var_same_value x xn (Q, b) x_val smap vmap bv' size rh rl); try easy.
  Check par_find_var_store_value.
  apply (par_find_var_store_value smap bv' size rl rh x (Q,b) xn x_val xl); try easy.
  rewrite H26.
  assert ((cut_n val size) = val).
  rewrite cut_n_eq. easy.
  rewrite <- eq9.
  Check stored_value_typed.
  assert (b = b0).
  destruct eq8. subst.
  destruct b0. destruct b. 1-5:easy.
  destruct H29. subst.
  destruct b0. destruct b. 1-5:easy.
  destruct H29. subst.
  destruct b0. destruct b. 1-3:easy.
  destruct b. 1-4:easy.
  subst.
  destruct b0. destruct b. 1-3:easy.
  destruct b. 1-4:easy. rewrite H29 in *.
  apply (stored_value_typed smap rh bv' size y val C b0); try easy.
  rewrite H29.
  assert ((cut_n x_val size) = x_val).
  rewrite cut_n_eq. easy.
  rewrite <- eq9.
  Check stored_value_typed_1.
  apply (stored_value_typed_1 smap rh bv' size x
           xn x_val xl Q b); try easy.
  rewrite H31.
  unfold apply_unary,unary_arith_op_sem.
  destruct eq8. subst. easy.
  destruct H32. subst. easy.
  destruct H32. subst. easy.
  subst. easy.
  simpl in *. rewrite V4. easy.
  simpl in *. lia.
  rewrite put_cus_neq_1 by iner_p.
  unfold store_match_st in *.
  rewrite <- get_cus_cua with (n := (aenv size stack)) by lia.
  apply H10. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply right_mode_exp_put_cus_same; try easy.
  apply qft_uniform_put_cus_same; try easy.
  apply qft_gt_put_cus_same; try easy.
  lia. simpl. lia.
  assert (op = nadd \/ op = nsub \/ op = fadd \/ op = fsub) as eq8.
  destruct op. left. easy.
  right. left. easy. right. right. left. easy. right. right. left. easy.
  right. right. right. 1-8:easy.
  assert (get_size size b = size) as eq9.
  unfold get_size. bdestruct (b =b= Bl).
  destruct eq8. subst. easy.
  destruct H31. subst. easy.
  destruct H31. subst. easy.
  subst. easy. easy.
  rewrite eq9 in *.
  assert (aenv size (vmap xn) = (get_size size (snd (Q,b)))) as V1.
  Check aenv_match_value_cfac.
  rewrite (aenv_match_value_cfac x (Q,b) xn size (aenv size) bv' smap vmap
           rh rl stack temp); try easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  assert (nor_modes f (vmap xn) size) as V2.
  simpl in V1. rewrite eq9 in *. rewrite <- V1.
  apply type_nor_modes with (env := tenv);try easy.
  Check all_nor_var.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  simpl in *. rewrite eq9 in *.
  destruct op.
  inv eq7.
  rewrite rz_adder_form_correct_1 with (tenv := tenv); try easy.
  rewrite get_put_cus_cut_n by easy.
  rewrite H0 in *. inv H32.
  simpl. unfold apply_unary.
  assert ((get_cus size f (vmap xn)) = x_val).
  rewrite <- V1.
  Check q_var_same_value.
  rewrite (q_var_same_value x xn (Q,b) x_val smap vmap bv' size rh rl f (aenv size)); try easy.
  apply cut_n_eq.
  rewrite V1. rewrite <- eq9.
  Check stored_value_typed_1.
  apply (stored_value_typed_1 smap rh bv' size x xn x_val xl Q b); try easy.
  apply (par_find_var_store_value smap bv' size rl rh x (Q,b) xn x_val xl); try easy.
  rewrite H29. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  inv eq7.
  rewrite rz_sub_right_sem_1 with (tenv := tenv); try easy.
  rewrite get_put_cus_cut_n by easy.
  rewrite H0 in *. inv H32.
  simpl. unfold apply_unary.
  assert ((get_cus size f (vmap xn)) = x_val).
  rewrite <- V1.
  Check q_var_same_value.
  rewrite (q_var_same_value x xn (Q,b) x_val smap vmap bv' size rh rl f (aenv size)); try easy.
  apply cut_n_eq.
  rewrite V1. rewrite <- eq9.
  Check stored_value_typed_1.
  apply (stored_value_typed_1 smap rh bv' size x xn x_val xl Q b); try easy.
  apply (par_find_var_store_value smap bv' size rl rh x (Q,b) xn x_val xl); try easy.
  rewrite H29. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  easy. inv eq7.
  rewrite rz_adder_form_correct_1 with (tenv := tenv); try easy.
  rewrite get_put_cus_cut_n by easy.
  rewrite H0 in *. inv H32.
  simpl. unfold apply_unary.
  assert ((get_cus size f (vmap xn)) = x_val).
  rewrite <- V1.
  Check q_var_same_value.
  rewrite (q_var_same_value x xn (Q,b) x_val smap vmap bv' size rh rl f (aenv size)); try easy.
  apply cut_n_eq.
  rewrite V1. rewrite <- eq9.
  Check stored_value_typed_1.
  apply (stored_value_typed_1 smap rh bv' size x xn x_val xl Q b); try easy.
  apply (par_find_var_store_value smap bv' size rl rh x (Q,b) xn x_val xl); try easy.
  rewrite H29. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  inv eq7.
  rewrite rz_sub_right_sem_1 with (tenv := tenv); try easy.
  rewrite get_put_cus_cut_n by easy.
  rewrite H0 in *. inv H32.
  simpl. unfold apply_unary.
  assert ((get_cus size f (vmap xn)) = x_val).
  rewrite <- V1.
  Check q_var_same_value.
  rewrite (q_var_same_value x xn (Q,b) x_val smap vmap bv' size rh rl f (aenv size)); try easy.
  apply cut_n_eq.
  rewrite V1. rewrite <- eq9.
  Check stored_value_typed_1.
  apply (stored_value_typed_1 smap rh bv' size x xn x_val xl Q b); try easy.
  apply (par_find_var_store_value smap bv' size rl rh x (Q,b) xn x_val xl); try easy.
  rewrite H29. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  1-9:easy.
  simpl in *.
  inv H2.
  apply par_find_eval_var_same_1 with (rh := rh) (t := (Q,b)) (x2 := Error) in eq4; try easy.
  inv H1. left. easy. inv H1. left. easy.
  inv H1. left. easy.
  rewrite <- sem_cfac_par_eval_same_c 
          with (t := (C,b0)) (bv := bv') (rl := rl) in H33; try easy.
  rewrite H33 in *. easy.
  easy.
  destruct a1.
  simpl in *. easy.
  simpl in *.
  destruct (par_find_var_check smap bv' size rl y) eqn:eq5. destruct v.
  simpl in *.
  inv H2.
  apply eval_cfac_sem_error in H29.
  apply type_cfac_find_var_error with (t := (Q, b)) (bv := bv') (rl := rl) in H29; try easy.
  rewrite H29 in *. easy.
  apply type_cfac_sem_value with (t := (Q,b0)) (bv := bv') (rh := rh) in eq5; try easy.
  destruct eq5.
  rewrite H29 in *. easy.
  unfold qvar_eq_eval in *. 
  destruct (eval_var smap size rh x) eqn:eq8. destruct v.
  destruct (eval_var smap size rh y) eqn:eq9. destruct v.
  simpl in *. easy. simpl in *.
  apply eval_cfac_sem_error in eq9.
  apply type_cfac_find_var_error with (t := (Q, b0)) (bv := bv') (rl := rl) in eq9; try easy.
  rewrite eq9 in *. easy.
  simpl in *. easy.
  destruct (eval_var smap size rh y ).
  simpl in *. 
  apply eval_cfac_sem_error in eq8.
  apply type_cfac_find_var_error with (t := (Q, b)) (bv := bv') (rl := rl) in eq8; try easy.
  rewrite eq8 in *. easy.
  simpl in *. easy.
  simpl in *. easy.
  unfold qvar_eq_eval in *.
  apply par_find_eval_var_same_2 with (rh := rh) (t := (Q,b)) in eq4; try easy.
  apply par_find_eval_var_same_2 with (rh := rh) (t := (Q,b0)) in eq5; try easy.
  rewrite eq4 in *. rewrite eq5 in *.
  simpl in *.
  bdestruct ((x0 =qd= x1)).
  inv H1. left. easy. easy.
  unfold qvar_eq_eval in *.
  apply par_find_eval_var_same_2 with (rh := rh) (t := (Q,b)) in eq4 as V3; try easy.
  apply par_find_eval_var_same_2 with (rh := rh) (t := (Q,b0)) in eq5 as V4; try easy.
  rewrite V3 in *. rewrite V4 in *.
  simpl in *.
  bdestruct ((x0 =qd= x1)).
  apply H27 in H0. easy.
  destruct (Store.find (elt:=list exp) x0 es) eqn:eq6. 
  destruct (unary_circuit_two op b size fl vmap x0 x1 stack sn) eqn:eq7. simpl in *.
  unfold unary_circuit_two in *. inv H28.
  assert (vmap xn <> vmap x1) as V1. apply H23. easy.
  assert (aenv (get_size size b) (vmap xn) = (get_size size (snd (Q,b)))) as V2.
  Check aenv_match_value_cfac.
  rewrite (aenv_match_value_cfac x (Q,b) xn size (aenv (get_size size b)) bv' smap vmap
           rh rl stack temp); try easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  assert (aenv (get_size size b) (vmap x1) = (get_size size (snd (Q,b0)))) as V5.
  Check aenv_match_value_cfac.
  rewrite (aenv_match_value_cfac y (Q,b0) x1 size (aenv (get_size size b)) bv' smap vmap
           rh rl stack temp); try easy.
  apply par_find_get_var in eq5 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl y x0 x1 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  apply par_find_get_var in eq5 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl y x0 x1 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy. simpl in *.
  assert (nor_modes f (vmap xn) (get_size size b)) as V6.
  rewrite <- V2.
  apply type_nor_modes with (env := tenv);try easy.
  Check all_nor_var.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  assert (nor_modes f (vmap x1) (get_size size b0)) as V7.
  rewrite <- V5.
  apply type_nor_modes with (env := tenv);try easy.
  Check all_nor_var.
  apply par_find_get_var in eq5 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl y x0 x1 (Q,b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  apply andb_true_iff in eq3.
  destruct eq3.
  apply andb_true_iff in H2. destruct H2.
  apply andb_true_iff in H2. destruct H2.
  apply andb_true_iff in H2. destruct H2.
  apply andb_true_iff in H2. destruct H2.
  right. right.
  unfold check_xor_type in *.
  bdestruct (op =op= qxor). subst.
  bdestruct (b =b= b0). subst. 
  inv H1. inv eq7.
  exists xn. exists (x_val :: xl). exists (copyto (vmap x1) (vmap xn) (get_size size b0)).
  exists l. split. easy. split. easy. split. easy. split.
  apply Store.find_2 in eq6. easy.
  rewrite copyto_sem with (tenv := tenv); try easy.
  rewrite get_put_cus_cut_n by easy.
  unfold apply_unary.
  rewrite H0 in *. inv H32.
  simpl in *.
  assert ((get_cus (get_size size b0) f (vmap xn)) = x_val).
  rewrite <- V2.
  rewrite (q_var_same_value x xn (Q,b0) x_val smap vmap 
        bv' size rh rl f (aenv (get_size size b0))); try easy.
  rewrite cut_n_eq. easy.
  rewrite V2.
  apply (stored_value_typed_1 smap rh bv' size x xn x_val xl Q b0); try easy.
  apply (par_find_var_store_value smap bv' size rl rh x (Q,b0) xn x_val xl); try easy.
  assert ((get_cus (get_size size b0) f (vmap x1)) = val).
  rewrite <- V5.
  rewrite (q_var_same_value y x1 (Q,b0) val smap vmap 
        bv' size rh rl f (aenv (get_size size b0))); try easy.
  rewrite cut_n_eq. easy.
  rewrite V5.
  apply (stored_value_typed smap rh bv' size y val Q b0); try easy.
  rewrite H1. rewrite H31.
  bdestruct (b0 =b= Bl).
  unfold bin_xor,get_size. subst. simpl.
  rewrite cut_n_twice_same. easy.
  unfold bin_xor,get_size. simpl.
  bdestruct (b0 =b= Bl). easy. 
  rewrite cut_n_twice_same. easy.
  apply par_find_get_var in eq5 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl y x0 x1 (Q,b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b0)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy. easy.
  inv H1.
  exists xn. exists (x_val :: xl). exists e.
  exists l. split. easy. split. easy. split. easy. split.
  apply Store.find_2 in eq6. easy.
  assert (op = nadd \/ op = nsub \/ op = fadd \/ op = fsub) as eq8.
  destruct op. left. easy.
  right. left. easy. right. right. left. easy. right. right. left. easy.
  right. right. right. 1-8:easy.
  assert (get_size size b = size) as eq9.
  unfold get_size. bdestruct (b =b= Bl).
  destruct eq8. subst. easy.
  destruct H34. subst. easy.
  destruct H34. subst. easy.
  subst. easy. easy.
  assert (get_size size b0 = size) as eq10.
  unfold get_size. bdestruct (b0 =b= Bl).
  destruct eq8. subst. easy.
  destruct H34. subst. easy.
  destruct H34. subst. easy.
  subst. easy. easy.
  rewrite eq9 in *. rewrite eq10 in *.
  bdestruct (fl =fl= Classic).
  assert (nor_modes f stack (aenv size stack)) as V8.
  apply type_nor_modes with (env := tenv); try easy.
  assert (vmap xn <> stack) as V9.
  apply par_find_get_var in eq4 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  assert (vmap xn <> temp) as V10.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl x x0 xn (Q, b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  assert (vmap x1 <> stack) as V11.
  apply par_find_get_var in eq5 as X1. destruct X1.
  Check not_eq_stack_var.
  apply (not_eq_stack_var stack temp vmap smap
         ((get_var_cfac x ++ get_var_cfac y)) bv' size rl y x0 x1 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  assert (vmap x1 <> temp) as V12.
  apply par_find_get_var in eq5 as X1. destruct X1.
  apply (not_eq_temp_var stack temp vmap smap
         (get_var_cfac x ++ get_var_cfac y) bv' size rl y x0 x1 (Q, b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  assert ((get_cus size f (vmap xn)) = x_val).
  rewrite <- V2.
  rewrite (q_var_same_value x xn (Q,b) x_val smap vmap 
        bv' size rh rl f (aenv size)); try easy.
  rewrite cut_n_eq. easy.
  rewrite V2. rewrite <- eq9.
  apply (stored_value_typed_1 smap rh bv' size x xn x_val xl Q b); try easy.
  apply (par_find_var_store_value smap bv' size rl rh x (Q,b) xn x_val xl); try easy.
  assert ((get_cus size f (vmap x1)) = val).
  rewrite <- V5.
  rewrite (q_var_same_value y x1 (Q,b0) val smap vmap 
        bv' size rh rl f (aenv size)); try easy.
  rewrite cut_n_eq. easy.
  rewrite V5. rewrite <- eq10.
  apply (stored_value_typed smap rh bv' size y val Q b0); try easy.
  assert (get_cua (f (stack,sn)) = false) as eq11.
  unfold nor_modes,nor_mode in *.
  specialize (V8 sn). assert (sn < aenv size stack) by lia. apply V8 in H36.
  unfold store_match_st in *.
  assert (sn <= sn) by lia. apply H10 in H37.
  rewrite get_cus_cua in H37. easy. lia.
  destruct eq8. subst.
  inv eq7.
  rewrite adder01_correct_fb; try easy.
  rewrite get_put_cus_cut_n; try easy.
  unfold apply_unary.
  rewrite eq11. easy.
  apply V8. lia. lia.
  destruct H36. subst.
  inv eq7.
  rewrite subtractor01_correct_fb with (tenv := tenv); try easy.
  rewrite get_put_cus_cut_n; try easy.
  unfold apply_unary.
  rewrite eq11. easy. simpl. lia.
  apply par_find_get_var in eq5 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl y x0 x1 (Q,b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy. lia.
  destruct H36. subst.
  inv eq7.
  rewrite adder01_correct_fb; try easy.
  rewrite get_put_cus_cut_n; try easy.
  unfold apply_unary.
  rewrite eq11. easy.
  apply V8. lia. lia.
  subst.
  inv eq7.
  rewrite subtractor01_correct_fb with (tenv := tenv); try easy.
  rewrite get_put_cus_cut_n; try easy.
  unfold apply_unary.
  rewrite eq11. easy. simpl. lia.
  apply par_find_get_var in eq5 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl y x0 x1 (Q,b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy. lia.
  assert ((get_cus size f (vmap xn)) = x_val).
  rewrite <- V2.
  rewrite (q_var_same_value x xn (Q,b) x_val smap vmap 
        bv' size rh rl f (aenv size)); try easy.
  rewrite cut_n_eq. easy.
  rewrite V2. rewrite <- eq9.
  apply (stored_value_typed_1 smap rh bv' size x xn x_val xl Q b); try easy.
  apply (par_find_var_store_value smap bv' size rl rh x (Q,b) xn x_val xl); try easy.
  assert ((get_cus size f (vmap x1)) = val).
  rewrite <- V5.
  rewrite (q_var_same_value y x1 (Q,b0) val smap vmap 
        bv' size rh rl f (aenv size)); try easy.
  rewrite cut_n_eq. easy.
  rewrite V5. rewrite <- eq10.
  apply (stored_value_typed smap rh bv' size y val Q b0); try easy.
  unfold apply_unary.
  destruct eq8. subst.
  inv eq7.
  rewrite rz_full_adder_form_correct with (tenv := tenv); try easy.
  rewrite get_put_cus_cut_n; try easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq5 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl y x0 x1 (Q,b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  destruct H36. subst. inv eq7.
  rewrite rz_full_sub_form_correct with (tenv := tenv); try easy.
  rewrite get_put_cus_cut_n; try easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq5 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl y x0 x1 (Q,b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  destruct H36. subst. inv eq7.
  rewrite rz_full_adder_form_correct with (tenv := tenv); try easy.
  rewrite get_put_cus_cut_n; try easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq5 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl y x0 x1 (Q,b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  subst. inv eq7.
  rewrite rz_full_sub_form_correct with (tenv := tenv); try easy.
  rewrite get_put_cus_cut_n; try easy.
  apply par_find_get_var in eq4 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl x x0 xn (Q,b)); try easy.
  simpl. apply in_or_app. left.
  apply hd_list_in. easy.
  apply par_find_get_var in eq5 as X1. destruct X1.
  apply (all_nor_var vmap smap tenv (get_var_cfac x ++ get_var_cfac y)
            bv' size rl y x0 x1 (Q,b0)); try easy.
  simpl. apply in_or_app. right.
  apply hd_list_in. easy.
  1-2:easy.
  simpl in *.
  inv H1. inv H2.
  left. easy.
  left. easy.
  left. easy.
  left. easy.
  apply type_cfac_sem_error with (t := (Q,b0)) (rh:= rh) in eq5; try easy.
  rewrite eq5 in *. easy.
  easy.
  simpl in *.
  assert (a0 = C). destruct a0. easy. easy. subst.
  apply andb_true_iff in eq3.
  destruct eq3.
  apply andb_true_iff in H16. destruct H16.
  apply andb_true_iff in H16. destruct H16.
  apply andb_true_iff in H16. destruct H16.
  apply andb_true_iff in H16. destruct H16.
  unfold sub_atype in H26.
  destruct a1. simpl in *.
  destruct (par_eval_cfac_check smap bv' size rl y) eqn:eq5.
  destruct (Store.find (elt:=nat -> bool) x0 rl) eqn:eq6. destruct v.
  simpl in *.
  right. left.
  destruct (unary_c_value op b size b1 x1) eqn:eq7.
  simpl in *. inv H1.
  inv H2.
  apply par_find_eval_var_same_1 with (rh := rh) (t := (C,b)) (x2 := Error) in eq4; try easy.
  rewrite sem_cfac_par_eval_same_c with (t := (C,b0)) (rh := rh) in eq5; try easy.
  rewrite eq5 in *. easy.
  unfold qvar_eq_eval in *.
  destruct (eval_var smap size rh x) eqn:eq8. destruct v.
  destruct (eval_var smap size rh y) eqn:eq9. destruct v.
  simpl in *. easy.
  simpl in *.
  apply eval_cfac_sem_error in eq9.
  rewrite sem_cfac_par_eval_same_c with (t := (C,b0)) (rh := rh) in eq5; try easy.
  rewrite eq5 in *. easy. easy.
  destruct (eval_var smap size rh y) eqn:eq9. destruct v. simpl in *.
  apply par_find_eval_var_same_1 with (rh := rh) (t := (C,b)) (x2 := Error) in eq4; try easy.
  simpl in *.
  apply par_find_eval_var_same_1 with (rh := rh) (t := (C,b)) (x2 := Error) in eq4; try easy. easy. easy.
  rewrite H0 in *. inv H33.
  apply par_find_eval_var_same with (rh := rh) (t := (C,b)) (x2 := xn) in eq4 as V1; try easy. subst.
  exists xn. exists (x_val :: xl). exists b2. split. easy. split. easy. split. easy.
  apply Store.find_2 in eq6.
  Check par_find_var_cstore_same.
  apply (par_find_var_cstore_same smap bv' size rl rh x b
          xn b1 x_val xl) in eq6; try easy. subst.
  unfold unary_c_value,apply_unary,is_unary,is_c_unary in *. simpl in *.
  rewrite sem_cfac_par_eval_same_c with (t := (C,b0)) (rh := rh) in eq5; try easy.
  rewrite eq5 in *. inv H37.
  destruct op. inv eq7. easy.
  inv eq7. easy. easy. inv eq7. easy. inv eq7. easy. easy.
  inv eq7.
  rewrite H0 in *. inv H36. unfold get_size. simpl in *.
  1-3:easy.
  inv eq7. easy.
  inv eq7. 1-3:easy.
  simpl in *. inv H1.
  inv H2. left. easy. left. easy. left. easy. left. easy.
  rewrite sem_cfac_par_eval_same_c with (t := (C,b0)) (rh := rh) in eq5; try easy.
  rewrite eq5 in *. easy. easy. easy.
  simpl in *. easy.
  simpl in *.
  inv H1.
  inv H2. left. easy. left. easy. left. easy. left. easy.
  apply par_find_eval_var_same_1 with (rh := rh) (t := t) (x2 := (Value xn)) in eq4; try easy.
  1-4:easy.
Qed.

Definition com_bin (op:qop) (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (f:flag) (r:cstore) (temp temp1 stack:var) (sn:nat) (es:estore) (x y z:cfac)
                 : option (@value (option exp * nat * cstore * estore)) :=
   match op with nmul =>  do bval <- qvar_eq smap bv size r x y @
                           match bval with (Value false) => 
                               do bval1 <- (qvar_eq smap bv size r x z) @
                           match bval1 with (Value false) => 
                               nqmul_c size smap vmap bv f r temp stack sn es x y z
                             | _ => Some Error
                           end
                             | _ => Some Error
                           end
               | fmul =>  do bval <- qvar_eq smap bv size r x y @
                           match bval with (Value false) => 
                               do bval1 <- (qvar_eq smap bv size r x z) @
                           match bval1 with (Value false) => 
                                   fmul_c size smap vmap bv f r temp stack sn es x y z
                             | _ => Some Error
                           end
                             | _ => Some Error
                           end
               | ndiv => do bval <- qvar_eq smap bv size r x y @ 
                          match bval with (Value false) => 
                             do t2v <- par_eval_cfac_check smap bv size r z @
                           match t2v with Value t2v' => div_c size smap vmap bv f r temp temp1 stack sn es x y t2v'
                                     | _ => Some Error
                           end
                             | _ => Some Error
                          end

               | nmod => do bval <- qvar_eq smap bv size r x y @ 
                          match bval with (Value false) => 
                             do t2v <- par_eval_cfac_check smap bv size r z @
                           match t2v with Value t2v' => mod_c size smap vmap bv f r temp temp1 stack sn es x y t2v'
                                     | _ => Some Error
                           end
                             | _ => Some Error
                          end

           | nadd => do t2v <- par_eval_cfac_check smap bv size r y @
                             do t3v <- par_eval_cfac_check smap bv size r z @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx' (nat2fb (((a_nat2fb t2v' size) + (a_nat2fb t3v' size)) mod 2^size)) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end

           | nsub => do t2v <- par_eval_cfac_check smap bv size r y @
                             do t3v <- par_eval_cfac_check smap bv size r z @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx' (nat2fb (((a_nat2fb t2v' size) - (a_nat2fb t3v' size)) mod 2^size)) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end

           | fadd => do t2v <- par_eval_cfac_check smap bv size r y @
                             do t3v <- par_eval_cfac_check smap bv size r z @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx'
                          (fbrev size (nat2fb (((a_nat2fb (fbrev size t2v') size) + (a_nat2fb (fbrev size t3v') size)) mod 2^size))) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end

           | fsub => do t2v <- par_eval_cfac_check smap bv size r y @
                             do t3v <- par_eval_cfac_check smap bv size r z @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx'
                          (fbrev size (nat2fb (((a_nat2fb (fbrev size t2v') size) - (a_nat2fb (fbrev size t3v') size)) mod 2^size))) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end

           | fndiv => do t2v <- par_eval_cfac_check smap bv size r y @
                             do t3v <- par_eval_cfac_check smap bv size r z @
                              do vx <- par_find_var_check smap bv size r x @
                               match t2v with Value t2v' => match t3v with Value t3v' => match vx with Value vx' =>
                               Some (Value ((None,sn,Store.add vx' (fbrev size (nat2fb ((((a_nat2fb t2v' size) * 2^size)
                                      / (a_nat2fb t3v' size)) mod 2^size))) r,es)))
                             | _ => Some Error end | _ => Some Error end | _ => Some Error end

               | _ => None
   end.

(* The main function to translate statements.
   C mode statements are evaluated, while Q mode statements are to generate circuits. *)
Fixpoint trans_qexp (size:nat) (smap : qvar -> nat) (vmap: (qvar*nat) -> var)
                 (bv:benv) (fl:flag) (r:cstore) (temp temp1 stack:var)
                  (sn:nat) (fv:fmap) (es:estore) (bases:estore) (e:qexp) : option (@value (option exp * nat * cstore * estore)) :=
   match e with
          | skip => Some (Value (None,sn,r,es))

          | qfor x n e' => 
     do t2v' <- par_eval_cfac_check smap bv size r n @
       match t2v' with Value t2v =>
         let fix trans_while (r:cstore) (sn:nat) (i:nat) : option (@value (option exp * nat * cstore * estore)) :=
            match i with 0 => Some (Value (None,sn,r,es))
                     | S m => do re <- trans_qexp size smap vmap bv fl r temp temp1 stack sn fv bases bases e' @
                               match re with Value (cir,sn',r',es') =>
                                 do re' <- trans_while r' sn' m @
                                  match re' with Value (cir',sn'',r'',es'') =>
                                     Some (Value (combine_c cir cir',sn'',r'',bases))
                                     | _ => Some Error
                                  end
                                     | _ => Some Error
                               end
            end in trans_while (Store.add (L x,0) (nat2fb 0) r) sn (a_nat2fb t2v size)
            | _ => Some Error

       end

           | qinv x => 
                 do vx <- par_find_var_check smap bv size r x @
                    match vx with Value vx' => 
                        do exps <- Store.find vx' es @
                             do exp <- hd_error exps @ Some (Value (Some (inv_exp exp),sn,r,Store.add vx' (tl exps) es))
                           | _ => Some Error
                    end

           | call x f vs => match lookup_fmap fv f with None => None
                       | Some (u,e',smap',vmap',bv',r') => 
                  do vuv <- par_find_var_check smap' bv' size r' u @
                   match vuv with Value vu =>
                    do t <- BEnv.find (fst vu) bv' @
                      do vxv <- par_find_var_check smap bv size r x @
                       match vxv with Value vx => 
                         do t' <- BEnv.find (fst vx) bv @
                         if (is_q t') && (is_q t) then
                            do exps <- Store.find vx es @
                             Some (Value (Some (e';  (copyto (vmap' vu) (vmap vx) (get_size size (get_ct t))); inv_exp e'),sn,r,
                               Store.add vx ((e';  (copyto (vmap' vu) (vmap vx) (get_size size (get_ct t))); inv_exp e')::exps) es))
                         else if (is_q t') && (is_c t) then
                            do exps <- Store.find vx es @
                             do uv <- Store.find vu r' @
                             Some (Value (Some ( (init_v (get_size size (get_ct t)) (vmap vx) uv)),sn,r,
                               Store.add vx (( (init_v (get_size size (get_ct t)) (vmap vx) uv))::exps) es))
                         else do uv <- Store.find vu r' @ 
                               do xv <- Store.find vx r @  Some (Value (None,sn,Store.add vx xv r,es))
                      | _ => Some Error end
                   | _ => Some Error end
                        end


           | qif ce e1 e2 => do ce_val <- compile_cexp size smap vmap bv fl r temp stack sn ce @
                 match ce_val with Value (cir,sn',Some true) => 
                   trans_qexp size smap vmap bv fl r temp temp1 stack sn' fv bases bases e1
                      | Value (cir,sn',Some false) => 
                   trans_qexp size smap vmap bv fl r temp temp1 stack sn' fv bases bases e2
                | Value (Some cir,sn',_) => 
                 do e1_val <- trans_qexp size smap vmap bv fl r temp temp1 stack sn' fv bases bases e1 @
                   match e1_val with Value (e1_cir,sn1,r1,es1)  =>
                  do e2_val <- trans_qexp size smap vmap bv fl r1 temp temp1 stack sn1 fv bases bases e2 @
                   match e2_val with Value (e2_cir,sn2,r2,es2) => 
                           Some (Value (combine_if stack sn cir e1_cir e2_cir,sn2,r2,es))
                         | _ => Some Error
                    end
                    | _ => Some Error
                  end
                | _ => Some Error
                 end

           | init x v => do bval <- qvar_eq smap bv size r x v @
                                   match bval with Value false => init_c size smap vmap bv r sn es x v 
                                                 | _ => Some Error
                                    end

           | slrot x => lrot_c size smap vmap bv r sn es x

           | unary x op v => com_unary op size smap vmap bv fl r temp stack sn es x v 

           | binapp x op y z => com_bin op size smap vmap bv fl r temp temp1 stack sn es x y z

           | qseq e1 e2 => match trans_qexp size smap vmap bv fl r temp temp1 stack sn fv es bases e1 with None => None
                    | Some (Value ( e1',sn1,store1,es1)) => 
                     match trans_qexp size smap vmap bv fl store1 temp temp1 stack sn1 fv es1 bases e2 with None => None
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


Fixpoint init_estore_n (es : estore)  (x:qvar) (n:nat) : estore :=
   match n with 0 => es
          | S m => Store.add (x,m) ([]) (init_estore_n es x m)
   end.


Fixpoint init_estore (r:estore) (l:list (typ * var)) : estore  :=
   match l with [] => r
             | ((t,x)::xl) => init_estore (init_estore_n r (L x) (get_type_num t)) xl
   end.

(*
Translating a list of functions to fmap, which contains generate circuits for functions,
and other information for compiling function call.

*) 

Fixpoint trans_funs (fv:fenv) (size sn:nat) (temp temp1 stack:var) (fl:flag) (r:cstore) (es:estore)
                  (smap: qvar -> nat) (vmap : (qvar*nat) -> var) 
            (vmaps: list ((qvar *nat)*var)) (vmap_num:nat) (fmap:fmap) (l:list func) :=
    match l with [] => Some (Value (vmaps , sn, fmap))
            | (( f , tvl, ls , e , rx)::xl) =>
                 match FEnv.find f fv with None => None
                           | Some (tvl',ls',e',bv,rx') => 
                    match trans_qexp size 
                   (gen_smap_l ls smap) (gen_vmap_l ls vmap vmap_num)
                     bv fl (init_cstore r (ls)) temp temp1 stack 0 fmap (init_estore es ls) (init_estore es ls) e
                    with None => None
                    | Some Error => Some Error
                    | Some (Value (None,sn1,store1,es)) => 
         trans_funs fv size sn temp temp1 stack fl r es smap vmap vmaps vmap_num ((f,rx, (SKIP ((stack),0)), (gen_smap_l ls smap),
                              (gen_vmap_l ls vmap vmap_num),bv,store1)::fmap) xl
                  | Some (Value (Some e1,sn1,store1,es)) =>
        match gen_vmap_ll ls vmaps vmap_num with (vmaps',vmap_num') =>
         trans_funs fv size (Nat.max sn sn1) temp temp1 stack fl r es smap (gen_vmap_l ls vmap vmap_num)
                 vmaps' vmap_num' ((f,rx, (SKIP ((stack),0)), (gen_smap_l ls smap),
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
Definition temp1 : var := 1.
Definition stack : var := 2.

Fixpoint gen_vmap_gl' (l:list (typ * var))  (vmaps: list ((qvar*nat) * var)) (i:nat) :=
         match l with [] => vmaps
              | ((t,x)::xl) => gen_vmap_gl' xl (gen_vmap_n_l vmaps (G x) i (get_type_num t)) (i+(get_type_num t))
         end.
Definition gen_vmap_gl (l:list (typ * var)) := gen_vmap_gl' l ([]) 3.


Fixpoint init_estore_g (l:list (typ * var)) : estore  :=
   match l with [] => empty_estore
             | ((t,x)::xl) => init_estore_n (init_estore_g xl) (G x) (get_type_num t)
   end.


(*
Generating a program compiled circuit.
We assume program is a dynamic entity, where we require users to give all inputs for the main arguments
so that we can run the main function, and then the function call of main is compiled.
*)

Definition trans_prog' (p:prog) (flag:flag) (fv:fenv) :=
   match p with (size,ls,fl,f,rx') =>
     let (vmap,vmap_num) := gen_vmap_g ls in
      do v <- (trans_funs fv size 0 temp temp1 stack flag empty_cstore (init_estore_g ls) (gen_smap_l ls (fun _ => 0))
            vmap (gen_vmap_gl ls) vmap_num ([]) fl) @
       match v with Error => Some Error
               | (Value (vmaps,sn,fmap)) => 
         match lookup_fmap fmap f with None => None
            | Some (rx,p,smap,vmap',bv,r) => 
               do vx <- par_find_var_check smap bv size r rx @
               match vx with Value vx' => 
                do t <- BEnv.find (fst vx') bv @ 
               if is_q t then 
                    Some (Value (vmaps,size,sn,p; 
                         (copyto (vmap' vx') (vmap ((G rx'),0)) (get_size size (get_ct t)))))
                else do vxv <- Store.find vx' r @
                    Some (Value (([((G rx',0),vmap (G rx',0))]),size,sn,(init_v (get_size size (get_ct t)) (vmap (G rx',0)) vxv)))
                   | _ => Some Error
               end
        end
    end
   end.


(*
Set up translation for generating code in Ocaml.
*)
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


Definition prog_to_sqir (p:prog) (f:flag) : option (nat * nat * exp * vars * (nat -> posi)) :=
   match trans_prog p f with Some (Value (vmaps,size,sn,p)) => 
          match gen_vars_vmap vmaps size sn with (vars,d) => 
             match avs_gen size (length vmaps) with avs =>
                 Some (d,size,p,vars,avs)
             end
          end
        | _ => None 
   end.

Check prog_to_sqir.

Check trans_exp.



