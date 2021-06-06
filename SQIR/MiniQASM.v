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
 destruct a. destruct b. easy. inv H.
 destruct b. inv H. easy.
Qed.

Lemma aty_eqb_neq : forall a b, a =a= b = false -> a <> b.
Proof.
 intros. unfold aty_eq in H.
 destruct a. destruct b. inv H. easy.
 destruct b. easy. inv H. 
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

Hint Resolve aty_eq_reflect qty_eq_reflect : bdestruct.

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
                 | Num (n:nat-> bool). (*a value is represented as a bool binary. *)

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

Inductive cexp := clt (f:flag) (x:factor) (y:factor)
                  | ceq (f:flag) (x:factor) (y:factor).

Inductive qexp := skip
                | qadd (f:flag) (v:factor) (x:qvar) (* *)
                | qsub (f:flag) (v:factor) (x:qvar)
                | qmul (f:flag) (v:factor) (x:qvar)
                | qfac (x:var) (v:factor)
                | qdiv (f:flag) (x:var) (v:factor)
                | call (f:fvar) (v: qvar)
                | qif (c:cexp) (e1:qexp) (e2:qexp)
                | qwhile (c:cexp) (e:qexp)
                | qseq (q1:qexp) (q2:qexp).

(*functions will do automatic inverse computation after a function is returned.
  for each ret statement, there is a list of pairs of vars, and the left one is the global variables to return,
   while the left one is the local variables. after a function call is returned,
    it will store all the local variables to their correponding global variables, and then reverse the computation.  *)

Definition func : Type := ( fvar * list var * qexp * qvar).
    (* a function is a fun name, a starting block label, and a list of blocks, and the returned variable. *)

Definition prog : Type := (nat * nat * nat * nat * list var * list func * fvar * var). 
   (* a program is a nat representing the stack size, a number for the number of while to allow in a loop
       and a number for the total number of bits in each binary. a nat number 
    indicating the number of denominator for each fixed-pointer number, and a list of global vars, and a list of functions.
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
Module BEnv := FMapList.Make Nat_as_OT.

Definition benv := BEnv.t atype.

Definition empty_benv := @BEnv.empty atype.

Module FEnv := FMapList.Make Nat_as_OT.

Definition fenv := FEnv.t (list (var) * qexp * benv * qvar). (*the final variable is the returned var. *)

Definition empty_fenv := @FEnv.empty (list (var) * qexp * benv * qvar).

Definition asubtype (t1 t2: atype) : bool :=
   if aty_eq t1 t2 then true else
           (match t1 with C => match t2 with Q => true
                                             | _ => false
                                 end
                         | _ => false
            end).

Inductive subtype : atype -> atype -> Prop :=
   subtype_ref : forall t, subtype t t
  | subtype_cq : subtype C Q.

Inductive type_factor (gs:list var) (benv:benv) : atype -> factor -> Prop :=
     type_fac_lvar : forall t x, BEnv.MapsTo x t benv -> type_factor gs benv t (Var (L x))
   | type_fac_gvar : forall x, In x gs -> type_factor gs benv Q (Var (G x))
   | type_fac_nat : forall n, type_factor gs benv C (Num n).

(*
Definition mat_cq (a:atype) (n:nat) : Prop :=
   match a with Q m => (n = m)
              | C m => (n = m)
   end.
*)

Definition meet_type (t1 t2 : atype) := if t1 =a= Q then Q else if t2 =a= Q then Q else C.


Inductive type_cexp (gs:list var) (benv:benv) : atype -> cexp -> Prop :=
   type_clt : forall c1 c2 f x y, type_factor gs benv c1 x -> 
                     type_factor gs benv c2 y -> type_cexp gs benv (meet_type c1 c2) (clt f x y)
  |  type_ceq : forall c1 c2 f x y, type_factor gs benv c1 x ->
                     type_factor gs benv c2 y -> type_cexp gs benv (meet_type c1 c2) (ceq f x y).

Definition var_raw (t:qvar) := match t with G x => x | L x => x end.

Inductive type_qexp (gs:list var) (fv:fenv): benv -> qexp -> benv -> Prop :=
 | htype_skip : forall benv, type_qexp gs fv benv skip benv
 | htype_qadd : forall benv t1 t2 f x y, type_factor gs benv t1 x
             -> type_factor gs benv t2 (Var y) ->
              type_qexp gs fv benv (qadd f x y) (BEnv.add (var_raw y) (meet_type t1 t2) benv)
 | htype_qsub : forall benv t1 t2 f x y, type_factor gs benv t1 x
             -> type_factor gs benv t2 (Var y) ->
              type_qexp gs fv benv (qsub f x y) (BEnv.add (var_raw y) (meet_type t1 t2) benv)
 | htype_qmul : forall benv t1 t2 f x y, type_factor gs benv t1 x
             -> type_factor gs benv t2 (Var y) ->
              type_qexp gs fv benv (qmul f x y) (BEnv.add (var_raw y) (meet_type t1 t2) benv)
 | htype_qdiv : forall benv f x y, BEnv.MapsTo x C benv -> type_factor gs benv C y ->
              type_qexp gs fv benv (qdiv f x y)  benv
 | htype_qfac : forall benv x y, BEnv.MapsTo x C benv -> type_factor gs benv C y ->
              type_qexp gs fv benv (qfac x y)  benv

 | htype_call_ll : forall benv fbenv f tvl e x t rx t', FEnv.MapsTo f (tvl,e,fbenv, L rx) fv ->
                    BEnv.MapsTo x t benv -> BEnv.MapsTo rx t' fbenv
                          -> type_qexp gs fv benv (call f (L x)) (BEnv.add x (meet_type t t') benv)
 | htype_call_lg : forall benv fbenv f tvl e x rx, FEnv.MapsTo f (tvl,e,fbenv, G rx) fv
                          -> type_qexp gs fv benv (call f (L x)) (BEnv.add x Q benv)
 | htype_call_g : forall benv fbenv f tvl e x rx, FEnv.MapsTo f (tvl,e,fbenv,rx) fv -> type_qexp gs fv benv (call f (G x)) benv
 | htype_if : forall benv benv' benv'' b ce e1 e2, type_cexp gs benv b ce -> type_qexp gs fv benv e1 benv' ->
                     type_qexp gs fv benv' e2 benv'' ->  type_qexp gs fv benv (qif ce e1 e2) benv''
 | htype_while : forall benv benv' t ce e, type_cexp gs benv t ce ->
                            type_qexp gs fv benv e benv' -> type_qexp gs fv benv (qwhile ce e) benv'
 | htype_qseq : forall benv benv' benv'' e1 e2, type_qexp gs fv benv e1 benv'
               -> type_qexp gs fv benv' e2 benv'' -> type_qexp gs fv benv (qseq e1 e2) benv''.

Fixpoint gen_env (l:list var) := 
   match l with [] => empty_benv
             | (x::xl) => BEnv.add x C (gen_env xl)
   end.

Inductive type_funs (gs:list var) : fenv -> list func -> fenv -> Prop :=
   type_fun_empty : forall fv, type_funs gs fv [] fv
 | type_fun_many_l : forall fv fv' benv f l e fs rx, type_qexp gs fv (gen_env l) e benv -> BEnv.In rx benv
                -> type_funs gs (FEnv.add f (l,e,benv,L rx) fv) fs fv' -> type_funs gs fv ((f,l,e,L rx)::fs) fv'
 | type_fun_many_g : forall fv fv' benv f l e fs rx, type_qexp gs fv (gen_env l) e benv -> In rx gs
                -> type_funs gs (FEnv.add f (l,e,benv,G rx) fv) fs fv' -> type_funs gs fv ((f,l,e,G rx)::fs) fv'.

(* ( fvar * list var * qexp ). *)

Inductive type_prog : prog -> Prop :=
  type_prog_t : forall si sloop n m l fl fenv main rx, m <= n -> FEnv.In main fenv ->
              type_funs l empty_fenv fl fenv -> type_prog (si,sloop,n,m,l,fl,main, rx).



(*The semantics of QLLVM. *)

Module Reg := FMapList.Make QvarType.

Definition reg := Reg.t ((nat -> bool)).

Definition empty_reg := @Reg.empty ((nat -> bool)).

Inductive sem_factor (size:nat): reg -> factor -> ((nat -> bool)) -> Prop :=
   | sem_factor_var : forall r x n, Reg.MapsTo x n r -> sem_factor size r (Var x) (cut_n n size)
   | sem_factor_num : forall r n, sem_factor size r (Num n) (cut_n n size).

Inductive sem_cexp (s_lit size:nat) : nat -> reg -> cexp -> nat -> bool -> Prop :=
   sem__clt : forall sn reg f x y n1 b1 n2 b2, sem_factor size reg x n1 -> 
                      sem_factor size reg y n2 -> n1 = nat2fb b1 -> n2 = nat2fb b2 -> 
                              S sn < s_lit -> sem_cexp s_lit size sn reg (clt f x y) (S sn) (b1 <? b2)
  | sem_ceq : forall sn reg f x y n1 b1 n2 b2, sem_factor size reg x n1 -> 
                      sem_factor size reg y n2 -> n1 = nat2fb b1 -> n2 = nat2fb b2 -> 
                             (S sn) < s_lit -> sem_cexp s_lit size sn reg (clt f x y) (S sn) (b1 =? b2).

Fixpoint init_reg (r:reg) (l:list var) : reg  :=
    match l with [] => r
              | (x::xl) => init_reg (Reg.add (L x) (nat2fb 0) r) xl
   end.

Inductive sem_qexp (fv:fenv) (s_lit size:nat): nat -> reg -> qexp -> nat -> reg -> qexp -> Prop :=
 | sem_add : forall sn reg f x vx y vy, sem_factor size reg x vx -> sem_factor size reg (Var y) vy ->
      sem_qexp fv s_lit size sn reg (qadd f x y) sn (Reg.add y (sumfb false vx vy) reg) skip
 | sem_sub : forall sn reg f x vx y vy, sem_factor size reg x vx -> sem_factor size reg (Var y) vy ->
      sem_qexp fv s_lit size sn reg (qsub f x y) sn (Reg.add y (sumfb true vx (negatem size vy)) reg) skip
 | sem_mul : forall sn reg f x vx n1 y vy n2, sem_factor size reg x vx -> sem_factor size reg (Var y) vy ->
             vx = nat2fb n1 -> vy = nat2fb n2 ->
      sem_qexp fv s_lit size sn reg (qmul f x y) sn (Reg.add y (nat2fb ((n1 * n2) mod size)) reg) skip
 | sem_div : forall sn reg f x vx n1 y vy n2, sem_factor size reg (Var (L x)) vx -> sem_factor size reg y vy ->
             vx = nat2fb n1 -> vy = nat2fb n2 ->
      sem_qexp fv s_lit size sn reg (qdiv f x y) sn (Reg.add (L x) (nat2fb ((n1 / n2) mod size)) reg) skip
 | sem_fac : forall sn reg x y vy n, sem_factor size reg y vy -> vy = nat2fb n ->
      sem_qexp fv s_lit size sn reg (qfac x y) sn (Reg.add (L x) (nat2fb ((fact n) mod size)) reg) skip
 | sem_call : forall sn reg reg' f x l e benv rx v, FEnv.MapsTo f (l,e,benv,rx) fv -> 
           sem_qexp fv s_lit size sn (init_reg reg l) e sn reg' skip ->
           Reg.MapsTo rx v reg' -> 
           sem_qexp fv s_lit size sn reg (call f x) sn (Reg.add x v reg) skip
 | sem_if_t : forall sn sn' reg ce e1 e2, sem_cexp s_lit size sn reg ce sn' true ->
                 sem_qexp fv s_lit size sn reg (qif ce e1 e2) sn' reg e1
 | sem_if_f : forall sn sn' reg ce e1 e2, sem_cexp s_lit size sn reg ce sn' false ->
                 sem_qexp fv s_lit size sn reg (qif ce e1 e2) sn' reg e2
 | sem_while : forall sn reg ce e,
                 sem_qexp fv s_lit size sn reg (qwhile ce e) sn reg ((qseq (qif ce e skip) (qwhile ce e)))
 | sem_qseq_con : forall sn reg e1 e2 sn' reg' e1',
                sem_qexp fv s_lit size sn reg e1 sn' reg' e1' ->
                  sem_qexp fv s_lit size sn reg (qseq e1 e2) sn' reg' (qseq e1' e2)
 | sem_qseq_skip : forall sn reg e, 
                  sem_qexp fv s_lit size sn reg (qseq skip e) sn reg e.


Fixpoint init_reg_g (r:reg) (l:list var) : reg  :=
    match l with [] => r
              | (x::xl) => init_reg_g (Reg.add (G x) (nat2fb 0) r) xl
   end.

Inductive sem_prog (fv:fenv) : prog -> (nat -> bool) -> Prop :=
    sem_main : forall s_lit sloop size m gl fl main rx' l e benv rx sn reg v, 
         FEnv.MapsTo main (l,e,benv,rx) fv ->
         sem_qexp fv s_lit size 0 (init_reg (init_reg_g empty_reg gl) l) e sn reg skip ->
         Reg.MapsTo rx v reg ->
         sem_prog fv (s_lit,sloop,size,m,gl,fl,main,rx') v.

Definition var_map := Reg.t var.

Definition empty_var_map := @Reg.empty var.

Definition ac_size (size:nat) := S (S size).

Fixpoint a_nat2fb (f:nat->bool) (n:nat) :=
             match n with 0 => 0
                       | S m => (Nat.b2n (f m)) + a_nat2fb f m
             end.                            


Definition find_factor_type (benv:benv) (fc:factor) : option atype :=
    match fc with (Var (L x)) => BEnv.find x benv
                | (Var (G x)) => Some Q
                | Num n => Some C
    end.

Lemma xor_not : forall a b, xorb (a<?b) (b<?a) = false -> a = b.
Proof.
  intros.
  bdestruct (a <? b).
  bdestruct (b <? a). lia. simpl in H. inv H.
  bdestruct (b <? a). simpl in H. inv H.
  lia.
Qed.

Notation "'do' X '<-' A '@' B" := (bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).


Definition compare_c (size:nat) (reg:reg) (x y : factor) (stack:var) (sn:nat) (op : nat -> nat -> bool) := 
    match x with Num n =>
       match y with Num m => 
        do sv <- (Reg.find (L stack) reg) @
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

