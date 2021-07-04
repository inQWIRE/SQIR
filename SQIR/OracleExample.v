Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
From QuickChick Require Import QuickChick.
Require Import VSQIR.
Require Import CLArith.
Require Import RZArith.
Require Import MiniQASM.

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monads.

Require Import Nat Bvector.
From Bits Require Import bits.
Require Import Testing.

(* The definition of QSSA. *)
Local Open Scope exp_scope.
Local Open Scope nat_scope.

Fixpoint rotate_left_n (x : qvar) n :=
  match n with
  | 0 => skip
  | S n' => slrot Nat (Nor (Var x));;; rotate_left_n x n'
  end.

(*define example hash_function as the oracle for grover's search.
  https://qibo.readthedocs.io/en/stable/tutorials/hash-grover/README.html *)
Definition qr_qexp (a b c d : qvar) :=
  nadd QFTA (Nor (Var b)) (Nor (Var a));;;
  qxor Nat (Nor (Var a)) (Nor (Var d));;;
  rotate_left_n d (32 - 16);;;
  nadd QFTA (Nor (Var d)) (Nor (Var c));;;
  qxor Nat (Nor (Var c)) (Nor (Var b));;;
  rotate_left_n b (32 - 12);;;
  nadd QFTA (Nor (Var b)) (Nor (Var a));;;
  qxor Nat (Nor (Var a)) (Nor (Var d));;;
  rotate_left_n d (32 - 8);;;
  nadd QFTA (Nor (Var d)) (Nor (Var c));;;
  qxor Nat (Nor (Var c)) (Nor (Var b));;;
  rotate_left_n b (32 - 7).

Open Scope bits_scope.

Definition rolBn (p : DWORD) k := iter k rolB p.

Infix "+" := addB : bits_scope.
Infix "^" := xorB : bits_scope.
Infix "<<<" := rolBn (at level 30, no associativity) : bits_scope.

Definition qr_spec (a b c d : DWORD) : DWORD * DWORD * DWORD * DWORD :=
  let a := a + b in
  let d := d ^ a in
  let d := d <<< 16 in
  let c := c + d in
  let b := b ^ c in
  let b := b <<< 12 in
  let a := a + b in
  let d := d ^ a in
  let d := d <<< 8 in
  let c := c + d in
  let b := b ^ c in
  let b := b <<< 7 in
  (a, b, c, d).

Definition bits2bvector {n : nat} (p : BITS n) : Bvector n :=
  n2bvector n (Z.to_N (toPosZ p)).

Definition bvector2bits {n : nat} (v : Bvector n) : BITS n :=
  fromZ (Z.of_N (bvector2n v)).

Module QRTesting.

Definition a : var := 0.
Definition b : var := 1.
Definition c : var := 2.
Definition d : var := 3.
Definition tmp : var := 4.
Definition stack : var := 5.

Definition qr_vmap : qvar * nat -> var :=
  fun '(x, _) =>
  match x with
  | L x' => x'
  | G x' => x'
  end.

Definition qr_benv :=
  gen_genv (cons (Nat, a) (cons (Nat, b) (cons (Nat, c) (cons (Nat, d) nil)))).

Definition compile_qr := 
  trans_qexp
    0 32 (fun _ => 1) qr_vmap qr_benv (Reg.empty _) tmp stack 0 nil
    (qr_qexp (G a) (G b) (G c) (G d)).

Definition qr_pexp : pexp.
Proof.
  destruct (compile_qr) eqn:E1.
  - destruct p, p, o.
    + apply p.
    + discriminate.
  - discriminate.
Defined.

Definition qr_env : f_env := fun _ => 32.

Conjecture qr_oracle_spec :
  forall va vb vc vd,
  let
    '(a', b', c', d') :=
    qr_spec (bvector2bits va) (bvector2bits vb)
            (bvector2bits vc) (bvector2bits vd)
  in
  let va' := bits2bvector a' in
  let vb' := bits2bvector b' in
  let vc' := bits2bvector c' in
  let vd' := bits2bvector d' in
  st_equiv (get_vars qr_pexp) qr_env (get_prec qr_env qr_pexp)
    (prog_sem qr_env qr_pexp (a |=> va, b |=> vb, c |=> vc, d |=> vd))
        (a |=> va', b |=> vb', c |=> vc', d |=> vd').

End QRTesting.

(*
QuickChickWith (updMaxSuccess stdArgs 1) QRTesting.qr_oracle_spec.
 *)

Definition dr_spec x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 :=
  let '(x0, x4, x8, x12) := qr_spec x0 x4 x8 x12 in
  let '(x1, x5, x9, x13) := qr_spec x1 x5 x9 x13 in
  let '(x2, x6, x10, x14) := qr_spec x2 x6 x10 x14 in
  let '(x3, x7, x11, x15) := qr_spec x3 x7 x11 x15 in
  let '(x0, x5, x10, x15) := qr_spec x0 x5 x10 x15 in
  let '(x1, x6, x11, x12) := qr_spec x1 x6 x11 x12 in
  let '(x2, x7, x8, x13) := qr_spec x2 x7 x8 x13 in
  let '(x3, x4, x9, x14) := qr_spec x3 x4 x9 x14 in
  (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15).

Definition dr_qexp x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 :=
  qr_qexp x0 x4 x8 x12;;;
  qr_qexp x1 x5 x9 x13;;;
  qr_qexp x2 x6 x10 x14;;;
  qr_qexp x3 x7 x11 x15;;;
  qr_qexp x0 x5 x10 x15;;;
  qr_qexp x1 x6 x11 x12;;;
  qr_qexp x2 x7 x8 x13;;;
  qr_qexp x3 x4 x9 x14.

Module DRTesting.

  Definition tmp : var := 16.
  Definition stack : var := 17.

  Definition dr_vmap : qvar * nat -> var :=
    fun '(x, _) =>
    match x with
    | L x' => x'
    | G x' => x'
    end.

  Definition dr_benv := gen_genv (map (fun x => (Nat, x)) (seq 0 16)).

  Definition compile_dr :=
    trans_qexp 0 32 (fun _ => 1) dr_vmap dr_benv (Reg.empty _) tmp stack 0 nil
    (dr_qexp (G 0) (G 1) (G 2) (G 3) (G 4) (G 5) (G 6) (G 7)
             (G 8) (G 9) (G 10) (G 11) (G 12) (G 13) (G 14) (G 15)).

  Definition dr_pexp : pexp.
  Proof.
    destruct (compile_dr) eqn:E1.
    - destruct p, p, o.
      + apply p.
      + discriminate.
    - discriminate.
  Defined.

  Definition dr_env : f_env := fun _ => 32.

  Conjecture dr_oracle_spec :
    forall v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
    let
      '(x0', x1', x2', x3', x4', x5', x6', x7',
        x8', x9', x10', x11', x12', x13', x14', x15') :=
      dr_spec
        (bvector2bits v0) (bvector2bits v1) (bvector2bits v2) (bvector2bits v3)
        (bvector2bits v4) (bvector2bits v5) (bvector2bits v6) (bvector2bits v7)
        (bvector2bits v8) (bvector2bits v9)
        (bvector2bits v10) (bvector2bits v11)
        (bvector2bits v12) (bvector2bits v13)
        (bvector2bits v14) (bvector2bits v15)
  in
  let v0' := bits2bvector x0' in
  let v1' := bits2bvector x1' in
  let v2' := bits2bvector x2' in
  let v3' := bits2bvector x3' in
  let v4' := bits2bvector x4' in
  let v5' := bits2bvector x5' in
  let v6' := bits2bvector x6' in
  let v7' := bits2bvector x7' in
  let v8' := bits2bvector x8' in
  let v9' := bits2bvector x9' in
  let v10' := bits2bvector x10' in
  let v11' := bits2bvector x11' in
  let v12' := bits2bvector x12' in
  let v13' := bits2bvector x13' in
  let v14' := bits2bvector x14' in
  let v15' := bits2bvector x15' in
  st_equiv (get_vars dr_pexp) dr_env (get_prec dr_env dr_pexp)
  (prog_sem dr_env dr_pexp
     (0 |=> v0, 1 |=> v1, 2 |=> v2, 3 |=> v3,
      4 |=> v4, 5 |=> v5, 6 |=> v6, 7 |=> v7,
      8 |=> v8, 9 |=> v9, 10 |=> v10, 11 |=> v11,
      12 |=> v12, 13 |=> v13, 14 |=> v14, 15 |=> v15))
  (0 |=> v0', 1 |=> v1', 2 |=> v2', 3 |=> v3',
   4 |=> v4', 5 |=> v5', 6 |=> v6', 7 |=> v7',
   8 |=> v8', 9 |=> v9', 10 |=> v10', 11 |=> v11',
   12 |=> v12', 13 |=> v13', 14 |=> v14', 15 |=> v15').

End DRTesting.

QuickChickWith (updMaxSuccess stdArgs 1) DRTesting.dr_oracle_spec.

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
         (s_size, size,[(Bl,result)],[hash_oracle key sndk],f,result).

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
                       ncmul (Nor (Var (L xc))) (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L xc))) (Nor (Var (L fac))) (Nor (Var (L rc)));;;
                       fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e)));;;
                       fsub QFTA (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv (fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e))));;;
                       nadd QFTA (Nor (Num (nat2fb 1))) (Nor (Var ((L g)))))
                      (nadd QFTA (Nor (Num (nat2fb 2))) (Nor (Var ((L n))));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       ncmul (Nor (Var (L xc))) (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L xc))) (Nor (Var (L fac))) (Nor (Var (L rc)));;;
                       fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e)));;;
                       fadd QFTA (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv (fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e))));;;
                       nadd QFTA (Nor (Num (nat2fb 1))) (Nor (Var ((L g))))))
             ,L re).

Definition sin_prog (s_size:nat) (size:nat) : prog := 
         (s_size, size,[(Flt,result)],(x_n size:: taylor_sin::[]),f,result).

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
                       ncmul (Nor (Var (L xc))) (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L xc))) (Nor (Var (L fac))) (Nor (Var (L rc)));;;
                       fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e)));;;
                       fsub QFTA (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv (fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e))));;;
                       nadd QFTA (Nor (Num (nat2fb 1))) (Nor (Var ((L g)))))
                      (nadd QFTA (Nor (Num (nat2fb 2))) (Nor (Var ((L n))));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       ncmul (Nor (Var (L xc))) (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L xc))) (Nor (Var (L fac))) (Nor (Var (L rc)));;;
                       fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e)));;;
                       fadd QFTA (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv (fmul QFTA (Nor (Var (L rc))) (Ptr x (Var (L g))) (Nor (Var (L e))));;;
                       nadd QFTA (Nor (Num (nat2fb 1))) (Nor (Var ((L g))))))
             ,L re).

Definition cos_prog (s_size:nat) (size:nat) : prog := 
         (s_size, size,[(Flt,result)],(x_n size:: taylor_cos::[]),f,result).


