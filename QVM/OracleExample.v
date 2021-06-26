Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import VSQIR.
Require Import CLArith.
Require Import RZArith.
Require Import MiniQASM.

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monads.

(* The definition of QSSA. *)
Local Open Scope exp_scope.
Local Open Scope nat_scope.



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


