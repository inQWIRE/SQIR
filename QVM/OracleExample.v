Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import PQASM.
Require Import CLArith.
Require Import RZArith.
Require Import QIMP.

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
Definition hash_qr (b:qvar) (a:qvar) := nadd (Nor (Var b)) (Nor (Var a));;;
             qxor (Nor (Var a)) (Nor (Var b));;; nadd (Nor (Var b)) (Nor (Var a))
                   ;;; qxor (Nor (Var a)) (Nor (Var b)).

Definition g :var := 1.
Definition x :var := 7.
Definition a :var := 3.
Definition b :var := 4.
Definition c :var := 6.
Definition d :var := 100.
Definition f :var := 8.
Definition result :var := 9.

Definition hash_oracle (key:nat) (sndk:nat) :func :=
     (f, ((TNor Q Bl,g)::(TNor C Nat,x)::(TNor Q Nat,a)::(TNor Q Nat,b)::(TNor Q Nat,c)::(TNor Q Nat,d)::[]),
      init (Nor (Var (L d))) (Nor (Num (nat2fb 1)));;;
      qfor x (Nor (Num (nat2fb 10)))
           (hash_qr (L a) (L c);;; hash_qr (L b) (L d) ;;; hash_qr (L a) (L d)
                ;;; hash_qr (L b) (L c);;;
      qif (ceq Nat (Nor (Var (L c))) (Nor (Num (nat2fb key))))
                (qif (ceq Nat (Nor (Var (L d))) (Nor (Num (nat2fb sndk))))
                    (init (Nor (Var (L g))) (Nor (Num (nat2fb 1)))) (skip)) (skip)), (Nor (Var (L g)))).

Definition hash_prog (size:nat) (key:nat) (sndk:nat) : prog := 
         (size,[(TNor Q Bl,result)],[hash_oracle key sndk],f,result).


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
   (f1, ((TNor C Nat,n)::(TNor C Nat,m)::(TArray C Nat 5, n1)::(TArray Q FixedP 5, x3)::(TArray Q FixedP 6, x4)
         ::(TNor C FixedP,e)::[]),
               qfor n (Nor (Num (nat2fb 5))) (
                nmod (Nor (Var (L m))) (Nor (Var (L n))) (Nor (Num (nat2fb 2)));;;
                qif (ceq Nat (Nor (Var (L m))) (Nor (Num (nat2fb 0)))) 
                 (ndiv (Nor (Var (L n))) (Nor (Var (L n))) (Nor (Num (nat2fb 2)));;;
                  ncadd (Index (L n1) (Var (L n))) (Index (L n1) (Var (L n))) (Nor (Num (nat2fb 1))))
                 (ndiv (Nor (Var (L n))) (Nor (Var (L n))) (Nor (Num (nat2fb 2)))));;;

               init (Index (L x3) ((Num (nat2fb 0)))) (Nor (Var (G x)));;;
               qfor n (Nor (Num (nat2fb 5))) (
                   qif (ceq Nat (Nor (Var (L n))) (Nor (Num (nat2fb 0))))
                   (skip)
                   (ncsub (Nor (Var (L m))) (Nor (Var (L n))) (Nor (Num (nat2fb 1)));;;
                    fmul (Index (L x3) (Var (L n))) (Index (L x3) (Var (L m))) (Index (L x3) (Var (L m)))
                    ));;;
               qfor n (Nor (Num (nat2fb 5))) (
                   qif (ceq Nat (Index (L n1) (Var (L n))) (Nor (Num (nat2fb 0))))
                   (skip)
                   (ncadd (Nor (Var (L m))) (Nor (Var (L n))) (Nor (Num (nat2fb 1)));;;
                    fmul (Index (L x3) (Var (L m))) (Index (L x4) (Var (L n))) (Index (L x4) (Var (L n)))
                    ));;;
                init (Nor (Var (L e))) (Index (L x4) (Num (nat2fb 5)))

,Nor (Var (L e))).

Definition taylor_sin : func := 
     (f, ((TArray Q FixedP 5,x3)::(TNor Q FixedP,x2)::(TNor Q FixedP,e)::
              (TNor C Nat,g)::(TNor C Nat,n)::(TNor C Nat, xc)::(TNor C Nat,fac)
               ::(TNor C FixedP,rc)::(TNor Q FixedP,re)::[]),
                         init (Nor (Var (L re))) (Nor (Var (G x)));;;
                         fmul (Nor (Var (L x2))) (Nor (Var (G x))) (Nor (Var (L re)));;;
                         fmul (Index (L x3) (Num (nat2fb 0))) (Nor (Var (L x2))) (Nor (Var (G x)));;;
                         fmul (Index (L x3) (Num (nat2fb 1))) (Index (L x3) (Num (nat2fb 0))) (Nor (Var (L x2)));;;
                         fmul (Index (L x3) (Num (nat2fb 2))) (Index (L x3) (Num (nat2fb 1))) (Nor (Var (L x2)));;;
                         fmul (Index (L x3) (Num (nat2fb 3))) (Index (L x3) (Num (nat2fb 2))) (Nor (Var (L x2)));;;
                         fmul (Index (L x3) (Num (nat2fb 4))) (Index (L x3) (Num (nat2fb 3))) (Nor (Var (L x2)));;;
                         ncadd (Nor (Var (L n))) (Nor (Num (nat2fb 1))) (Nor (Var (L n)));;;
                         ncadd (Nor (Var  (L xc))) (Nor (Num (nat2fb 1))) (Nor (Var  (L xc)));;;
         qfor g (Nor (Num (nat2fb 5))) 
             (qif (iseven (Nor (Var (L g)))) 
                      (ncadd (Nor (Var ((L n)))) (Nor (Var ((L n)))) (Nor (Num (nat2fb 2)));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       ncmul (Nor (Var (L xc))) (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L rc))) (Nor (Var (L xc))) (Nor (Var (L fac)));;;
                       fmul (Nor (Var (L e))) (Nor (Var (L rc))) (Index (L x3) (Var (L g)));;;
                       fsub (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv ((Nor (Var (L e)))))
                      (ncadd (Nor (Var ((L n)))) (Nor (Num (nat2fb 2))) (Nor (Var ((L n))));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       ncmul (Nor (Var (L xc))) (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L rc))) (Nor (Var (L xc))) (Nor (Var (L fac)));;;
                       fmul (Nor (Var (L e))) (Nor (Var (L rc))) (Index (L x3) (Var (L g)));;;
                       fadd (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv ((Nor (Var (L e))))))
             ,Nor (Var (L re))).

Definition sin_prog (size:nat) : prog := 
         (size,((TNor Q FixedP, x)::[(TNor Q FixedP,result)]),(taylor_sin::[]),f,result).

Definition smapa := fun i => if i =? x3 then 5 else 1.

Definition vmapa := 
   match (gen_vmap_g ((TNor Q FixedP, x)::[(TNor Q FixedP,result)])) with (vmapg,i) =>
          gen_vmap_l ((TArray Q FixedP 5,x3)::(TNor Q FixedP,x2)::(TNor Q FixedP,e)::
              (TNor C Nat,g)::(TNor C Nat,n)::(TNor C Nat, xc)::(TNor C Nat,fac)
               ::(TNor C FixedP,rc)::(TNor Q FixedP,re)::[]) vmapg i
   end.


Parameter Pi_4 : nat -> bool. (*a binary representation of PI/4 *)

Definition taylor_cos : func := 
     (f, ((TArray Q FixedP 5,x3)::(TNor Q FixedP,x2)::(TNor Q FixedP,e)::
              (TNor C Nat,g)::(TNor C Nat,n)::(TNor C Nat, xc)::(TNor C Nat,fac)
                ::(TNor C FixedP,rc)::(TNor Q FixedP,re)::[]),
                         fsub (Nor (Var (G x))) (Nor (Num Pi_4)) ;;;
                         init (Nor (Var (L re))) (Nor (Var (G x)));;;
                         fmul (Nor (Var (L x2))) (Nor (Var (G x))) (Nor (Var (L re)));;;
                         fmul (Index (L x3) (Num (nat2fb 0))) (Nor (Var (G x))) (Nor (Var (L x2)));;;
                         fmul (Index (L x3) (Num (nat2fb 1))) (Nor (Var (L x2))) (Index (L x3) (Num (nat2fb 0)));;;
                         fmul (Index (L x3) (Num (nat2fb 2))) (Nor (Var (L x2))) (Index (L x3) (Num (nat2fb 1)));;;
                         fmul (Index (L x3) (Num (nat2fb 3))) (Nor (Var (L x2))) (Index (L x3) (Num (nat2fb 2)));;;
                         fmul (Index (L x3) (Num (nat2fb 4))) (Nor (Var (L x2))) (Index (L x3) (Num (nat2fb 3)));;;
                         ncadd (Nor (Var (L n))) (Nor (Var (L n))) (Nor (Num (nat2fb 1))) ;;;
                         ncadd (Nor (Var  (L xc))) (Nor (Var  (L xc))) (Nor (Num (nat2fb 1))) ;;;
         qfor g (Nor (Num (nat2fb 5))) 
             (qif (iseven (Nor (Var (L g)))) 
                      (ncadd (Nor (Var ((L n)))) (Nor (Var ((L n)))) (Nor (Num (nat2fb 2)));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       ncmul (Nor (Var (L xc))) (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L rc))) (Nor (Var (L xc))) (Nor (Var (L fac)));;;
                       fmul (Nor (Var (L e))) (Nor (Var (L rc))) (Index (L x3) (Var (L g)));;;
                       fsub (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv ((Nor (Var (L e)))))
                      (ncadd (Nor (Var ((L n)))) (Nor (Num (nat2fb 2))) (Nor (Var ((L n))));;;
                       nfac (Nor (Var (L fac))) (Nor (Var (L n)));;;
                       ncmul (Nor (Var (L xc))) (Nor (Num (nat2fb 4))) (Nor (Var (L xc)));;;
                       fndiv (Nor (Var (L rc))) (Nor (Var (L xc))) (Nor (Var (L fac)));;;
                       fmul (Nor (Var (L e))) (Nor (Var (L rc))) (Index (L x3) (Var (L g)));;;
                       fadd (Nor (Var (L re))) (Nor (Var (L e)));;;
                       qinv ((Nor (Var (L e))))))
             ,Nor (Var (L re))).

Definition cos_prog (size:nat) : prog := 
         (size,((TNor Q FixedP, x)::[(TNor Q FixedP,result)]),(taylor_cos::[]),f,result).


