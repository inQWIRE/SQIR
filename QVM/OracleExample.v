Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
From QuickChick Require Import QuickChick.
Require Import MathSpec BasicUtility PQASM.
Require Import CLArith.
Require Import RZArith.
Require Import QIMP.

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monads.

(*
Require Import Nat Bvector.
From Bits Require Import bits.
Require Import Testing.
*)

Local Open Scope exp_scope.
Local Open Scope nat_scope.

Fixpoint rotate_left_n (x : qvar) n :=
  match n with
  | 0 => skip
  | S n' => slrot (Nor (Var x));; rotate_left_n x n'
  end.

Definition chacha_estore :=
  init_estore_g (map (fun x => (TNor Q Nat, x)) (seq 0 16)).

(*define example hash_function as the oracle for grover's search.
  https://qibo.readthedocs.io/en/stable/tutorials/hash-grover/README.html *)
Definition qr_qexp (a b c d : qvar) :=
  unary (Nor (Var a)) nadd (Nor (Var b));;
  unary (Nor (Var d)) qxor (Nor (Var a)) ;;
  rotate_left_n d (32 - 16);;
  unary (Nor (Var c)) nadd (Nor (Var d));;
  unary (Nor (Var b)) qxor (Nor (Var c));;
  rotate_left_n b (32 - 12);;
  unary (Nor (Var a)) nadd (Nor (Var b));;
  unary (Nor (Var d)) qxor (Nor (Var a));;
  rotate_left_n d (32 - 8);;
  unary (Nor (Var c)) nadd (Nor (Var d));;
  unary (Nor (Var b)) qxor (Nor (Var c));;
  rotate_left_n b (32 - 7).

Definition sha256_k : var := 1.

Definition sha256_init (sha256_k m_h:qvar) :=
  init (Index sha256_k (Num Nat (nat2fb 0))) (Nor (Num Nat (nat2fb 1116352408)));;
    init (Index sha256_k (Num Nat (nat2fb 1))) (Nor (Num Nat (nat2fb 1899447441)));;
  init (Index sha256_k (Num Nat (nat2fb 2))) (Nor (Num Nat (nat2fb 3049323471)));;
  init (Index sha256_k (Num Nat (nat2fb 3))) (Nor (Num Nat (nat2fb 3921009573)));;
  init (Index sha256_k (Num Nat (nat2fb 4))) (Nor (Num Nat (nat2fb 961987163)));;
  init (Index sha256_k (Num Nat (nat2fb 5))) (Nor (Num Nat (nat2fb 1508970993)));;
  init (Index sha256_k (Num Nat (nat2fb 6))) (Nor (Num Nat (nat2fb 2453635748)));;
  init (Index sha256_k (Num Nat (nat2fb 7))) (Nor (Num Nat (nat2fb 2870763221)));;
  init (Index sha256_k (Num Nat (nat2fb 8))) (Nor (Num Nat (nat2fb 3624381080)));;
  init (Index sha256_k (Num Nat (nat2fb 9))) (Nor (Num Nat (nat2fb 310598401)));;
  init (Index sha256_k (Num Nat (nat2fb 10))) (Nor (Num Nat (nat2fb 607225278)));;
  init (Index sha256_k (Num Nat (nat2fb 11))) (Nor (Num Nat (nat2fb 1426881987)));;
  init (Index sha256_k (Num Nat (nat2fb 12))) (Nor (Num Nat (nat2fb 1925078388)));;
  init (Index sha256_k (Num Nat (nat2fb 13))) (Nor (Num Nat (nat2fb 2162078206)));;
  init (Index sha256_k (Num Nat (nat2fb 14))) (Nor (Num Nat (nat2fb 2614888103)));;
  init (Index sha256_k (Num Nat (nat2fb 15))) (Nor (Num Nat (nat2fb 3248222580)));;
  init (Index sha256_k (Num Nat (nat2fb 16))) (Nor (Num Nat (nat2fb 3835390401)));;
  init (Index sha256_k (Num Nat (nat2fb 17))) (Nor (Num Nat (nat2fb 4022224774)));;
  init (Index sha256_k (Num Nat (nat2fb 18))) (Nor (Num Nat (nat2fb 264347078)));;
  init (Index sha256_k (Num Nat (nat2fb 19))) (Nor (Num Nat (nat2fb 604807628)));;
  init (Index sha256_k (Num Nat (nat2fb 20))) (Nor (Num Nat (nat2fb 770255983)));;
  init (Index sha256_k (Num Nat (nat2fb 21))) (Nor (Num Nat (nat2fb 1249150122)));;
  init (Index sha256_k (Num Nat (nat2fb 22))) (Nor (Num Nat (nat2fb 1555081692)));;
  init (Index sha256_k (Num Nat (nat2fb 23))) (Nor (Num Nat (nat2fb 1996064986)));;
  init (Index sha256_k (Num Nat (nat2fb 24))) (Nor (Num Nat (nat2fb 2554220882)));;
  init (Index sha256_k (Num Nat (nat2fb 25))) (Nor (Num Nat (nat2fb 2821834349)));;
  init (Index sha256_k (Num Nat (nat2fb 26))) (Nor (Num Nat (nat2fb 2952996808)));;
  init (Index sha256_k (Num Nat (nat2fb 27))) (Nor (Num Nat (nat2fb 3210313671)));;
  init (Index sha256_k (Num Nat (nat2fb 28))) (Nor (Num Nat (nat2fb 3336571891)));;
  init (Index sha256_k (Num Nat (nat2fb 29))) (Nor (Num Nat (nat2fb 3584528711)));;
  init (Index sha256_k (Num Nat (nat2fb 30))) (Nor (Num Nat (nat2fb 113926993)));;
  init (Index sha256_k (Num Nat (nat2fb 31))) (Nor (Num Nat (nat2fb 338241895)));;
  init (Index sha256_k (Num Nat (nat2fb 32))) (Nor (Num Nat (nat2fb 666307205)));;
  init (Index sha256_k (Num Nat (nat2fb 33))) (Nor (Num Nat (nat2fb 773529912)));;
  init (Index sha256_k (Num Nat (nat2fb 34))) (Nor (Num Nat (nat2fb 1294757372)));;
  init (Index sha256_k (Num Nat (nat2fb 35))) (Nor (Num Nat (nat2fb 1396182291)));;
  init (Index sha256_k (Num Nat (nat2fb 36))) (Nor (Num Nat (nat2fb 1695183700)));;
  init (Index sha256_k (Num Nat (nat2fb 37))) (Nor (Num Nat (nat2fb 1986661051)));;
  init (Index sha256_k (Num Nat (nat2fb 38))) (Nor (Num Nat (nat2fb 2177026350)));;
  init (Index sha256_k (Num Nat (nat2fb 39))) (Nor (Num Nat (nat2fb 2456956037)));;
  init (Index sha256_k (Num Nat (nat2fb 40))) (Nor (Num Nat (nat2fb 2730485921)));;
  init (Index sha256_k (Num Nat (nat2fb 41))) (Nor (Num Nat (nat2fb 2820302411)));;
  init (Index sha256_k (Num Nat (nat2fb 42))) (Nor (Num Nat (nat2fb 3259730800)));;
  init (Index sha256_k (Num Nat (nat2fb 43))) (Nor (Num Nat (nat2fb 3345764771)));;
  init (Index sha256_k (Num Nat (nat2fb 44))) (Nor (Num Nat (nat2fb 3516065817)));;
  init (Index sha256_k (Num Nat (nat2fb 45))) (Nor (Num Nat (nat2fb 3600352804)));;
  init (Index sha256_k (Num Nat (nat2fb 46))) (Nor (Num Nat (nat2fb 4094571909)));;
  init (Index sha256_k (Num Nat (nat2fb 47))) (Nor (Num Nat (nat2fb 275423344)));;
  init (Index sha256_k (Num Nat (nat2fb 48))) (Nor (Num Nat (nat2fb 430227734)));;
  init (Index sha256_k (Num Nat (nat2fb 49))) (Nor (Num Nat (nat2fb 506948616)));;
  init (Index sha256_k (Num Nat (nat2fb 50))) (Nor (Num Nat (nat2fb 659060556)));;
  init (Index sha256_k (Num Nat (nat2fb 51))) (Nor (Num Nat (nat2fb 883997877)));;
  init (Index sha256_k (Num Nat (nat2fb 52))) (Nor (Num Nat (nat2fb 958139571)));;
  init (Index sha256_k (Num Nat (nat2fb 53))) (Nor (Num Nat (nat2fb 1322822218)));;
  init (Index sha256_k (Num Nat (nat2fb 54))) (Nor (Num Nat (nat2fb 1537002063)));;
  init (Index sha256_k (Num Nat (nat2fb 55))) (Nor (Num Nat (nat2fb 1747873779)));;
  init (Index sha256_k (Num Nat (nat2fb 56))) (Nor (Num Nat (nat2fb 1955562222)));;
  init (Index sha256_k (Num Nat (nat2fb 57))) (Nor (Num Nat (nat2fb 2024104815)));;
  init (Index sha256_k (Num Nat (nat2fb 58))) (Nor (Num Nat (nat2fb 2227730452)));;
  init (Index sha256_k (Num Nat (nat2fb 59))) (Nor (Num Nat (nat2fb 2361852424)));;
  init (Index sha256_k (Num Nat (nat2fb 60))) (Nor (Num Nat (nat2fb 2428436474)));;
  init (Index sha256_k (Num Nat (nat2fb 61))) (Nor (Num Nat (nat2fb 2756734187)));;
  init (Index sha256_k (Num Nat (nat2fb 62))) (Nor (Num Nat (nat2fb 3204031479)));;
  init (Index sha256_k (Num Nat (nat2fb 63))) (Nor (Num Nat (nat2fb 3329325298)));;
  init (Index m_h (Num Nat (nat2fb 0))) (Nor (Num Nat (nat2fb 3238371032)));;
  init (Index m_h (Num Nat (nat2fb 1))) (Nor (Num Nat (nat2fb 914150663)));;
  init (Index m_h (Num Nat (nat2fb 2))) (Nor (Num Nat (nat2fb 812702999)));;
  init (Index m_h (Num Nat (nat2fb 3))) (Nor (Num Nat (nat2fb 4144912697)));;
  init (Index m_h (Num Nat (nat2fb 4))) (Nor (Num Nat (nat2fb 4290775857)));;
  init (Index m_h (Num Nat (nat2fb 5))) (Nor (Num Nat (nat2fb 1750603025)));;
  init (Index m_h (Num Nat (nat2fb 6))) (Nor (Num Nat (nat2fb 1694076839)));;
  init (Index m_h (Num Nat (nat2fb 7))) (Nor (Num Nat (nat2fb 3204075428)))
.



Open Scope list_scope.


Definition g :var := 1.
Definition x :var := 7.
Definition a :var := 3.
Definition b :var := 4.
Definition c :var := 6.
Definition d :var := 100.
Definition f :var := 8.
Definition result :var := 9.

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
   (f1, ([]), ((TNor C Nat,n)::(TNor C Nat,m)::(TArray C Nat 5, n1)::(TArray Q FixedP 5, x3)::(TArray Q FixedP 6, x4)
         ::(TNor C FixedP,e)::[]),
               qfor n (Nor (Num Nat (nat2fb 5))) (
                binapp (Nor (Var (L m))) nmod (Nor (Var (L n))) (Nor (Num Nat (nat2fb 2)));;
                qif (ceq (Nor (Var (L m))) (Nor (Num Nat (nat2fb 0)))) 
                 (binapp (Nor (Var (L n))) ndiv (Nor (Var (L n))) (Nor (Num Nat (nat2fb 2)));;
                  binapp (Index (L n1) (Var (L n))) nadd (Index (L n1) (Var (L n))) (Nor (Num Nat (nat2fb 1))))
                 (binapp (Nor (Var (L n))) ndiv (Nor (Var (L n))) (Nor (Num Nat (nat2fb 2)))));;

               init (Index (L x3) ((Num Nat (nat2fb 0)))) (Nor (Var (G x)));;
               qfor n (Nor (Num Nat (nat2fb 5))) (
                   qif (ceq (Nor (Var (L n))) (Nor (Num Nat (nat2fb 0))))
                   (skip)
                   (binapp (Nor (Var (L m))) nsub (Nor (Var (L n))) (Nor (Num Nat (nat2fb 1)));;
                    binapp (Index (L x3) (Var (L n))) fmul (Index (L x3) (Var (L m))) (Index (L x3) (Var (L m)))
                    ));;
               qfor n (Nor (Num Nat (nat2fb 5))) (
                   qif (ceq (Index (L n1) (Var (L n))) (Nor (Num Nat (nat2fb 0))))
                   (skip)
                   (binapp (Nor (Var (L m))) nadd (Nor (Var (L n))) (Nor (Num Nat (nat2fb 1)));;
                     binapp (Index (L x3) (Var (L m))) fmul (Index (L x4) (Var (L n))) (Index (L x4) (Var (L n)))
                    ));;
                init (Nor (Var (L e))) (Index (L x4) (Num Nat (nat2fb 5)))

,Nor (Var (L e))).

Definition taylor_sin : func := 
     (f, ([]), ((TNor C Nat, m)::(TArray Q FixedP 5,x3)::(TNor Q FixedP,x2)::(TNor Q FixedP,e)::
              (TNor C Nat,g)::(TNor C Nat,n)::(TNor C Nat, xc)::(TNor C Nat,fac)
               ::(TNor C FixedP,rc)::(TNor Q FixedP,re)::[]),
                         init (Nor (Var (L re))) (Nor (Var (G x)));;
                         binapp (Nor (Var (L x2))) fmul (Nor (Var (G x))) (Nor (Var (L re)));;
                         binapp (Index (L x3) (Num Nat (nat2fb 0))) fmul (Nor (Var (L x2))) (Nor (Var (G x)));;
                         binapp (Index (L x3) (Num Nat (nat2fb 1))) fmul (Index (L x3) (Num Nat (nat2fb 0))) (Nor (Var (L x2)));;
                         binapp (Index (L x3) (Num Nat (nat2fb 2))) fmul (Index (L x3) (Num Nat (nat2fb 1))) (Nor (Var (L x2)));;
                         binapp (Index (L x3) (Num Nat (nat2fb 3))) fmul (Index (L x3) (Num Nat (nat2fb 2))) (Nor (Var (L x2)));;
                         binapp (Index (L x3) (Num Nat (nat2fb 4))) fmul (Index (L x3) (Num Nat (nat2fb 3))) (Nor (Var (L x2)));;
                         binapp (Nor (Var (L n))) nadd (Nor (Num Nat (nat2fb 1))) (Nor (Var (L n)));;
                         binapp (Nor (Var  (L xc))) nadd (Nor (Num Nat (nat2fb 1))) (Nor (Var  (L xc)));;
         qfor g (Nor ((Var (L m)))) 
             (qif (iseven (Nor (Var (L g)))) 
                      (binapp (Nor (Var ((L n)))) nadd (Nor (Var ((L n)))) (Nor (Num Nat (nat2fb 2)));;
                       unary (Nor (Var (L fac))) nfac (Nor (Var (L n)));;
                       binapp (Nor (Var (L xc))) nmul (Nor (Num Nat (nat2fb 4))) (Nor (Var (L xc)));;
                       binapp (Nor (Var (L rc))) fndiv (Nor (Var (L xc))) (Nor (Var (L fac)));;
                       binapp (Nor (Var (L e))) fmul (Nor (Var (L rc))) (Index (L x3) (Var (L g)));;
                       unary (Nor (Var (L re))) fsub (Nor (Var (L e)));;
                       qinv ((Nor (Var (L e)))))
                      (binapp (Nor (Var ((L n)))) nadd (Nor (Num Nat (nat2fb 2))) (Nor (Var ((L n))));;
                       unary (Nor (Var (L fac))) nfac (Nor (Var (L n)));;
                       binapp (Nor (Var (L xc))) nmul (Nor (Num Nat (nat2fb 4))) (Nor (Var (L xc)));;
                       binapp (Nor (Var (L rc))) fndiv (Nor (Var (L xc))) (Nor (Var (L fac)));;
                       binapp (Nor (Var (L e))) fmul (Nor (Var (L rc))) (Index (L x3) (Var (L g)));;
                       unary (Nor (Var (L re))) fadd (Nor (Var (L e)));;
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
     (f, ([]),((TArray Q FixedP 5,x3)::(TNor Q FixedP,x2)::(TNor Q FixedP,e)::
              (TNor C Nat,g)::(TNor C Nat,n)::(TNor C Nat, xc)::(TNor C Nat,fac)
                ::(TNor C FixedP,rc)::(TNor Q FixedP,re)::[]),
                         unary (Nor (Var (G x))) fsub (Nor (Num FixedP Pi_4)) ;;
                         init (Nor (Var (L re))) (Nor (Var (G x)));;
                         binapp (Nor (Var (L x2))) fmul (Nor (Var (G x))) (Nor (Var (L re)));;
                         binapp (Index (L x3) (Num Nat (nat2fb 0))) fmul (Nor (Var (G x))) (Nor (Var (L x2)));;
                         binapp (Index (L x3) (Num Nat (nat2fb 1))) fmul (Nor (Var (L x2))) (Index (L x3) (Num Nat (nat2fb 0)));;
                         binapp (Index (L x3) (Num Nat (nat2fb 2))) fmul (Nor (Var (L x2))) (Index (L x3) (Num Nat (nat2fb 1)));;
                         binapp (Index (L x3) (Num Nat (nat2fb 3))) fmul (Nor (Var (L x2))) (Index (L x3) (Num Nat (nat2fb 2)));;
                         binapp (Index (L x3) (Num Nat (nat2fb 4))) fmul (Nor (Var (L x2))) (Index (L x3) (Num Nat (nat2fb 3)));;
                         binapp (Nor (Var (L n))) nadd (Nor (Var (L n))) (Nor (Num Nat (nat2fb 1))) ;;
                         binapp (Nor (Var  (L xc))) nadd (Nor (Var  (L xc))) (Nor (Num Nat (nat2fb 1))) ;;
         qfor g (Nor (Num Nat (nat2fb 5))) 
             (qif (iseven (Nor (Var (L g)))) 
                      (binapp (Nor (Var ((L n)))) nadd (Nor (Var ((L n)))) (Nor (Num Nat (nat2fb 2)));;
                       unary (Nor (Var (L fac))) nfac (Nor (Var (L n)));;
                       binapp (Nor (Var (L xc))) nmul (Nor (Num Nat (nat2fb 4))) (Nor (Var (L xc)));;
                       binapp (Nor (Var (L rc))) fndiv (Nor (Var (L xc))) (Nor (Var (L fac)));;
                       binapp (Nor (Var (L e))) fmul (Nor (Var (L rc))) (Index (L x3) (Var (L g)));;
                       unary (Nor (Var (L re))) fsub (Nor (Var (L e)));;
                       qinv ((Nor (Var (L e)))))
                      (binapp (Nor (Var ((L n)))) nadd (Nor (Num Nat (nat2fb 2))) (Nor (Var ((L n))));;
                       unary (Nor (Var (L fac))) nfac (Nor (Var (L n)));;
                       binapp (Nor (Var (L xc))) nmul (Nor (Num Nat (nat2fb 4))) (Nor (Var (L xc)));;
                       binapp (Nor (Var (L rc))) fndiv (Nor (Var (L xc))) (Nor (Var (L fac)));;
                       binapp (Nor (Var (L e))) fmul (Nor (Var (L rc))) (Index (L x3) (Var (L g)));;
                       unary (Nor (Var (L re))) fadd (Nor (Var (L e)));;
                       qinv ((Nor (Var (L e))))))
             ,Nor (Var (L re))).

Definition cos_prog (size:nat) : prog := 
         (size,((TNor Q FixedP, x)::[(TNor Q FixedP,result)]),(taylor_cos::[]),f,result).



Definition test_fun : qexp := binapp (Nor (Var (L x_var))) ndiv (Nor (Var (L y_var))) (Nor (Var (L z_var)))
                           ;; binapp (Nor (Var (L s_var))) nmul (Nor (Var (L x_var))) (Nor (Var (L c_var))).


Definition temp_var := 5. Definition temp1_var := 6. Definition stack_var := 7.

Definition var_list := (cons (TNor C Nat, x_var) (cons (TNor C Nat, y_var) 
                   (cons (TNor C Nat, z_var) (cons (TNor Q Nat, s_var) (cons (TNor Q Nat, c_var) nil))))).

Definition dmc_benv :=
 match
  gen_env var_list empty_benv
  with None => empty_benv | Some bv => bv
 end.

Fixpoint dmc_vmap'  (l : list (typ * var)) (n:nat) :=
  match l with [] => (fun _ => 100)
       | (t,x)::xl => if is_q t then (fun i => if i =qd= (L x,0) then n else dmc_vmap' xl (S n) i) else dmc_vmap' xl (S n)
  end.
Definition dmc_vmap := dmc_vmap' var_list 0.


Definition dmc_estore := init_estore empty_estore var_list.

Definition dmc_cstore := Store.add (L z_var,0) (nat2fb 5) (Store.add (L y_var,0) (nat2fb 10) (init_cstore empty_cstore var_list)).

Definition compile_dm_qft (size:nat) := 
  trans_qexp
    size (fun _ => 1) dmc_vmap dmc_benv QFTA dmc_cstore temp_var temp1_var stack_var 0 nil dmc_estore dmc_estore
    (test_fun).

Definition compile_dm_classic (size:nat) := 
  trans_qexp
    size (fun _ => 1) dmc_vmap dmc_benv Classic dmc_cstore temp_var temp1_var stack_var 0 nil dmc_estore dmc_estore
    (test_fun).

Definition vars_for_dm_c' (size:nat) := 
  gen_vars size ((0::(1::([])))).

Definition vars_for_dm_c (size:nat) :=
  fun x => if x =? stack_var then (size * 2,1,id_nat,id_nat) 
        else vars_for_dm_c' size x.

Definition var_list_q := (cons (TNor Q Nat, x_var) (cons (TNor Q Nat, y_var) 
                   (cons (TNor C Nat, z_var) (cons (TNor Q Nat, s_var) (cons (TNor Q Nat, c_var) nil))))).

Definition dmq_benv :=
 match
  gen_env var_list_q empty_benv
  with None => empty_benv | Some bv => bv
 end.

Definition dmq_vmap := dmc_vmap' var_list_q 0.

Definition dmq_estore := init_estore empty_estore var_list_q.

Definition dmq_cstore := Store.add (L z_var,0) (nat2fb 5) (init_cstore empty_cstore var_list_q).

Definition compile_dmq_qft (size:nat)  := 
  trans_qexp
    size (fun _ => 1) dmq_vmap dmq_benv QFTA dmq_cstore temp_var temp1_var stack_var 0 nil dmq_estore dmq_estore
    (test_fun).

Definition compile_dmq_classic (size:nat)  := 
  trans_qexp
    size (fun _ => 1) dmq_vmap dmq_benv Classic dmq_cstore temp_var temp1_var stack_var 0 nil dmq_estore dmq_estore
    (test_fun).

Definition vars_for_dm_q' (size:nat) := 
  gen_vars size ((0::(1::(2::(3::[]))))).

Definition vars_for_dm_q (size:nat) :=
  fun x => if x =? temp_var then (size * 4,size,id_nat,id_nat) 
        else if x =? temp1_var then (size * 5,size,id_nat,id_nat)
             else if x =? stack_var then (size * 6, 1,id_nat,id_nat)
              else vars_for_dm_c' size x.



