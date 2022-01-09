open Matrix
open Nat
open Quantum
open SQIR

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val pad : int -> int -> int -> coq_Matrix -> coq_Matrix **)

let pad n start dim a =
  if (<=) (add start n) dim
  then kron
         (mul (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) start)
           (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) n))
         (mul (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) start)
           (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) n))
         (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
           (sub dim (add start n)))
         (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
           (sub dim (add start n)))
         (kron (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) start)
           (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) start)
           (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) n)
           (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) n)
           (coq_I
             (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) start))
           a)
         (coq_I
           (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
             (sub dim (add start n))))
  else coq_Zero (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim)
         (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim)

(** val ueval_r : int -> int -> base_Unitary -> coq_Matrix **)

let ueval_r dim n = function
| U_R (_UU03b8_, _UU03d5_, _UU03bb_) ->
  pad (Pervasives.succ 0) n dim (rotation _UU03b8_ _UU03d5_ _UU03bb_)
| U_CNOT -> Obj.magic __

(** val ueval_cnot : int -> int -> int -> coq_Matrix **)

let ueval_cnot dim m n =
  if PeanoNat.Nat.ltb m n
  then pad
         (add (add (Pervasives.succ 0) (sub (sub n m) (Pervasives.succ 0)))
           (Pervasives.succ 0)) m dim
         (coq_Mplus
           (mul
             (mul (Pervasives.succ (Pervasives.succ 0))
               (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                 (sub (sub n m) (Pervasives.succ 0)))) (Pervasives.succ
             (Pervasives.succ 0)))
           (mul
             (mul (Pervasives.succ (Pervasives.succ 0))
               (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                 (sub (sub n m) (Pervasives.succ 0)))) (Pervasives.succ
             (Pervasives.succ 0)))
           (kron
             (mul (Pervasives.succ (Pervasives.succ 0))
               (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                 (sub (sub n m) (Pervasives.succ 0))))
             (mul (Pervasives.succ (Pervasives.succ 0))
               (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                 (sub (sub n m) (Pervasives.succ 0)))) (Pervasives.succ
             (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
             (kron (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ
               (Pervasives.succ 0))
               (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                 (sub (sub n m) (Pervasives.succ 0)))
               (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                 (sub (sub n m) (Pervasives.succ 0)))
               (coq_Mmult (Pervasives.succ (Pervasives.succ 0))
                 (Pervasives.succ 0) (Pervasives.succ (Pervasives.succ 0))
                 qubit1
                 (adjoint (Pervasives.succ (Pervasives.succ 0))
                   (Pervasives.succ 0) qubit1))
               (coq_I
                 (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                   (sub (sub n m) (Pervasives.succ 0))))) _UU03c3_x)
           (kron
             (mul (Pervasives.succ (Pervasives.succ 0))
               (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                 (sub (sub n m) (Pervasives.succ 0))))
             (mul (Pervasives.succ (Pervasives.succ 0))
               (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                 (sub (sub n m) (Pervasives.succ 0)))) (Pervasives.succ
             (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
             (kron (Pervasives.succ (Pervasives.succ 0)) (Pervasives.succ
               (Pervasives.succ 0))
               (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                 (sub (sub n m) (Pervasives.succ 0)))
               (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                 (sub (sub n m) (Pervasives.succ 0)))
               (coq_Mmult (Pervasives.succ (Pervasives.succ 0))
                 (Pervasives.succ 0) (Pervasives.succ (Pervasives.succ 0))
                 qubit0
                 (adjoint (Pervasives.succ (Pervasives.succ 0))
                   (Pervasives.succ 0) qubit0))
               (coq_I
                 (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                   (sub (sub n m) (Pervasives.succ 0)))))
             (coq_I (Pervasives.succ (Pervasives.succ 0)))))
  else if PeanoNat.Nat.ltb n m
       then pad
              (add
                (add (Pervasives.succ 0) (sub (sub m n) (Pervasives.succ 0)))
                (Pervasives.succ 0)) n dim
              (coq_Mplus
                (mul
                  (mul (Pervasives.succ (Pervasives.succ 0))
                    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                      (sub (sub m n) (Pervasives.succ 0)))) (Pervasives.succ
                  (Pervasives.succ 0)))
                (mul
                  (mul (Pervasives.succ (Pervasives.succ 0))
                    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                      (sub (sub m n) (Pervasives.succ 0)))) (Pervasives.succ
                  (Pervasives.succ 0)))
                (kron
                  (mul (Pervasives.succ (Pervasives.succ 0))
                    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                      (sub (sub m n) (Pervasives.succ 0))))
                  (mul (Pervasives.succ (Pervasives.succ 0))
                    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                      (sub (sub m n) (Pervasives.succ 0)))) (Pervasives.succ
                  (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
                  (kron (Pervasives.succ (Pervasives.succ 0))
                    (Pervasives.succ (Pervasives.succ 0))
                    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                      (sub (sub m n) (Pervasives.succ 0)))
                    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                      (sub (sub m n) (Pervasives.succ 0))) _UU03c3_x
                    (coq_I
                      (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                        (sub (sub m n) (Pervasives.succ 0)))))
                  (coq_Mmult (Pervasives.succ (Pervasives.succ 0))
                    (Pervasives.succ 0) (Pervasives.succ (Pervasives.succ 0))
                    qubit1
                    (adjoint (Pervasives.succ (Pervasives.succ 0))
                      (Pervasives.succ 0) qubit1)))
                (kron
                  (mul (Pervasives.succ (Pervasives.succ 0))
                    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                      (sub (sub m n) (Pervasives.succ 0))))
                  (mul (Pervasives.succ (Pervasives.succ 0))
                    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                      (sub (sub m n) (Pervasives.succ 0)))) (Pervasives.succ
                  (Pervasives.succ 0)) (Pervasives.succ (Pervasives.succ 0))
                  (kron (Pervasives.succ (Pervasives.succ 0))
                    (Pervasives.succ (Pervasives.succ 0))
                    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                      (sub (sub m n) (Pervasives.succ 0)))
                    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                      (sub (sub m n) (Pervasives.succ 0)))
                    (coq_I (Pervasives.succ (Pervasives.succ 0)))
                    (coq_I
                      (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0))
                        (sub (sub m n) (Pervasives.succ 0)))))
                  (coq_Mmult (Pervasives.succ (Pervasives.succ 0))
                    (Pervasives.succ 0) (Pervasives.succ (Pervasives.succ 0))
                    qubit0
                    (adjoint (Pervasives.succ (Pervasives.succ 0))
                      (Pervasives.succ 0) qubit0))))
       else coq_Zero
              (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim)
              (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim)

(** val uc_eval : int -> base_ucom -> coq_Matrix **)

let rec uc_eval dim = function
| Coq_useq (c1, c2) ->
  coq_Mmult (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim)
    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim)
    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim)
    (uc_eval dim c2) (uc_eval dim c1)
| Coq_uapp1 (u, n) -> ueval_r dim n u
| Coq_uapp2 (_, m, n) -> ueval_cnot dim m n
| Coq_uapp3 (_, _, _, _) ->
  coq_Zero (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim)
    (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim)
