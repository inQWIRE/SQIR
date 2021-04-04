open BinNums
open List
open ModMult
open Nat
open RCIR
open Rdefinitions
open Rpow_def
open Rtrigo1
open Shor
open ShorAux

(** val modexp : int -> int -> int -> int **)

let modexp = fun a x n -> Z.to_int (Z.powm (Z.of_int a) (Z.of_int x) (Z.of_int n))

type bcswap =
| Skip
| X of int
| Swap of int * int
| Ctrl of int * bcswap
| Seq of bcswap * bcswap

(** val bccom_to_bcswap : bccom -> bcswap **)

let rec bccom_to_bcswap = function
| Coq_bcskip -> Skip
| Coq_bcx n -> X n
| Coq_bccont (n, p) -> Ctrl (n, (bccom_to_bcswap p))
| Coq_bcseq (p1, p2) ->
  (match p1 with
   | Coq_bcseq (p0, p3) ->
     (match p0 with
      | Coq_bccont (a, p) ->
        (match p with
         | Coq_bcx b ->
           (match p3 with
            | Coq_bccont (c, p4) ->
              (match p4 with
               | Coq_bcx d ->
                 (match p2 with
                  | Coq_bccont (e, p5) ->
                    (match p5 with
                     | Coq_bcx f ->
                       if (&&) ((&&) ((&&) ((=) a d) ((=) d e)) ((=) b c))
                            ((=) c f)
                       then Swap (a, b)
                       else Seq ((Seq ((Ctrl (a, (X b))), (Ctrl (c, (X
                              d))))), (Ctrl (e, (X f))))
                     | _ -> Seq ((bccom_to_bcswap p1), (bccom_to_bcswap p2)))
                  | _ -> Seq ((bccom_to_bcswap p1), (bccom_to_bcswap p2)))
               | _ -> Seq ((bccom_to_bcswap p1), (bccom_to_bcswap p2)))
            | _ -> Seq ((bccom_to_bcswap p1), (bccom_to_bcswap p2)))
         | _ -> Seq ((bccom_to_bcswap p1), (bccom_to_bcswap p2)))
      | _ -> Seq ((bccom_to_bcswap p1), (bccom_to_bcswap p2)))
   | _ -> Seq ((bccom_to_bcswap p1), (bccom_to_bcswap p2)))

type coq_U =
| U_X
| U_H
| U_U1 of coq_R
| U_U2 of coq_R * coq_R
| U_U3 of coq_R * coq_R * coq_R
| U_CX
| U_CU1 of coq_R
| U_SWAP
| U_CCX
| U_CSWAP
| U_C3X
| U_C4X

type 'u ucom =
| Coq_useq of 'u ucom * 'u ucom
| Coq_uapp of int * 'u * int list

(** val coq_Xg : int -> coq_U ucom **)

let coq_Xg q =
  Coq_uapp ((Pervasives.succ 0), U_X, (q :: []))

(** val coq_H : int -> coq_U ucom **)

let coq_H q =
  Coq_uapp ((Pervasives.succ 0), U_H, (q :: []))

(** val coq_U1 : coq_R -> int -> coq_U ucom **)

let coq_U1 r1 q =
  Coq_uapp ((Pervasives.succ 0), (U_U1 r1), (q :: []))

(** val coq_U3 : coq_R -> coq_R -> coq_R -> int -> coq_U ucom **)

let coq_U3 r1 r2 r3 q =
  Coq_uapp ((Pervasives.succ 0), (U_U3 (r1, r2, r3)), (q :: []))

(** val coq_T : int -> coq_U ucom **)

let coq_T q =
  coq_U1 (coq_Rdiv coq_PI (coq_IZR (Zpos (Coq_xO (Coq_xO Coq_xH))))) q

(** val coq_Tdg : int -> coq_U ucom **)

let coq_Tdg q =
  coq_U1
    (coq_Ropp (coq_Rdiv coq_PI (coq_IZR (Zpos (Coq_xO (Coq_xO Coq_xH)))))) q

(** val coq_SKIP : coq_U ucom **)

let coq_SKIP =
  coq_U1 (coq_IZR Z0) 0

(** val coq_CX : int -> int -> coq_U ucom **)

let coq_CX q1 q2 =
  Coq_uapp ((Pervasives.succ (Pervasives.succ 0)), U_CX, (q1 :: (q2 :: [])))

(** val coq_CU1 : coq_R -> int -> int -> coq_U ucom **)

let coq_CU1 r q1 q2 =
  Coq_uapp ((Pervasives.succ (Pervasives.succ 0)), (U_CU1 r),
    (q1 :: (q2 :: [])))

(** val coq_SWAP : int -> int -> coq_U ucom **)

let coq_SWAP q1 q2 =
  Coq_uapp ((Pervasives.succ (Pervasives.succ 0)), U_SWAP, (q1 :: (q2 :: [])))

(** val coq_CCX : int -> int -> int -> coq_U ucom **)

let coq_CCX q1 q2 q3 =
  Coq_uapp ((Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), U_CCX,
    (q1 :: (q2 :: (q3 :: []))))

(** val coq_CSWAP : int -> int -> int -> coq_U ucom **)

let coq_CSWAP q1 q2 q3 =
  Coq_uapp ((Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), U_CSWAP,
    (q1 :: (q2 :: (q3 :: []))))

(** val coq_C3X : int -> int -> int -> int -> coq_U ucom **)

let coq_C3X q1 q2 q3 q4 =
  Coq_uapp ((Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0)))), U_C3X, (q1 :: (q2 :: (q3 :: (q4 :: [])))))

(** val coq_C4X : int -> int -> int -> int -> int -> coq_U ucom **)

let coq_C4X q1 q2 q3 q4 q5 =
  Coq_uapp ((Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0))))), U_C4X,
    (q1 :: (q2 :: (q3 :: (q4 :: (q5 :: []))))))

(** val decompose_CH : int -> int -> coq_U ucom **)

let decompose_CH a b =
  Coq_useq ((Coq_useq
    ((coq_U3 (coq_Rdiv coq_PI (coq_IZR (Zpos (Coq_xO (Coq_xO Coq_xH)))))
       (coq_IZR Z0) (coq_IZR Z0) b), (coq_CX a b))),
    (coq_U3
      (coq_Ropp (coq_Rdiv coq_PI (coq_IZR (Zpos (Coq_xO (Coq_xO Coq_xH))))))
      (coq_IZR Z0) (coq_IZR Z0) b))

(** val decompose_CU1 : coq_R -> int -> int -> coq_U ucom **)

let decompose_CU1 r1 a b =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((coq_U1 (coq_Rdiv r1 (coq_IZR (Zpos (Coq_xO Coq_xH)))) a),
    (coq_U1 (coq_Rdiv r1 (coq_IZR (Zpos (Coq_xO Coq_xH)))) b))),
    (coq_CX a b))),
    (coq_U1 (coq_Ropp (coq_Rdiv r1 (coq_IZR (Zpos (Coq_xO Coq_xH))))) b))),
    (coq_CX a b))

(** val decompose_CU2 : coq_R -> coq_R -> int -> int -> coq_U ucom **)

let decompose_CU2 r1 r2 a b =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((coq_U1 (coq_Rdiv (coq_Rplus r2 r1) (coq_IZR (Zpos (Coq_xO Coq_xH)))) a),
    (coq_U1 (coq_Rdiv (coq_Rminus r2 r1) (coq_IZR (Zpos (Coq_xO Coq_xH)))) b))),
    (coq_CX a b))),
    (coq_U3
      (coq_Ropp (coq_Rdiv coq_PI (coq_IZR (Zpos (Coq_xO (Coq_xO Coq_xH))))))
      (coq_IZR Z0)
      (coq_Rdiv (coq_Ropp (coq_Rplus r1 r2)) (coq_IZR (Zpos (Coq_xO Coq_xH))))
      b))), (coq_CX a b))),
    (coq_U3 (coq_Rdiv coq_PI (coq_IZR (Zpos (Coq_xO (Coq_xO Coq_xH))))) r1
      (coq_IZR Z0) b))

(** val decompose_CU3 :
    coq_R -> coq_R -> coq_R -> int -> int -> coq_U ucom **)

let decompose_CU3 r1 r2 r3 a b =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((coq_U1 (coq_Rdiv (coq_Rplus r3 r2) (coq_IZR (Zpos (Coq_xO Coq_xH)))) a),
    (coq_U1 (coq_Rdiv (coq_Rminus r3 r2) (coq_IZR (Zpos (Coq_xO Coq_xH)))) b))),
    (coq_CX a b))),
    (coq_U3 (coq_Ropp (coq_Rdiv r1 (coq_IZR (Zpos (Coq_xO Coq_xH)))))
      (coq_IZR Z0)
      (coq_Rdiv (coq_Ropp (coq_Rplus r2 r3)) (coq_IZR (Zpos (Coq_xO Coq_xH))))
      b))), (coq_CX a b))),
    (coq_U3 (coq_Rdiv r1 (coq_IZR (Zpos (Coq_xO Coq_xH)))) r2 (coq_IZR Z0) b))

(** val decompose_CSWAP : int -> int -> int -> coq_U ucom **)

let decompose_CSWAP a b c =
  Coq_useq ((Coq_useq ((coq_CCX a b c), (coq_CCX a c b))), (coq_CCX a b c))

(** val decompose_CCX : int -> int -> int -> coq_U ucom **)

let decompose_CCX a b c =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((Coq_useq ((coq_H c), (coq_CX b c))), (coq_Tdg c))), (coq_CX a c))),
    (coq_T c))), (coq_CX b c))), (coq_Tdg c))), (coq_CX a c))),
    (coq_CX a b))), (coq_Tdg b))), (coq_CX a b))), (coq_T a))), (coq_T b))),
    (coq_T c))), (coq_H c))

(** val control' : int -> coq_U ucom -> int -> coq_U ucom **)

let rec control' a c n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun n' ->
    match c with
    | Coq_useq (c1, c2) -> Coq_useq ((control' a c1 n'), (control' a c2 n'))
    | Coq_uapp (_, u, l) ->
      (match u with
       | U_X ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 -> (match l0 with
                        | [] -> coq_CX a b
                        | _ :: _ -> coq_SKIP))
       | U_H ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> decompose_CH a b
             | _ :: _ -> coq_SKIP))
       | U_U1 r ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_CU1 r a b
             | _ :: _ -> coq_SKIP))
       | U_U2 (r1, r2) ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> decompose_CU2 r1 r2 a b
             | _ :: _ -> coq_SKIP))
       | U_U3 (r1, r2, r3) ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> decompose_CU3 r1 r2 r3 a b
             | _ :: _ -> coq_SKIP))
       | U_CX ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> coq_CCX a b c0
                | _ :: _ -> coq_SKIP)))
       | U_CU1 r ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> control' a (decompose_CU1 r b c0) n'
                | _ :: _ -> coq_SKIP)))
       | U_SWAP ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> coq_CSWAP a b c0
                | _ :: _ -> coq_SKIP)))
       | U_CCX ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> coq_SKIP
                | d :: l2 ->
                  (match l2 with
                   | [] -> coq_C3X a b c0 d
                   | _ :: _ -> coq_SKIP))))
       | U_CSWAP ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> coq_SKIP
                | d :: l2 ->
                  (match l2 with
                   | [] -> control' a (decompose_CSWAP b c0 d) n'
                   | _ :: _ -> coq_SKIP))))
       | U_C3X ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> coq_SKIP
                | d :: l2 ->
                  (match l2 with
                   | [] -> coq_SKIP
                   | e :: l3 ->
                     (match l3 with
                      | [] -> coq_C4X a b c0 d e
                      | _ :: _ -> coq_SKIP)))))
       | U_C4X ->
         (match l with
          | [] -> coq_SKIP
          | b :: l0 ->
            (match l0 with
             | [] -> coq_SKIP
             | c0 :: l1 ->
               (match l1 with
                | [] -> coq_SKIP
                | d :: l2 ->
                  (match l2 with
                   | [] -> coq_SKIP
                   | e :: l3 ->
                     (match l3 with
                      | [] -> coq_SKIP
                      | f :: l4 ->
                        (match l4 with
                         | [] ->
                           control' a
                             (control' b
                               (control' c0 (decompose_CCX d e f) n') n') n'
                         | _ :: _ -> coq_SKIP))))))))
    n

(** val fuel_CU1 : int **)

let fuel_CU1 =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))

(** val fuel_CSWAP : int **)

let fuel_CSWAP =
  Pervasives.succ (Pervasives.succ 0)

(** val fuel_CCX : int **)

let fuel_CCX =
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ 0)))))))))))))

(** val fuel : coq_U ucom -> int **)

let rec fuel = function
| Coq_useq (c1, c2) -> Pervasives.succ (Pervasives.max (fuel c1) (fuel c2))
| Coq_uapp (_, u, _) ->
  (match u with
   | U_CU1 _ -> Pervasives.succ fuel_CU1
   | U_CSWAP -> Pervasives.succ fuel_CSWAP
   | U_C4X -> Pervasives.succ (Pervasives.succ (Pervasives.succ fuel_CCX))
   | _ -> 0)

(** val control : int -> coq_U ucom -> coq_U ucom **)

let control a c =
  control' a c (Pervasives.succ (fuel c))

(** val bcswap2ucom : bcswap -> coq_U ucom **)

let rec bcswap2ucom = function
| Skip -> coq_SKIP
| X a -> coq_Xg a
| Swap (a, b) -> coq_SWAP a b
| Ctrl (a, bc1) -> control a (bcswap2ucom bc1)
| Seq (bc1, bc2) -> Coq_useq ((bcswap2ucom bc1), (bcswap2ucom bc2))

(** val modmult_circuit : int -> int -> int -> int -> int -> bcswap **)

let modmult_circuit a ainv n n0 i =
  bccom_to_bcswap
    (bcelim
      (modmult_rev n
        (modexp a (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) i)
          n)
        (modexp ainv
          (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) i) n) n0))

(** val num_qubits : int -> int **)

let num_qubits n =
  add n (modmult_rev_anc n)

(** val controlled_rotations : int -> coq_U ucom **)

let rec controlled_rotations n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_SKIP)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        coq_CU1
          (coq_Rdiv (coq_Rmult (coq_IZR (Zpos (Coq_xO Coq_xH))) coq_PI)
            (pow (coq_IZR (Zpos (Coq_xO Coq_xH))) n)) (Pervasives.succ 0) 0)
        (fun _ -> Coq_useq ((controlled_rotations n'),
        (coq_CU1
          (coq_Rdiv (coq_Rmult (coq_IZR (Zpos (Coq_xO Coq_xH))) coq_PI)
            (pow (coq_IZR (Zpos (Coq_xO Coq_xH))) n)) n' 0)))
        n0)
      n')
    n

(** val map_qubits : (int -> int) -> coq_U ucom -> coq_U ucom **)

let rec map_qubits f = function
| Coq_useq (c1, c2) -> Coq_useq ((map_qubits f c1), (map_qubits f c2))
| Coq_uapp (n, g, qs) -> Coq_uapp (n, g, (map f qs))

(** val coq_QFT : int -> coq_U ucom **)

let rec coq_QFT n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_H 0)
      (fun _ -> Coq_useq ((Coq_useq ((coq_H 0), (controlled_rotations n))),
      (map_qubits (fun x -> Pervasives.succ x) (coq_QFT n'))))
      n')
    n

(** val reverse_qubits' : int -> int -> coq_U ucom **)

let rec reverse_qubits' dim n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> coq_SWAP 0 (sub dim (Pervasives.succ 0)))
      (fun _ -> Coq_useq ((reverse_qubits' dim n'),
      (coq_SWAP n' (sub (sub dim n') (Pervasives.succ 0)))))
      n')
    n

(** val reverse_qubits : int -> coq_U ucom **)

let reverse_qubits n =
  reverse_qubits' n (PeanoNat.Nat.div n (Pervasives.succ (Pervasives.succ 0)))

(** val coq_QFT_w_reverse : int -> coq_U ucom **)

let coq_QFT_w_reverse n =
  Coq_useq ((coq_QFT n), (reverse_qubits n))

(** val controlled_powers_var' : (int -> bcswap) -> int -> int -> bcswap **)

let rec controlled_powers_var' f k kmax =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Skip)
    (fun k' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Ctrl ((sub kmax (Pervasives.succ 0)), (f 0)))
      (fun _ -> Seq ((controlled_powers_var' f k' kmax), (Ctrl
      ((sub (sub kmax k') (Pervasives.succ 0)), (f k')))))
      k')
    k

(** val controlled_powers_var : (int -> bcswap) -> int -> coq_U ucom **)

let controlled_powers_var f k =
  bcswap2ucom (controlled_powers_var' f k k)

(** val npar : int -> coq_U -> coq_U ucom **)

let rec npar n u =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_SKIP)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Coq_uapp ((Pervasives.succ 0), u, (0 :: [])))
      (fun _ -> Coq_useq ((npar n' u), (Coq_uapp ((Pervasives.succ 0), u,
      (n' :: [])))))
      n')
    n

(** val map_bcswap : (int -> int) -> bcswap -> bcswap **)

let rec map_bcswap f = function
| Skip -> Skip
| X a -> X (f a)
| Swap (a, b) -> Swap ((f a), (f b))
| Ctrl (a, bc1) -> Ctrl ((f a), (map_bcswap f bc1))
| Seq (bc1, bc2) -> Seq ((map_bcswap f bc1), (map_bcswap f bc2))

(** val invert : coq_U ucom -> coq_U ucom **)

let rec invert = function
| Coq_useq (u1, u2) -> Coq_useq ((invert u2), (invert u1))
| Coq_uapp (_, g, qs) ->
  (match g with
   | U_X ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l -> (match l with
                    | [] -> coq_Xg q1
                    | _ :: _ -> coq_SKIP))
   | U_H ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l -> (match l with
                    | [] -> coq_H q1
                    | _ :: _ -> coq_SKIP))
   | U_U1 r1 ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_U1 (coq_Ropp r1) q1
         | _ :: _ -> coq_SKIP))
   | U_U2 (r1, r2) ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] ->
           coq_U3
             (coq_Ropp (coq_Rdiv coq_PI (coq_IZR (Zpos (Coq_xO Coq_xH)))))
             (coq_Ropp r1) (coq_Ropp r2) q1
         | _ :: _ -> coq_SKIP))
   | U_U3 (r1, r2, r3) ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_U3 (coq_Ropp r1) (coq_Ropp r2) (coq_Ropp r3) q1
         | _ :: _ -> coq_SKIP))
   | U_CX ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 -> (match l0 with
                        | [] -> coq_CX q1 q2
                        | _ :: _ -> coq_SKIP)))
   | U_CU1 r ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 ->
           (match l0 with
            | [] -> coq_CU1 r q1 q2
            | _ :: _ -> coq_SKIP)))
   | U_SWAP ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 ->
           (match l0 with
            | [] -> coq_SWAP q1 q2
            | _ :: _ -> coq_SKIP)))
   | U_CCX ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 ->
           (match l0 with
            | [] -> coq_SKIP
            | q3 :: l1 ->
              (match l1 with
               | [] -> coq_CCX q1 q2 q3
               | _ :: _ -> coq_SKIP))))
   | U_CSWAP ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 ->
           (match l0 with
            | [] -> coq_SKIP
            | q3 :: l1 ->
              (match l1 with
               | [] -> coq_CSWAP q1 q2 q3
               | _ :: _ -> coq_SKIP))))
   | U_C3X ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 ->
           (match l0 with
            | [] -> coq_SKIP
            | q3 :: l1 ->
              (match l1 with
               | [] -> coq_SKIP
               | q4 :: l2 ->
                 (match l2 with
                  | [] -> coq_C3X q1 q2 q3 q4
                  | _ :: _ -> coq_SKIP)))))
   | U_C4X ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_SKIP
         | q2 :: l0 ->
           (match l0 with
            | [] -> coq_SKIP
            | q3 :: l1 ->
              (match l1 with
               | [] -> coq_SKIP
               | q4 :: l2 ->
                 (match l2 with
                  | [] -> coq_SKIP
                  | q5 :: l3 ->
                    (match l3 with
                     | [] -> coq_C4X q1 q2 q3 q4 q5
                     | _ :: _ -> coq_SKIP)))))))

(** val coq_QPE_var : int -> (int -> bcswap) -> coq_U ucom **)

let coq_QPE_var k f =
  Coq_useq ((Coq_useq ((npar k U_H),
    (controlled_powers_var (fun x -> map_bcswap (fun q -> add k q) (f x)) k))),
    (invert (coq_QFT_w_reverse k)))

(** val shor_circuit : int -> int -> (coq_U ucom * int) * int **)

let shor_circuit a n =
  let m =
    PeanoNat.Nat.log2
      (mul (Pervasives.succ (Pervasives.succ 0))
        (PeanoNat.Nat.pow n (Pervasives.succ (Pervasives.succ 0))))
  in
  let n0 = PeanoNat.Nat.log2 (mul (Pervasives.succ (Pervasives.succ 0)) n) in
  let ainv = modinv a n in
  let numq = num_qubits n0 in
  let f = fun i -> modmult_circuit a ainv n n0 i in
  (((Coq_useq ((coq_Xg (sub (add m n0) (Pervasives.succ 0))),
  (coq_QPE_var m f))), (add m numq)), m)

(** val coq_OF_post' : int -> int -> int -> int -> int -> int **)

let rec coq_OF_post' step a n o m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun step' ->
    let pre = coq_OF_post' step' a n o m in
    if (=) pre 0
    then if (=) (modexp a (coq_OF_post_step step' o m) n) (Pervasives.succ 0)
         then coq_OF_post_step step' o m
         else 0
    else pre)
    step

(** val coq_OF_post : int -> int -> int -> int -> int **)

let coq_OF_post a n o m =
  coq_OF_post'
    (add (mul (Pervasives.succ (Pervasives.succ 0)) m) (Pervasives.succ
      (Pervasives.succ 0))) a n o m

(** val post_process : int -> int -> int -> int **)

let post_process a n o =
  let m =
    PeanoNat.Nat.log2
      (mul (Pervasives.succ (Pervasives.succ 0))
        (PeanoNat.Nat.pow n (Pervasives.succ (Pervasives.succ 0))))
  in
  coq_OF_post a n o m
