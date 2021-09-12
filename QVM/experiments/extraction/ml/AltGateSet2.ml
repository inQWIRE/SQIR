
type 'u ucom =
| Coq_useq of 'u ucom * 'u ucom
| Coq_uapp of int * 'u * int list

type coq_U =
| U_X
| U_H
| U_U1 of float
| U_U2 of float * float
| U_U3 of float * float * float
| U_CX
| U_CCX

(** val coq_X : int -> coq_U ucom **)

let coq_X q =
  Coq_uapp ((Pervasives.succ 0), U_X, (q :: []))

(** val coq_H : int -> coq_U ucom **)

let coq_H q =
  Coq_uapp ((Pervasives.succ 0), U_H, (q :: []))

(** val coq_U1 : float -> int -> coq_U ucom **)

let coq_U1 r1 q =
  Coq_uapp ((Pervasives.succ 0), (U_U1 r1), (q :: []))

(** val coq_U2 : float -> float -> int -> coq_U ucom **)

let coq_U2 r1 r2 q =
  Coq_uapp ((Pervasives.succ 0), (U_U2 (r1, r2)), (q :: []))

(** val coq_U3 : float -> float -> float -> int -> coq_U ucom **)

let coq_U3 r1 r2 r3 q =
  Coq_uapp ((Pervasives.succ 0), (U_U3 (r1, r2, r3)), (q :: []))

(** val coq_T : int -> coq_U ucom **)

let coq_T q =
  coq_U1 (( /. ) Float.pi 4.0) q

(** val coq_Tdg : int -> coq_U ucom **)

let coq_Tdg q =
  coq_U1 (((-.) 0.0) (( /. ) Float.pi 4.0)) q

(** val coq_SKIP : coq_U ucom **)

let coq_SKIP =
  coq_U1 0.0 0

(** val coq_ID : int -> coq_U ucom **)

let coq_ID q =
  coq_U1 0.0 q

(** val coq_CX : int -> int -> coq_U ucom **)

let coq_CX q1 q2 =
  Coq_uapp ((Pervasives.succ (Pervasives.succ 0)), U_CX, (q1 :: (q2 :: [])))

(** val coq_CCX : int -> int -> int -> coq_U ucom **)

let coq_CCX q1 q2 q3 =
  Coq_uapp ((Pervasives.succ (Pervasives.succ (Pervasives.succ 0))), U_CCX,
    (q1 :: (q2 :: (q3 :: []))))

(** val decompose_CH : int -> int -> coq_U ucom **)

let decompose_CH a b =
  Coq_useq ((Coq_useq ((coq_U3 (( /. ) Float.pi 4.0) 0.0 0.0 b),
    (coq_CX a b))), (coq_U3 (((-.) 0.0) (( /. ) Float.pi 4.0)) 0.0 0.0 b))

(** val decompose_CU1 : float -> int -> int -> coq_U ucom **)

let decompose_CU1 r1 a b =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((coq_U1 (( /. ) r1 2.0) a),
    (coq_U1 (( /. ) r1 2.0) b))), (coq_CX a b))),
    (coq_U1 (((-.) 0.0) (( /. ) r1 2.0)) b))), (coq_CX a b))

(** val decompose_CU2 : float -> float -> int -> int -> coq_U ucom **)

let decompose_CU2 r1 r2 a b =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((coq_U1 (( /. ) (( +. ) r2 r1) 2.0) a),
    (coq_U1 (( /. ) (( -. ) r2 r1) 2.0) b))), (coq_CX a b))),
    (coq_U3 (((-.) 0.0) (( /. ) Float.pi 4.0)) 0.0
      (( /. ) (((-.) 0.0) (( +. ) r1 r2)) 2.0) b))), (coq_CX a b))),
    (coq_U3 (( /. ) Float.pi 4.0) r1 0.0 b))

(** val decompose_CU3 :
    float -> float -> float -> int -> int -> coq_U ucom **)

let decompose_CU3 r1 r2 r3 a b =
  Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq ((Coq_useq
    ((coq_U1 (( /. ) (( +. ) r3 r2) 2.0) a),
    (coq_U1 (( /. ) (( -. ) r3 r2) 2.0) b))), (coq_CX a b))),
    (coq_U3 (((-.) 0.0) (( /. ) r1 2.0)) 0.0
      (( /. ) (((-.) 0.0) (( +. ) r2 r3)) 2.0) b))), (coq_CX a b))),
    (coq_U3 (( /. ) r1 2.0) r2 0.0 b))

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
             | [] -> decompose_CU1 r a b
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
                   | [] -> control' a (decompose_CCX b c0 d) n'
                   | _ :: _ -> coq_SKIP))))))
    n

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
   | U_CCX -> Pervasives.succ fuel_CCX
   | _ -> 0)

(** val control : int -> coq_U ucom -> coq_U ucom **)

let control a c =
  control' a c (Pervasives.succ (fuel c))

(** val invert : coq_U ucom -> coq_U ucom **)

let rec invert = function
| Coq_useq (u1, u2) -> Coq_useq ((invert u2), (invert u1))
| Coq_uapp (_, g, qs) ->
  (match g with
   | U_X ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l -> (match l with
                    | [] -> coq_X q1
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
         | [] -> coq_U1 (((-.) 0.0) r1) q1
         | _ :: _ -> coq_SKIP))
   | U_U2 (r1, r2) ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] ->
           coq_U2 (( -. ) (((-.) 0.0) r2) Float.pi)
             (( +. ) (((-.) 0.0) r1) Float.pi) q1
         | _ :: _ -> coq_SKIP))
   | U_U3 (r1, r2, r3) ->
     (match qs with
      | [] -> coq_SKIP
      | q1 :: l ->
        (match l with
         | [] -> coq_U3 (((-.) 0.0) r1) (((-.) 0.0) r3) (((-.) 0.0) r2) q1
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
               | _ :: _ -> coq_SKIP)))))
