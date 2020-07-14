open UnitaryListRepresentation

module RzQGateSet =
 struct
  type coq_RzQ_Unitary =
  | URzQ_H
  | URzQ_X
  | URzQ_Rz of Q.t
  | URzQ_CNOT 


  type coq_U = coq_RzQ_Unitary

  (** val match_gate : int -> coq_U -> coq_U -> bool **)

  let match_gate _ u u' =
    match u with
    | URzQ_H -> (match u' with
                 | URzQ_H -> true
                 | _ -> false)
    | URzQ_X -> (match u' with
                 | URzQ_X -> true
                 | _ -> false)
    | URzQ_Rz q -> (match u' with
                    | URzQ_Rz q' -> Q.equal q q'
                    | _ -> false)
    | URzQ_CNOT -> (match u' with
                    | URzQ_CNOT -> true
                    | _ -> false)
 end

(** val coq_URzQ_T : RzQGateSet.coq_RzQ_Unitary **)

let coq_URzQ_T = RzQGateSet.URzQ_Rz (Q.of_ints 1 4)

(** val coq_URzQ_P : RzQGateSet.coq_RzQ_Unitary **)

let coq_URzQ_P = RzQGateSet.URzQ_Rz (Q.of_ints 1 2)

(** val coq_URzQ_Z : RzQGateSet.coq_RzQ_Unitary **)

let coq_URzQ_Z = RzQGateSet.URzQ_Rz (Q.of_int 1)

(** val coq_URzQ_PDAG : RzQGateSet.coq_RzQ_Unitary **)

let coq_URzQ_PDAG = RzQGateSet.URzQ_Rz (Q.of_ints 3 2)

(** val coq_URzQ_TDAG : RzQGateSet.coq_RzQ_Unitary **)

let coq_URzQ_TDAG = RzQGateSet.URzQ_Rz (Q.of_ints 7 4)

(** val coq_T : int -> RzQGateSet.coq_RzQ_Unitary gate_app **)

let coq_T q =
  App1 (coq_URzQ_T, q)

(** val coq_TDAG : int -> RzQGateSet.coq_RzQ_Unitary gate_app **)

let coq_TDAG q =
  App1 (coq_URzQ_TDAG, q)

(** val coq_P : int -> RzQGateSet.coq_RzQ_Unitary gate_app **)

let coq_P q =
  App1 (coq_URzQ_P, q)

(** val coq_PDAG : int -> RzQGateSet.coq_RzQ_Unitary gate_app **)

let coq_PDAG q =
  App1 (coq_URzQ_PDAG, q)

(** val coq_Z : int -> RzQGateSet.coq_RzQ_Unitary gate_app **)

let coq_Z q =
  App1 (coq_URzQ_Z, q)

(** val coq_Rz : Q.t -> int -> RzQGateSet.coq_RzQ_Unitary gate_app **)

let coq_Rz i q =
  App1 ((RzQGateSet.URzQ_Rz i), q)

(** val coq_H : int -> RzQGateSet.coq_RzQ_Unitary gate_app **)

let coq_H q =
  App1 (RzQGateSet.URzQ_H, q)

(** val coq_X : int -> RzQGateSet.coq_RzQ_Unitary gate_app **)

let coq_X q =
  App1 (RzQGateSet.URzQ_X, q)

(** val coq_CNOT : int -> int -> RzQGateSet.coq_RzQ_Unitary gate_app **)

let coq_CNOT q1 q2 =
  App2 (RzQGateSet.URzQ_CNOT, q1, q2)

type coq_RzQ_ucom_l = RzQGateSet.coq_RzQ_Unitary gate_list

(** val coq_CCX : int -> int -> int -> coq_RzQ_ucom_l **)

let coq_CCX a b c =
  (coq_H c) :: ((coq_CNOT b c) :: ((coq_TDAG c) :: ((coq_CNOT a c) :: (
    (coq_T c) :: ((coq_CNOT b c) :: ((coq_TDAG c) :: ((coq_CNOT a c) :: (
    (coq_CNOT a b) :: ((coq_TDAG b) :: ((coq_CNOT a b) :: ((coq_T a) :: (
    (coq_T b) :: ((coq_T c) :: ((coq_H c) :: []))))))))))))))

(** val coq_CCZ : int -> int -> int -> coq_RzQ_ucom_l **)


let coq_CCZ a b c =
  (coq_CNOT b c) :: ((coq_TDAG c) :: ((coq_CNOT a c) :: ((coq_T c) :: (
    (coq_CNOT b c) :: ((coq_TDAG c) :: ((coq_CNOT a c) :: ((coq_CNOT a b) :: (
    (coq_TDAG b) :: ((coq_CNOT a b) :: ((coq_T a) :: ((coq_T b) :: ((coq_T c) :: []))))))))))))

(** val remove_prefix :
    coq_RzQ_ucom_l -> coq_RzQ_ucom_l -> RzQGateSet.coq_RzQ_Unitary gate_list
    option **)

let remove_prefix l pfx =
  remove_prefix l pfx RzQGateSet.match_gate

(** val replace_pattern :
    coq_RzQ_ucom_l -> coq_RzQ_ucom_l -> coq_RzQ_ucom_l ->
    RzQGateSet.coq_RzQ_Unitary gate_list option **)

let replace_pattern l pat rep =
  replace_pattern l pat rep RzQGateSet.match_gate

(** val bound : Q.t -> Q.t **)

let bound = let round_to_multiple_of_2 q = 
      let num = Q.num q in 
      let den = Q.den q in
      Z.mul (Z.of_int 2) (Z.div num (Z.mul den (Z.of_int 2))) in
   fun q ->
   if (Q.leq (Q.of_int 0) q) && not (Q.leq (Q.of_int 2) q) then q
   else if (Q.leq (Q.of_int 2) q)
        then Q.sub q (Q.of_bigint (round_to_multiple_of_2 q))
        else Q.add q (Q.of_bigint (round_to_multiple_of_2 q))

(** val combine_rotations : Q.t -> Q.t -> int -> coq_RzQ_ucom_l **)

let combine_rotations a a' q =
  let anew = bound (Q.add a a') in
  if Q.equal anew (Q.of_int 0) then [] else (coq_Rz anew q) :: []

(** val invert_rotation :
    Q.t -> int -> RzQGateSet.coq_RzQ_Unitary gate_app **)

let invert_rotation a q =
  coq_Rz (Q.sub (Q.of_int 2) a) q
