open BinNums
open Datatypes

type coq_C = float * float

(** val coq_RtoC : float -> coq_C **)

let coq_RtoC x =
  (x, (Float.of_int Z0))

(** val coq_Cplus : coq_C -> coq_C -> coq_C **)

let coq_Cplus x y =
  ((( +. ) (fst x) (fst y)), (( +. ) (snd x) (snd y)))

(** val coq_Copp : coq_C -> coq_C **)

let coq_Copp x =
  ((((-.) 0.0) (fst x)), (((-.) 0.0) (snd x)))

(** val coq_Cmult : coq_C -> coq_C -> coq_C **)

let coq_Cmult x y =
  ((( -. ) (( *. ) (fst x) (fst y)) (( *. ) (snd x) (snd y))),
    (( +. ) (( *. ) (fst x) (snd y)) (( *. ) (snd x) (fst y))))

(** val coq_Cconj : coq_C -> coq_C **)

let coq_Cconj x =
  ((fst x), (((-.) 0.0) (snd x)))

(** val coq_Cexp : float -> coq_C **)

let coq_Cexp _UU03b8_ =
  ((cos _UU03b8_), (sin _UU03b8_))

(** val coq_Csum : (int -> coq_C) -> int -> coq_C **)

let rec coq_Csum f n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> coq_RtoC (Float.of_int Z0))
    (fun n' -> coq_Cplus (coq_Csum f n') (f n'))
    n
