open BinNums
open Complex
open Datatypes
open List
open Matrix
open Nat
open RIneq
open Raxioms
open SQIR
open UnitarySem
open VectorStates

(** val coq_Cmod2 : coq_C -> float **)

let coq_Cmod2 c =
  ( +. )
    ((fun a b -> a ** Float.of_int b) (fst c) (Pervasives.succ
      (Pervasives.succ 0)))
    ((fun a b -> a ** Float.of_int b) (snd c) (Pervasives.succ
      (Pervasives.succ 0)))

(** val sample : float list -> float -> int **)

let rec sample l r =
  match l with
  | [] -> 0
  | x :: l' ->
    if coq_Rlt_le_dec r x then 0 else Pervasives.succ (sample l' (( -. ) r x))

(** val run : int -> base_ucom -> float list **)

let run dim c =
  let v =
    coq_Mmult (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim)
      (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim)
      (Pervasives.succ 0) (uc_eval dim c)
      (basis_vector
        (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim) 0)
  in
  List.map coq_Cmod2
    (vec_to_list (PeanoNat.Nat.pow (Pervasives.succ (Pervasives.succ 0)) dim)
      v)

(** val uniform : int -> int -> float list **)

let uniform lower upper =
  List.append (repeat (Float.of_int Z0) lower)
    (repeat (( /. ) (Float.of_int (Zpos Coq_xH)) (coq_INR (sub upper lower)))
      (sub upper lower))

(** val scale : float -> float list -> float list **)

let rec scale r = function
| [] -> []
| h :: t -> (( *. ) r h) :: (scale r t)

(** val join' : float list -> (int -> float list) -> int -> float list **)

let rec join' l1 l2 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' ->
    List.append (join' l1 l2 n') (scale (nth n' l1 (Float.of_int Z0)) (l2 n')))
    n

(** val join : float list -> (int -> float list) -> float list **)

let join l1 l2 =
  join' l1 l2 (List.length l1)

(** val fst_join : int -> int -> int **)

let fst_join m x =
  PeanoNat.Nat.div x m

(** val snd_join : int -> int -> int **)

let snd_join m x =
  PeanoNat.Nat.modulo x m

(** val iterate : float list -> (float -> 'a1 option) -> 'a1 option **)

let rec iterate rnds body =
  match rnds with
  | [] -> None
  | rnd :: rnds' ->
    (match body rnd with
     | Some v -> Some v
     | None -> iterate rnds' body)
