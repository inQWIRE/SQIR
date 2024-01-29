open Datatypes
open List0
open Nat
open RealAux
open Summation

(** val sum_over_list : float list -> float **)

let sum_over_list l =
  big_sum coq_R_is_monoid (fun i -> nth i l (Z.to_float Z.zero)) (length l)

(** val sample : float list -> float -> Z.t **)

let rec sample = 
  let rec aux l r =
    match l with
    | [] -> Z.zero
    | x :: l' ->
      if r < x then Z.zero else Z.succ (aux l' (r -. x)) in
  fun l r -> 
  let x = aux l r in
  (Printf.printf "Random sampling selected a = %d\n%!" (Z.to_int x); x)

(** val uniform : Z.t -> Z.t -> float list **)

let uniform lower upper =
  List.append (repeat (Z.to_float Z.zero) lower)
    (repeat (( /. ) (Z.to_float Z.one) (Z.to_float (sub upper lower)))
      (sub upper lower))

(** val fst : Z.t -> Z.t -> Z.t **)

let fst m x =
  Z.div x (PeanoNat.Nat.pow (Z.succ (Z.succ Z.zero)) m)

(** val compute_new_rnd : float -> float list -> Z.t -> float **)

let compute_new_rnd rnd l o =
  ( /. ) (( -. ) rnd (sum_over_list (firstn o l)))
    (nth o l (Z.to_float Z.zero))

(** val iterate : float list -> (float -> 'a1 option) -> 'a1 option **)

let rec iterate rnds body =
  match rnds with
  | [] -> None
  | rnd :: rnds' ->
    (match body rnd with
     | Some v -> Some v
     | None -> iterate rnds' body)
