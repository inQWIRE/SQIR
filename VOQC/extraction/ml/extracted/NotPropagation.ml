open Datatypes
open FSetAVL
open OrderedTypeEx
open UnitaryListRepresentation

module FSet = Make(Nat_as_OT)

(** val finalize : FSet.t -> RzQGateSet.coq_RzQ_ucom_l **)

let finalize qs =
  FSet.fold (fun q a -> (RzQGateSet.coq_X q) :: a) qs []

(** val not_propagation' :
    RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.coq_RzQ_ucom_l -> FSet.t ->
    RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app list **)

let rec not_propagation' l acc qs =
  match l with
  | [] -> List.rev_append acc (finalize qs)
  | g :: t0 ->
    (match g with
     | App1 (r, q) ->
       (match r with
        | RzQGateSet.RzQGateSet.URzQ_H ->
          if FSet.mem q qs
          then not_propagation' t0
                 ((RzQGateSet.coq_Z q) :: ((RzQGateSet.coq_H q) :: acc))
                 (FSet.remove q qs)
          else not_propagation' t0 ((RzQGateSet.coq_H q) :: acc) qs
        | RzQGateSet.RzQGateSet.URzQ_X ->
          let qs' = if FSet.mem q qs then FSet.remove q qs else FSet.add q qs
          in
          not_propagation' t0 acc qs'
        | RzQGateSet.RzQGateSet.URzQ_Rz a ->
          if FSet.mem q qs
          then not_propagation' t0 ((RzQGateSet.invert_rotation a q) :: acc)
                 qs
          else not_propagation' t0 ((RzQGateSet.coq_Rz a q) :: acc) qs
        | RzQGateSet.RzQGateSet.URzQ_CNOT -> acc)
     | App2 (r, m, n) ->
       (match r with
        | RzQGateSet.RzQGateSet.URzQ_CNOT ->
          let qs' =
            if FSet.mem m qs
            then if FSet.mem n qs then FSet.remove n qs else FSet.add n qs
            else qs
          in
          not_propagation' t0 ((RzQGateSet.coq_CNOT m n) :: acc) qs'
        | _ -> acc)
     | App3 (_, _, _, _) -> acc)

(** val not_propagation :
    RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list **)

let not_propagation l =
  not_propagation' l [] FSet.empty
