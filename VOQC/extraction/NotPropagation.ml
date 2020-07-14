open UnitaryListRepresentation
open RzQGateSet.RzQGateSet

(** val propagate_X :
    RzQGateSet.coq_RzQ_ucom_l -> int -> int ->
    RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app list ->
    RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app list **)


let rec propagate_X l q n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> List.rev_append acc ((RzQGateSet.coq_X q) :: l))
    (fun n' ->
    match l with
    | [] -> List.rev_append acc ((RzQGateSet.coq_X q) :: [])
    | u :: t ->
      if does_not_reference_appl q u
      then propagate_X t q n' (u :: acc)
      else (match u with
            | App1 (r, n0) ->
              (match r with
               | RzQGateSet.RzQGateSet.URzQ_H ->
                 List.rev_append acc (u :: ((RzQGateSet.coq_Z q) :: t))
               | RzQGateSet.RzQGateSet.URzQ_X -> List.rev_append acc t
               | RzQGateSet.RzQGateSet.URzQ_Rz a ->
                 propagate_X t q n' ((RzQGateSet.invert_rotation a n0) :: acc)
               | RzQGateSet.RzQGateSet.URzQ_CNOT ->
                 List.rev_append acc ((RzQGateSet.coq_X q) :: l))
            | App2 (r, m, n0) ->
              (match r with
               | RzQGateSet.RzQGateSet.URzQ_CNOT ->
                 if (=) q m
                 then let t' = propagate_X t n0 n' [] in
                      propagate_X t' m n' (u :: acc)
                 else propagate_X t q n' (u :: acc)
               | _ -> List.rev_append acc ((RzQGateSet.coq_X q) :: l))
            | App3 (_, _, _, _) ->
              List.rev_append acc ((RzQGateSet.coq_X q) :: l)))
    n

(** val not_propagation' :
    RzQGateSet.coq_RzQ_ucom_l -> int -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app list **)

let rec not_propagation' l n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> List.rev_append acc l)
    (fun n' ->
    match l with
    | [] -> List.rev_append acc []
    | u :: t ->
      (match u with
       | App1 (r, q) ->
         (match r with
          | RzQGateSet.RzQGateSet.URzQ_X ->
            not_propagation' (propagate_X t q n []) n' acc
          | _ -> not_propagation' t n' (u :: acc))
       | _ -> not_propagation' t n' (u :: acc)))
    n

(** val not_propagation :
    RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list **)

let not_propagation l =
  not_propagation' l
    (( * ) (Pervasives.succ (Pervasives.succ 0)) (List.length l)) []
