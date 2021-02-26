open UnitaryListRepresentation

(** val cx_cancellation' :
    IBMGateSet.coq_IBM_ucom_l -> int -> IBMGateSet.IBMGateSet.coq_IBM_Unitary
    gate_app list -> IBMGateSet.coq_IBM_ucom_l **)

let rec cx_cancellation' l n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> List.rev_append acc l)
    (fun n' ->
    match l with
    | [] -> List.rev_append acc []
    | g :: t ->
      (match g with
       | App2 (_, q1, q2) ->
         (match next_two_qubit_gate t q1 with
          | Some p ->
            let (p0, l2) = p in
            let (p1, q2') = p0 in
            let (p2, q1') = p1 in
            let (l1, _) = p2 in
            if (&&) ((&&) ((=) q1 q1') ((=) q2 q2'))
                 (does_not_reference l1 q2)
            then cx_cancellation' (List.append l1 l2) n' acc
            else cx_cancellation' t n' (g :: acc)
          | None -> cx_cancellation' t n' (g :: acc))
       | _ -> cx_cancellation' t n' (g :: acc)))
    n

(** val cx_cancellation :
    IBMGateSet.coq_IBM_ucom_l -> IBMGateSet.coq_IBM_ucom_l **)

let cx_cancellation l =
  cx_cancellation' l (List.length l) []
