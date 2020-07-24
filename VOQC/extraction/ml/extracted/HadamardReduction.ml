open UnitaryListRepresentation

(** val apply_H_equivalence1 :
    int -> RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_list option **)

let apply_H_equivalence1 q l =
  RzQGateSet.replace_pattern l
    ((RzQGateSet.coq_H q) :: ((RzQGateSet.coq_P q) :: ((RzQGateSet.coq_H q) :: [])))
    ((RzQGateSet.coq_PDAG q) :: ((RzQGateSet.coq_H q) :: ((RzQGateSet.coq_PDAG
                                                            q) :: [])))

(** val apply_H_equivalence2 :
    int -> RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_list option **)

let apply_H_equivalence2 q l =
  RzQGateSet.replace_pattern l
    ((RzQGateSet.coq_H q) :: ((RzQGateSet.coq_PDAG q) :: ((RzQGateSet.coq_H q) :: [])))
    ((RzQGateSet.coq_P q) :: ((RzQGateSet.coq_H q) :: ((RzQGateSet.coq_P q) :: [])))

(** val apply_H_equivalence3 :
    int -> RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list option **)

let apply_H_equivalence3 q l =
  match next_single_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (l1, r) = p0 in
    (match r with
     | RzQGateSet.RzQGateSet.URzQ_H ->
       let l0 = List.append l1 l2 in
       (match next_two_qubit_gate l0 q with
        | Some p1 ->
          let (p2, l3) = p1 in
          let (p3, n) = p2 in
          let (p4, m) = p3 in
          let (l4, r0) = p4 in
          (match r0 with
           | RzQGateSet.RzQGateSet.URzQ_CNOT ->
             if (=) q m
             then (match last_single_qubit_gate l4 n with
                   | Some p5 ->
                     let (p6, l1_2) = p5 in
                     let (l1_1, r1) = p6 in
                     (match r1 with
                      | RzQGateSet.RzQGateSet.URzQ_H ->
                        let l5 = List.append l1_1 l1_2 in
                        (match next_single_qubit_gate l3 q with
                         | Some p7 ->
                           let (p8, l2_2) = p7 in
                           let (l2_1, r2) = p8 in
                           (match r2 with
                            | RzQGateSet.RzQGateSet.URzQ_H ->
                              let l6 = List.append l2_1 l2_2 in
                              (match next_single_qubit_gate l6 n with
                               | Some p9 ->
                                 let (p10, l2_3) = p9 in
                                 let (l2_4, r3) = p10 in
                                 (match r3 with
                                  | RzQGateSet.RzQGateSet.URzQ_H ->
                                    let l7 = List.append l2_4 l2_3 in
                                    Some
                                    (List.append l5
                                      (List.append
                                        ((RzQGateSet.coq_CNOT n q) :: []) l7))
                                  | _ -> None)
                               | None -> None)
                            | _ -> None)
                         | None -> None)
                      | _ -> None)
                   | None -> None)
             else (match last_single_qubit_gate l4 m with
                   | Some p5 ->
                     let (p6, l1_2) = p5 in
                     let (l1_1, r1) = p6 in
                     (match r1 with
                      | RzQGateSet.RzQGateSet.URzQ_H ->
                        let l5 = List.append l1_1 l1_2 in
                        (match next_single_qubit_gate l3 q with
                         | Some p7 ->
                           let (p8, l2_2) = p7 in
                           let (l2_1, r2) = p8 in
                           (match r2 with
                            | RzQGateSet.RzQGateSet.URzQ_H ->
                              let l6 = List.append l2_1 l2_2 in
                              (match next_single_qubit_gate l6 m with
                               | Some p9 ->
                                 let (p10, l2_3) = p9 in
                                 let (l2_4, r3) = p10 in
                                 (match r3 with
                                  | RzQGateSet.RzQGateSet.URzQ_H ->
                                    let l7 = List.append l2_4 l2_3 in
                                    Some
                                    (List.append l5
                                      (List.append
                                        ((RzQGateSet.coq_CNOT q m) :: []) l7))
                                  | _ -> None)
                               | None -> None)
                            | _ -> None)
                         | None -> None)
                      | _ -> None)
                   | None -> None)
           | _ -> None)
        | None -> None)
     | _ -> None)
  | None -> None

(** val apply_H_equivalence4 :
    int -> RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list option **)

let apply_H_equivalence4 q l =
  match RzQGateSet.remove_prefix l
          ((RzQGateSet.coq_H q) :: ((RzQGateSet.coq_P q) :: [])) with
  | Some l1 ->
    (match next_two_qubit_gate l1 q with
     | Some p ->
       let (p0, l3) = p in
       let (p1, q2) = p0 in
       let (p2, q1) = p1 in
       let (l2, r) = p2 in
       (match r with
        | RzQGateSet.RzQGateSet.URzQ_CNOT ->
          if (=) q q2
          then (match RzQGateSet.remove_prefix l3
                        ((RzQGateSet.coq_PDAG q) :: ((RzQGateSet.coq_H q) :: [])) with
                | Some l4 ->
                  Some
                    (List.append l2
                      (List.append
                        ((RzQGateSet.coq_PDAG q2) :: ((RzQGateSet.coq_CNOT q1
                                                        q2) :: ((RzQGateSet.coq_P
                                                                  q2) :: [])))
                        l4))
                | None -> None)
          else None
        | _ -> None)
     | None -> None)
  | None -> None

(** val apply_H_equivalence5 :
    int -> RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list option **)

let apply_H_equivalence5 q l =
  match RzQGateSet.remove_prefix l
          ((RzQGateSet.coq_H q) :: ((RzQGateSet.coq_PDAG q) :: [])) with
  | Some l1 ->
    (match next_two_qubit_gate l1 q with
     | Some p ->
       let (p0, l3) = p in
       let (p1, q2) = p0 in
       let (p2, q1) = p1 in
       let (l2, r) = p2 in
       (match r with
        | RzQGateSet.RzQGateSet.URzQ_CNOT ->
          if (=) q q2
          then (match RzQGateSet.remove_prefix l3
                        ((RzQGateSet.coq_P q) :: ((RzQGateSet.coq_H q) :: [])) with
                | Some l4 ->
                  Some
                    (List.append l2
                      (List.append
                        ((RzQGateSet.coq_P q2) :: ((RzQGateSet.coq_CNOT q1 q2) :: (
                        (RzQGateSet.coq_PDAG q2) :: []))) l4))
                | None -> None)
          else None
        | _ -> None)
     | None -> None)
  | None -> None

(** val apply_H_equivalence :
    RzQGateSet.coq_RzQ_ucom_l -> int -> RzQGateSet.coq_RzQ_ucom_l option **)

let apply_H_equivalence l q =
  try_rewrites l
    ((apply_H_equivalence1 q) :: ((apply_H_equivalence2 q) :: ((apply_H_equivalence3
                                                                 q) :: (
    (apply_H_equivalence4 q) :: ((apply_H_equivalence5 q) :: [])))))

(** val apply_H_equivalences' :
    RzQGateSet.coq_RzQ_ucom_l -> int -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list -> RzQGateSet.coq_RzQ_ucom_l **)

let rec apply_H_equivalences' l n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> List.rev_append acc l)
    (fun n' ->
    match l with
    | [] -> List.rev_append acc []
    | g :: t ->
      (match g with
       | App1 (r, q) ->
         (match r with
          | RzQGateSet.RzQGateSet.URzQ_H ->
            (match apply_H_equivalence l q with
             | Some l' -> apply_H_equivalences' l' n' acc
             | None ->
               apply_H_equivalences' t n' ((RzQGateSet.coq_H q) :: acc))
          | _ -> apply_H_equivalences' t n' (g :: acc))
       | _ -> apply_H_equivalences' t n' (g :: acc)))
    n

(** val hadamard_reduction :
    RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.coq_RzQ_ucom_l **)

let hadamard_reduction l =
  apply_H_equivalences' l
    (( * ) (Pervasives.succ (Pervasives.succ 0)) (List.length l)) []
