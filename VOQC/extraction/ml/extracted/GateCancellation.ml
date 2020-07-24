open UnitaryListRepresentation

(** val coq_Rz_commute_rule1 :
    int -> RzQGateSet.coq_RzQ_ucom_l ->
    (RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app
    list * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_list) option **)

let coq_Rz_commute_rule1 q l =
  match next_single_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (l1, r) = p0 in
    (match r with
     | RzQGateSet.RzQGateSet.URzQ_H ->
       (match next_two_qubit_gate l2 q with
        | Some p1 ->
          let (p2, l4) = p1 in
          let (p3, q2) = p2 in
          let (p4, q1) = p3 in
          let (l3, r0) = p4 in
          (match r0 with
           | RzQGateSet.RzQGateSet.URzQ_CNOT ->
             if (=) q q2
             then (match next_single_qubit_gate l4 q with
                   | Some p5 ->
                     let (p6, l6) = p5 in
                     let (l5, r1) = p6 in
                     (match r1 with
                      | RzQGateSet.RzQGateSet.URzQ_H ->
                        Some
                          ((List.append l1
                             (List.append ((RzQGateSet.coq_H q) :: [])
                               (List.append l3
                                 (List.append
                                   ((RzQGateSet.coq_CNOT q1 q) :: [])
                                   (List.append l5
                                     ((RzQGateSet.coq_H q) :: [])))))), l6)
                      | _ -> None)
                   | None -> None)
             else None
           | _ -> None)
        | None -> None)
     | _ -> None)
  | None -> None

(** val coq_Rz_commute_rule2 :
    int -> RzQGateSet.coq_RzQ_ucom_l ->
    (RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app
    list * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_list) option **)

let coq_Rz_commute_rule2 q l =
  match next_two_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2) = p0 in
    let (p2, q1) = p1 in
    let (l1, r) = p2 in
    (match r with
     | RzQGateSet.RzQGateSet.URzQ_CNOT ->
       if (=) q q2
       then (match next_single_qubit_gate l2 q with
             | Some p3 ->
               let (p4, l4) = p3 in
               let (l3, u) = p4 in
               (match u with
                | RzQGateSet.RzQGateSet.URzQ_Rz _ ->
                  (match next_two_qubit_gate l4 q with
                   | Some p5 ->
                     let (p6, l6) = p5 in
                     let (p7, q4) = p6 in
                     let (p8, q3) = p7 in
                     let (l5, r0) = p8 in
                     (match r0 with
                      | RzQGateSet.RzQGateSet.URzQ_CNOT ->
                        if (&&) ((&&) ((=) q q4) ((=) q1 q3))
                             (does_not_reference (List.append l3 l5) q3)
                        then Some
                               ((List.append l1
                                  (List.append
                                    ((RzQGateSet.coq_CNOT q1 q) :: [])
                                    (List.append l3
                                      (List.append ((App1 (u, q)) :: [])
                                        (List.append l5
                                          ((RzQGateSet.coq_CNOT q1 q) :: [])))))),
                               l6)
                        else None
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | None -> None)
       else None
     | _ -> None)
  | None -> None

(** val coq_Rz_commute_rule3 :
    int -> RzQGateSet.coq_RzQ_ucom_l ->
    (RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app
    list * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_list) option **)

let coq_Rz_commute_rule3 q l =
  match next_two_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2) = p0 in
    let (p2, q1) = p1 in
    let (l1, r) = p2 in
    (match r with
     | RzQGateSet.RzQGateSet.URzQ_CNOT ->
       if (=) q q1
       then Some ((List.append l1 ((RzQGateSet.coq_CNOT q1 q2) :: [])), l2)
       else None
     | _ -> None)
  | None -> None

(** val coq_Rz_commute_rules :
    int -> (RzQGateSet.coq_RzQ_ucom_l ->
    (RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app
    list * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_list) option) list **)

let coq_Rz_commute_rules q =
  (coq_Rz_commute_rule1 q) :: ((coq_Rz_commute_rule2 q) :: ((coq_Rz_commute_rule3
                                                              q) :: []))

(** val coq_Rz_cancel_rule :
    int -> Q.t -> RzQGateSet.coq_RzQ_ucom_l ->
    RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app list option **)

let coq_Rz_cancel_rule q a l =
  match next_single_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (l1, r) = p0 in
    (match r with
     | RzQGateSet.RzQGateSet.URzQ_Rz a' ->
       Some
         (List.append (RzQGateSet.combine_rotations a a' q)
           (List.append l1 l2))
     | _ -> None)
  | None -> None

(** val coq_H_cancel_rule :
    int -> RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list option **)

let coq_H_cancel_rule q l =
  match next_single_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (l1, r) = p0 in
    (match r with
     | RzQGateSet.RzQGateSet.URzQ_H -> Some (List.append l1 l2)
     | _ -> None)
  | None -> None

(** val coq_X_commute_rule :
    int -> RzQGateSet.coq_RzQ_ucom_l ->
    (RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app
    list * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_list) option **)

let coq_X_commute_rule q l =
  match next_two_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2) = p0 in
    let (p2, q1) = p1 in
    let (l1, r) = p2 in
    (match r with
     | RzQGateSet.RzQGateSet.URzQ_CNOT ->
       if (=) q q2
       then Some ((List.append l1 ((RzQGateSet.coq_CNOT q1 q2) :: [])), l2)
       else None
     | _ -> None)
  | None -> None

(** val coq_X_cancel_rule :
    int -> RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list option **)

let coq_X_cancel_rule q l =
  match next_single_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (l1, r) = p0 in
    (match r with
     | RzQGateSet.RzQGateSet.URzQ_X -> Some (List.append l1 l2)
     | _ -> None)
  | None -> None

(** val coq_CNOT_commute_rule1 :
    int -> RzQGateSet.coq_RzQ_ucom_l ->
    (RzQGateSet.coq_RzQ_ucom_l * RzQGateSet.coq_RzQ_ucom_l) option **)

let coq_CNOT_commute_rule1 q1 l =
  match next_single_qubit_gate l q1 with
  | Some p ->
    let (p0, l2) = p in
    let (l1, u) = p0 in
    (match u with
     | RzQGateSet.RzQGateSet.URzQ_Rz _ ->
       Some (((App1 (u, q1)) :: []), (List.append l1 l2))
     | _ -> None)
  | None -> None

(** val coq_CNOT_commute_rule2 :
    int -> int -> RzQGateSet.coq_RzQ_ucom_l ->
    (RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app
    list * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_list) option **)

let coq_CNOT_commute_rule2 q1 q2 l =
  match next_two_qubit_gate l q2 with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2') = p0 in
    let (p2, q1') = p1 in
    let (l1, r) = p2 in
    (match r with
     | RzQGateSet.RzQGateSet.URzQ_CNOT ->
       if (=) q2 q2'
       then if does_not_reference l1 q1
            then Some ((List.append l1 ((RzQGateSet.coq_CNOT q1' q2) :: [])),
                   l2)
            else None
       else None
     | _ -> None)
  | None -> None

(** val coq_CNOT_commute_rule3 :
    int -> int -> RzQGateSet.coq_RzQ_ucom_l ->
    (RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app
    list * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_list) option **)

let coq_CNOT_commute_rule3 q1 q2 l =
  match next_two_qubit_gate l q1 with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2') = p0 in
    let (p2, q1') = p1 in
    let (l1, r) = p2 in
    (match r with
     | RzQGateSet.RzQGateSet.URzQ_CNOT ->
       if (=) q1 q1'
       then if does_not_reference l1 q2
            then Some ((List.append l1 ((RzQGateSet.coq_CNOT q1 q2') :: [])),
                   l2)
            else None
       else None
     | _ -> None)
  | None -> None

(** val coq_CNOT_commute_rule4 :
    int -> int -> RzQGateSet.coq_RzQ_ucom_l ->
    (RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app
    list * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app list) option **)

let coq_CNOT_commute_rule4 q1 q2 l =
  match next_single_qubit_gate l q2 with
  | Some p ->
    let (p0, l2) = p in
    let (l1, r) = p0 in
    (match r with
     | RzQGateSet.RzQGateSet.URzQ_H ->
       (match next_two_qubit_gate l2 q2 with
        | Some p1 ->
          let (p2, l4) = p1 in
          let (p3, q2') = p2 in
          let (p4, q1') = p3 in
          let (l3, r0) = p4 in
          (match r0 with
           | RzQGateSet.RzQGateSet.URzQ_CNOT ->
             if (&&) ((&&) ((=) q2 q1') (not ((=) q1 q2')))
                  (does_not_reference (List.append l1 l3) q1)
             then (match next_single_qubit_gate l4 q2 with
                   | Some p5 ->
                     let (p6, l6) = p5 in
                     let (l5, r1) = p6 in
                     (match r1 with
                      | RzQGateSet.RzQGateSet.URzQ_H ->
                        Some
                          ((List.append l1
                             (List.append ((RzQGateSet.coq_H q2) :: [])
                               (List.append l3
                                 (List.append
                                   ((RzQGateSet.coq_CNOT q2 q2') :: [])
                                   ((RzQGateSet.coq_H q2) :: []))))),
                          (List.append l5 l6))
                      | _ -> None)
                   | None -> None)
             else None
           | _ -> None)
        | None -> None)
     | _ -> None)
  | None -> None

(** val coq_CNOT_commute_rule5 :
    int -> int -> RzQGateSet.coq_RzQ_ucom_l ->
    (RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app
    list * RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app list) option **)

let coq_CNOT_commute_rule5 q1 q2 l =
  match next_single_qubit_gate l q2 with
  | Some p ->
    let (p0, l2) = p in
    let (l1, u) = p0 in
    (match u with
     | RzQGateSet.RzQGateSet.URzQ_Rz _ ->
       (match next_two_qubit_gate l2 q2 with
        | Some p1 ->
          let (p2, l4) = p1 in
          let (p3, q2') = p2 in
          let (p4, q1') = p3 in
          let (l3, r) = p4 in
          (match r with
           | RzQGateSet.RzQGateSet.URzQ_CNOT ->
             if (&&) ((&&) ((=) q1 q1') ((=) q2 q2'))
                  (does_not_reference (List.append l1 l3) q1)
             then (match next_single_qubit_gate l4 q2 with
                   | Some p5 ->
                     let (p6, l6) = p5 in
                     let (l5, u') = p6 in
                     (match u' with
                      | RzQGateSet.RzQGateSet.URzQ_Rz _ ->
                        Some
                          ((List.append l1
                             (List.append ((App1 (u', q2)) :: [])
                               (List.append l3
                                 (List.append
                                   ((RzQGateSet.coq_CNOT q1' q2') :: [])
                                   ((App1 (u, q2)) :: []))))),
                          (List.append l5 l6))
                      | _ -> None)
                   | None -> None)
             else None
           | _ -> None)
        | None -> None)
     | _ -> None)
  | None -> None

(** val coq_CNOT_commute_rules :
    int -> int -> (RzQGateSet.coq_RzQ_ucom_l ->
    (RzQGateSet.coq_RzQ_ucom_l * RzQGateSet.coq_RzQ_ucom_l) option) list **)

let coq_CNOT_commute_rules q1 q2 =
  (coq_CNOT_commute_rule1 q1) :: ((coq_CNOT_commute_rule2 q1 q2) :: (
    (coq_CNOT_commute_rule3 q1 q2) :: ((coq_CNOT_commute_rule4 q1 q2) :: (
    (coq_CNOT_commute_rule5 q1 q2) :: []))))

(** val coq_CNOT_cancel_rule :
    int -> int -> RzQGateSet.coq_RzQ_ucom_l ->
    RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app list option **)

let coq_CNOT_cancel_rule q1 q2 l =
  match next_two_qubit_gate l q1 with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2') = p0 in
    let (p2, q1') = p1 in
    let (l1, r) = p2 in
    (match r with
     | RzQGateSet.RzQGateSet.URzQ_CNOT ->
       if (&&) ((&&) ((=) q1 q1') ((=) q2 q2')) (does_not_reference l1 q2)
       then Some (List.append l1 l2)
       else None
     | _ -> None)
  | None -> None

(** val propagate_Rz :
    Q.t -> RzQGateSet.coq_RzQ_ucom_l -> int ->
    RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app list option **)

let propagate_Rz a l q =
  propagate l (coq_Rz_commute_rules q) ((coq_Rz_cancel_rule q a) :: [])
    (List.length l)

(** val propagate_H :
    RzQGateSet.coq_RzQ_ucom_l -> int -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list option **)

let propagate_H l q =
  propagate l [] ((coq_H_cancel_rule q) :: []) (Pervasives.succ 0)

(** val propagate_X :
    RzQGateSet.coq_RzQ_ucom_l -> int -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list option **)

let propagate_X l q =
  propagate l ((coq_X_commute_rule q) :: []) ((coq_X_cancel_rule q) :: [])
    (List.length l)

(** val propagate_CNOT :
    RzQGateSet.coq_RzQ_ucom_l -> int -> int ->
    RzQGateSet.RzQGateSet.coq_RzQ_Unitary gate_app list option **)

let propagate_CNOT l q1 q2 =
  propagate l (coq_CNOT_commute_rules q1 q2)
    ((coq_CNOT_cancel_rule q1 q2) :: []) (List.length l)

(** val cancel_single_qubit_gates' :
    RzQGateSet.coq_RzQ_ucom_l -> int -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list -> RzQGateSet.coq_RzQ_ucom_l **)

let rec cancel_single_qubit_gates' l n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> List.rev_append acc l)
    (fun n' ->
    match l with
    | [] -> List.rev_append acc []
    | u :: t ->
      (match u with
       | App1 (r, q) ->
         (match r with
          | RzQGateSet.RzQGateSet.URzQ_H ->
            (match propagate_H t q with
             | Some l' -> cancel_single_qubit_gates' l' n' acc
             | None ->
               cancel_single_qubit_gates' t n' ((RzQGateSet.coq_H q) :: acc))
          | RzQGateSet.RzQGateSet.URzQ_X ->
            (match propagate_X t q with
             | Some l' -> cancel_single_qubit_gates' l' n' acc
             | None ->
               cancel_single_qubit_gates' t n' ((RzQGateSet.coq_X q) :: acc))
          | RzQGateSet.RzQGateSet.URzQ_Rz a ->
            (match propagate_Rz a t q with
             | Some l' -> cancel_single_qubit_gates' l' n' acc
             | None ->
               cancel_single_qubit_gates' t n'
                 ((RzQGateSet.coq_Rz a q) :: acc))
          | RzQGateSet.RzQGateSet.URzQ_CNOT ->
            cancel_single_qubit_gates' t n' (u :: acc))
       | _ -> cancel_single_qubit_gates' t n' (u :: acc)))
    n

(** val cancel_single_qubit_gates :
    RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.coq_RzQ_ucom_l **)

let cancel_single_qubit_gates l =
  cancel_single_qubit_gates' l (List.length l) []

(** val cancel_two_qubit_gates' :
    RzQGateSet.coq_RzQ_ucom_l -> int -> RzQGateSet.RzQGateSet.coq_RzQ_Unitary
    gate_app list -> RzQGateSet.coq_RzQ_ucom_l **)

let rec cancel_two_qubit_gates' l n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> List.rev_append acc l)
    (fun n' ->
    match l with
    | [] -> List.rev_append acc []
    | u :: t ->
      (match u with
       | App2 (r, q1, q2) ->
         (match r with
          | RzQGateSet.RzQGateSet.URzQ_CNOT ->
            (match propagate_CNOT t q1 q2 with
             | Some l' -> cancel_two_qubit_gates' l' n' acc
             | None ->
               cancel_two_qubit_gates' t n'
                 ((RzQGateSet.coq_CNOT q1 q2) :: acc))
          | _ -> cancel_two_qubit_gates' t n' (u :: acc))
       | _ -> cancel_two_qubit_gates' t n' (u :: acc)))
    n

(** val cancel_two_qubit_gates :
    RzQGateSet.coq_RzQ_ucom_l -> RzQGateSet.coq_RzQ_ucom_l **)

let cancel_two_qubit_gates l =
  cancel_two_qubit_gates' l (List.length l) []
