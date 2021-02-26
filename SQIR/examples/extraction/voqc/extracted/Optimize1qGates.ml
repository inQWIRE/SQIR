open UnitaryListRepresentation

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val optimize_1q_gates' :
    IBMGateSet.coq_IBM_ucom_l -> int -> IBMGateSet.IBMGateSet.coq_IBM_Unitary
    gate_app list -> IBMGateSet.coq_IBM_ucom_l **)

let rec optimize_1q_gates' l n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> List.rev_append acc l)
    (fun n' ->
    match l with
    | [] -> List.rev_append acc []
    | g :: t ->
      (match g with
       | App1 (u, q) ->
         (match next_single_qubit_gate t q with
          | Some p ->
            let (p0, l2) = p in
            let (l1, u') = p0 in
            let unew =
              match u with
              | IBMGateSet.IBMGateSet.UIBM_U1 a ->
                (match u' with
                 | IBMGateSet.IBMGateSet.UIBM_U1 a' ->
                   IBMGateSet.IBMGateSet.UIBM_U1 (( +. ) a' a)
                 | IBMGateSet.IBMGateSet.UIBM_U2 (a', b) ->
                   IBMGateSet.IBMGateSet.UIBM_U2 (a', (( +. ) a b))
                 | IBMGateSet.IBMGateSet.UIBM_U3 (a', b, c) ->
                   IBMGateSet.IBMGateSet.UIBM_U3 (a', b, (( +. ) a c))
                 | IBMGateSet.IBMGateSet.UIBM_CNOT -> Obj.magic __)
              | IBMGateSet.IBMGateSet.UIBM_U2 (a, b) ->
                (match u' with
                 | IBMGateSet.IBMGateSet.UIBM_U1 a' ->
                   IBMGateSet.IBMGateSet.UIBM_U2 ((( +. ) a a'), b)
                 | IBMGateSet.IBMGateSet.UIBM_U2 (a', b') ->
                   IBMGateSet.IBMGateSet.UIBM_U3
                     ((( -. ) Float.pi (( +. ) a b')),
                     (( +. ) a'
                       (( /. ) Float.pi (Float.of_int ((fun p->2*p) 1)))),
                     (( +. ) b
                       (( /. ) Float.pi (Float.of_int ((fun p->2*p) 1)))))
                 | IBMGateSet.IBMGateSet.UIBM_U3 (a', b', c) ->
                   IBMGateSet.compose_u3
                     (( /. ) Float.pi (Float.of_int ((fun p->2*p) 1))) a b a'
                     b' c
                 | IBMGateSet.IBMGateSet.UIBM_CNOT -> Obj.magic __)
              | IBMGateSet.IBMGateSet.UIBM_U3 (a, b, c) ->
                (match u' with
                 | IBMGateSet.IBMGateSet.UIBM_U1 a' ->
                   IBMGateSet.IBMGateSet.UIBM_U3 (a, (( +. ) b a'), c)
                 | IBMGateSet.IBMGateSet.UIBM_U2 (a', b') ->
                   IBMGateSet.compose_u3 a b c
                     (( /. ) Float.pi (Float.of_int ((fun p->2*p) 1))) a' b'
                 | IBMGateSet.IBMGateSet.UIBM_U3 (a', b', c') ->
                   IBMGateSet.compose_u3 a b c a' b' c'
                 | IBMGateSet.IBMGateSet.UIBM_CNOT -> Obj.magic __)
              | IBMGateSet.IBMGateSet.UIBM_CNOT -> Obj.magic __
            in
            optimize_1q_gates' (List.append l1 l2) n' ((App1 (unew,
              q)) :: acc)
          | None -> optimize_1q_gates' t n' ((App1 (u, q)) :: acc))
       | _ -> optimize_1q_gates' t n' (g :: acc)))
    n

(** val simplify_1q_gates :
    IBMGateSet.coq_IBM_ucom_l -> IBMGateSet.IBMGateSet.coq_IBM_Unitary
    gate_app list -> IBMGateSet.coq_IBM_ucom_l **)

let rec simplify_1q_gates l acc =
  match l with
  | [] -> List.rev_append acc []
  | g :: t ->
    (match g with
     | App1 (i, q) ->
       (match i with
        | IBMGateSet.IBMGateSet.UIBM_U1 a ->
          if ( = ) (cos a) (Float.of_int 1)
          then simplify_1q_gates t acc
          else simplify_1q_gates t ((IBMGateSet.coq_U1 a q) :: acc)
        | IBMGateSet.IBMGateSet.UIBM_U3 (a, b, c) ->
          if ( = ) (cos a) (Float.of_int 1)
          then if ( = ) (cos (( +. ) b c)) (Float.of_int 1)
               then simplify_1q_gates t acc
               else simplify_1q_gates t
                      ((IBMGateSet.coq_U1 (( +. ) b c) q) :: acc)
          else if ( = ) (sin a) (Float.of_int 1)
               then simplify_1q_gates t ((IBMGateSet.coq_U2 b c q) :: acc)
               else if ( = ) (sin a) (Float.of_int ((~-) 1))
                    then simplify_1q_gates t
                           ((IBMGateSet.coq_U2 (( +. ) b Float.pi)
                              (( -. ) c Float.pi) q) :: acc)
                    else simplify_1q_gates t
                           ((IBMGateSet.coq_U3 a b c q) :: acc)
        | _ -> simplify_1q_gates t (g :: acc))
     | _ -> simplify_1q_gates t (g :: acc))

(** val optimize_1q_gates :
    IBMGateSet.coq_IBM_ucom_l -> IBMGateSet.coq_IBM_ucom_l **)

let optimize_1q_gates l =
  let l' = optimize_1q_gates' l (List.length l) [] in simplify_1q_gates l' []
