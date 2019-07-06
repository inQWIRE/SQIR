
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val length : 'a1 list -> int **)

let rec length = List.length

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app = List.append

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

module Nat =
 struct
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = List.rev

type fUnitary =
| FU_H
| FU_X
| FU_Z
| FU_P
| FU_PDAG
| FU_T
| FU_TDAG
| FU_CNOT

(** val match_gate : fUnitary -> fUnitary -> bool **)

let match_gate u u' =
  match u with
  | FU_H -> (match u' with
             | FU_H -> true
             | _ -> false)
  | FU_X -> (match u' with
             | FU_X -> true
             | _ -> false)
  | FU_Z -> (match u' with
             | FU_Z -> true
             | _ -> false)
  | FU_P -> (match u' with
             | FU_P -> true
             | _ -> false)
  | FU_PDAG -> (match u' with
                | FU_PDAG -> true
                | _ -> false)
  | FU_T -> (match u' with
             | FU_T -> true
             | _ -> false)
  | FU_TDAG -> (match u' with
                | FU_TDAG -> true
                | _ -> false)
  | FU_CNOT -> (match u' with
                | FU_CNOT -> true
                | _ -> false)

type gate_app =
| App1 of fUnitary * int
| App2 of fUnitary * int * int

(** val _H : int -> gate_app **)

let _H n =
  App1 (FU_H, n)

(** val _X : int -> gate_app **)

let _X n =
  App1 (FU_X, n)

(** val _Z : int -> gate_app **)

let _Z n =
  App1 (FU_Z, n)

(** val _P : int -> gate_app **)

let _P n =
  App1 (FU_P, n)

(** val _PDAG : int -> gate_app **)

let _PDAG n =
  App1 (FU_PDAG, n)

(** val _T : int -> gate_app **)

let _T n =
  App1 (FU_T, n)

(** val _TDAG : int -> gate_app **)

let _TDAG n =
  App1 (FU_TDAG, n)

(** val _CNOT : int -> int -> gate_app **)

let _CNOT m n =
  App2 (FU_CNOT, m, n)

type gate_list = gate_app list

(** val next_single_qubit_gate :
    gate_list -> int -> (fUnitary * gate_list) option **)

let rec next_single_qubit_gate l q =
  match l with
  | [] -> None
  | g :: t ->
    (match g with
     | App1 (u, n) ->
       if (=) n q
       then Some (u, t)
       else (match next_single_qubit_gate t q with
             | Some p -> let (u', l') = p in Some (u', ((App1 (u, n)) :: l'))
             | None -> None)
     | App2 (u, m, n) ->
       if (||) ((=) m q) ((=) n q)
       then None
       else (match next_single_qubit_gate t q with
             | Some p -> let (u', l') = p in Some (u', ((App2 (u, m, n)) :: l'))
             | None -> None))

(** val next_two_qubit_gate :
    gate_list -> int -> (((gate_list * int) * int) * gate_list) option **)

let rec next_two_qubit_gate l q =
  match l with
  | [] -> None
  | g :: t ->
    (match g with
     | App1 (u, n) ->
       if (=) n q
       then None
       else (match next_two_qubit_gate t q with
             | Some p ->
               let (p0, l2) = p in
               let (p1, n') = p0 in
               let (l1, m') = p1 in Some (((((App1 (u, n)) :: l1), m'), n'), l2)
             | None -> None)
     | App2 (u, m, n) ->
       if (||) ((=) m q) ((=) n q)
       then Some ((([], m), n), t)
       else (match next_two_qubit_gate t q with
             | Some p ->
               let (p0, l2) = p in
               let (p1, n') = p0 in
               let (l1, m') = p1 in Some (((((App2 (u, m, n)) :: l1), m'), n'), l2)
             | None -> None))

(** val does_not_reference : gate_list -> int -> bool **)

let rec does_not_reference l q =
  match l with
  | [] -> true
  | g :: t ->
    (match g with
     | App1 (_, n) -> (&&) (negb ((=) n q)) (does_not_reference t q)
     | App2 (_, m, n) ->
       (&&) (negb ((||) ((=) m q) ((=) n q))) (does_not_reference t q))

(** val count_H_gates : gate_list -> int **)

let rec count_H_gates = function
| [] -> 0
| _ :: t -> add (Pervasives.succ 0) (count_H_gates t)

(** val count_X_gates : gate_list -> int **)

let rec count_X_gates = function
| [] -> 0
| _ :: t -> add (Pervasives.succ 0) (count_X_gates t)

(** val count_rotation_gates : gate_list -> int **)

let rec count_rotation_gates = function
| [] -> 0
| _ :: t -> add (Pervasives.succ 0) (count_rotation_gates t)

(** val count_CNOT_gates : gate_list -> int **)

let rec count_CNOT_gates = function
| [] -> 0
| _ :: t -> add (Pervasives.succ 0) (count_CNOT_gates t)

type benchmark_gate_app =
| Bench_H of int
| Bench_X of int
| Bench_Z of int
| Bench_CNOT of int * int
| Bench_TOFF of int * int * int

(** val tOFF : int -> int -> int -> gate_list **)

let tOFF a b c =
  (_H c) :: ((_CNOT b c) :: ((_TDAG c) :: ((_CNOT a c) :: ((_T c) :: ((_CNOT b c) :: (
    (_TDAG c) :: ((_CNOT a c) :: ((_CNOT a b) :: ((_TDAG b) :: ((_CNOT a b) :: (
    (_T a) :: ((_T b) :: ((_T c) :: ((_H c) :: []))))))))))))))

(** val benchmark_to_list : benchmark_gate_app list -> gate_list **)

let rec benchmark_to_list = function
| [] -> []
| b :: t ->
  (match b with
   | Bench_H n -> (App1 (FU_H, n)) :: (benchmark_to_list t)
   | Bench_X n -> (App1 (FU_X, n)) :: (benchmark_to_list t)
   | Bench_Z n -> (App1 (FU_Z, n)) :: (benchmark_to_list t)
   | Bench_CNOT (m, n) -> (App2 (FU_CNOT, m, n)) :: (benchmark_to_list t)
   | Bench_TOFF (m, n, p) -> app (tOFF m n p) (benchmark_to_list t))

(** val propagate_not : gate_list -> int -> gate_list option **)

let rec propagate_not l q =
  match l with
  | [] -> None
  | g :: t ->
    (match g with
     | App1 (u, q') ->
       (match u with
        | FU_X ->
          if (=) q q'
          then Some t
          else (match propagate_not t q with
                | Some l' -> Some ((_X q') :: l')
                | None -> None)
        | _ ->
          if (=) q q'
          then None
          else (match propagate_not t q with
                | Some l' -> Some ((App1 (u, q')) :: l')
                | None -> None))
     | App2 (f, q1, q2) ->
       (match f with
        | FU_CNOT ->
          if (=) q q1
          then None
          else (match propagate_not t q with
                | Some l' -> Some ((_CNOT q1 q2) :: l')
                | None -> None)
        | _ -> None))

(** val propagate_nots : gate_list -> int -> gate_list **)

let rec propagate_nots l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> l
    | h :: t ->
      (match h with
       | App1 (f, q) ->
         (match f with
          | FU_X ->
            (match propagate_not t q with
             | Some l' -> propagate_nots l' n'
             | None -> (App1 (FU_X, q)) :: (propagate_nots t n'))
          | _ -> h :: (propagate_nots t n'))
       | App2 (_, _, _) -> h :: (propagate_nots t n')))
    n

(** val rm_nots : gate_list -> gate_list **)

let rm_nots l =
  propagate_nots l (length l)

type single_qubit_pattern = fUnitary list

(** val single_qubit_pattern_to_program :
    single_qubit_pattern -> int -> gate_list **)

let rec single_qubit_pattern_to_program pat q =
  match pat with
  | [] -> []
  | u :: t -> (App1 (u, q)) :: (single_qubit_pattern_to_program t q)

(** val remove_single_qubit_pattern :
    gate_list -> int -> single_qubit_pattern -> gate_list option **)

let rec remove_single_qubit_pattern l q = function
| [] -> Some l
| u :: t ->
  (match next_single_qubit_gate l q with
   | Some p ->
     let (u', l') = p in
     if match_gate u u' then remove_single_qubit_pattern l' q t else None
   | None -> None)

(** val replace_single_qubit_pattern :
    gate_list -> int -> single_qubit_pattern -> single_qubit_pattern -> gate_list
    option **)

let replace_single_qubit_pattern l q pat rep =
  match remove_single_qubit_pattern l q pat with
  | Some l' -> Some (app (single_qubit_pattern_to_program rep q) l')
  | None -> None

(** val try_rewrites :
    gate_list -> (gate_list -> gate_list option) list -> gate_list option **)

let rec try_rewrites l = function
| [] -> None
| h :: t -> (match h l with
             | Some l' -> Some l'
             | None -> try_rewrites l t)

(** val apply_H_equivalence1 : int -> gate_list -> gate_list option **)

let apply_H_equivalence1 q l =
  replace_single_qubit_pattern l q (FU_H :: (FU_P :: (FU_H :: [])))
    (FU_PDAG :: (FU_H :: (FU_PDAG :: [])))

(** val apply_H_equivalence2 : int -> gate_list -> gate_list option **)

let apply_H_equivalence2 q l =
  replace_single_qubit_pattern l q (FU_H :: (FU_PDAG :: (FU_H :: [])))
    (FU_P :: (FU_H :: (FU_P :: [])))

(** val apply_H_equivalence3 : int -> gate_list -> gate_app list option **)

let apply_H_equivalence3 q l =
  match next_single_qubit_gate l q with
  | Some p ->
    let (f, l1) = p in
    (match f with
     | FU_H ->
       (match next_two_qubit_gate l1 q with
        | Some p0 ->
          let (p1, l3) = p0 in
          let (p2, n) = p1 in
          let (l2, m) = p2 in
          (match next_single_qubit_gate l3 q with
           | Some p3 ->
             let (f0, l4) = p3 in
             (match f0 with
              | FU_H ->
                if (=) q m
                then (match next_single_qubit_gate (rev l2) n with
                      | Some p4 ->
                        let (f1, l5) = p4 in
                        (match f1 with
                         | FU_H ->
                           (match next_single_qubit_gate l4 n with
                            | Some p5 ->
                              let (f2, l6) = p5 in
                              (match f2 with
                               | FU_H ->
                                 Some (app (rev l5) (app ((_CNOT n m) :: []) l6))
                               | _ -> None)
                            | None -> None)
                         | _ -> None)
                      | None -> None)
                else (match next_single_qubit_gate (rev l2) m with
                      | Some p4 ->
                        let (f1, l5) = p4 in
                        (match f1 with
                         | FU_H ->
                           (match next_single_qubit_gate l4 m with
                            | Some p5 ->
                              let (f2, l6) = p5 in
                              (match f2 with
                               | FU_H ->
                                 Some (app (rev l5) (app ((_CNOT n m) :: []) l6))
                               | _ -> None)
                            | None -> None)
                         | _ -> None)
                      | None -> None)
              | _ -> None)
           | None -> None)
        | None -> None)
     | _ -> None)
  | None -> None

(** val apply_H_equivalence4 : int -> gate_list -> gate_app list option **)

let apply_H_equivalence4 q l =
  match remove_single_qubit_pattern l q (FU_H :: (FU_P :: [])) with
  | Some l1 ->
    (match next_two_qubit_gate l1 q with
     | Some p ->
       let (p0, l3) = p in
       let (p1, q2) = p0 in
       let (l2, q1) = p1 in
       if (=) q q2
       then (match remove_single_qubit_pattern l3 q (FU_PDAG :: (FU_H :: [])) with
             | Some l4 ->
               Some
                 (app l2 (app ((_PDAG q2) :: ((_CNOT q1 q2) :: ((_P q2) :: []))) l4))
             | None -> None)
       else None
     | None -> None)
  | None -> None

(** val apply_H_equivalence5 : int -> gate_list -> gate_app list option **)

let apply_H_equivalence5 q l =
  match remove_single_qubit_pattern l q (FU_H :: (FU_PDAG :: [])) with
  | Some l1 ->
    (match next_two_qubit_gate l1 q with
     | Some p ->
       let (p0, l3) = p in
       let (p1, q2) = p0 in
       let (l2, q1) = p1 in
       if (=) q q2
       then (match remove_single_qubit_pattern l3 q (FU_P :: (FU_H :: [])) with
             | Some l4 ->
               Some
                 (app l2 (app ((_P q2) :: ((_CNOT q1 q2) :: ((_PDAG q2) :: []))) l4))
             | None -> None)
       else None
     | None -> None)
  | None -> None

(** val apply_H_equivalence : gate_list -> int -> gate_list option **)

let apply_H_equivalence l q =
  try_rewrites l
    ((apply_H_equivalence1 q) :: ((apply_H_equivalence2 q) :: ((apply_H_equivalence3
                                                                 q) :: ((apply_H_equivalence4
                                                                          q) :: (
    (apply_H_equivalence5 q) :: [])))))

(** val apply_H_equivalences : gate_list -> int -> gate_list **)

let rec apply_H_equivalences l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | g :: t ->
      (match g with
       | App1 (f, q) ->
         (match f with
          | FU_H ->
            (match apply_H_equivalence l q with
             | Some l' -> apply_H_equivalences l' n'
             | None -> (_H q) :: (apply_H_equivalences t n'))
          | _ -> g :: (apply_H_equivalences t n'))
       | App2 (_, _, _) -> g :: (apply_H_equivalences t n')))
    n

(** val hadamard_reduction : gate_list -> gate_list **)

let hadamard_reduction l =
  apply_H_equivalences l (mul (Pervasives.succ (Pervasives.succ 0)) (length l))

(** val cancel_gates_simple' : gate_list -> int -> gate_list **)

let rec cancel_gates_simple' l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | g :: t ->
      (match g with
       | App1 (f, q) ->
         (match f with
          | FU_H ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_H -> cancel_gates_simple' t' n'
                | _ -> (_H q) :: (cancel_gates_simple' t n'))
             | None -> (_H q) :: (cancel_gates_simple' t n'))
          | FU_X ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_X -> cancel_gates_simple' t' n'
                | _ -> (_X q) :: (cancel_gates_simple' t n'))
             | None -> (_X q) :: (cancel_gates_simple' t n'))
          | FU_Z ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_Z -> cancel_gates_simple' t' n'
                | FU_P -> cancel_gates_simple' ((_PDAG q) :: t') n'
                | FU_PDAG -> cancel_gates_simple' ((_P q) :: t') n'
                | _ -> (_Z q) :: (cancel_gates_simple' t n'))
             | None -> (_Z q) :: (cancel_gates_simple' t n'))
          | FU_P ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_Z -> cancel_gates_simple' ((_PDAG q) :: t') n'
                | FU_P -> cancel_gates_simple' ((_Z q) :: t') n'
                | FU_PDAG -> cancel_gates_simple' t' n'
                | FU_TDAG -> cancel_gates_simple' ((_T q) :: t') n'
                | _ -> (_P q) :: (cancel_gates_simple' t n'))
             | None -> (_P q) :: (cancel_gates_simple' t n'))
          | FU_PDAG ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_Z -> cancel_gates_simple' ((_P q) :: t') n'
                | FU_P -> cancel_gates_simple' t' n'
                | FU_PDAG -> cancel_gates_simple' ((_Z q) :: t') n'
                | FU_T -> cancel_gates_simple' ((_TDAG q) :: t') n'
                | _ -> (_PDAG q) :: (cancel_gates_simple' t n'))
             | None -> (_PDAG q) :: (cancel_gates_simple' t n'))
          | FU_T ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_PDAG -> cancel_gates_simple' ((_TDAG q) :: t') n'
                | FU_T -> cancel_gates_simple' ((_P q) :: t') n'
                | FU_TDAG -> cancel_gates_simple' t' n'
                | _ -> (_T q) :: (cancel_gates_simple' t n'))
             | None -> (_T q) :: (cancel_gates_simple' t n'))
          | FU_TDAG ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_P -> cancel_gates_simple' ((_T q) :: t') n'
                | FU_T -> cancel_gates_simple' t' n'
                | FU_TDAG -> cancel_gates_simple' ((_PDAG q) :: t') n'
                | _ -> (_TDAG q) :: (cancel_gates_simple' t n'))
             | None -> (_TDAG q) :: (cancel_gates_simple' t n'))
          | FU_CNOT -> [])
       | App2 (f, q1, q2) ->
         (match f with
          | FU_CNOT ->
            (match next_two_qubit_gate t q1 with
             | Some p ->
               let (p0, l2) = p in
               let (p1, q2') = p0 in
               let (l1, q1') = p1 in
               if (&&) ((&&) ((=) q1 q1') ((=) q2 q2')) (does_not_reference l1 q2)
               then cancel_gates_simple' (app l1 l2) n'
               else (_CNOT q1 q2) :: (cancel_gates_simple' t n')
             | None -> (_CNOT q1 q2) :: (cancel_gates_simple' t n'))
          | _ -> [])))
    n

(** val cancel_gates_simple : gate_list -> gate_list **)

let cancel_gates_simple l =
  cancel_gates_simple' l (length l)

(** val search_for_pat1 : gate_list -> int -> (gate_app list * gate_list) option **)

let search_for_pat1 l q =
  match next_single_qubit_gate l q with
  | Some p ->
    let (f, l') = p in
    (match f with
     | FU_H ->
       (match next_two_qubit_gate l' q with
        | Some p0 ->
          let (p1, l2) = p0 in
          let (p2, q2) = p1 in
          let (l1, q1) = p2 in
          if (=) q q2
          then (match next_single_qubit_gate l2 q with
                | Some p3 ->
                  let (f0, l2') = p3 in
                  (match f0 with
                   | FU_H ->
                     Some
                       ((app ((_H q) :: [])
                          (app l1 (app ((_CNOT q1 q) :: []) ((_H q) :: [])))), l2')
                   | _ -> None)
                | None -> None)
          else None
        | None -> None)
     | _ -> None)
  | None -> None

(** val search_for_pat2 : gate_list -> int -> (gate_app list * gate_list) option **)

let search_for_pat2 l q =
  match next_two_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2) = p0 in
    let (l1, q1) = p1 in
    if (=) q q2
    then (match next_single_qubit_gate l2 q with
          | Some p2 ->
            let (u, l2') = p2 in
            (match u with
             | FU_H -> None
             | FU_X -> None
             | FU_CNOT -> None
             | _ ->
               (match next_two_qubit_gate l2' q with
                | Some p3 ->
                  let (p4, l4) = p3 in
                  let (p5, q4) = p4 in
                  let (l3, q3) = p5 in
                  if (&&) ((&&) ((=) q q4) ((=) q1 q3)) (does_not_reference l3 q3)
                  then Some
                         ((app l1
                            (app ((_CNOT q1 q) :: [])
                              (app ((App1 (u, q)) :: [])
                                (app l3 ((_CNOT q1 q) :: []))))), l4)
                  else None
                | None -> None))
          | None -> None)
    else None
  | None -> None

(** val search_for_pat3 : gate_list -> int -> (gate_app list * gate_list) option **)

let search_for_pat3 l q =
  match next_two_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2) = p0 in
    let (l1, q1) = p1 in
    if (=) q q1 then Some ((app l1 ((_CNOT q1 q2) :: [])), l2) else None
  | None -> None

(** val search_for_commuting_pat :
    gate_list -> int -> (gate_app list * gate_list) option **)

let search_for_commuting_pat l q =
  match search_for_pat1 l q with
  | Some p -> Some p
  | None ->
    (match search_for_pat2 l q with
     | Some p -> Some p
     | None -> search_for_pat3 l q)

(** val propagate_Z : gate_list -> int -> int -> gate_list option **)

let rec propagate_Z l q n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some l)
    (fun n' ->
    match next_single_qubit_gate l q with
    | Some p ->
      let (f, l') = p in
      (match f with
       | FU_Z -> Some l'
       | FU_P -> Some ((_PDAG q) :: l')
       | FU_PDAG -> Some ((_P q) :: l')
       | _ ->
         (match search_for_commuting_pat l q with
          | Some p0 ->
            let (l1, l2) = p0 in
            (match propagate_Z l2 q n' with
             | Some l'0 -> Some (app l1 l'0)
             | None -> None)
          | None -> None))
    | None ->
      (match search_for_commuting_pat l q with
       | Some p ->
         let (l1, l2) = p in
         (match propagate_Z l2 q n' with
          | Some l' -> Some (app l1 l')
          | None -> None)
       | None -> None))
    n

(** val propagate_P : gate_list -> int -> int -> gate_list option **)

let rec propagate_P l q n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some l)
    (fun n' ->
    match next_single_qubit_gate l q with
    | Some p ->
      let (f, l') = p in
      (match f with
       | FU_Z -> Some ((_PDAG q) :: l')
       | FU_P -> Some ((_Z q) :: l')
       | FU_PDAG -> Some l'
       | FU_TDAG -> Some ((_T q) :: l')
       | _ ->
         (match search_for_commuting_pat l q with
          | Some p0 ->
            let (l1, l2) = p0 in
            (match propagate_P l2 q n' with
             | Some l'0 -> Some (app l1 l'0)
             | None -> None)
          | None -> None))
    | None ->
      (match search_for_commuting_pat l q with
       | Some p ->
         let (l1, l2) = p in
         (match propagate_P l2 q n' with
          | Some l' -> Some (app l1 l')
          | None -> None)
       | None -> None))
    n

(** val propagate_PDAG : gate_list -> int -> int -> gate_list option **)

let rec propagate_PDAG l q n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some l)
    (fun n' ->
    match next_single_qubit_gate l q with
    | Some p ->
      let (f, l') = p in
      (match f with
       | FU_Z -> Some ((_P q) :: l')
       | FU_P -> Some l'
       | FU_PDAG -> Some ((_Z q) :: l')
       | FU_T -> Some ((_TDAG q) :: l')
       | _ ->
         (match search_for_commuting_pat l q with
          | Some p0 ->
            let (l1, l2) = p0 in
            (match propagate_PDAG l2 q n' with
             | Some l'0 -> Some (app l1 l'0)
             | None -> None)
          | None -> None))
    | None ->
      (match search_for_commuting_pat l q with
       | Some p ->
         let (l1, l2) = p in
         (match propagate_PDAG l2 q n' with
          | Some l' -> Some (app l1 l')
          | None -> None)
       | None -> None))
    n

(** val propagate_T : gate_list -> int -> int -> gate_list option **)

let rec propagate_T l q n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some l)
    (fun n' ->
    match next_single_qubit_gate l q with
    | Some p ->
      let (f, l') = p in
      (match f with
       | FU_PDAG -> Some ((_TDAG q) :: l')
       | FU_T -> Some ((_P q) :: l')
       | FU_TDAG -> Some l'
       | _ ->
         (match search_for_commuting_pat l q with
          | Some p0 ->
            let (l1, l2) = p0 in
            (match propagate_T l2 q n' with
             | Some l'0 -> Some (app l1 l'0)
             | None -> None)
          | None -> None))
    | None ->
      (match search_for_commuting_pat l q with
       | Some p ->
         let (l1, l2) = p in
         (match propagate_T l2 q n' with
          | Some l' -> Some (app l1 l')
          | None -> None)
       | None -> None))
    n

(** val propagate_TDAG : gate_list -> int -> int -> gate_list option **)

let rec propagate_TDAG l q n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some l)
    (fun n' ->
    match next_single_qubit_gate l q with
    | Some p ->
      let (f, l') = p in
      (match f with
       | FU_P -> Some ((_T q) :: l')
       | FU_T -> Some l'
       | FU_TDAG -> Some ((_PDAG q) :: l')
       | _ ->
         (match search_for_commuting_pat l q with
          | Some p0 ->
            let (l1, l2) = p0 in
            (match propagate_TDAG l2 q n' with
             | Some l'0 -> Some (app l1 l'0)
             | None -> None)
          | None -> None))
    | None ->
      (match search_for_commuting_pat l q with
       | Some p ->
         let (l1, l2) = p in
         (match propagate_TDAG l2 q n' with
          | Some l' -> Some (app l1 l')
          | None -> None)
       | None -> None))
    n

(** val cancel_gates : gate_list -> int -> gate_list **)

let rec cancel_gates l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | h :: t ->
      (match h with
       | App1 (f, q) ->
         (match f with
          | FU_Z ->
            (match propagate_Z t q (length t) with
             | Some l' -> cancel_gates l' n'
             | None -> (_Z q) :: (cancel_gates t n'))
          | FU_P ->
            (match propagate_P t q (length t) with
             | Some l' -> cancel_gates l' n'
             | None -> (_P q) :: (cancel_gates t n'))
          | FU_PDAG ->
            (match propagate_PDAG t q (length t) with
             | Some l' -> cancel_gates l' n'
             | None -> (_PDAG q) :: (cancel_gates t n'))
          | FU_T ->
            (match propagate_T t q (length t) with
             | Some l' -> cancel_gates l' n'
             | None -> (_T q) :: (cancel_gates t n'))
          | FU_TDAG ->
            (match propagate_TDAG t q (length t) with
             | Some l' -> cancel_gates l' n'
             | None -> (_TDAG q) :: (cancel_gates t n'))
          | _ -> h :: (cancel_gates t n'))
       | App2 (_, _, _) -> h :: (cancel_gates t n')))
    n

(** val single_qubit_gate_cancellation : gate_list -> gate_list **)

let single_qubit_gate_cancellation l =
  cancel_gates l (length l)



(** Small Example Programs **)

(* rm_nots example1 --> [_H 1; _CNOT 2 1] *)
let example1 = [_X 0; _H 1; _X 0;  _X 1; _CNOT 2 1; _X 1]

(* rm_nots example2 --> [_X 0; _X 1; _X 2] *)
let example2 = [_X 0; _X 1; _X 2]

(* next_single_qubit_gate example3 0 --> Some (_X 0, ...) *)
(* next_single_qubit_gate example3 1 --> Some (_H 1, ...) *)
(* next_two_qubit_gate example3 3 --> Some ([_H 1; _X 0], 2, 3, ...) *)
(* replace_single_qubit_pattern example3 0 [_X 0; _X 0] [_H 0; _H 0]
    --> [_H 0; _H 0; _H 1; _CNOT 2 3; _H 0; _P 1; _P 2; _CNOT 0 2] *)
(* replace_single_qubit_pattern example3 0 [_X 0; _H 0] [_H 0; _H 0]
    --> None *)
let example3 = [_H 1; _X 0; _CNOT 2 3; _X 0; _H 0; _P 1; _P 2; _CNOT 0 2]

(* hadamard_reduction example4 --> [_PDAG 1; _H 1; _PDAG 1; _CNOT 3 0; _X 2] *)
let example4 = [_H 1; _H 3; _H 0; _P 1; _CNOT 0 3; _H 0; _H 1; _H 3; _X 2]

(* benchmark_to_list example5 --> 
        [App2 (FU_CNOT, 0, 1); App1 (FU_H, 2); App2 (FU_CNOT, 1, 2);
        App1 (FU_TDAG, 2); App2 (FU_CNOT, 0, 2); App1 (FU_T, 2);
        App2 (FU_CNOT, 1, 2); App1 (FU_TDAG, 2); App2 (FU_CNOT, 0, 2);
        App2 (FU_CNOT, 0, 1); App1 (FU_TDAG, 1); App2 (FU_CNOT, 0, 1);
        App1 (FU_T, 0); App1 (FU_T, 1); App1 (FU_T, 2); App1 (FU_H, 2);
        App1 (FU_H, 3); App1 (FU_X, 4)] 
*)
let example5 = [Bench_CNOT(0,1); Bench_TOFF(0,1,2); Bench_H(3); Bench_X(4)]


