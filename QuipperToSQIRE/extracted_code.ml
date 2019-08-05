
(** val length : 'a1 list -> int **)

let rec length = List.length

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app = List.append

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
    gate_list -> int -> (gate_app * gate_list) option **)

let rec next_single_qubit_gate l q =
  match l with
  | [] -> None
  | g :: t ->
    (match g with
     | App1 (u, n) ->
       if (=) n q
       then Some ((App1 (u, n)), t)
       else (match next_single_qubit_gate t q with
             | Some p -> let (g0, l') = p in Some (g0, ((App1 (u, n)) :: l'))
             | None -> None)
     | App2 (u, m, n) ->
       if (||) ((=) m q) ((=) n q)
       then None
       else (match next_single_qubit_gate t q with
             | Some p -> let (g0, l') = p in Some (g0, ((App2 (u, m, n)) :: l'))
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

(** val remove_single_qubit_pattern :
    gate_list -> int -> gate_list -> gate_list option **)

let rec remove_single_qubit_pattern l q = function
| [] -> Some l
| g :: pat' ->
  (match g with
   | App1 (u, _) ->
     (match next_single_qubit_gate l q with
      | Some p ->
        let (g0, l') = p in
        (match g0 with
         | App1 (u', _) ->
           if match_gate u u' then remove_single_qubit_pattern l' q pat' else None
         | App2 (_, _, _) -> None)
      | None -> None)
   | App2 (_, _, _) -> None)

(** val replace_single_qubit_pattern :
    gate_list -> int -> gate_list -> gate_list -> gate_list option **)

let replace_single_qubit_pattern l q pat rep =
  match remove_single_qubit_pattern l q pat with
  | Some l' -> Some (app rep l')
  | None -> None

(** val apply_equivalence1 : gate_list -> int -> gate_list option **)

let apply_equivalence1 l q =
  replace_single_qubit_pattern l q ((_H q) :: ((_P q) :: ((_H q) :: [])))
    ((_PDAG q) :: ((_H q) :: ((_PDAG q) :: [])))

(** val apply_equivalence2 : gate_list -> int -> gate_list option **)

let apply_equivalence2 l q =
  replace_single_qubit_pattern l q ((_H q) :: ((_PDAG q) :: ((_H q) :: [])))
    ((_P q) :: ((_H q) :: ((_P q) :: [])))

(** val apply_equivalence3 : gate_list -> int -> gate_list option **)

let apply_equivalence3 l q =
  match next_single_qubit_gate l q with
  | Some p ->
    let (g, l1) = p in
    (match g with
     | App1 (f, _) ->
       (match f with
        | FU_H ->
          (match next_two_qubit_gate l1 q with
           | Some p0 ->
             let (p1, l3) = p0 in
             let (p2, n) = p1 in
             let (l2, m) = p2 in
             (match next_single_qubit_gate l3 q with
              | Some p3 ->
                let (g0, l4) = p3 in
                (match g0 with
                 | App1 (f0, _) ->
                   (match f0 with
                    | FU_H ->
                      if (=) q m
                      then (match next_single_qubit_gate (rev l2) n with
                            | Some p4 ->
                              let (g1, l5) = p4 in
                              (match g1 with
                               | App1 (f1, _) ->
                                 (match f1 with
                                  | FU_H ->
                                    (match next_single_qubit_gate l4 n with
                                     | Some p5 ->
                                       let (g2, l6) = p5 in
                                       (match g2 with
                                        | App1 (f2, _) ->
                                          (match f2 with
                                           | FU_H ->
                                             Some
                                               (app (rev l5)
                                                 (app ((_CNOT n m) :: []) l6))
                                           | _ -> None)
                                        | App2 (_, _, _) -> None)
                                     | None -> None)
                                  | _ -> None)
                               | App2 (_, _, _) -> None)
                            | None -> None)
                      else (match next_single_qubit_gate (rev l2) m with
                            | Some p4 ->
                              let (g1, l5) = p4 in
                              (match g1 with
                               | App1 (f1, _) ->
                                 (match f1 with
                                  | FU_H ->
                                    (match next_single_qubit_gate l4 m with
                                     | Some p5 ->
                                       let (g2, l6) = p5 in
                                       (match g2 with
                                        | App1 (f2, _) ->
                                          (match f2 with
                                           | FU_H ->
                                             Some
                                               (app (rev l5)
                                                 (app ((_CNOT n m) :: []) l6))
                                           | _ -> None)
                                        | App2 (_, _, _) -> None)
                                     | None -> None)
                                  | _ -> None)
                               | App2 (_, _, _) -> None)
                            | None -> None)
                    | _ -> None)
                 | App2 (_, _, _) -> None)
              | None -> None)
           | None -> None)
        | _ -> None)
     | App2 (_, _, _) -> None)
  | None -> None

(** val apply_equivalence4 : gate_list -> int -> gate_app list option **)

let apply_equivalence4 l q =
  match remove_single_qubit_pattern l q ((_H q) :: ((_P q) :: [])) with
  | Some l1 ->
    (match next_two_qubit_gate l1 q with
     | Some p ->
       let (p0, l3) = p in
       let (p1, q2) = p0 in
       let (l2, q1) = p1 in
       if (=) q q2
       then (match remove_single_qubit_pattern l3 q ((_PDAG q) :: ((_H q) :: [])) with
             | Some l4 ->
               Some
                 (app l2 (app ((_PDAG q2) :: ((_CNOT q1 q2) :: ((_P q2) :: []))) l4))
             | None -> None)
       else None
     | None -> None)
  | None -> None

(** val apply_equivalence5 : gate_list -> int -> gate_app list option **)

let apply_equivalence5 l q =
  match remove_single_qubit_pattern l q ((_H q) :: ((_PDAG q) :: [])) with
  | Some l1 ->
    (match next_two_qubit_gate l1 q with
     | Some p ->
       let (p0, l3) = p in
       let (p1, q2) = p0 in
       let (l2, q1) = p1 in
       if (=) q q2
       then (match remove_single_qubit_pattern l3 q ((_P q) :: ((_H q) :: [])) with
             | Some l4 ->
               Some
                 (app l2 (app ((_P q2) :: ((_CNOT q1 q2) :: ((_PDAG q2) :: []))) l4))
             | None -> None)
       else None
     | None -> None)
  | None -> None

(** val apply_H_equivalence : gate_list -> int -> gate_list option **)

let apply_H_equivalence l q =
  match apply_equivalence1 l q with
  | Some l' -> Some l'
  | None ->
    (match apply_equivalence2 l q with
     | Some l' -> Some l'
     | None ->
       (match apply_equivalence3 l q with
        | Some l' -> Some l'
        | None ->
          (match apply_equivalence4 l q with
           | Some l' -> Some l'
           | None -> apply_equivalence5 l q)))

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


