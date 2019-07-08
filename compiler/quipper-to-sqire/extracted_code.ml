
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

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Nat =
 struct
 end

type r (* AXIOM TO BE REALIZED *)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = List.rev

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val zero : ascii **)

let zero =
  Ascii (false, false, false, false, false, false, false, false)

(** val one : ascii **)

let one =
  Ascii (true, false, false, false, false, false, false, false)

(** val shift : bool -> ascii -> ascii **)

let shift c = function
| Ascii (a1, a2, a3, a4, a5, a6, a7, _) -> Ascii (c, a1, a2, a3, a4, a5, a6, a7)

(** val ascii_of_pos : positive -> ascii **)

let ascii_of_pos =
  let rec loop n0 p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> zero)
      (fun n' ->
      match p with
      | XI p' -> shift true (loop n' p')
      | XO p' -> shift false (loop n' p')
      | XH -> one)
      n0
  in loop (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
       (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))

(** val ascii_of_N : n -> ascii **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

type string =
| EmptyString
| String of ascii * string

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

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

let _H n0 =
  App1 (FU_H, n0)

(** val _X : int -> gate_app **)

let _X n0 =
  App1 (FU_X, n0)

(** val _Z : int -> gate_app **)

let _Z n0 =
  App1 (FU_Z, n0)

(** val _P : int -> gate_app **)

let _P n0 =
  App1 (FU_P, n0)

(** val _PDAG : int -> gate_app **)

let _PDAG n0 =
  App1 (FU_PDAG, n0)

(** val _T : int -> gate_app **)

let _T n0 =
  App1 (FU_T, n0)

(** val _TDAG : int -> gate_app **)

let _TDAG n0 =
  App1 (FU_TDAG, n0)

(** val _CNOT : int -> int -> gate_app **)

let _CNOT m n0 =
  App2 (FU_CNOT, m, n0)

type gate_list = gate_app list

(** val next_single_qubit_gate :
    gate_list -> int -> (fUnitary * gate_list) option **)

let rec next_single_qubit_gate l q =
  match l with
  | [] -> None
  | g :: t ->
    (match g with
     | App1 (u, n0) ->
       if (=) n0 q
       then Some (u, t)
       else (match next_single_qubit_gate t q with
             | Some p -> let (u', l') = p in Some (u', ((App1 (u, n0)) :: l'))
             | None -> None)
     | App2 (u, m, n0) ->
       if (||) ((=) m q) ((=) n0 q)
       then None
       else (match next_single_qubit_gate t q with
             | Some p -> let (u', l') = p in Some (u', ((App2 (u, m, n0)) :: l'))
             | None -> None))

(** val next_two_qubit_gate :
    gate_list -> int -> (((gate_list * int) * int) * gate_list) option **)

let rec next_two_qubit_gate l q =
  match l with
  | [] -> None
  | g :: t ->
    (match g with
     | App1 (u, n0) ->
       if (=) n0 q
       then None
       else (match next_two_qubit_gate t q with
             | Some p ->
               let (p0, l2) = p in
               let (p1, n') = p0 in
               let (l1, m') = p1 in Some (((((App1 (u, n0)) :: l1), m'), n'), l2)
             | None -> None)
     | App2 (u, m, n0) ->
       if (||) ((=) m q) ((=) n0 q)
       then Some ((([], m), n0), t)
       else (match next_two_qubit_gate t q with
             | Some p ->
               let (p0, l2) = p in
               let (p1, n') = p0 in
               let (l1, m') = p1 in Some (((((App2 (u, m, n0)) :: l1), m'), n'), l2)
             | None -> None))

(** val does_not_reference : gate_list -> int -> bool **)

let rec does_not_reference l q =
  match l with
  | [] -> true
  | g :: t ->
    (match g with
     | App1 (_, n0) -> (&&) (negb ((=) n0 q)) (does_not_reference t q)
     | App2 (_, m, n0) ->
       (&&) (negb ((||) ((=) m q) ((=) n0 q))) (does_not_reference t q))

(** val count_H_gates : gate_list -> int **)

let rec count_H_gates l =
  let rec aux l0 acc =
    match l0 with
    | [] -> acc
    | y :: t ->
      (match y with
       | App1 (f, _) ->
         (match f with
          | FU_H -> aux t (add acc (Pervasives.succ 0))
          | _ -> aux t acc)
       | App2 (_, _, _) -> aux t acc)
  in aux l 0

(** val count_X_gates : gate_list -> int **)

let rec count_X_gates l =
  let rec aux l0 acc =
    match l0 with
    | [] -> acc
    | y :: t ->
      (match y with
       | App1 (f, _) ->
         (match f with
          | FU_X -> aux t (add acc (Pervasives.succ 0))
          | _ -> aux t acc)
       | App2 (_, _, _) -> aux t acc)
  in aux l 0

(** val count_rotation_gates : gate_list -> int **)

let rec count_rotation_gates l =
  let rec aux l0 acc =
    match l0 with
    | [] -> acc
    | y :: t ->
      (match y with
       | App1 (f, _) ->
         (match f with
          | FU_H -> aux t acc
          | FU_X -> aux t acc
          | FU_CNOT -> aux t acc
          | _ -> aux t (add acc (Pervasives.succ 0)))
       | App2 (_, _, _) -> aux t acc)
  in aux l 0

(** val count_CNOT_gates : gate_list -> int **)

let rec count_CNOT_gates l =
  let rec aux l0 acc =
    match l0 with
    | [] -> acc
    | y :: t ->
      (match y with
       | App1 (_, _) -> aux t acc
       | App2 (f, _, _) ->
         (match f with
          | FU_CNOT -> aux t (add acc (Pervasives.succ 0))
          | _ -> aux t acc))
  in aux l 0

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
   | Bench_H n0 -> (App1 (FU_H, n0)) :: (benchmark_to_list t)
   | Bench_X n0 -> (App1 (FU_X, n0)) :: (benchmark_to_list t)
   | Bench_Z n0 -> (App1 (FU_Z, n0)) :: (benchmark_to_list t)
   | Bench_CNOT (m, n0) -> (App2 (FU_CNOT, m, n0)) :: (benchmark_to_list t)
   | Bench_TOFF (m, n0, p) -> app (tOFF m n0 p) (benchmark_to_list t))

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

let rec propagate_nots l n0 =
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
    n0

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
          let (p2, n0) = p1 in
          let (l2, m) = p2 in
          (match next_single_qubit_gate l3 q with
           | Some p3 ->
             let (f0, l4) = p3 in
             (match f0 with
              | FU_H ->
                if (=) q m
                then (match next_single_qubit_gate (rev l2) n0 with
                      | Some p4 ->
                        let (f1, l5) = p4 in
                        (match f1 with
                         | FU_H ->
                           (match next_single_qubit_gate l4 n0 with
                            | Some p5 ->
                              let (f2, l6) = p5 in
                              (match f2 with
                               | FU_H ->
                                 Some (app (rev l5) (app ((_CNOT n0 m) :: []) l6))
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
                                 Some (app (rev l5) (app ((_CNOT n0 m) :: []) l6))
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

let rec apply_H_equivalences l n0 =
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
    n0

(** val hadamard_reduction : gate_list -> gate_list **)

let hadamard_reduction l =
  apply_H_equivalences l (mul (Pervasives.succ (Pervasives.succ 0)) (length l))

(** val cancel_gates_simple' : gate_list -> gate_list -> int -> gate_list **)

let rec cancel_gates_simple' l acc n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> app (rev acc) l)
    (fun n' ->
    match l with
    | [] -> rev acc
    | g :: t ->
      (match g with
       | App1 (f, q) ->
         (match f with
          | FU_H ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_H -> cancel_gates_simple' t' acc n'
                | _ -> cancel_gates_simple' t ((_H q) :: acc) n')
             | None -> cancel_gates_simple' t ((_H q) :: acc) n')
          | FU_X ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_X -> cancel_gates_simple' t' acc n'
                | _ -> cancel_gates_simple' t ((_X q) :: acc) n')
             | None -> cancel_gates_simple' t ((_X q) :: acc) n')
          | FU_Z ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_Z -> cancel_gates_simple' t' acc n'
                | FU_P -> cancel_gates_simple' ((_PDAG q) :: t') acc n'
                | FU_PDAG -> cancel_gates_simple' ((_P q) :: t') acc n'
                | _ -> cancel_gates_simple' t ((_Z q) :: acc) n')
             | None -> cancel_gates_simple' t ((_Z q) :: acc) n')
          | FU_P ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_Z -> cancel_gates_simple' ((_PDAG q) :: t') acc n'
                | FU_P -> cancel_gates_simple' ((_Z q) :: t') acc n'
                | FU_PDAG -> cancel_gates_simple' t' acc n'
                | FU_TDAG -> cancel_gates_simple' ((_T q) :: t') acc n'
                | _ -> cancel_gates_simple' t ((_P q) :: acc) n')
             | None -> cancel_gates_simple' t ((_P q) :: acc) n')
          | FU_PDAG ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_Z -> cancel_gates_simple' ((_P q) :: t') acc n'
                | FU_P -> cancel_gates_simple' t' acc n'
                | FU_PDAG -> cancel_gates_simple' ((_Z q) :: t') acc n'
                | FU_T -> cancel_gates_simple' ((_TDAG q) :: t') acc n'
                | _ -> cancel_gates_simple' t ((_PDAG q) :: acc) n')
             | None -> cancel_gates_simple' t ((_PDAG q) :: acc) n')
          | FU_T ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_PDAG -> cancel_gates_simple' ((_TDAG q) :: t') acc n'
                | FU_T -> cancel_gates_simple' ((_P q) :: t') acc n'
                | FU_TDAG -> cancel_gates_simple' t' acc n'
                | _ -> cancel_gates_simple' t ((_T q) :: acc) n')
             | None -> cancel_gates_simple' t ((_T q) :: acc) n')
          | FU_TDAG ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_P -> cancel_gates_simple' ((_T q) :: t') acc n'
                | FU_T -> cancel_gates_simple' t' acc n'
                | FU_TDAG -> cancel_gates_simple' ((_PDAG q) :: t') acc n'
                | _ -> cancel_gates_simple' t ((_TDAG q) :: acc) n')
             | None -> cancel_gates_simple' t ((_TDAG q) :: acc) n')
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
               then cancel_gates_simple' (app l1 l2) acc n'
               else cancel_gates_simple' t ((_CNOT q1 q2) :: acc) n'
             | None -> cancel_gates_simple' t ((_CNOT q1 q2) :: acc) n')
          | _ -> [])))
    n0

(** val cancel_gates_simple : gate_list -> gate_list **)

let cancel_gates_simple l =
  cancel_gates_simple' l [] (length l)

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

let rec propagate_Z l q n0 =
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
    n0

(** val propagate_P : gate_list -> int -> int -> gate_list option **)

let rec propagate_P l q n0 =
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
    n0

(** val propagate_PDAG : gate_list -> int -> int -> gate_list option **)

let rec propagate_PDAG l q n0 =
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
    n0

(** val propagate_T : gate_list -> int -> int -> gate_list option **)

let rec propagate_T l q n0 =
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
    n0

(** val propagate_TDAG : gate_list -> int -> int -> gate_list option **)

let rec propagate_TDAG l q n0 =
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
    n0

(** val cancel_gates : gate_list -> int -> gate_list **)

let rec cancel_gates l n0 =
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
    n0

(** val single_qubit_gate_cancellation : gate_list -> gate_list **)

let single_qubit_gate_cancellation l =
  cancel_gates l (length l)

type mop =
| Plus
| Minus
| Times
| Div

(** val print_mop : mop -> string **)

let print_mop = function
| Plus ->
  String ((Ascii (true, true, false, true, false, true, false, false)), EmptyString)
| Minus ->
  String ((Ascii (true, false, true, true, false, true, false, false)), EmptyString)
| Times ->
  String ((Ascii (false, true, false, true, false, true, false, false)), EmptyString)
| Div ->
  String ((Ascii (true, true, true, true, false, true, false, false)), EmptyString)

type exp =
| E_nat of int
| E_real of r
| E_pi
| E_str of string
| E_mop of mop * exp * exp

(** val nat_to_string : int -> string **)

let nat_to_string n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> String ((Ascii (false, false, false, false, true, true, false,
    false)), EmptyString))
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> String ((Ascii (true, false, false, false, true, true, false,
      false)), EmptyString))
      (fun n2 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> String ((Ascii (false, true, false, false, true, true, false,
        false)), EmptyString))
        (fun n3 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> String ((Ascii (true, true, false, false, true, true, false,
          false)), EmptyString))
          (fun n4 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> String ((Ascii (false, false, true, false, true, true, false,
            false)), EmptyString))
            (fun n5 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> String ((Ascii (true, false, true, false, true, true, false,
              false)), EmptyString))
              (fun n6 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> String ((Ascii (false, true, true, false, true, true,
                false, false)), EmptyString))
                (fun n7 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> String ((Ascii (true, true, true, false, true, true,
                  false, false)), EmptyString))
                  (fun n8 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> String ((Ascii (false, false, false, true, true, true,
                    false, false)), EmptyString))
                    (fun _ -> String ((Ascii (true, false, false, true, true, true,
                    false, false)), EmptyString))
                    n8)
                  n7)
                n6)
              n5)
            n4)
          n3)
        n2)
      n1)
    n0

(** val print_exp : exp -> string **)

let rec print_exp = function
| E_nat n0 -> nat_to_string n0
| E_real _ ->
  String ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String ((Ascii
    (true, false, false, false, false, true, true, false)), (String ((Ascii (false,
    false, true, true, false, true, true, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), (String ((Ascii (false, true, true,
    true, false, true, true, false)), (String ((Ascii (true, false, true, false,
    true, true, true, false)), (String ((Ascii (true, false, true, true, false,
    true, true, false)), (String ((Ascii (false, true, false, false, false, true,
    true, false)), (String ((Ascii (true, false, true, false, false, true, true,
    false)), (String ((Ascii (false, true, false, false, true, true, true, false)),
    (String ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)), (String ((Ascii
    (true, true, true, true, false, true, true, false)), (String ((Ascii (false,
    false, false, false, false, true, false, false)), (String ((Ascii (true, false,
    false, true, false, true, true, false)), (String ((Ascii (true, false, true,
    true, false, true, true, false)), (String ((Ascii (false, false, false, false,
    true, true, true, false)), (String ((Ascii (false, false, true, true, false,
    true, true, false)), (String ((Ascii (true, false, true, false, false, true,
    true, false)), (String ((Ascii (true, false, true, true, false, true, true,
    false)), (String ((Ascii (true, false, true, false, false, true, true, false)),
    (String ((Ascii (false, true, true, true, false, true, true, false)), (String
    ((Ascii (false, false, true, false, true, true, true, false)),
    EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))
| E_pi ->
  String ((Ascii (false, false, false, false, true, true, true, false)), (String
    ((Ascii (true, false, false, true, false, true, true, false)), EmptyString)))
| E_str s -> s
| E_mop (m, e1, e2) -> append (print_exp e1) (append (print_mop m) (print_exp e2))

type decl =
| Qreg of int * int
| Creg of int * int

(** val print_decl : decl -> string **)

let print_decl = function
| Qreg (n0, m) ->
  append (String ((Ascii (true, false, false, false, true, true, true, false)),
    (String ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String ((Ascii
    (true, true, true, false, false, true, true, false)), (String ((Ascii (false,
    false, false, false, false, true, false, false)), (String ((Ascii (true, false,
    false, false, true, true, true, false)), EmptyString))))))))))))
    (append (nat_to_string n0)
      (append (String ((Ascii (true, true, false, true, true, false, true, false)),
        EmptyString))
        (append (nat_to_string m) (String ((Ascii (true, false, true, true, true,
          false, true, false)), EmptyString)))))
| Creg (n0, m) ->
  append (String ((Ascii (true, true, false, false, false, true, true, false)),
    (String ((Ascii (false, true, false, false, true, true, true, false)), (String
    ((Ascii (true, false, true, false, false, true, true, false)), (String ((Ascii
    (true, true, true, false, false, true, true, false)), (String ((Ascii (false,
    false, false, false, false, true, false, false)), (String ((Ascii (true, true,
    false, false, false, true, true, false)), EmptyString))))))))))))
    (append (nat_to_string n0)
      (append (String ((Ascii (true, true, false, true, true, false, true, false)),
        EmptyString))
        (append (nat_to_string m) (String ((Ascii (true, false, true, true, true,
          false, true, false)), EmptyString)))))

type qmem =
| Qubit of int
| Qlist of int * int

(** val print_qmem : qmem -> string **)

let print_qmem = function
| Qubit n0 ->
  append (String ((Ascii (true, false, false, false, true, true, true, false)),
    EmptyString)) (nat_to_string n0)
| Qlist (n0, m) ->
  append (String ((Ascii (true, false, false, false, true, true, true, false)),
    EmptyString))
    (append (nat_to_string n0)
      (append (String ((Ascii (true, true, false, true, true, false, true, false)),
        EmptyString))
        (append (nat_to_string m) (String ((Ascii (true, false, true, true, true,
          false, true, false)), EmptyString)))))

type cmem =
| Cbit of int
| Clist of int * int

(** val print_cmem : cmem -> string **)

let print_cmem = function
| Cbit n0 ->
  append (String ((Ascii (true, true, false, false, false, true, true, false)),
    EmptyString)) (nat_to_string n0)
| Clist (n0, m) ->
  append (String ((Ascii (true, true, false, false, false, true, true, false)),
    EmptyString))
    (append (nat_to_string n0)
      (append (String ((Ascii (true, true, false, true, true, false, true, false)),
        EmptyString))
        (append (nat_to_string m) (String ((Ascii (true, false, true, true, true,
          false, true, false)), EmptyString)))))

type unitary =
| U_U of exp list * qmem
| U_CX of qmem * qmem

(** val print_explist : exp list -> string **)

let rec print_explist = function
| [] -> EmptyString
| e :: l ->
  (match l with
   | [] -> print_exp e
   | _ :: _ ->
     append (print_exp e)
       (append (String ((Ascii (false, false, true, true, false, true, false,
         false)), EmptyString)) (print_explist l)))

(** val print_unitary : unitary -> string **)

let print_unitary = function
| U_U (l, q) ->
  append (String ((Ascii (true, false, true, false, true, false, true, false)),
    (String ((Ascii (false, false, false, true, false, true, false, false)),
    EmptyString))))
    (append (print_explist l)
      (append (String ((Ascii (true, false, false, true, false, true, false,
        false)), (String ((Ascii (false, false, false, false, false, true, false,
        false)), EmptyString)))) (print_qmem q)))
| U_CX (q1, q2) ->
  append (String ((Ascii (true, true, false, false, false, false, true, false)),
    (String ((Ascii (false, false, false, true, true, false, true, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)),
    EmptyString))))))
    (append (print_qmem q1)
      (append (String ((Ascii (false, false, true, true, false, true, false,
        false)), (String ((Ascii (false, false, false, false, false, true, false,
        false)), EmptyString)))) (print_qmem q2)))

type op =
| O_app of unitary
| O_meas of qmem * cmem
| O_reset of qmem

(** val print_op : op -> string **)

let rec print_op = function
| O_app u -> print_unitary u
| O_meas (q, c) ->
  append (String ((Ascii (true, false, true, true, false, true, true, false)),
    (String ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, false, false, false, false, true, true, false)), (String ((Ascii
    (true, true, false, false, true, true, true, false)), (String ((Ascii (true,
    false, true, false, true, true, true, false)), (String ((Ascii (false, true,
    false, false, true, true, true, false)), (String ((Ascii (true, false, true,
    false, false, true, true, false)), (String ((Ascii (false, false, false, false,
    false, true, false, false)), EmptyString))))))))))))))))
    (append (print_qmem q)
      (append (String ((Ascii (false, false, false, false, false, true, false,
        false)), (String ((Ascii (true, false, true, true, false, true, false,
        false)), (String ((Ascii (false, true, true, true, true, true, false,
        false)), (String ((Ascii (false, false, false, false, false, true, false,
        false)), EmptyString)))))))) (print_cmem c)))
| O_reset q ->
  append (String ((Ascii (false, true, false, false, true, true, true, false)),
    (String ((Ascii (true, false, true, false, false, true, true, false)), (String
    ((Ascii (true, true, false, false, true, true, true, false)), (String ((Ascii
    (true, false, true, false, false, true, true, false)), (String ((Ascii (false,
    false, true, false, true, true, true, false)), (String ((Ascii (false, false,
    false, false, false, true, false, false)), EmptyString)))))))))))) (print_qmem q)

type statement =
| S_decl of decl
| S_op of op
| S_if of cmem * exp * statement
| S_err of string

(** val print_statement : statement -> string **)

let rec print_statement = function
| S_decl d -> print_decl d
| S_op o -> print_op o
| S_if (m, e, s) ->
  append (String ((Ascii (true, false, false, true, false, true, true, false)),
    (String ((Ascii (false, true, true, false, false, true, true, false)), (String
    ((Ascii (false, false, false, true, false, true, false, false)),
    EmptyString))))))
    (append (print_cmem m)
      (append (String ((Ascii (true, false, true, true, true, true, false, false)),
        (String ((Ascii (true, false, true, true, true, true, false, false)),
        EmptyString))))
        (append (print_exp e)
          (append (String ((Ascii (true, false, false, true, false, true, false,
            false)), (String ((Ascii (false, false, false, false, false, true,
            false, false)), EmptyString)))) (print_statement s)))))
| S_err s -> s

type program = statement list

(** val newline : string **)

let newline =
  String ((ascii_of_N (Npos (XO (XI (XO XH))))), EmptyString)

(** val print_program : program -> string **)

let rec print_program = function
| [] -> EmptyString
| s :: p' ->
  (match p' with
   | [] -> print_statement s
   | _ :: _ ->
     append (print_statement s)
       (append (String ((Ascii (true, true, false, true, true, true, false, false)),
         EmptyString)) (append newline (print_program p'))))

(** val printer : program -> string **)

let printer p =
  append (String ((Ascii (true, true, true, true, false, false, true, false)),
    (String ((Ascii (false, false, false, false, true, false, true, false)), (String
    ((Ascii (true, false, true, false, false, false, true, false)), (String ((Ascii
    (false, true, true, true, false, false, true, false)), (String ((Ascii (true,
    false, false, false, true, false, true, false)), (String ((Ascii (true, false,
    false, false, false, false, true, false)), (String ((Ascii (true, true, false,
    false, true, false, true, false)), (String ((Ascii (true, false, true, true,
    false, false, true, false)), (String ((Ascii (false, false, false, false, false,
    true, false, false)), (String ((Ascii (false, true, false, false, true, true,
    false, false)), (String ((Ascii (false, true, true, true, false, true, false,
    false)), (String ((Ascii (false, false, false, false, true, true, false,
    false)), (String ((Ascii (true, true, false, true, true, true, false, false)),
    EmptyString))))))))))))))))))))))))))
    (append newline
      (append (String ((Ascii (true, false, false, true, false, true, true, false)),
        (String ((Ascii (false, true, true, true, false, true, true, false)),
        (String ((Ascii (true, true, false, false, false, true, true, false)),
        (String ((Ascii (false, false, true, true, false, true, true, false)),
        (String ((Ascii (true, false, true, false, true, true, true, false)),
        (String ((Ascii (false, false, true, false, false, true, true, false)),
        (String ((Ascii (true, false, true, false, false, true, true, false)),
        (String ((Ascii (false, false, false, false, false, true, false, false)),
        (String ((Ascii (false, true, false, false, false, true, false, false)),
        (String ((Ascii (true, false, false, false, true, true, true, false)),
        (String ((Ascii (true, false, true, false, false, true, true, false)),
        (String ((Ascii (false, false, true, true, false, true, true, false)),
        (String ((Ascii (true, false, false, true, false, true, true, false)),
        (String ((Ascii (false, true, false, false, false, true, true, false)),
        (String ((Ascii (true, false, false, false, true, true, false, false)),
        (String ((Ascii (false, true, true, true, false, true, false, false)),
        (String ((Ascii (true, false, false, true, false, true, true, false)),
        (String ((Ascii (false, true, true, true, false, true, true, false)),
        (String ((Ascii (true, true, false, false, false, true, true, false)),
        (String ((Ascii (false, true, false, false, false, true, false, false)),
        (String ((Ascii (true, true, false, true, true, true, false, false)),
        EmptyString))))))))))))))))))))))))))))))))))))))))))
        (append newline (print_program p))))
