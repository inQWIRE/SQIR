
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val length : 'a1 list -> int **)

let rec length = List.length

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app = List.append

type comparison =
| Eq
| Lt
| Gt

(** val add : int -> int -> int **)

let rec add = (+)

module Nat =
 struct
 end

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Pervasives.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : int -> int -> bool **)

  let rec eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        y)
      x
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = List.rev

type fUnitary =
| FU_H
| FU_X
| FU_PI4 of int
| FU_CNOT

type gate_app =
| App1 of fUnitary * int
| App2 of fUnitary * int * int

(** val _H : int -> gate_app **)

let _H n =
  App1 (FU_H, n)

(** val _X : int -> gate_app **)

let _X n =
  App1 (FU_X, n)

(** val _PI4 : int -> int -> gate_app **)

let _PI4 k n =
  App1 ((FU_PI4 k), n)

(** val _CNOT : int -> int -> gate_app **)

let _CNOT m n =
  App2 (FU_CNOT, m, n)

(** val _T : int -> gate_app **)

let _T n =
  App1 ((FU_PI4 1), n)

(** val _Z : int -> gate_app **)

let _Z n =
  App1 ((FU_PI4 ((fun p->2*p) ((fun p->2*p) 1))), n)

(** val _TDAG : int -> gate_app **)

let _TDAG n =
  App1 ((FU_PI4 ((fun p->1+2*p) ((fun p->1+2*p) 1))), n)

type gate_list = gate_app list

(** val next_single_qubit_gate : gate_list -> int -> (fUnitary * gate_list) option **)

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

(** val next_two_qubit_gate : gate_list -> int -> (((gate_list * int) * int) * gate_list) option **)

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
               let (p1, n') = p0 in let (l1, m') = p1 in Some (((((App1 (u, n)) :: l1), m'), n'), l2)
             | None -> None)
     | App2 (u, m, n) ->
       if (||) ((=) m q) ((=) n q)
       then Some ((([], m), n), t)
       else (match next_two_qubit_gate t q with
             | Some p ->
               let (p0, l2) = p in
               let (p1, n') = p0 in let (l1, m') = p1 in Some (((((App2 (u, m, n)) :: l1), m'), n'), l2)
             | None -> None))

(** val does_not_reference : gate_list -> int -> bool **)

let rec does_not_reference l q =
  match l with
  | [] -> true
  | g :: t ->
    (match g with
     | App1 (_, n) -> (&&) (negb ((=) n q)) (does_not_reference t q)
     | App2 (_, m, n) -> (&&) (negb ((||) ((=) m q) ((=) n q))) (does_not_reference t q))

(** val count_H_gates : gate_list -> int **)

let rec count_H_gates l =
  let rec aux l0 acc =
    match l0 with
    | [] -> acc
    | y :: t ->
      (match y with
       | App1 (f, _) -> (match f with
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
       | App1 (f, _) -> (match f with
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
       | App1 (f, _) -> (match f with
                         | FU_PI4 _ -> aux t (add acc (Pervasives.succ 0))
                         | _ -> aux t acc)
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
       | App2 (f, _, _) -> (match f with
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
  (_H c) :: ((_CNOT b c) :: ((_TDAG c) :: ((_CNOT a c) :: ((_T c) :: ((_CNOT b c) :: ((_TDAG c) :: (
    (_CNOT a c) :: ((_CNOT a b) :: ((_TDAG b) :: ((_CNOT a b) :: ((_T a) :: ((_T b) :: ((_T c) :: (
    (_H c) :: []))))))))))))))

(** val benchmark_to_list : benchmark_gate_app list -> gate_list **)

let rec benchmark_to_list = function
| [] -> []
| b :: t ->
  (match b with
   | Bench_H n -> (_H n) :: (benchmark_to_list t)
   | Bench_X n -> (_X n) :: (benchmark_to_list t)
   | Bench_Z n -> (_Z n) :: (benchmark_to_list t)
   | Bench_CNOT (m, n) -> (_CNOT m n) :: (benchmark_to_list t)
   | Bench_TOFF (m, n, p) -> app (tOFF m n p) (benchmark_to_list t))

(** val cancel_gates_simple' : gate_list -> gate_list -> int -> gate_list **)

let rec cancel_gates_simple' l acc n =
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
          | FU_PI4 k ->
            (match next_single_qubit_gate t q with
             | Some p ->
               let (f0, t') = p in
               (match f0 with
                | FU_PI4 k' ->
                  let k'' = Z.add k k' in
                  if Z.eqb k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
                  then cancel_gates_simple' t' acc n'
                  else if Z.ltb k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
                       then cancel_gates_simple' ((_PI4 k'' q) :: t') acc n'
                       else cancel_gates_simple'
                              ((_PI4 (Z.sub k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))) q) :: t')
                              acc n'
                | _ -> cancel_gates_simple' t ((_PI4 k q) :: acc) n')
             | None -> cancel_gates_simple' t ((_PI4 k q) :: acc) n')
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
    n

(** val cancel_gates_simple : gate_list -> gate_list **)

let cancel_gates_simple l =
  cancel_gates_simple' l [] (length l)

(** val search_for_commuting_X_pat : gate_list -> int -> (gate_app list * gate_list) option **)

let search_for_commuting_X_pat l q =
  match next_two_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2) = p0 in
    let (l1, q1) = p1 in if (=) q q2 then Some ((app l1 ((_CNOT q1 q2) :: [])), l2) else None
  | None -> None

(** val search_for_Rz_pat1 : gate_list -> int -> (gate_app list * gate_list) option **)

let search_for_Rz_pat1 l q =
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
                     Some ((app ((_H q) :: []) (app l1 (app ((_CNOT q1 q) :: []) ((_H q) :: [])))), l2')
                   | _ -> None)
                | None -> None)
          else None
        | None -> None)
     | _ -> None)
  | None -> None

(** val search_for_Rz_pat2 : gate_list -> int -> (gate_app list * gate_list) option **)

let search_for_Rz_pat2 l q =
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
             | FU_PI4 _ ->
               (match next_two_qubit_gate l2' q with
                | Some p3 ->
                  let (p4, l4) = p3 in
                  let (p5, q4) = p4 in
                  let (l3, q3) = p5 in
                  if (&&) ((&&) ((=) q q4) ((=) q1 q3)) (does_not_reference l3 q3)
                  then Some
                         ((app l1
                            (app ((_CNOT q1 q) :: [])
                              (app ((App1 (u, q)) :: []) (app l3 ((_CNOT q1 q) :: []))))), l4)
                  else None
                | None -> None)
             | _ -> None)
          | None -> None)
    else None
  | None -> None

(** val search_for_Rz_pat3 : gate_list -> int -> (gate_app list * gate_list) option **)

let search_for_Rz_pat3 l q =
  match next_two_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2) = p0 in
    let (l1, q1) = p1 in if (=) q q1 then Some ((app l1 ((_CNOT q1 q2) :: [])), l2) else None
  | None -> None

(** val search_for_commuting_Rz_pat : gate_list -> int -> (gate_app list * gate_list) option **)

let search_for_commuting_Rz_pat l q =
  match search_for_Rz_pat1 l q with
  | Some p -> Some p
  | None -> (match search_for_Rz_pat2 l q with
             | Some p -> Some p
             | None -> search_for_Rz_pat3 l q)

(** val propagate_PI4 : int -> gate_list -> int -> int -> gate_list option **)

let rec propagate_PI4 k l q n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n' ->
    match next_single_qubit_gate l q with
    | Some p ->
      let (f, l') = p in
      (match f with
       | FU_PI4 k' ->
         let k'' = Z.add k k' in
         if Z.eqb k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
         then Some l'
         else if Z.ltb k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
              then Some ((_PI4 k'' q) :: l')
              else Some ((_PI4 (Z.sub k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))) q) :: l')
       | _ ->
         (match search_for_commuting_Rz_pat l q with
          | Some p0 ->
            let (l1, l2) = p0 in
            (match propagate_PI4 k l2 q n' with
             | Some l'0 -> Some (app l1 l'0)
             | None -> None)
          | None -> None))
    | None ->
      (match search_for_commuting_Rz_pat l q with
       | Some p ->
         let (l1, l2) = p in
         (match propagate_PI4 k l2 q n' with
          | Some l' -> Some (app l1 l')
          | None -> None)
       | None -> None))
    n

(** val propagate_H : gate_list -> int -> gate_list option **)

let propagate_H l q =
  match next_single_qubit_gate l q with
  | Some p -> let (f, l') = p in (match f with
                                  | FU_H -> Some l'
                                  | _ -> None)
  | None -> None

(** val propagate_X : gate_list -> int -> int -> gate_list option **)

let rec propagate_X l q n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n' ->
    match next_single_qubit_gate l q with
    | Some p ->
      let (f, l') = p in
      (match f with
       | FU_X -> Some l'
       | _ ->
         (match search_for_commuting_X_pat l q with
          | Some p0 ->
            let (l1, l2) = p0 in
            (match propagate_X l2 q n' with
             | Some l'0 -> Some (app l1 l'0)
             | None -> None)
          | None -> None))
    | None ->
      (match search_for_commuting_X_pat l q with
       | Some p ->
         let (l1, l2) = p in (match propagate_X l2 q n' with
                              | Some l' -> Some (app l1 l')
                              | None -> None)
       | None -> None))
    n

(** val propagate_CNOT : gate_list -> int -> int -> int -> gate_list option **)

let propagate_CNOT l q1 q2 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun _ ->
    match next_two_qubit_gate l q1 with
    | Some p ->
      let (p0, l2) = p in
      let (p1, q2') = p0 in
      let (l1, q1') = p1 in
      if (&&) ((&&) ((=) q1 q1') ((=) q2 q2')) (does_not_reference l1 q2) then Some (app l1 l2) else None
    | None -> None)
    n

(** val cancel_gates' : gate_list -> int -> gate_list **)

let rec cancel_gates' l n =
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
            (match propagate_H t q with
             | Some l' -> cancel_gates' l' n'
             | None -> (_H q) :: (cancel_gates' t n'))
          | FU_X ->
            (match propagate_X t q (length t) with
             | Some l' -> cancel_gates' l' n'
             | None -> (_X q) :: (cancel_gates' t n'))
          | FU_PI4 k ->
            (match propagate_PI4 k t q (length t) with
             | Some l' -> cancel_gates' l' n'
             | None -> (_PI4 k q) :: (cancel_gates' t n'))
          | FU_CNOT -> [])
       | App2 (f, q1, q2) ->
         (match f with
          | FU_CNOT ->
            (match propagate_CNOT t q1 q2 (length t) with
             | Some l' -> cancel_gates' l' n'
             | None -> (_CNOT q1 q2) :: (cancel_gates' t n'))
          | _ -> [])))
    n

(** val cancel_gates : gate_list -> gate_list **)

let cancel_gates l =
  cancel_gates' l (length l)
