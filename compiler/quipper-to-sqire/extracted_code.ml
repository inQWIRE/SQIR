
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

(** val mul : int -> int -> int **)

let rec mul = ( * )

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

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

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

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

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

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul ((fun p->2*p) 1) r) 1 in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q), r')
      else ((add (mul ((fun p->2*p) 1) q) 1), (sub r' b)))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul ((fun p->2*p) 1) r in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q), r')
      else ((add (mul ((fun p->2*p) 1) q) 1), (sub r' b)))
      (fun _ -> if leb ((fun p->2*p) 1) b then (0, 1) else (1, 0))
      a

  (** val div_eucl : int -> int -> int * int **)

  let div_eucl a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, 0))
        (fun _ -> pos_div_eucl a' b)
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q), 0))
           (fun _ -> ((opp (add q 1)), (add b r)))
           (fun _ -> ((opp (add q 1)), (add b r)))
           r))
        b)
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, 0))
        (fun _ ->
        let (q, r) = pos_div_eucl a' b in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q), 0))
           (fun _ -> ((opp (add q 1)), (sub b r)))
           (fun _ -> ((opp (add q 1)), (sub b r)))
           r))
        (fun b' -> let (q, r) = pos_div_eucl a' b' in (q, (opp r)))
        b)
      a

  (** val modulo : int -> int -> int **)

  let modulo a b =
    let (_, r) = div_eucl a b in r
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = List.rev

type fUnitary =
| FU_H
| FU_X
| FU_PI4 of int
| FU_CNOT

(** val fU_P : fUnitary **)

let fU_P =
  FU_PI4 ((fun p->2*p) 1)

(** val fU_PDAG : fUnitary **)

let fU_PDAG =
  FU_PI4 ((fun p->2*p) ((fun p->1+2*p) 1))

(** val match_gate : fUnitary -> fUnitary -> bool **)

let match_gate u u' =
  match u with
  | FU_H -> (match u' with
             | FU_H -> true
             | _ -> false)
  | FU_X -> (match u' with
             | FU_X -> true
             | _ -> false)
  | FU_PI4 k -> (match u' with
                 | FU_PI4 k' -> Z.eqb k k'
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

(** val _PI4 : int -> int -> gate_app **)

let _PI4 k n =
  App1 ((FU_PI4 k), n)

(** val _CNOT : int -> int -> gate_app **)

let _CNOT m n =
  App2 (FU_CNOT, m, n)

(** val _T : int -> gate_app **)

let _T n =
  App1 ((FU_PI4 1), n)

(** val _P : int -> gate_app **)

let _P n =
  App1 ((FU_PI4 ((fun p->2*p) 1)), n)

(** val _Z : int -> gate_app **)

let _Z n =
  App1 ((FU_PI4 ((fun p->2*p) ((fun p->2*p) 1))), n)

(** val _PDAG : int -> gate_app **)

let _PDAG n =
  App1 ((FU_PI4 ((fun p->2*p) ((fun p->1+2*p) 1))), n)

(** val _TDAG : int -> gate_app **)

let _TDAG n =
  App1 ((FU_PI4 ((fun p->1+2*p) ((fun p->1+2*p) 1))), n)

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
               let (l1, m') = p1 in
               Some (((((App2 (u, m, n)) :: l1), m'), n'), l2)
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
  (_H c) :: ((_CNOT b c) :: ((_TDAG c) :: ((_CNOT a c) :: ((_T c) :: ((_CNOT b
                                                                      c) :: (
    (_TDAG c) :: ((_CNOT a c) :: ((_CNOT a b) :: ((_TDAG b) :: ((_CNOT a b) :: (
    (_T a) :: ((_T b) :: ((_T c) :: ((_H c) :: []))))))))))))))

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
    gate_list -> int -> single_qubit_pattern -> single_qubit_pattern ->
    gate_list option **)

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
  replace_single_qubit_pattern l q (FU_H :: (fU_P :: (FU_H :: [])))
    (fU_PDAG :: (FU_H :: (fU_PDAG :: [])))

(** val apply_H_equivalence2 : int -> gate_list -> gate_list option **)

let apply_H_equivalence2 q l =
  replace_single_qubit_pattern l q (FU_H :: (fU_PDAG :: (FU_H :: [])))
    (fU_P :: (FU_H :: (fU_P :: [])))

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
                                 Some
                                   (app (rev l5) (app ((_CNOT n m) :: []) l6))
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
                                 Some
                                   (app (rev l5) (app ((_CNOT n m) :: []) l6))
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
  match remove_single_qubit_pattern l q (FU_H :: (fU_P :: [])) with
  | Some l1 ->
    (match next_two_qubit_gate l1 q with
     | Some p ->
       let (p0, l3) = p in
       let (p1, q2) = p0 in
       let (l2, q1) = p1 in
       if (=) q q2
       then (match remove_single_qubit_pattern l3 q (fU_PDAG :: (FU_H :: [])) with
             | Some l4 ->
               Some
                 (app l2
                   (app ((_PDAG q2) :: ((_CNOT q1 q2) :: ((_P q2) :: []))) l4))
             | None -> None)
       else None
     | None -> None)
  | None -> None

(** val apply_H_equivalence5 : int -> gate_list -> gate_app list option **)

let apply_H_equivalence5 q l =
  match remove_single_qubit_pattern l q (FU_H :: (fU_PDAG :: [])) with
  | Some l1 ->
    (match next_two_qubit_gate l1 q with
     | Some p ->
       let (p0, l3) = p in
       let (p1, q2) = p0 in
       let (l2, q1) = p1 in
       if (=) q q2
       then (match remove_single_qubit_pattern l3 q (fU_P :: (FU_H :: [])) with
             | Some l4 ->
               Some
                 (app l2
                   (app ((_P q2) :: ((_CNOT q1 q2) :: ((_PDAG q2) :: []))) l4))
             | None -> None)
       else None
     | None -> None)
  | None -> None

(** val apply_H_equivalence : gate_list -> int -> gate_list option **)

let apply_H_equivalence l q =
  try_rewrites l
    ((apply_H_equivalence1 q) :: ((apply_H_equivalence2 q) :: ((apply_H_equivalence3
                                                                 q) :: (
    (apply_H_equivalence4 q) :: ((apply_H_equivalence5 q) :: [])))))

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
                  if Z.eqb
                       (Z.modulo (Z.add k k') ((fun p->2*p) ((fun p->2*p)
                         ((fun p->2*p) 1)))) 0
                  then cancel_gates_simple' t' acc n'
                  else cancel_gates_simple'
                         ((_PI4
                            (Z.modulo (Z.add k k') ((fun p->2*p) ((fun p->2*p)
                              ((fun p->2*p) 1)))) q) :: t') acc n'
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
               if (&&) ((&&) ((=) q1 q1') ((=) q2 q2'))
                    (does_not_reference l1 q2)
               then cancel_gates_simple' (app l1 l2) acc n'
               else cancel_gates_simple' t ((_CNOT q1 q2) :: acc) n'
             | None -> cancel_gates_simple' t ((_CNOT q1 q2) :: acc) n')
          | _ -> [])))
    n

(** val cancel_gates_simple : gate_list -> gate_list **)

let cancel_gates_simple l =
  cancel_gates_simple' l [] (length l)

(** val search_for_commuting_X_pat :
    gate_list -> int -> (gate_app list * gate_list) option **)

let search_for_commuting_X_pat l q =
  match next_two_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2) = p0 in
    let (l1, q1) = p1 in
    if (=) q q2 then Some ((app l1 ((_CNOT q1 q2) :: [])), l2) else None
  | None -> None

(** val search_for_Rz_pat1 :
    gate_list -> int -> (gate_app list * gate_list) option **)

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
                     Some
                       ((app ((_H q) :: [])
                          (app l1 (app ((_CNOT q1 q) :: []) ((_H q) :: [])))),
                       l2')
                   | _ -> None)
                | None -> None)
          else None
        | None -> None)
     | _ -> None)
  | None -> None

(** val search_for_Rz_pat2 :
    gate_list -> int -> (gate_app list * gate_list) option **)

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
                  if (&&) ((&&) ((=) q q4) ((=) q1 q3))
                       (does_not_reference l3 q3)
                  then Some
                         ((app l1
                            (app ((_CNOT q1 q) :: [])
                              (app ((App1 (u, q)) :: [])
                                (app l3 ((_CNOT q1 q) :: []))))), l4)
                  else None
                | None -> None)
             | _ -> None)
          | None -> None)
    else None
  | None -> None

(** val search_for_Rz_pat3 :
    gate_list -> int -> (gate_app list * gate_list) option **)

let search_for_Rz_pat3 l q =
  match next_two_qubit_gate l q with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2) = p0 in
    let (l1, q1) = p1 in
    if (=) q q1 then Some ((app l1 ((_CNOT q1 q2) :: [])), l2) else None
  | None -> None

(** val search_for_commuting_Rz_pat :
    gate_list -> int -> (gate_app list * gate_list) option **)

let search_for_commuting_Rz_pat l q =
  match search_for_Rz_pat1 l q with
  | Some p -> Some p
  | None ->
    (match search_for_Rz_pat2 l q with
     | Some p -> Some p
     | None -> search_for_Rz_pat3 l q)

(** val search_for_CNOT_pat1 :
    gate_list -> int -> int -> (gate_list * gate_list) option **)

let search_for_CNOT_pat1 l q1 _ =
  match next_single_qubit_gate l q1 with
  | Some p ->
    let (f, l') = p in
    (match f with
     | FU_PI4 k -> Some (((_PI4 k q1) :: []), l')
     | _ -> None)
  | None -> None

(** val search_for_CNOT_pat2 :
    gate_list -> int -> int -> (gate_app list * gate_list) option **)

let search_for_CNOT_pat2 l q1 q2 =
  match next_two_qubit_gate l q2 with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2') = p0 in
    let (l1, q1') = p1 in
    if (=) q2 q2'
    then if (&&) (does_not_reference l1 q1) (does_not_reference l1 q1')
         then Some ((app l1 ((_CNOT q1' q2) :: [])), l2)
         else None
    else None
  | None -> None

(** val search_for_CNOT_pat3 :
    gate_list -> int -> int -> (gate_app list * gate_list) option **)

let search_for_CNOT_pat3 l q1 q2 =
  match next_two_qubit_gate l q1 with
  | Some p ->
    let (p0, l2) = p in
    let (p1, q2') = p0 in
    let (l1, q1') = p1 in
    if (=) q1 q1'
    then if (&&) (does_not_reference l1 q2) (does_not_reference l1 q2')
         then Some ((app l1 ((_CNOT q1 q2') :: [])), l2)
         else None
    else None
  | None -> None

(** val search_for_CNOT_pat4 :
    gate_list -> int -> int -> (gate_app list * gate_list) option **)

let search_for_CNOT_pat4 l q1 q2 =
  match next_single_qubit_gate l q2 with
  | Some p ->
    let (f, l') = p in
    (match f with
     | FU_H ->
       (match next_two_qubit_gate l' q2 with
        | Some p0 ->
          let (p1, l2) = p0 in
          let (p2, q2') = p1 in
          let (l1, q1') = p2 in
          if (&&) ((=) q2 q1') (does_not_reference l1 q1)
          then (match next_single_qubit_gate l2 q2 with
                | Some p3 ->
                  let (f0, l2') = p3 in
                  (match f0 with
                   | FU_H ->
                     Some
                       ((app ((_H q2) :: [])
                          (app l1 (app ((_CNOT q2 q2') :: []) ((_H q2) :: [])))),
                       l2')
                   | _ -> None)
                | None -> None)
          else None
        | None -> None)
     | _ -> None)
  | None -> None

(** val search_for_commuting_CNOT_pat :
    gate_list -> int -> int -> (gate_list * gate_list) option **)

let search_for_commuting_CNOT_pat l q1 q2 =
  match search_for_CNOT_pat1 l q1 q2 with
  | Some p -> Some p
  | None ->
    (match search_for_CNOT_pat2 l q1 q2 with
     | Some p -> Some p
     | None ->
       (match search_for_CNOT_pat3 l q1 q2 with
        | Some p -> Some p
        | None -> search_for_CNOT_pat4 l q1 q2))

(** val propagate_PI4 : int -> gate_list -> int -> int -> gate_list option **)

let rec propagate_PI4 k l q n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some l)
    (fun n' ->
    match next_single_qubit_gate l q with
    | Some p ->
      let (f, l') = p in
      (match f with
       | FU_PI4 k' ->
         if Z.eqb
              (Z.modulo (Z.add k k') ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                1)))) 0
         then Some l'
         else Some
                ((_PI4
                   (Z.modulo (Z.add k k') ((fun p->2*p) ((fun p->2*p)
                     ((fun p->2*p) 1)))) q) :: l')
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

let rec propagate_H l q =
  match next_single_qubit_gate l q with
  | Some p -> let (f, l') = p in (match f with
                                  | FU_H -> Some l'
                                  | _ -> None)
  | None -> None

(** val propagate_X : gate_list -> int -> int -> gate_list option **)

let rec propagate_X l q n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some l)
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
         let (l1, l2) = p in
         (match propagate_X l2 q n' with
          | Some l' -> Some (app l1 l')
          | None -> None)
       | None -> None))
    n

(** val propagate_CNOT : gate_list -> int -> int -> int -> gate_list option **)

let rec propagate_CNOT l q1 q2 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some l)
    (fun n' ->
    match next_two_qubit_gate l q1 with
    | Some p ->
      let (p0, l2) = p in
      let (p1, q2') = p0 in
      let (l1, q1') = p1 in
      if (&&) ((&&) ((=) q1 q1') ((=) q2 q2')) (does_not_reference l1 q2)
      then Some (app l1 l2)
      else None
    | None ->
      (match search_for_commuting_CNOT_pat l q1 q2 with
       | Some p ->
         let (l1, l2) = p in
         (match propagate_CNOT l2 q1 q2 n' with
          | Some l' -> Some (app l1 l')
          | None -> None)
       | None -> None))
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
