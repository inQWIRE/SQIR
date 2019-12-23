
(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

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

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Pervasives.succ n) m
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = List.rev

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Pervasives.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x0 y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p0 q))
        (fun q -> (fun p->2*p) (add_carry p0 q))
        (fun _ -> (fun p->1+2*p) (succ p0))
        y)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p0 q))
        (fun q -> (fun p->1+2*p) (add p0 q))
        (fun _ -> (fun p->2*p) (succ p0))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x0

  (** val pred_double : int -> int **)

  let rec pred_double x0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> (fun p->1+2*p) ((fun p->2*p) p0))
      (fun p0 -> (fun p->1+2*p) (pred_double p0))
      (fun _ -> 1)
      x0

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let rec eqb p0 q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p1 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p1 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p1 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p1 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p0
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p0 -> ((fun p->2*p) p0))
      (fun p0 -> (~-) ((fun p->2*p) p0))
      x0

  (** val succ_double : int -> int **)

  let succ_double x0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p0 -> ((fun p->1+2*p) p0))
      (fun p0 -> (~-) (Pos.pred_double p0))
      x0

  (** val pred_double : int -> int **)

  let pred_double x0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p0 -> (Pos.pred_double p0))
      (fun p0 -> (~-) ((fun p->1+2*p) p0))
      x0

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x0 y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p0 q))
        (fun q -> succ_double (pos_sub p0 q))
        (fun _ -> ((fun p->2*p) p0))
        y)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p0 q))
        (fun q -> double (pos_sub p0 q))
        (fun _ -> (Pos.pred_double p0))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x0

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val ltb : int -> int -> bool **)

  let ltb x0 y =
    match compare x0 y with
    | Lt -> true
    | _ -> false

  (** val eqb : int -> int -> bool **)

  let rec eqb x0 y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Pos.eqb p0 q)
        (fun _ -> false)
        y)
      (fun p0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Pos.eqb p0 q)
        y)
      x0
 end

(** val inb : int -> int list -> bool **)

let rec inb a = function
| [] -> false
| b :: ls' -> (||) ((=) b a) (inb a ls')

type 'u gate_app =
| App1 of 'u * int
| App2 of 'u * int * int
| App3 of 'u * int * int * int

type 'u gate_list = 'u gate_app list

(** val uc_well_typed_l_b : int -> 'a1 gate_list -> bool **)

let rec uc_well_typed_l_b dim = function
| [] -> Nat.ltb 0 dim
| g :: t0 ->
  (match g with
   | App1 (_, n) -> (&&) (Nat.ltb n dim) (uc_well_typed_l_b dim t0)
   | App2 (_, m, n) ->
     (&&) ((&&) ((&&) (Nat.ltb m dim) (Nat.ltb n dim)) (negb ((=) m n)))
       (uc_well_typed_l_b dim t0)
   | App3 (_, m, n, p0) ->
     (&&)
       ((&&)
         ((&&)
           ((&&)
             ((&&) ((&&) (Nat.ltb m dim) (Nat.ltb n dim)) (Nat.ltb p0 dim))
             (negb ((=) m n))) (negb ((=) n p0))) (negb ((=) m p0)))
       (uc_well_typed_l_b dim t0))

(** val next_single_qubit_gate :
    'a1 gate_list -> int -> (('a1 gate_list * 'a1) * 'a1 gate_list) option **)

let rec next_single_qubit_gate l q =
  match l with
  | [] -> None
  | g :: t0 ->
    (match g with
     | App1 (u, n) ->
       if (=) n q
       then Some (([], u), t0)
       else (match next_single_qubit_gate t0 q with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (l1, u') = p1 in Some ((((App1 (u, n)) :: l1), u'), l2)
             | None -> None)
     | App2 (u, m, n) ->
       if (||) ((=) m q) ((=) n q)
       then None
       else (match next_single_qubit_gate t0 q with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (l1, u') = p1 in Some ((((App2 (u, m, n)) :: l1), u'), l2)
             | None -> None)
     | App3 (u, m, n, p0) ->
       if (||) ((||) ((=) m q) ((=) n q)) ((=) p0 q)
       then None
       else (match next_single_qubit_gate t0 q with
             | Some p1 ->
               let (p2, l2) = p1 in
               let (l1, u') = p2 in
               Some ((((App3 (u, m, n, p0)) :: l1), u'), l2)
             | None -> None))

(** val last_single_qubit_gate :
    'a1 gate_list -> int -> (('a1 gate_list * 'a1) * 'a1 gate_list) option **)

let last_single_qubit_gate l q =
  match next_single_qubit_gate (rev l) q with
  | Some p0 ->
    let (p1, l2) = p0 in let (l1, u) = p1 in Some (((rev l2), u), (rev l1))
  | None -> None

(** val next_two_qubit_gate :
    'a1 gate_list -> int -> (((('a1 gate_list * 'a1) * int) * int) * 'a1
    gate_list) option **)

let rec next_two_qubit_gate l q =
  match l with
  | [] -> None
  | g :: t0 ->
    (match g with
     | App1 (u, n) ->
       if (=) n q
       then None
       else (match next_two_qubit_gate t0 q with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (p2, n') = p1 in
               let (p3, m') = p2 in
               let (l1, u') = p3 in
               Some ((((((App1 (u, n)) :: l1), u'), m'), n'), l2)
             | None -> None)
     | App2 (u, m, n) ->
       if (||) ((=) m q) ((=) n q)
       then Some (((([], u), m), n), t0)
       else (match next_two_qubit_gate t0 q with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (p2, n') = p1 in
               let (p3, m') = p2 in
               let (l1, u') = p3 in
               Some ((((((App2 (u, m, n)) :: l1), u'), m'), n'), l2)
             | None -> None)
     | App3 (u, m, n, p0) ->
       if (||) ((||) ((=) m q) ((=) n q)) ((=) p0 q)
       then None
       else (match next_two_qubit_gate t0 q with
             | Some p1 ->
               let (p2, l2) = p1 in
               let (p3, n') = p2 in
               let (p4, m') = p3 in
               let (l1, u') = p4 in
               Some ((((((App3 (u, m, n, p0)) :: l1), u'), m'), n'), l2)
             | None -> None))

(** val next_gate :
    'a1 gate_list -> int list -> (('a1 gate_list * 'a1 gate_app) * 'a1
    gate_list) option **)

let rec next_gate l qs =
  match l with
  | [] -> None
  | g :: t0 ->
    (match g with
     | App1 (u, q) ->
       if inb q qs
       then Some (([], (App1 (u, q))), t0)
       else (match next_gate t0 qs with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (l1, g0) = p1 in Some ((((App1 (u, q)) :: l1), g0), l2)
             | None -> None)
     | App2 (u, q1, q2) ->
       if (||) (inb q1 qs) (inb q2 qs)
       then Some (([], (App2 (u, q1, q2))), t0)
       else (match next_gate t0 qs with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (l1, g0) = p1 in
               Some ((((App2 (u, q1, q2)) :: l1), g0), l2)
             | None -> None)
     | App3 (u, q1, q2, q3) ->
       if (||) ((||) (inb q1 qs) (inb q2 qs)) (inb q3 qs)
       then Some (([], (App3 (u, q1, q2, q3))), t0)
       else (match next_gate t0 qs with
             | Some p0 ->
               let (p1, l2) = p0 in
               let (l1, g0) = p1 in
               Some ((((App3 (u, q1, q2, q3)) :: l1), g0), l2)
             | None -> None))

(** val does_not_reference_appl : int -> 'a1 gate_app -> bool **)

let does_not_reference_appl q = function
| App1 (_, n) -> negb ((=) n q)
| App2 (_, m, n) -> negb ((||) ((=) m q) ((=) n q))
| App3 (_, m, n, p0) -> negb ((||) ((||) ((=) m q) ((=) n q)) ((=) p0 q))

(** val does_not_reference : 'a1 gate_list -> int -> bool **)

let does_not_reference l q =
  forallb (does_not_reference_appl q) l

(** val try_rewrites :
    'a1 gate_list -> ('a1 gate_list -> 'a1 gate_list option) list -> 'a1
    gate_list option **)

let rec try_rewrites l = function
| [] -> None
| h0 :: t0 -> (match h0 l with
               | Some l' -> Some l'
               | None -> try_rewrites l t0)

(** val try_rewrites2 :
    'a1 gate_list -> ('a1 gate_list -> ('a1 gate_list * 'a1 gate_list)
    option) list -> ('a1 gate_list * 'a1 gate_list) option **)

let rec try_rewrites2 l = function
| [] -> None
| h0 :: t0 ->
  (match h0 l with
   | Some l' -> Some l'
   | None -> try_rewrites2 l t0)

(** val propagate :
    'a1 gate_list -> ('a1 gate_list -> ('a1 gate_list * 'a1 gate_list)
    option) list -> ('a1 gate_list -> 'a1 gate_list option) list -> int ->
    'a1 gate_list option **)

let rec propagate l commute_rules cancel_rules n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n' ->
    match try_rewrites l cancel_rules with
    | Some l' -> Some l'
    | None ->
      (match try_rewrites2 l commute_rules with
       | Some p0 ->
         let (l1, l2) = p0 in
         (match propagate l2 commute_rules cancel_rules n' with
          | Some l2' -> Some (app l1 l2')
          | None -> None)
       | None -> None))
    n

type 'u single_qubit_pattern = 'u list

(** val single_qubit_pattern_to_program :
    'a1 single_qubit_pattern -> int -> 'a1 gate_list **)

let rec single_qubit_pattern_to_program pat q =
  match pat with
  | [] -> []
  | u :: t0 -> (App1 (u, q)) :: (single_qubit_pattern_to_program t0 q)

(** val remove_single_qubit_pattern :
    'a1 gate_list -> int -> 'a1 single_qubit_pattern -> ('a1 -> 'a1 -> bool)
    -> 'a1 gate_list option **)

let rec remove_single_qubit_pattern l q pat match_gate0 =
  match pat with
  | [] -> Some l
  | u :: t0 ->
    (match next_single_qubit_gate l q with
     | Some p0 ->
       let (p1, l2) = p0 in
       let (l1, u') = p1 in
       if match_gate0 u u'
       then remove_single_qubit_pattern (app l1 l2) q t0 match_gate0
       else None
     | None -> None)

(** val replace_single_qubit_pattern :
    'a1 gate_list -> int -> 'a1 single_qubit_pattern -> 'a1
    single_qubit_pattern -> ('a1 -> 'a1 -> bool) -> 'a1 gate_list option **)

let replace_single_qubit_pattern l q pat rep match_gate0 =
  match remove_single_qubit_pattern l q pat match_gate0 with
  | Some l' -> Some (app (single_qubit_pattern_to_program rep q) l')
  | None -> None

type pI4_Unitary =
| UPI4_H
| UPI4_X
| UPI4_PI4 of int
| UPI4_CNOT

(** val uPI4_T : pI4_Unitary **)

let uPI4_T =
  UPI4_PI4 1

(** val uPI4_P : pI4_Unitary **)

let uPI4_P =
  UPI4_PI4 ((fun p->2*p) 1)

(** val uPI4_Z : pI4_Unitary **)

let uPI4_Z =
  UPI4_PI4 ((fun p->2*p) ((fun p->2*p) 1))

(** val uPI4_PDAG : pI4_Unitary **)

let uPI4_PDAG =
  UPI4_PI4 ((fun p->2*p) ((fun p->1+2*p) 1))

(** val uPI4_TDAG : pI4_Unitary **)

let uPI4_TDAG =
  UPI4_PI4 ((fun p->1+2*p) ((fun p->1+2*p) 1))

(** val t : int -> pI4_Unitary gate_app **)

let t q =
  App1 (uPI4_T, q)

(** val tDAG : int -> pI4_Unitary gate_app **)

let tDAG q =
  App1 (uPI4_TDAG, q)

(** val p : int -> pI4_Unitary gate_app **)

let p q =
  App1 (uPI4_P, q)

(** val pDAG : int -> pI4_Unitary gate_app **)

let pDAG q =
  App1 (uPI4_PDAG, q)

(** val z : int -> pI4_Unitary gate_app **)

let z q =
  App1 (uPI4_Z, q)

(** val h : int -> pI4_Unitary gate_app **)

let h q =
  App1 (UPI4_H, q)

(** val x : int -> pI4_Unitary gate_app **)

let x q =
  App1 (UPI4_X, q)

(** val cNOT : int -> int -> pI4_Unitary gate_app **)

let cNOT q1 q2 =
  App2 (UPI4_CNOT, q1, q2)

type pI4_ucom_l = pI4_Unitary gate_list

(** val cCX : int -> int -> int -> pI4_ucom_l **)

let cCX a b c =
  (h c) :: ((cNOT b c) :: ((tDAG c) :: ((cNOT a c) :: ((t c) :: ((cNOT b c) :: (
    (tDAG c) :: ((cNOT a c) :: ((cNOT a b) :: ((tDAG b) :: ((cNOT a b) :: (
    (t a) :: ((t b) :: ((t c) :: ((h c) :: []))))))))))))))

(** val cCZ : int -> int -> int -> pI4_ucom_l **)

let cCZ a b c =
  (cNOT b c) :: ((tDAG c) :: ((cNOT a c) :: ((t c) :: ((cNOT b c) :: (
    (tDAG c) :: ((cNOT a c) :: ((cNOT a b) :: ((tDAG b) :: ((cNOT a b) :: (
    (t a) :: ((t b) :: ((t c) :: []))))))))))))

(** val match_gate : pI4_Unitary -> pI4_Unitary -> bool **)

let match_gate u u' =
  match u with
  | UPI4_H -> (match u' with
               | UPI4_H -> true
               | _ -> false)
  | UPI4_X -> (match u' with
               | UPI4_X -> true
               | _ -> false)
  | UPI4_PI4 k -> (match u' with
                   | UPI4_PI4 k' -> Z.eqb k k'
                   | _ -> false)
  | UPI4_CNOT -> (match u' with
                  | UPI4_CNOT -> true
                  | _ -> false)

(** val pI4_list_well_typed_b : int -> pI4_ucom_l -> bool **)

let pI4_list_well_typed_b =
  uc_well_typed_l_b

(** val rz_commute_rule1 :
    int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
    option **)

let rz_commute_rule1 q l =
  match next_single_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_H ->
       (match next_two_qubit_gate l2 q with
        | Some p3 ->
          let (p4, l4) = p3 in
          let (p5, q2) = p4 in
          let (p6, q1) = p5 in
          let (l3, p7) = p6 in
          (match p7 with
           | UPI4_CNOT ->
             if (=) q q2
             then (match next_single_qubit_gate l4 q with
                   | Some p8 ->
                     let (p9, l6) = p8 in
                     let (l5, p10) = p9 in
                     (match p10 with
                      | UPI4_H ->
                        Some
                          ((app l1
                             (app ((h q) :: [])
                               (app l3
                                 (app ((cNOT q1 q) :: [])
                                   (app l5 ((h q) :: [])))))), l6)
                      | _ -> None)
                   | None -> None)
             else None
           | _ -> None)
        | None -> None)
     | _ -> None)
  | None -> None

(** val rz_commute_rule2 :
    int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
    option **)

let rz_commute_rule2 q l =
  match next_two_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q2) = p1 in
    let (p3, q1) = p2 in
    let (l1, p4) = p3 in
    (match p4 with
     | UPI4_CNOT ->
       if (=) q q2
       then (match next_single_qubit_gate l2 q with
             | Some p5 ->
               let (p6, l4) = p5 in
               let (l3, u) = p6 in
               (match u with
                | UPI4_PI4 _ ->
                  (match next_two_qubit_gate l4 q with
                   | Some p7 ->
                     let (p8, l6) = p7 in
                     let (p9, q4) = p8 in
                     let (p10, q3) = p9 in
                     let (l5, p11) = p10 in
                     (match p11 with
                      | UPI4_CNOT ->
                        if (&&) ((&&) ((=) q q4) ((=) q1 q3))
                             (does_not_reference (app l3 l5) q3)
                        then Some
                               ((app l1
                                  (app ((cNOT q1 q) :: [])
                                    (app l3
                                      (app ((App1 (u, q)) :: [])
                                        (app l5 ((cNOT q1 q) :: [])))))), l6)
                        else None
                      | _ -> None)
                   | None -> None)
                | _ -> None)
             | None -> None)
       else None
     | _ -> None)
  | None -> None

(** val rz_commute_rule3 :
    int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
    option **)

let rz_commute_rule3 q l =
  match next_two_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q2) = p1 in
    let (p3, q1) = p2 in
    let (l1, p4) = p3 in
    (match p4 with
     | UPI4_CNOT ->
       if (=) q q1 then Some ((app l1 ((cNOT q1 q2) :: [])), l2) else None
     | _ -> None)
  | None -> None

(** val rz_commute_rules :
    int -> (pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
    option) list **)

let rz_commute_rules q =
  (rz_commute_rule1 q) :: ((rz_commute_rule2 q) :: ((rz_commute_rule3 q) :: []))

(** val rz_cancel_rule :
    int -> int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let rz_cancel_rule q k l =
  match next_single_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_PI4 k' ->
       let k'' = Z.add k k' in
       if Z.eqb k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
       then Some (app l1 l2)
       else if Z.ltb k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
            then Some ((App1 ((UPI4_PI4 k''), q)) :: (app l1 l2))
            else Some ((App1 ((UPI4_PI4
                   (Z.sub k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))),
                   q)) :: (app l1 l2))
     | _ -> None)
  | None -> None

(** val h_cancel_rule :
    int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let h_cancel_rule q l =
  match next_single_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_H -> Some (app l1 l2)
     | _ -> None)
  | None -> None

(** val x_commute_rule :
    int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary gate_list)
    option **)

let x_commute_rule q l =
  match next_two_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q2) = p1 in
    let (p3, q1) = p2 in
    let (l1, p4) = p3 in
    (match p4 with
     | UPI4_CNOT ->
       if (=) q q2 then Some ((app l1 ((cNOT q1 q2) :: [])), l2) else None
     | _ -> None)
  | None -> None

(** val x_cancel_rule :
    int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let x_cancel_rule q l =
  match next_single_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_X -> Some (app l1 l2)
     | _ -> None)
  | None -> None

(** val cNOT_commute_rule1 :
    int -> pI4_ucom_l -> (pI4_ucom_l * pI4_ucom_l) option **)

let cNOT_commute_rule1 q1 l =
  match next_single_qubit_gate l q1 with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, u) = p1 in
    (match u with
     | UPI4_PI4 _ -> Some (((App1 (u, q1)) :: []), (app l1 l2))
     | _ -> None)
  | None -> None

(** val cNOT_commute_rule2 :
    int -> int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary
    gate_list) option **)

let cNOT_commute_rule2 q1 q2 l =
  match next_two_qubit_gate l q2 with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q2') = p1 in
    let (p3, q1') = p2 in
    let (l1, p4) = p3 in
    (match p4 with
     | UPI4_CNOT ->
       if (=) q2 q2'
       then if does_not_reference l1 q1
            then Some ((app l1 ((cNOT q1' q2) :: [])), l2)
            else None
       else None
     | _ -> None)
  | None -> None

(** val cNOT_commute_rule3 :
    int -> int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary
    gate_list) option **)

let cNOT_commute_rule3 q1 q2 l =
  match next_two_qubit_gate l q1 with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q2') = p1 in
    let (p3, q1') = p2 in
    let (l1, p4) = p3 in
    (match p4 with
     | UPI4_CNOT ->
       if (=) q1 q1'
       then if does_not_reference l1 q2
            then Some ((app l1 ((cNOT q1 q2') :: [])), l2)
            else None
       else None
     | _ -> None)
  | None -> None

(** val cNOT_commute_rule4 :
    int -> int -> pI4_ucom_l -> (pI4_Unitary gate_app list * pI4_Unitary
    gate_app list) option **)

let cNOT_commute_rule4 q1 q2 l =
  match next_single_qubit_gate l q2 with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_H ->
       (match next_two_qubit_gate l2 q2 with
        | Some p3 ->
          let (p4, l4) = p3 in
          let (p5, q2') = p4 in
          let (p6, q1') = p5 in
          let (l3, p7) = p6 in
          (match p7 with
           | UPI4_CNOT ->
             if (&&) ((&&) ((=) q2 q1') (negb ((=) q1 q2')))
                  (does_not_reference (app l1 l3) q1)
             then (match next_single_qubit_gate l4 q2 with
                   | Some p8 ->
                     let (p9, l6) = p8 in
                     let (l5, p10) = p9 in
                     (match p10 with
                      | UPI4_H ->
                        Some
                          ((app l1
                             (app ((h q2) :: [])
                               (app l3
                                 (app ((cNOT q2 q2') :: []) ((h q2) :: []))))),
                          (app l5 l6))
                      | _ -> None)
                   | None -> None)
             else None
           | _ -> None)
        | None -> None)
     | _ -> None)
  | None -> None

(** val cNOT_commute_rules :
    int -> int -> (pI4_ucom_l -> (pI4_ucom_l * pI4_ucom_l) option) list **)

let cNOT_commute_rules q1 q2 =
  (cNOT_commute_rule1 q1) :: ((cNOT_commute_rule2 q1 q2) :: ((cNOT_commute_rule3
                                                               q1 q2) :: (
    (cNOT_commute_rule4 q1 q2) :: [])))

(** val cNOT_cancel_rule :
    int -> int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let cNOT_cancel_rule q1 q2 l =
  match next_two_qubit_gate l q1 with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (p2, q2') = p1 in
    let (p3, q1') = p2 in
    let (l1, p4) = p3 in
    (match p4 with
     | UPI4_CNOT ->
       if (&&) ((&&) ((=) q1 q1') ((=) q2 q2')) (does_not_reference l1 q2)
       then Some (app l1 l2)
       else None
     | _ -> None)
  | None -> None

(** val propagate_PI4 :
    int -> pI4_ucom_l -> int -> int -> pI4_Unitary gate_list option **)

let propagate_PI4 k l q n =
  propagate l (rz_commute_rules q) ((rz_cancel_rule q k) :: []) n

(** val propagate_H : pI4_ucom_l -> int -> pI4_Unitary gate_list option **)

let propagate_H l q =
  propagate l [] ((h_cancel_rule q) :: []) (Pervasives.succ 0)

(** val propagate_X :
    pI4_ucom_l -> int -> int -> pI4_Unitary gate_list option **)

let propagate_X l q n =
  propagate l ((x_commute_rule q) :: []) ((x_cancel_rule q) :: []) n

(** val propagate_CNOT :
    pI4_ucom_l -> int -> int -> int -> pI4_Unitary gate_list option **)

let propagate_CNOT l q1 q2 n =
  propagate l (cNOT_commute_rules q1 q2) ((cNOT_cancel_rule q1 q2) :: []) n

(** val cancel_single_qubit_gates' : pI4_ucom_l -> int -> pI4_ucom_l **)

let rec cancel_single_qubit_gates' l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | u :: t0 ->
      (match u with
       | App1 (p0, q) ->
         (match p0 with
          | UPI4_H ->
            (match propagate_H t0 q with
             | Some l' -> cancel_single_qubit_gates' l' n'
             | None -> (h q) :: (cancel_single_qubit_gates' t0 n'))
          | UPI4_X ->
            (match propagate_X t0 q (length t0) with
             | Some l' -> cancel_single_qubit_gates' l' n'
             | None -> (x q) :: (cancel_single_qubit_gates' t0 n'))
          | UPI4_PI4 k ->
            (match propagate_PI4 k t0 q (length t0) with
             | Some l' -> cancel_single_qubit_gates' l' n'
             | None ->
               (App1 ((UPI4_PI4 k), q)) :: (cancel_single_qubit_gates' t0 n'))
          | UPI4_CNOT -> u :: (cancel_single_qubit_gates' t0 n'))
       | _ -> u :: (cancel_single_qubit_gates' t0 n')))
    n

(** val cancel_single_qubit_gates : pI4_ucom_l -> pI4_ucom_l **)

let cancel_single_qubit_gates l =
  cancel_single_qubit_gates' l (length l)

(** val cancel_two_qubit_gates' : pI4_ucom_l -> int -> pI4_ucom_l **)

let rec cancel_two_qubit_gates' l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | u :: t0 ->
      (match u with
       | App2 (p0, q1, q2) ->
         (match p0 with
          | UPI4_CNOT ->
            (match propagate_CNOT t0 q1 q2 (length t0) with
             | Some l' -> cancel_two_qubit_gates' l' n'
             | None -> (cNOT q1 q2) :: (cancel_two_qubit_gates' t0 n'))
          | _ -> u :: (cancel_two_qubit_gates' t0 n'))
       | _ -> u :: (cancel_two_qubit_gates' t0 n')))
    n

(** val cancel_two_qubit_gates : pI4_ucom_l -> pI4_ucom_l **)

let cancel_two_qubit_gates l =
  cancel_two_qubit_gates' l (length l)

(** val apply_H_equivalence1 :
    int -> pI4_ucom_l -> pI4_Unitary gate_list option **)

let apply_H_equivalence1 q l =
  replace_single_qubit_pattern l q (UPI4_H :: (uPI4_P :: (UPI4_H :: [])))
    (uPI4_PDAG :: (UPI4_H :: (uPI4_PDAG :: []))) match_gate

(** val apply_H_equivalence2 :
    int -> pI4_ucom_l -> pI4_Unitary gate_list option **)

let apply_H_equivalence2 q l =
  replace_single_qubit_pattern l q (UPI4_H :: (uPI4_PDAG :: (UPI4_H :: [])))
    (uPI4_P :: (UPI4_H :: (uPI4_P :: []))) match_gate

(** val apply_H_equivalence3 :
    int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let apply_H_equivalence3 q l =
  match next_single_qubit_gate l q with
  | Some p0 ->
    let (p1, l2) = p0 in
    let (l1, p2) = p1 in
    (match p2 with
     | UPI4_H ->
       let l0 = app l1 l2 in
       (match next_two_qubit_gate l0 q with
        | Some p3 ->
          let (p4, l3) = p3 in
          let (p5, n) = p4 in
          let (p6, m) = p5 in
          let (l4, p7) = p6 in
          (match p7 with
           | UPI4_CNOT ->
             if (=) q m
             then (match last_single_qubit_gate l4 n with
                   | Some p8 ->
                     let (p9, l1_2) = p8 in
                     let (l1_1, p10) = p9 in
                     (match p10 with
                      | UPI4_H ->
                        let l5 = app l1_1 l1_2 in
                        (match next_single_qubit_gate l3 q with
                         | Some p11 ->
                           let (p12, l2_2) = p11 in
                           let (l2_1, p13) = p12 in
                           (match p13 with
                            | UPI4_H ->
                              let l6 = app l2_1 l2_2 in
                              (match next_single_qubit_gate l6 n with
                               | Some p14 ->
                                 let (p15, l2_3) = p14 in
                                 let (l2_4, p16) = p15 in
                                 (match p16 with
                                  | UPI4_H ->
                                    let l7 = app l2_4 l2_3 in
                                    Some (app l5 (app ((cNOT n q) :: []) l7))
                                  | _ -> None)
                               | None -> None)
                            | _ -> None)
                         | None -> None)
                      | _ -> None)
                   | None -> None)
             else (match last_single_qubit_gate l4 m with
                   | Some p8 ->
                     let (p9, l1_2) = p8 in
                     let (l1_1, p10) = p9 in
                     (match p10 with
                      | UPI4_H ->
                        let l5 = app l1_1 l1_2 in
                        (match next_single_qubit_gate l3 q with
                         | Some p11 ->
                           let (p12, l2_2) = p11 in
                           let (l2_1, p13) = p12 in
                           (match p13 with
                            | UPI4_H ->
                              let l6 = app l2_1 l2_2 in
                              (match next_single_qubit_gate l6 m with
                               | Some p14 ->
                                 let (p15, l2_3) = p14 in
                                 let (l2_4, p16) = p15 in
                                 (match p16 with
                                  | UPI4_H ->
                                    let l7 = app l2_4 l2_3 in
                                    Some (app l5 (app ((cNOT q m) :: []) l7))
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
    int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let apply_H_equivalence4 q l =
  match remove_single_qubit_pattern l q (UPI4_H :: (uPI4_P :: [])) match_gate with
  | Some l1 ->
    (match next_two_qubit_gate l1 q with
     | Some p0 ->
       let (p1, l3) = p0 in
       let (p2, q2) = p1 in
       let (p3, q1) = p2 in
       let (l2, p4) = p3 in
       (match p4 with
        | UPI4_CNOT ->
          if (=) q q2
          then (match remove_single_qubit_pattern l3 q
                        (uPI4_PDAG :: (UPI4_H :: [])) match_gate with
                | Some l4 ->
                  Some
                    (app l2
                      (app ((pDAG q2) :: ((cNOT q1 q2) :: ((p q2) :: []))) l4))
                | None -> None)
          else None
        | _ -> None)
     | None -> None)
  | None -> None

(** val apply_H_equivalence5 :
    int -> pI4_ucom_l -> pI4_Unitary gate_app list option **)

let apply_H_equivalence5 q l =
  match remove_single_qubit_pattern l q (UPI4_H :: (uPI4_PDAG :: []))
          match_gate with
  | Some l1 ->
    (match next_two_qubit_gate l1 q with
     | Some p0 ->
       let (p1, l3) = p0 in
       let (p2, q2) = p1 in
       let (p3, q1) = p2 in
       let (l2, p4) = p3 in
       (match p4 with
        | UPI4_CNOT ->
          if (=) q q2
          then (match remove_single_qubit_pattern l3 q
                        (uPI4_P :: (UPI4_H :: [])) match_gate with
                | Some l4 ->
                  Some
                    (app l2
                      (app ((p q2) :: ((cNOT q1 q2) :: ((pDAG q2) :: []))) l4))
                | None -> None)
          else None
        | _ -> None)
     | None -> None)
  | None -> None

(** val apply_H_equivalence : pI4_ucom_l -> int -> pI4_ucom_l option **)

let apply_H_equivalence l q =
  try_rewrites l
    ((apply_H_equivalence1 q) :: ((apply_H_equivalence2 q) :: ((apply_H_equivalence3
                                                                 q) :: (
    (apply_H_equivalence4 q) :: ((apply_H_equivalence5 q) :: [])))))

(** val apply_H_equivalences : pI4_ucom_l -> int -> pI4_ucom_l **)

let rec apply_H_equivalences l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | g :: t0 ->
      (match g with
       | App1 (p0, q) ->
         (match p0 with
          | UPI4_H ->
            (match apply_H_equivalence l q with
             | Some l' -> apply_H_equivalences l' n'
             | None -> (h q) :: (apply_H_equivalences t0 n'))
          | _ -> g :: (apply_H_equivalences t0 n'))
       | _ -> g :: (apply_H_equivalences t0 n')))
    n

(** val hadamard_reduction : pI4_ucom_l -> pI4_ucom_l **)

let hadamard_reduction l =
  apply_H_equivalences l
    (mul (Pervasives.succ (Pervasives.succ 0)) (length l))

(** val update : (int -> 'a1) -> int -> 'a1 -> int -> 'a1 **)

let update f i x0 j =
  if (=) j i then x0 else f j

(** val add0 : int -> int list -> int list **)

let add0 x0 l =
  if inb x0 l then l else x0 :: l

(** val get_subcircuit' :
    pI4_ucom_l -> int list -> int list -> int -> (pI4_Unitary gate_app
    list * pI4_Unitary gate_app list) * pI4_ucom_l **)

let rec get_subcircuit' l qs blst n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (([], []), l))
    (fun n' ->
    if (=) (length qs) (length blst)
    then (([], []), l)
    else (match next_gate l qs with
          | Some p0 ->
            let (p1, l2) = p0 in
            let (l1, g) = p1 in
            (match g with
             | App1 (u, q) ->
               (match u with
                | UPI4_H ->
                  let (p2, l2') = get_subcircuit' l2 qs (add0 q blst) n' in
                  let (l1', s) = p2 in
                  (((app l1 l1'), (app ((h q) :: []) s)), l2')
                | _ ->
                  let (p2, l2') = get_subcircuit' l2 qs blst n' in
                  let (l1', s) = p2 in
                  (((app l1 l1'), (app ((App1 (u, q)) :: []) s)), l2'))
             | App2 (p2, q1, q2) ->
               (match p2 with
                | UPI4_CNOT ->
                  let qs' = add0 q1 (add0 q2 qs) in
                  let blst' = if inb q1 blst then add0 q2 blst else blst in
                  let (p3, l2') = get_subcircuit' l2 qs' blst' n' in
                  let (l1', s) = p3 in
                  (((app l1 l1'), (app ((cNOT q1 q2) :: []) s)), l2')
                | _ -> (([], []), l))
             | App3 (_, _, _, _) -> (([], []), l))
          | None -> (([], []), l)))
    n

(** val get_subcircuit :
    pI4_ucom_l -> int -> (pI4_Unitary gate_app list * pI4_Unitary gate_app
    list) * pI4_ucom_l **)

let get_subcircuit l q =
  get_subcircuit' l (q :: []) [] (length l)

(** val f_eqb : (int -> bool) -> (int -> bool) -> int -> bool **)

let rec f_eqb f1 f2 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun n' -> (&&) (eqb (f1 n') (f2 n')) (f_eqb f1 f2 n'))
    n

(** val neg : (int -> bool) -> int -> int -> bool **)

let neg f dim i =
  if (=) i dim then negb (f i) else f i

(** val xor : (int -> bool) -> (int -> bool) -> int -> bool **)

let xor f1 f2 i =
  xorb (f1 i) (f2 i)

(** val merge' :
    int -> pI4_ucom_l -> int list -> int -> int -> (int -> int -> bool) ->
    pI4_Unitary gate_app list option **)

let rec merge' dim l blst k q f =
  match l with
  | [] -> None
  | g :: t0 ->
    (match g with
     | App1 (p0, q') ->
       (match p0 with
        | UPI4_H ->
          (match merge' dim t0 (add0 q' blst) k q f with
           | Some l0 -> Some ((h q') :: l0)
           | None -> None)
        | UPI4_X ->
          let f' = if inb q' blst then f else update f q' (neg (f q') dim) in
          (match merge' dim t0 blst k q f' with
           | Some l0 -> Some ((x q') :: l0)
           | None -> None)
        | UPI4_PI4 k' ->
          if (&&) (negb (inb q' blst))
               (f_eqb (f q') (fun x0 -> (=) x0 q)
                 (add dim (Pervasives.succ 0)))
          then let k'' = Z.add k k' in
               if Z.eqb k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
               then Some t0
               else if Z.ltb k'' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                         1)))
                    then Some ((App1 ((UPI4_PI4 k''), q')) :: t0)
                    else Some ((App1 ((UPI4_PI4
                           (Z.sub k'' ((fun p->2*p) ((fun p->2*p)
                             ((fun p->2*p) 1))))), q')) :: t0)
          else (match merge' dim t0 blst k q f with
                | Some l0 -> Some ((App1 ((UPI4_PI4 k'), q')) :: l0)
                | None -> None)
        | UPI4_CNOT -> None)
     | App2 (p0, q1, q2) ->
       (match p0 with
        | UPI4_CNOT ->
          if (||) (inb q1 blst) (inb q2 blst)
          then let blst' = if inb q1 blst then add0 q2 blst else blst in
               (match merge' dim t0 blst' k q f with
                | Some l0 -> Some ((cNOT q1 q2) :: l0)
                | None -> None)
          else let f' = update f q2 (xor (f q1) (f q2)) in
               (match merge' dim t0 blst k q f' with
                | Some l0 -> Some ((cNOT q1 q2) :: l0)
                | None -> None)
        | _ -> None)
     | App3 (_, _, _, _) -> None)

(** val merge :
    int -> pI4_ucom_l -> int -> int -> pI4_Unitary gate_app list option **)

let merge dim l k q =
  let finit = fun i j -> (=) j i in merge' dim l [] k q finit

(** val merge_rotation :
    int -> pI4_ucom_l -> int -> int -> pI4_Unitary gate_app list option **)

let merge_rotation dim l k q =
  let (tmp, l2) = get_subcircuit l q in
  let (l1, s) = tmp in
  (match merge dim s k q with
   | Some s' -> Some (app l1 (app s' l2))
   | None -> None)

(** val merge_rotations' : int -> pI4_ucom_l -> int -> pI4_ucom_l **)

let rec merge_rotations' dim l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | g :: t0 ->
      (match g with
       | App1 (p0, q) ->
         (match p0 with
          | UPI4_PI4 k ->
            (match merge_rotation dim t0 k q with
             | Some l' -> merge_rotations' dim l' n'
             | None ->
               (App1 ((UPI4_PI4 k), q)) :: (merge_rotations' dim t0 n'))
          | _ -> g :: (merge_rotations' dim t0 n'))
       | _ -> g :: (merge_rotations' dim t0 n')))
    n

(** val merge_rotations : int -> pI4_ucom_l -> pI4_ucom_l **)

let merge_rotations dim l =
  merge_rotations' dim l (length l)

(** val propagate_Z :
    pI4_ucom_l -> int -> int -> pI4_Unitary gate_app list **)

let rec propagate_Z l q n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (z q) :: l)
    (fun n' ->
    match l with
    | [] -> (z q) :: []
    | u :: t0 ->
      if does_not_reference_appl q u
      then u :: (propagate_Z t0 q n')
      else (match u with
            | App1 (p0, _) ->
              (match p0 with
               | UPI4_H -> u :: (propagate_X0 t0 q n')
               | UPI4_CNOT -> (z q) :: l
               | _ -> u :: (propagate_Z t0 q n'))
            | App2 (p0, m, n0) ->
              (match p0 with
               | UPI4_CNOT ->
                 if (=) q n0
                 then u :: (propagate_Z (propagate_Z t0 n0 n') m n')
                 else u :: (propagate_Z t0 q n')
               | _ -> (z q) :: l)
            | App3 (_, _, _, _) -> (z q) :: l))
    n

(** val propagate_X0 :
    pI4_ucom_l -> int -> int -> pI4_Unitary gate_app list **)

and propagate_X0 l q n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (x q) :: l)
    (fun n' ->
    match l with
    | [] -> (x q) :: []
    | u :: t0 ->
      if does_not_reference_appl q u
      then u :: (propagate_X0 t0 q n')
      else (match u with
            | App1 (p0, n0) ->
              (match p0 with
               | UPI4_H -> u :: (propagate_Z t0 q n')
               | UPI4_X -> t0
               | UPI4_PI4 k ->
                 (App1 ((UPI4_PI4
                   (Z.sub ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))) k)),
                   n0)) :: (propagate_X0 t0 q n')
               | UPI4_CNOT -> (x q) :: l)
            | App2 (p0, m, n0) ->
              (match p0 with
               | UPI4_CNOT ->
                 if (=) q m
                 then u :: (propagate_X0 (propagate_X0 t0 m n') n0 n')
                 else u :: (propagate_X0 t0 q n')
               | _ -> (x q) :: l)
            | App3 (_, _, _, _) -> (x q) :: l))
    n

(** val not_propagation' : pI4_ucom_l -> int -> pI4_ucom_l **)

let rec not_propagation' l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n' ->
    match l with
    | [] -> []
    | u :: t0 ->
      (match u with
       | App1 (p0, q) ->
         (match p0 with
          | UPI4_X -> let l' = propagate_X0 t0 q n in not_propagation' l' n'
          | _ -> u :: (not_propagation' t0 n'))
       | _ -> u :: (not_propagation' t0 n')))
    n

(** val not_propagation : pI4_ucom_l -> pI4_ucom_l **)

let not_propagation l =
  not_propagation' l (mul (Pervasives.succ (Pervasives.succ 0)) (length l))

(** val optimize : int -> pI4_ucom_l -> pI4_ucom_l **)

let optimize dim l =
  cancel_single_qubit_gates
    (cancel_two_qubit_gates
      (merge_rotations dim
        (cancel_single_qubit_gates
          (hadamard_reduction
            (cancel_two_qubit_gates
              (cancel_single_qubit_gates
                (cancel_two_qubit_gates
                  (hadamard_reduction (not_propagation l)))))))))

(** val optimize_check_for_type_errors :
    int -> pI4_ucom_l -> pI4_ucom_l option **)

let optimize_check_for_type_errors dim l =
  if pI4_list_well_typed_b dim l then Some (optimize dim l) else None
